using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using Sparrow;
using Sparrow.Utils;
using Voron.Data.BTrees;
using Voron.Data.Fixed;
using Voron.Exceptions;
using Voron.Impl.FreeSpace;
using Voron.Impl.Journal;
using Voron.Impl.Paging;
using Voron.Impl.Scratch;
using Voron.Global;
using Voron.Debugging;
using Voron.Util;

namespace Voron.Impl
{
    public interface IPagerLevelTransactionState : IDisposable
    {
        Dictionary<AbstractPager, SparseMemoryMappedPager.TransactionState> SparsePagerTransactionState { get; set; }
        event Action<IPagerLevelTransactionState> OnDispose;
        void EnsurePagerStateReference(PagerState state);
        StorageEnvironment Environment { get; }
    }

    public unsafe class LowLevelTransaction : IPagerLevelTransactionState
    {
        private const int PagesTakenByHeader = 1;

        public readonly AbstractPager DataPager;
        private readonly StorageEnvironment _env;
        private readonly long _id;
        private readonly ByteStringContext _allocator;
        private readonly bool _disposeAllocator;

        private Tree _root;
        public Tree RootObjects => _root;

        public bool FlushedToJournal;

        private readonly WriteAheadJournal _journal;
        internal readonly List<JournalSnapshot> JournalSnapshots = new List<JournalSnapshot>();

        Dictionary<AbstractPager, SparseMemoryMappedPager.TransactionState> IPagerLevelTransactionState.SparsePagerTransactionState
        {
            get;
            set;
        }

        internal class WriteTransactionPool
        {
            public Dictionary<long, PageFromScratchBuffer> ScratchPagesTablePool = new Dictionary<long, PageFromScratchBuffer>(NumericEqualityComparer.Instance);
            public Dictionary<long, long> DirtyOverflowPagesPool = new Dictionary<long, long>(NumericEqualityComparer.Instance);
            public HashSet<long> DirtyPagesPool = new HashSet<long>(NumericEqualityComparer.Instance);

            public void Reset()
            {
                ScratchPagesTablePool.Clear();
                DirtyOverflowPagesPool.Clear();
                DirtyPagesPool.Clear();
            }

        }

        // BEGIN: Structures that are safe to pool.
        private readonly HashSet<long> _dirtyPages;
        private readonly Dictionary<long, long> _dirtyOverflowPages;
        private readonly Stack<long> _pagesToFreeOnCommit;
        private readonly Dictionary<long, PageFromScratchBuffer> _scratchPagesTable;
        private readonly HashSet<PagerState> _pagerStates;
        private readonly Dictionary<int, PagerState> _scratchPagerStates;
        // END: Structures that are safe to pool.


        public event Action<LowLevelTransaction> OnCommit;
        public event Action<IPagerLevelTransactionState> OnDispose;
        public event Action AfterCommitWhenNewReadTransactionsPrevented;

        private readonly IFreeSpaceHandling _freeSpaceHandling;
        internal FixedSizeTree _freeSpaceTree;

        private int _allocatedPagesInTransaction;
        private int _overflowPagesInTransaction;
        private TransactionHeader* _txHeader;

        private PageFromScratchBuffer _transactionHeaderPage;
        private readonly HashSet<PageFromScratchBuffer> _transactionPages;
        private readonly HashSet<long> _freedPages;
        private readonly List<PageFromScratchBuffer> _unusedScratchPages;


        private readonly StorageEnvironmentState _state;

        private CommitStats _requestedCommitStats;

        public TransactionPersistentContext PersistentContext { get; }
        public TransactionFlags Flags { get; }

        public bool IsLazyTransaction
        {
            get { return _isLazyTransaction; }
            set
            {
                _isLazyTransaction = value;
                if (_isLazyTransaction)
                    _env.Journal.HasLazyTransactions = true;
            }
        }

        public StorageEnvironment Environment => _env;

        public long Id => _id;

        public bool Committed { get; private set; }

        public bool RolledBack { get; private set; }

        public StorageEnvironmentState State => _state;

        public ByteStringContext Allocator => _allocator;

        public ulong Hash => _txHeader->Hash;

        public LowLevelTransaction(StorageEnvironment env, long id, TransactionPersistentContext transactionPersistentContext, TransactionFlags flags, IFreeSpaceHandling freeSpaceHandling, ByteStringContext context = null)
        {
            env.AssertNoCatastrophicFailure();

            DataPager = env.Options.DataPager;
            _env = env;
            _journal = env.Journal;
            _id = id;
            _freeSpaceHandling = freeSpaceHandling;
            _allocator = context ?? new ByteStringContext();
            _disposeAllocator = context == null;
            _pagerStates = new HashSet<PagerState>(ReferenceEqualityComparer<PagerState>.Default);

            PersistentContext = transactionPersistentContext;
            Flags = flags;

            var scratchPagerStates = env.ScratchBufferPool.GetPagerStatesOfAllScratches();
            foreach (var scratchPagerState in scratchPagerStates.Values)
            {
                scratchPagerState.AddRef();
                _pagerStates.Add(scratchPagerState);
            }

            if (flags != TransactionFlags.ReadWrite)
            {
                // for read transactions, we need to keep the pager state frozen
                // for write transactions, we can use the current one (which == null)
                _scratchPagerStates = scratchPagerStates;

                _state = env.State.Clone();

                InitializeRoots();

                JournalSnapshots = _journal.GetSnapshots();

                return;
            }

            EnsureNoDuplicateTransactionId(id);

            _env.WriteTransactionPool.Reset();
            _dirtyOverflowPages = _env.WriteTransactionPool.DirtyOverflowPagesPool;
            _scratchPagesTable = _env.WriteTransactionPool.ScratchPagesTablePool;
            _dirtyPages = _env.WriteTransactionPool.DirtyPagesPool;
            _freedPages = new HashSet<long>(NumericEqualityComparer.Instance);
            _unusedScratchPages = new List<PageFromScratchBuffer>();
            _transactionPages = new HashSet<PageFromScratchBuffer>(PageFromScratchBufferEqualityComparer.Instance);
            _pagesToFreeOnCommit = new Stack<long>();

            _state = env.State.Clone();
            InitializeRoots();
            InitTransactionHeader();
        }

        [Conditional("DEBUG")]
        private void EnsureNoDuplicateTransactionId(long id)
        {
            foreach (var journalFile in _journal.Files)
            {
                var lastSeenTxIdByJournal = journalFile.PageTranslationTable.GetLastSeenTransactionId();

                if (id <= lastSeenTxIdByJournal)
                    VoronUnrecoverableErrorException.Raise(_env,
                        $"PTT of journal {journalFile.Number} already contains records for a new write tx. " +
                        $"Tx id = {id}, last seen by journal = {lastSeenTxIdByJournal}");

                if (journalFile.PageTranslationTable.IsEmpty)
                    continue;

                var maxTxIdInJournal = journalFile.PageTranslationTable.MaxTransactionId();

                if (id <= maxTxIdInJournal)
                    VoronUnrecoverableErrorException.Raise(_env,
                        $"PTT of journal {journalFile.Number} already contains records for a new write tx. " +
                        $"Tx id = {id}, max id in journal = {maxTxIdInJournal}");
            }
        }
        internal void UpdateRootsIfNeeded(Tree root)
        {
            //can only happen during initial transaction that creates Root and FreeSpaceRoot trees
            if (State.Root != null)
                return;

            State.Root = root.State;

            _root = root;
        }

        private void InitializeRoots()
        {
            if (_state.Root != null)
            {
                _root = new Tree(this, null, _state.Root) { Name = Constants.RootTreeNameSlice };
            }
        }

        private void InitTransactionHeader()
        {
            var allocation = _env.ScratchBufferPool.Allocate(this, 1);
            var page = _env.ScratchBufferPool.ReadPage(this, allocation.ScratchFileNumber, allocation.PositionInScratchBuffer);

            _transactionHeaderPage = allocation;

            UnmanagedMemory.Set(page.Pointer, 0, Constants.Storage.PageSize);
            _txHeader = (TransactionHeader*)page.Pointer;
            _txHeader->HeaderMarker = Constants.TransactionHeaderMarker;

            _txHeader->TransactionId = _id;
            _txHeader->NextPageNumber = _state.NextPageNumber;
            _txHeader->LastPageNumber = -1;
            _txHeader->PageCount = -1;
            _txHeader->Hash = 0;
            _txHeader->TimeStampTicksUtc = DateTime.UtcNow.Ticks;
            _txHeader->TxMarker = TransactionMarker.None;
            _txHeader->CompressedSize = 0;
            _txHeader->UncompressedSize = 0;

            _allocatedPagesInTransaction = 0;
            _overflowPagesInTransaction = 0;
        }

        internal PageFromScratchBuffer GetTransactionHeaderPage()
        {
            return this._transactionHeaderPage;
        }

        internal HashSet<PageFromScratchBuffer> GetTransactionPages()
        {
            VerifyNoDuplicateScratchPages();
            return _transactionPages;
        }

        internal List<PageFromScratchBuffer> GetUnusedScratchPages()
        {
            return _unusedScratchPages;
        }

        internal HashSet<long> GetFreedPagesNumbers()
        {
            return _freedPages;
        }

        internal Page ModifyPage(long num)
        {
            Debug.Assert(this.Flags == TransactionFlags.ReadWrite);

            _env.AssertNoCatastrophicFailure();

            // Check if we can hit the lowest level locality cache.
            Page currentPage = GetPage(num);

            if (_dirtyPages.Contains(num))
                return currentPage;

            int pageSize;
            Page newPage;
            if (currentPage.IsOverflow)
            {
                newPage = AllocateOverflowRawPage(currentPage.OverflowSize, num, currentPage, zeroPage: false);
                pageSize = Constants.Storage.PageSize *
                           DataPager.GetNumberOfOverflowPages(currentPage.OverflowSize);
            }
            else
            {
                newPage = AllocatePage(1, num, currentPage, zeroPage: false); // allocate new page in a log file but with the same number			
                pageSize = Environment.Options.PageSize;
            }

            Memory.BulkCopy(newPage.Pointer, currentPage.Pointer, pageSize);

            TrackWritablePage(newPage);

            return newPage;
        }

        private const int InvalidScratchFile = -1;
        private PagerStateCacheItem _lastScratchFileUsed = new PagerStateCacheItem(InvalidScratchFile, null);
        private bool _disposed;

        public Page GetPage(long pageNumber)
        {
            if (_disposed)
                throw new ObjectDisposedException("Transaction");

            // Check if we can hit the lowest level locality cache.
            Page p;
            PageFromScratchBuffer value;
            if (_scratchPagesTable != null && _scratchPagesTable.TryGetValue(pageNumber, out value)) // Scratch Pages Table will be null in read transactions
            {
                Debug.Assert(value != null);
                PagerState state = null;
                if (_scratchPagerStates != null)
                {
                    var lastUsed = _lastScratchFileUsed;
                    if (lastUsed.FileNumber == value.ScratchFileNumber)
                    {
                        state = lastUsed.State;
                    }
                    else
                    {
                        state = _scratchPagerStates[value.ScratchFileNumber];
                        _lastScratchFileUsed = new PagerStateCacheItem(value.ScratchFileNumber, state);
                    }
                }

                p = _env.ScratchBufferPool.ReadPage(this, value.ScratchFileNumber, value.PositionInScratchBuffer, state);
                Debug.Assert(p.PageNumber == pageNumber, string.Format("Requested ReadOnly page #{0}. Got #{1} from scratch", pageNumber, p.PageNumber));
            }
            else
            {
                var pageFromJournal = _journal.ReadPage(this, pageNumber, _scratchPagerStates);
                if (pageFromJournal != null)
                {
                    p = pageFromJournal.Value;
                    Debug.Assert(p.PageNumber == pageNumber,
                        string.Format("Requested ReadOnly page #{0}. Got #{1} from journal", pageNumber, p.PageNumber));
                }
                else
                {
                    p = DataPager.ReadPage(this, pageNumber);
                    Debug.Assert(p.PageNumber == pageNumber,
                        string.Format("Requested ReadOnly page #{0}. Got #{1} from data file", pageNumber, p.PageNumber));
                }
            }

            TrackReadOnlyPage(p);

            return p;
        }

        public Page AllocatePage(int numberOfPages, long? pageNumber = null, Page? previousPage = null, bool zeroPage = true)
        {
            if (pageNumber == null)
            {
                pageNumber = _freeSpaceHandling.TryAllocateFromFreeSpace(this, numberOfPages);
                if (pageNumber == null) // allocate from end of file
                {
                    pageNumber = State.NextPageNumber;
                    State.NextPageNumber += numberOfPages;
                }
            }
            return AllocatePage(numberOfPages, pageNumber.Value, previousPage, zeroPage);
        }

        public Page AllocateOverflowRawPage(long pageSize, long? pageNumber = null, Page? previousPage = null, bool zeroPage = true)
        {
            long overflowSize = 0 + pageSize;
            if (overflowSize > int.MaxValue - 1)
                throw new InvalidOperationException($"Cannot allocate chunks bigger than { int.MaxValue / 1024 * 1024 } Mb.");

            Debug.Assert(overflowSize >= 0);

            long numberOfPages = (overflowSize / Constants.Storage.PageSize) + (overflowSize % Constants.Storage.PageSize == 0 ? 0 : 1);

            var overflowPage = AllocatePage((int)numberOfPages, pageNumber, previousPage, zeroPage);
            overflowPage.Flags = PageFlags.Overflow;
            overflowPage.OverflowSize = (int)overflowSize;

            return overflowPage;
        }

        /// <summary>
        /// This method of allocating pages will ensure all pages are going to be allocated one after the other. 
        /// This way of allocating will ensure that pages have data locality among themselves.
        /// </summary>
        /// <param name="numberOfPages">The size of the pages to allocate</param>
        /// <returns>The actual allocated pages.</returns>
        public Page[] AllocatePages(int[] numberOfPages, int? totalPages = null, long? pageNumber = null, bool zeroPage = true)
        {
            if (pageNumber == null)
            {
                if (totalPages == null)
                {
                    totalPages = 0;
                    for (int i = 0; i < numberOfPages.Length; i++)
                        totalPages += i;
                }

                pageNumber = _freeSpaceHandling.TryAllocateFromFreeSpace(this, totalPages.Value);
                if (pageNumber == null) // allocate from end of file
                {
                    pageNumber = State.NextPageNumber;
                    State.NextPageNumber += totalPages.Value;
                }
            }

            var result = new Page[numberOfPages.Length];
            int count = 0;
            for (int i = 0; i < numberOfPages.Length; i++)
            {
                result[i] = AllocatePage(numberOfPages[i], pageNumber + count, zeroPage: zeroPage);
                count += numberOfPages[i];
            }

            if (totalPages.HasValue && count != totalPages.Value)
                throw new InvalidOperationException("The total pages (if passed) must be equal to the actual pages requested.");

            return result;
        }

        private Page AllocatePage(int numberOfPages, long pageNumber, Page? previousVersion, bool zeroPage)
        {
            Debug.Assert(this.Flags == TransactionFlags.ReadWrite);

            if (_disposed)
                throw new ObjectDisposedException("Transaction");

            if (_env.Options.MaxStorageSize.HasValue) // check against quota
            {
                var maxAvailablePageNumber = _env.Options.MaxStorageSize / Constants.Storage.PageSize;

                if (pageNumber > maxAvailablePageNumber)
                    ThrowQuotaExceededException(pageNumber, maxAvailablePageNumber);
            }


            Debug.Assert(pageNumber < State.NextPageNumber);

#if VALIDATE
            VerifyNoDuplicateScratchPages();
#endif
            var pageFromScratchBuffer = _env.ScratchBufferPool.Allocate(this, numberOfPages);
            pageFromScratchBuffer.PreviousVersion = previousVersion;
            _transactionPages.Add(pageFromScratchBuffer);

            _allocatedPagesInTransaction++;
            if (numberOfPages > 1)
            {
                _overflowPagesInTransaction += (numberOfPages - 1);
            }

            _scratchPagesTable[pageNumber] = pageFromScratchBuffer;
            
            _dirtyPages.Add(pageNumber);

            if (numberOfPages > 1)
                _dirtyOverflowPages.Add(pageNumber + 1, numberOfPages - 1);

            if (numberOfPages != 1)
            {
                _env.ScratchBufferPool.EnsureMapped(this,
                    pageFromScratchBuffer.ScratchFileNumber,
                    pageFromScratchBuffer.PositionInScratchBuffer,
                    numberOfPages);
            }

            var newPage = _env.ScratchBufferPool.ReadPage(this, pageFromScratchBuffer.ScratchFileNumber,
                pageFromScratchBuffer.PositionInScratchBuffer);
            
            if (zeroPage)
                UnmanagedMemory.Set(newPage.Pointer, 0, Constants.Storage.PageSize * numberOfPages);

            newPage.PageNumber = pageNumber;
            
            if (numberOfPages > 1)
            {
                newPage.Flags = PageFlags.Overflow;
                newPage.OverflowSize = numberOfPages * this.PageSize;
            }
            else
            {
                newPage.Flags = PageFlags.Single;
            }


            TrackWritablePage(newPage);

#if VALIDATE
            VerifyNoDuplicateScratchPages();
#endif

            return newPage;
        }

        private void ThrowQuotaExceededException(long pageNumber, long? maxAvailablePageNumber)
        {
            throw new QuotaException(
                string.Format(
                    "The maximum storage size quota ({0} bytes) has been reached. " +
                    "Currently configured storage quota is allowing to allocate the following maximum page number {1}, while the requested page number is {2}. " +
                    "To increase the quota, use the MaxStorageSize property on the storage environment options.",
                    _env.Options.MaxStorageSize, maxAvailablePageNumber, pageNumber));
        }

        internal void BreakLargeAllocationToSeparatePages(long pageNumber)
        {
            if (_disposed)
                throw new ObjectDisposedException("Transaction");

            PageFromScratchBuffer value;
            if (_scratchPagesTable.TryGetValue(pageNumber, out value) == false)
                throw new InvalidOperationException("The page " + pageNumber + " was not previous allocated in this transaction");

            if (value.NumberOfPages == 1)
                return;

            _transactionPages.Remove(value);
            _env.ScratchBufferPool.BreakLargeAllocationToSeparatePages(value);
            _allocatedPagesInTransaction += value.NumberOfPages - 1;
            _overflowPagesInTransaction -= value.NumberOfPages - 1;

            for (int i = 0; i < value.NumberOfPages; i++)
            {
                var pageFromScratchBuffer = new PageFromScratchBuffer(value.ScratchFileNumber, value.PositionInScratchBuffer + i, 1, 1);
                _transactionPages.Add(pageFromScratchBuffer);
                _scratchPagesTable[pageNumber + i] = pageFromScratchBuffer;
                _dirtyOverflowPages.Remove(pageNumber + i);
                _dirtyPages.Add(pageNumber + i);

                var newPage = _env.ScratchBufferPool.ReadPage(this, value.ScratchFileNumber, value.PositionInScratchBuffer + i);
                newPage.PageNumber = pageNumber + i;
                newPage.Flags = PageFlags.Single;
                newPage.OverflowSize = 0;
                
                TrackWritablePage(newPage);
            }
        }


        [Conditional("DEBUG")]
        public void VerifyNoDuplicateScratchPages()
        {
            var pageNums = new HashSet<long>();
            foreach (var txPage in _transactionPages)
            {
                var scratchPage = Environment.ScratchBufferPool.ReadPage(this, txPage.ScratchFileNumber,
                    txPage.PositionInScratchBuffer);
                if (pageNums.Add(scratchPage.PageNumber) == false)
                    throw new InvalidDataException("Duplicate page in transaction: " + scratchPage.PageNumber);
            }
        }


        public bool IsDisposed => _disposed;

        public void Dispose()
        {
            if (_disposed)
                return;

            if (!Committed && !RolledBack && Flags == TransactionFlags.ReadWrite)
                Rollback();

            _disposed = true;

            if (Flags == TransactionFlags.ReadWrite)
                _env.WriteTransactionPool.Reset();

            _env.TransactionCompleted(this);

            foreach (var pagerState in _pagerStates)
            {
                pagerState.Release();
            }

            _root?.Dispose();
            _freeSpaceTree?.Dispose();

            if (_disposeAllocator)
                _allocator.Dispose();

            OnDispose?.Invoke(this);
        }

        internal void FreePageOnCommit(long pageNumber)
        {
            _pagesToFreeOnCommit.Push(pageNumber);
        }

        internal void FreePage(long pageNumber)
        {
            if (_disposed)
                throw new ObjectDisposedException("Transaction");

            UntrackPage(pageNumber);
            Debug.Assert(pageNumber >= 0);

            _freeSpaceHandling.FreePage(this, pageNumber);

            _freedPages.Add(pageNumber);

            PageFromScratchBuffer scratchPage;
            if (_scratchPagesTable.TryGetValue(pageNumber, out scratchPage))
            {
                _transactionPages.Remove(scratchPage);
                _unusedScratchPages.Add(scratchPage);

                _scratchPagesTable.Remove(pageNumber);
            }

            long numberOfOverflowPages;

            if (_dirtyPages.Remove(pageNumber))
            {
                _allocatedPagesInTransaction--;
            }
            else if (_dirtyOverflowPages.TryGetValue(pageNumber, out numberOfOverflowPages))
            {
                _overflowPagesInTransaction--;

                _dirtyOverflowPages.Remove(pageNumber);

                if (numberOfOverflowPages > 1) // prevent adding range which length is 0
                    _dirtyOverflowPages.Add(pageNumber + 1, numberOfOverflowPages - 1); // change the range of the overflow page
            }
        }


        private class PagerStateCacheItem
        {
            public readonly int FileNumber;
            public readonly PagerState State;

            public PagerStateCacheItem(int file, PagerState state)
            {
                this.FileNumber = file;
                this.State = state;
            }
        }


        public void Commit()
        {
            if (_disposed)
                throw new ObjectDisposedException("Transaction");

            if (Flags != (TransactionFlags.ReadWrite))
                return; // nothing to do

            if (Committed)
                throw new InvalidOperationException("Cannot commit already committed transaction.");

            if (RolledBack)
                throw new InvalidOperationException("Cannot commit rolled-back transaction.");

            while (_pagesToFreeOnCommit.Count > 0)
            {
                FreePage(_pagesToFreeOnCommit.Pop());
            }
            _txHeader->LastPageNumber = _state.NextPageNumber - 1;
            _state.Root.CopyTo(&_txHeader->Root);

            _txHeader->TxMarker |= TransactionMarker.Commit;

            var totalNumberOfAllocatedPages = _allocatedPagesInTransaction + _overflowPagesInTransaction;
            if (totalNumberOfAllocatedPages > 0 || // nothing changed in this transaction
                                                   // allow call to writeToJournal for flushing lazy tx
                (IsLazyTransaction == false && _journal?.HasDataInLazyTxBuffer() == true))
            {
                // In the case of non-lazy transactions, we must flush the data from older lazy transactions
                // to ensure the sequentiality of the data.
                var numberOfWrittenPages = _journal.WriteToJournal(this, totalNumberOfAllocatedPages + PagesTakenByHeader);
                FlushedToJournal = true;

                if (_requestedCommitStats != null)
                {
                    _requestedCommitStats.NumberOfModifiedPages = totalNumberOfAllocatedPages + PagesTakenByHeader;
                    _requestedCommitStats.NumberOfPagesWrittenToDisk = numberOfWrittenPages;
                }
            }

            // an exception being throw after the transaction has been committed to disk 
            // will corrupt the in memory state, and require us to restart (and recover) to 
            // be in a valid state
            try
            {
                ValidateAllPages();

                // release scratch file page allocated for the transaction header
                _env.ScratchBufferPool.Free(_transactionHeaderPage.ScratchFileNumber, _transactionHeaderPage.PositionInScratchBuffer, null);

                Committed = true;
                _env.TransactionAfterCommit(this);
            }
            catch (Exception e)
            {
                _env.CatastrophicFailure = ExceptionDispatchInfo.Capture(e);

                throw;
            }
            OnCommit?.Invoke(this);
        }


        public void Rollback()
        {
            if (_disposed)
                throw new ObjectDisposedException("Transaction");


            if (Committed || RolledBack || Flags != (TransactionFlags.ReadWrite))
                return;

            ValidateReadOnlyPages();

            foreach (var pageFromScratch in _transactionPages)
            {
                _env.ScratchBufferPool.Free(pageFromScratch.ScratchFileNumber, pageFromScratch.PositionInScratchBuffer, null);
            }

            foreach (var pageFromScratch in _unusedScratchPages)
            {
                _env.ScratchBufferPool.Free(pageFromScratch.ScratchFileNumber, pageFromScratch.PositionInScratchBuffer, null);
            }

            // release scratch file page allocated for the transaction header
            _env.ScratchBufferPool.Free(_transactionHeaderPage.ScratchFileNumber, _transactionHeaderPage.PositionInScratchBuffer, null);

            _env.ScratchBufferPool.UpdateCacheForPagerStatesOfAllScratches();
            _env.Journal.UpdateCacheForJournalSnapshots();

            RolledBack = true;
        }
        public void RetrieveCommitStats(out CommitStats stats)
        {
            _requestedCommitStats = stats = new CommitStats();
        }

        private PagerState _lastState;
        private bool _isLazyTransaction;

        internal ActiveTransactions.Node ActiveTransactionNode;
        internal bool FlushInProgressLockTaken;

        public void EnsurePagerStateReference(PagerState state)
        {
            if (state == _lastState || state == null)
                return;

            _lastState = state;
            if (_pagerStates.Add(state) == false)
                return;
            state.AddRef();
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal void OnAfterCommitWhenNewReadTransactionsPrevented()
        {
            // the event cannot be called outside this class while we need to call it in StorageEnvironment.TransactionAfterCommit
            AfterCommitWhenNewReadTransactionsPrevented?.Invoke();
        }


#if VALIDATE_PAGES

        private Dictionary<long, ulong> readOnlyPages = new Dictionary<long, ulong>();
        private Dictionary<long, ulong> writablePages = new Dictionary<long, ulong>();

        private void ValidateAllPages()
        {
            ValidateWritablePages();
            ValidateReadOnlyPages();
        }

        private void ValidateReadOnlyPages()
        {
            foreach (var readOnlyKey in readOnlyPages)
            {
                long pageNumber = readOnlyKey.Key;
                if (_dirtyPages.Contains(pageNumber))
                    VoronUnrecoverableErrorException.Raise(_env, "Read only page is dirty (which means you are modifying a page directly in the data -- non transactionally -- ).");

                var page = this.GetPage(pageNumber);

                ulong pageHash = Hashing.XXHash64.Calculate(page.Pointer, (ulong)Environment.Options.PageSize);
                if (pageHash != readOnlyKey.Value)
                    VoronUnrecoverableErrorException.Raise(_env, "Read only page content is different (which means you are modifying a page directly in the data -- non transactionally -- ).");
            }
        }

        private void ValidateWritablePages()
        {
            foreach (var writableKey in writablePages)
            {
                long pageNumber = writableKey.Key;
                if (!_dirtyPages.Contains(pageNumber))
                    VoronUnrecoverableErrorException.Raise(_env, "Writable key is not dirty (which means you are asking for a page modification for no reason).");
            }
        }

        private void UntrackPage(long pageNumber)
        {
            readOnlyPages.Remove(pageNumber);
            writablePages.Remove(pageNumber);
        }

        private void TrackWritablePage(Page page)
        {
            if (readOnlyPages.ContainsKey(page.PageNumber))
                readOnlyPages.Remove(page.PageNumber);

            if (!writablePages.ContainsKey(page.PageNumber))
            {
                ulong pageHash = Hashing.XXHash64.Calculate(page.Pointer, (ulong)Environment.Options.PageSize);
                writablePages[page.PageNumber] = pageHash;
            }
        }

        private void TrackReadOnlyPage(Page page)
        {
            if (writablePages.ContainsKey(page.PageNumber))
                return;

            ulong pageHash = Hashing.XXHash64.Calculate(page.Pointer, (ulong)Environment.Options.PageSize);

            ulong storedHash;
            if (readOnlyPages.TryGetValue(page.PageNumber, out storedHash))
            {
                if (pageHash != storedHash)
                    VoronUnrecoverableErrorException.Raise(_env, "Read Only Page has change between tracking requests. Page #" + page.PageNumber);
            }
            else
            {
                readOnlyPages[page.PageNumber] = pageHash;
            }
        }

#else
        // This will only be used as placeholder for compilation when not running with validation started.

        [Conditional("VALIDATE_PAGES")]
        private void ValidateAllPages() { }

        [Conditional("VALIDATE_PAGES")]
        private void ValidateReadOnlyPages() { }

        [Conditional("VALIDATE_PAGES")]
        private void TrackWritablePage(Page page) { }

        [Conditional("VALIDATE_PAGES")]
        private void TrackReadOnlyPage(Page page) { }

        [Conditional("VALIDATE_PAGES")]
        private void UntrackPage(long pageNumber) { }
#endif
    }
}