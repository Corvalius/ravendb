﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading.Tasks;
using Sparrow;
using Voron.Data.BTrees.Cedar;
using Voron.Impl;

namespace Voron.Data.BTrees
{
    /// <summary>
    /// Each CedarPage is composed of the following components:
    /// - Header
    /// - BlocksMetadata (in the header page)
    /// - BlocksPages with as many as <see cref="CedarRootHeader.NumberOfBlocksPages"/>
    ///     - NodeInfo sequence
    ///     - Node sequence
    /// - TailPages with as many as <see cref="CedarRootHeader.NumberOfTailPages"/>
    /// - NodesPages with as many as <see cref="CedarRootHeader.NumberOfDataNodePages"/>    
    /// </summary>
    public unsafe partial class CedarPage
    {
        public struct HeaderAccessor
        {
            private readonly CedarPage _page;
            private PageHandlePtr _currentPtr;
            public CedarPageHeader* Ptr;

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public HeaderAccessor(CedarPage page, PageHandlePtr pagePtr)
            {
                _page = page;
                _currentPtr = pagePtr;

                Ptr = (CedarPageHeader*)_currentPtr.Value.Pointer;
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void SetWritable()
            {
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetMainPage(true);

                Ptr = (CedarPageHeader*)_currentPtr.Value.Pointer;
            }
        }

        public struct DataAccessor
        {
            private readonly CedarPage _page;
            private PageHandlePtr _currentPtr;

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public DataAccessor(CedarPage page)
            {
                _page = page;
                _currentPtr = _page.GetDataNodesPage();
            }

            public CedarDataPtr* DirectRead(long i = 0)
            {
                return (CedarDataPtr*)_currentPtr.Value.DataPointer + sizeof(int) + i;
            }

            public CedarDataPtr* DirectWrite(long i = 0)
            {
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetDataNodesPage(true);

                return (CedarDataPtr*)_currentPtr.Value.DataPointer + sizeof(int) + i;
            }

            internal int NextFree
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return *_currentPtr.Value.DataPointer; }
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                set { *(int*)_currentPtr.Value.DataPointer = value; }
            }

            public bool TryAllocateNode(out int index, out CedarDataPtr* ptr)
            {
                // If there are no more allocable nodes, we fail.
                if (NextFree == -1)
                {
                    index = -1;                 
                    ptr = null;
                    return false;
                }

                // We need write access.
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetDataNodesPage(true);

                index = NextFree;
                ptr = (CedarDataPtr*)_currentPtr.Value.DataPointer + sizeof(int) + index;

                Debug.Assert(index >= 0, "Index cannot be negative.");
                Debug.Assert(index < _page.Header.Ptr->DataNodesPerPage, "Index cannot be bigger than the quantity of nodes available to use.");
                Debug.Assert(ptr->IsFree);

                // We will store in the data pointer the next free.
                NextFree = (int) ptr->Data;
                ptr->IsFree = false;

                return true;
            }

            public void FreeNode(int index)
            {
                Debug.Assert(index >= 0, "Index cannot be negative.");
                Debug.Assert(index < _page.Header.Ptr->DataNodesPerPage, "Index cannot be bigger than the quantity of nodes available to use.");

                // We need write access.
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetDataNodesPage(true);

                var ptr = (CedarDataPtr*)_currentPtr.Value.DataPointer + sizeof(int) + index;
                Debug.Assert(!ptr->IsFree);

                int currentFree = NextFree;

                ptr->IsFree = true;
                ptr->Data = currentFree;

                NextFree = index;
            }
        }

        protected struct BlocksAccessor
        {
            private readonly CedarPage _page;
            private PageHandlePtr _currentPtr;
            private PageHandlePtr _currentMetadataPtr;

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public BlocksAccessor(CedarPage page)
            {
                _page = page;
                _currentMetadataPtr = _page.GetBlocksMetadataPage();
                _currentPtr = _page.GetBlocksPage();
            }

            /// <summary>
            /// Returns the first <see cref="Node"/>. CAUTION: Can only be used for reading, use DirectWrite if you need to write to it.
            /// </summary>
            internal Node* Nodes
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return (Node*)DirectRead<Node>(); }
            }

            /// <summary>
            /// Returns the first <see cref="NodeInfo"/>. CAUTION: Can only be used for reading, use DirectWrite if you need to write to it.
            /// </summary>
            internal NodeInfo* NodesInfo
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return (NodeInfo*)DirectRead<NodeInfo>(); }
            }

            /// <summary>
            /// Returns the first <see cref="BlockMetadata"/>. CAUTION: Can only be used for reading, use DirectWrite if you need to write to it.
            /// </summary>
            internal BlockMetadata* Metadata
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return (BlockMetadata*)DirectRead<BlockMetadata>(); }
            }


            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void* DirectRead<T>(long i = 0) where T : struct
            {
                if (typeof(T) == typeof(BlockMetadata))
                {
                    return ((BlockMetadata*)_currentMetadataPtr.Value.Pointer + _page.Header.Ptr->MetadataOffset) + i;
                }

                if (typeof(T) == typeof(NodeInfo))
                {
                    return (NodeInfo*)_currentPtr.Value.DataPointer + i;
                }

                // We prefer the Node to go last because sizeof(NodeInfo) == 2 therefore we only shift _blocksPerPage instead of multiply.
                if (typeof(T) == typeof(Node))
                {
                    return (Node*)(_currentPtr.Value.DataPointer + sizeof(NodeInfo) * _page.Header.Ptr->BlocksPerPage) + i;
                }

                throw new NotSupportedException("Access type not supported by this accessor.");
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void* DirectWrite<T>(long i = 0) where T : struct
            {
                if (typeof(T) == typeof(BlockMetadata))
                {
                    if (!_currentMetadataPtr.IsWritable)
                        _currentMetadataPtr = _page.GetBlocksMetadataPage(true);

                    return ((BlockMetadata*)_currentMetadataPtr.Value.Pointer + _page.Header.Ptr->MetadataOffset) + i;
                }

                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetBlocksPage(true);

                if (typeof(T) == typeof(NodeInfo))
                {
                    return (NodeInfo*)_currentPtr.Value.DataPointer + i;
                }

                // We prefer the Node to go last because sizeof(NodeInfo) == 2 therefore we only shift _blocksPerPage instead of multiply.
                if (typeof(T) == typeof(Node))
                {
                    return (Node*)(_currentPtr.Value.DataPointer + sizeof(NodeInfo) * _page.Header.Ptr->BlocksPerPage) + i;
                }

                throw new NotSupportedException("Access type not supported by this accessor.");
            }
        }

        protected struct Tail0Accessor
        {
            private readonly CedarPage _page;
            private PageHandlePtr _currentPtr;

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public Tail0Accessor(CedarPage page)
            {
                _page = page;
                _currentPtr = _page.GetMainPage();
            }

            public int Length
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return this[0]; }
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                set { this[0] = value; }
            }

            public int this[long i]
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get
                {
                    int* ptr = (int*)(_currentPtr.Value.Pointer + _page.Header.Ptr->Tail0Offset);
                    return *(ptr + i);
                }
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                set
                {
                    SetWritable();

                    int* ptr = (int*)(_currentPtr.Value.Pointer + _page.Header.Ptr->Tail0Offset);
                    *(ptr + i) = value;
                }
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void SetWritable()
            {
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetMainPage(true);
            }

        }

        protected struct TailAccessor
        {
            private readonly CedarPage _page;
            private PageHandlePtr _currentPtr;


            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public TailAccessor(CedarPage page)
            {
                _page = page;
                _currentPtr = _page.GetTailPage();
            }

            public int Length
            {
                get { return *(int*)_currentPtr.Value.DataPointer; }
                set
                {
                    if (!_currentPtr.IsWritable)
                        _currentPtr = _page.GetTailPage(true);

                    *(int*)_currentPtr.Value.DataPointer = value;
                }
            }

            public byte this[int i]
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return *(_currentPtr.Value.DataPointer + i); }
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                set
                {
                    if (!_currentPtr.IsWritable)
                        _currentPtr = _page.GetTailPage(true);

                    *(_currentPtr.Value.DataPointer + i) = value;
                }
            }

            public byte this[long i]
            {
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                get { return *(_currentPtr.Value.DataPointer + i); }
                [MethodImpl(MethodImplOptions.AggressiveInlining)]
                set
                {
                    if (!_currentPtr.IsWritable)
                        _currentPtr = _page.GetTailPage(true);

                    *(_currentPtr.Value.DataPointer + i) = value;
                }
            }

            public byte* DirectRead(long i = 0)
            {
                return _currentPtr.Value.DataPointer + i;
            }

            public byte* DirectWrite(long i = 0)
            {
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetTailPage(true);

                return _currentPtr.Value.DataPointer + i;
            }

            public void SetWritable()
            {
                if (!_currentPtr.IsWritable)
                    _currentPtr = _page.GetTailPage(true);
            }
        }



        internal const int BlockSize = 256;

        private readonly LowLevelTransaction _llt;
        private readonly PageLocator _pageLocator;
        private Page _mainPage;

        public HeaderAccessor Header;
        protected BlocksAccessor Blocks;
         TailAccessor Tail;
        protected Tail0Accessor Tail0;
        public DataAccessor Data;        

        public CedarPage(LowLevelTransaction llt, long pageNumber, CedarPage page = null)
        {
            this._llt = llt;
            this._pageLocator = new PageLocator(_llt);

            if (page != null)
            {
                Debug.Assert(page.PageNumber == pageNumber);
                this._mainPage = page._mainPage;
            }
            else
            {
                this._mainPage = _pageLocator.GetReadOnlyPage(pageNumber);
            }

            this.Header = new HeaderAccessor(this, new PageHandlePtr(this._mainPage, false));
            this.Blocks = new BlocksAccessor(this);
            this.Tail = new TailAccessor(this);
            this.Tail0 = new Tail0Accessor(this);
            this.Data = new DataAccessor(this);            
        }

        public long PageNumber
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get { return Header.Ptr->PageNumber; }
        }

        public bool IsBranch
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get { return Header.Ptr->IsBranchPage; }
        }

        public bool IsLeaf
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get { return !Header.Ptr->IsBranchPage; }
        }

        public static CedarPage Allocate(LowLevelTransaction llt, int[] layout, int totalNumberOfPages)
        {
            var pages = llt.AllocatePages(layout, totalNumberOfPages);

            // Bulk zero out the pages. 
            foreach (var page in pages)
            {
                byte* ptr = page.DataPointer;
                Memory.Set(ptr, 0, page.OverflowSize - sizeof(PageHeader));
            }

            var header = (CedarPageHeader*) pages[0].Pointer;

            // We do not allow changing the amount of pages because of now we will consider them constants.
            header->BlocksPageCount = CedarRootHeader.NumberOfBlocksPages;
            header->BlocksPerPage = (llt.PageSize * header->BlocksPageCount - sizeof(PageHeader)) / (sizeof(Node) + sizeof(NodeInfo));

            header->TailPageCount = CedarRootHeader.NumberOfTailPages;
            header->TailBytesPerPage = llt.PageSize * header->TailPageCount - sizeof(PageHeader);

            header->DataPageCount = CedarRootHeader.NumberOfDataNodePages;
            header->DataNodesPerPage = (llt.PageSize * header->DataPageCount - sizeof(PageHeader) - sizeof(int)) / sizeof(CedarDataPtr);

            return new CedarPage(llt, pages[0].PageNumber);
        }

        internal void Initialize()
        {
            Header.SetWritable();

            CedarPageHeader* header = Header.Ptr;

            // We make sure we do now account for any block that is not complete. 
            header->Size = BlockSize;
            header->Capacity = header->BlocksPerPage - (header->BlocksPerPage % BlockSize);

            // Aligned to 16 bytes
            int offset = sizeof(CedarPageHeader*) + 16;
            header->MetadataOffset = offset - offset % 16;
            header->Tail0Offset = header->MetadataOffset + (header->BlocksPerPage + 1) / BlockSize * sizeof(BlockMetadata);

            Debug.Assert(header->Tail0Offset < _llt.PageSize - 1024); // We need at least 1024 bytes for it. 
        
            for (int i = 0; i < BlockSize; i++)
                header->Reject[i] = (short)(i + 1);

            // Request for writing all the pages. 
            var array = (Node*)Blocks.DirectWrite<Node>();
            var block = (BlockMetadata*)Blocks.DirectWrite<BlockMetadata>();
            var data = Data.DirectWrite();

            array[0] = new Node(0, -1);
            for (int i = 1; i < 256; ++i)
                array[i] = new Node(i == 1 ? -255 : -(i - 1), i == 255 ? -1 : -(i + 1));

            // Create a default block
            block[0] = BlockMetadata.Create();
            block[0].Ehead = 1; // bug fix for erase

            // Initialize the free data node linked list.
            int count = Header.Ptr->DataNodesPerPage - 1;            
            for (int i = 0; i < count; i++)
            {
                // Link the current node to the next.
                data->Header = CedarDataPtr.FreeNode;
                data->Data = i + 1;

                data++;
            }

            // Close the linked list.
            data->Header = CedarDataPtr.FreeNode;
            data->Data = -1;

            Debug.Assert(Data.DirectRead(Header.Ptr->DataNodesPerPage - 1)->IsFree, "Last node is not free.");
            Debug.Assert(Data.DirectRead(Header.Ptr->DataNodesPerPage - 1)->Data == -1, "Free node linked list does not end.");            

            Data.NextFree = 0;


            Tail.Length = sizeof(int);

        }


        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private PageHandlePtr GetMainPage(bool writable = false)
        {
            if (writable)
                Debug.Assert(_llt.Flags == TransactionFlags.ReadWrite, "Create is being called in a read transaction.");

            this._mainPage = writable ?
                _pageLocator.GetWritablePage(_mainPage.PageNumber) :
                _pageLocator.GetReadOnlyPage(_mainPage.PageNumber);

            return new PageHandlePtr(_mainPage, writable);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private PageHandlePtr GetBlocksPage(bool writable = false)
        {
            if (writable)
                Debug.Assert(_llt.Flags == TransactionFlags.ReadWrite, "Create is being called in a read transaction.");

            long pageNumber = Header.Ptr->BlocksPageNumber;
            return writable ?
                new PageHandlePtr(_pageLocator.GetWritablePage(pageNumber), true) :
                new PageHandlePtr(_pageLocator.GetReadOnlyPage(pageNumber), false);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private PageHandlePtr GetTailPage(bool writable = false)
        {
            if (writable)
                Debug.Assert(_llt.Flags == TransactionFlags.ReadWrite, "Create is being called in a read transaction.");

            long pageNumber = Header.Ptr->TailPageNumber;
            return writable ?
                new PageHandlePtr(_pageLocator.GetWritablePage(pageNumber), true) :
                new PageHandlePtr(_pageLocator.GetReadOnlyPage(pageNumber), false);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private PageHandlePtr GetDataNodesPage(bool writable = false)
        {
            if (writable)
                Debug.Assert(_llt.Flags == TransactionFlags.ReadWrite, "Create is being called in a read transaction.");

            long pageNumber = Header.Ptr->NodesPageNumber;
            return writable ?
                new PageHandlePtr(_pageLocator.GetWritablePage(pageNumber), true) :
                new PageHandlePtr(_pageLocator.GetReadOnlyPage(pageNumber), false);
        }


        private PageHandlePtr GetBlocksMetadataPage(bool writable = false)
        {
            if (writable)
                Debug.Assert(_llt.Flags == TransactionFlags.ReadWrite, "Create is being called in a read transaction.");

            long pageNumber = _mainPage.PageNumber;
            return writable ?
                new PageHandlePtr(_pageLocator.GetWritablePage(pageNumber), true) :
                new PageHandlePtr(_pageLocator.GetReadOnlyPage(pageNumber), false);
        }

    }

}
