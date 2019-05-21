using Sparrow.Collections.Cedar;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading.Tasks;

namespace Sparrow.Collections
{
    namespace Cedar
    {
        public struct ValueRef<T> : ICedarResult<T>
           where T : struct
        {
            public T Value;

            void ICedarResult<T>.SetResult(T value, int length, long pos)
            {
                Value = value;
            }
        }

        public struct ValuePair<T> : ICedarResult<T>
            where T : struct
        {
            public T Value;
            public int Length; // prefix length

            void ICedarResult<T>.SetResult(T value, int length, long pos)
            {
                Value = value;
                Length = length;
            }
        }

        public struct ValueTuple<T> : ICedarResult<T>  // for predict ()
            where T : struct
        {
            public T Value;
            public int Length; // suffix length
            public long Node; // node id of value

            void ICedarResult<T>.SetResult(T value, int length, long pos)
            {
                Value = value;
                Length = length;
                Node = pos;
            }
        }

        public interface IOrderableDirective { }
        public struct Ordered : IOrderableDirective { };
        public struct Unordered : IOrderableDirective { };

        public enum ErrorCode : short
        {
            Success = 0,
            NoValue = -1,
            NoPath = -2
        }
    }

    public interface ICedarResult<T> where T : struct
    {
        void SetResult(T value, int length, long pos);
    };

    public class CedarTrie : CedarTrie<int>
    { }

    public class CedarTrie<T> : CedarTrie<T, Ordered> where T : struct
    { }

    public unsafe class CedarTrie<T, TOrdered> : IDisposable
        where T : struct
        where TOrdered : IOrderableDirective
    {
        protected readonly int _nodeSize;
        protected readonly int _tSize;
        protected readonly int _maxTrial = 1;

        private const long TAIL_OFFSET_MASK = 0xffffffff;
        private const long NODE_INDEX_MASK = 0xffffffff << 32;

        public CedarTrie()
        {
            _tSize = Unsafe.SizeOf<T>();
            Debug.Assert(_tSize <= sizeof(int), "Value types bigger than 4 bytes are not supported yet");

            // This is the internal size of the CedarNode<T>
            // The SizeOf<T> function wont work if we use a generic struct (even if the type size is not dependent on T). 
            _nodeSize = Unsafe.SizeOf<node>();

            Initialize();
        }

        private int MAX_ALLOC_SIZE = 256;

        private node[] _array;
        private ninfo[] _ninfo;
        private block[] _block;

        private int _bheadF;  // first block of Full;   0
        private int _bheadC;  // first block of Closed; 0 if no Closed
        private int _bheadO;  // first block of Open;   0 if no Open

        private int _quota;
        private int _quota0;

        private int _no_delete;

        private readonly short[] _reject = new short[257];

        private ElementUnion u1;
        private SizeUnion u2;

        public int Capacity { get; private set; }
        public int Size { get; private set; }
        public int Length { get; private set; }

        public int AllocatedSize => _array.Length * sizeof(node) + _ninfo.Length * sizeof(ninfo) + 
                                    _block.Length * sizeof(block) + u1.Tail.Length + u2.Tail0.Length + 
                                    _reject.Length * sizeof(short);

        public int AllocatedSize64Kb => _array.Length * sizeof(node) / 2 + _ninfo.Length * sizeof(ninfo) +
                                        _block.Length * sizeof(block) + u1.Tail.Length + u2.Tail0.Length +
                                        _reject.Length * sizeof(short);

        public void DumpInformation64Kb()
        {
            Console.WriteLine($"Estimated size within 64Kb pages");
            Console.WriteLine($"Nodes = {_array.Length} ({_array.Length * sizeof(node) / 2})");
            Console.WriteLine($"Nodes Info = {_ninfo.Length} ({_ninfo.Length * sizeof(ninfo)})");
            Console.WriteLine($"Blocks = {_block.Length} ({_block.Length * sizeof(block)})");
            Console.WriteLine($"Tail = {u1.Tail.Length} ({u1.Tail.Length})");
            Console.WriteLine($"Tail0 = {u2.Tail0.Length} ({u2.Tail0.Length * sizeof(int)})");
        }

        public void DumpInformation()
        {
            Console.WriteLine($"Nodes = {_array.Length} ({_array.Length * sizeof(node)})");
            Console.WriteLine($"Nodes Info = {_ninfo.Length} ({_ninfo.Length * sizeof(ninfo)})");
            Console.WriteLine($"Blocks = {_block.Length} ({_block.Length * sizeof(block)})");
            Console.WriteLine($"Tail = {u1.Tail.Length} ({u1.Tail.Length})");
            Console.WriteLine($"Tail0 = {u2.Tail0.Length} ({u2.Tail0.Length * sizeof(int)})");
        }

        public int TotalSize => _nodeSize * Size;
        public int UnitSize => _nodeSize;

        public int NonZeroSize
        {
            get
            {
                int i = 0;
                for (int to = 0; to < Size; to++)
                {
                    if (_array[to].Check >= 0)
                        i++;
                }
                return i;
            }
        }

        public int NonZeroLength
        {
            get
            {
                int i = 0;
                int j = 0;

                for (int to = 0; to < Size; to++)
                {
                    node n = _array[to];
                    if (n.Check >= 0 && _array[n.Check].Base != to && n.Base < 0)
                    {
                        j++;

                        for (int index = -n.Base; u1.Tail[index] != 0; index++)
                            i++;
                    }
                }

                return i + j * (1 + _tSize);
            }
        }

        public int NumberOfKeys
        {
            get
            {
                int i = 0;
                for (int to = 0; to < Size; to++)
                {
                    node n = _array[to];
                    if (n.Check >= 0 && (_array[n.Check].Base == to || n.Base < 0))
                        i++;
                }

                return i;
            }
        }

        public ErrorCode ExactMatchSearch(byte[] key, out T result, int from = 0)
        {
            fixed (byte* keyPtr = key)
            {
                ValueRef<T> r;
                var errorCode = ExactMatchSearch(keyPtr, key.Length, out r, from);
                result = r.Value;

                return errorCode;
            }
        }

        public ErrorCode ExactMatchSearch(byte* key, int len, out T result, int from = 0)
        {
            ValueRef<T> r;
            var errorCode = ExactMatchSearch(key, len, out r, from);
            result = r.Value;

            return errorCode;
        }

        public ErrorCode ExactMatchSearch<TResult>(byte[] key, out TResult result, int from = 0)
            where TResult : struct, ICedarResult<T>
        {
            fixed (byte* keyPtr = key)
                return ExactMatchSearch(keyPtr, key.Length, out result, from);
        }

        public ErrorCode ExactMatchSearch<TResult>(byte* key, int size, out TResult value, long from = 0)
            where TResult : struct, ICedarResult<T>
        {
            long pos = 0;

            var errorCode = _find(key, ref from, ref pos, size, out T r);
            if (errorCode == ErrorCode.NoPath)
                errorCode = ErrorCode.NoValue;

            value = default(TResult);
            value.SetResult(r, size, from);

            return errorCode;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private ErrorCode _find(byte* key, ref long from, ref long pos, int len, out T result)
        {
            result = default(T);

            long offset = from >> 32;
            if (offset == 0)
            {
                // node on trie
                ref node array = ref _array[0];

                for (byte* key_ = key; Unsafe.Add(ref array, (int)from).Base >= 0;)
                {
                    if (pos == len)
                    {
                        int offset_ = Unsafe.Add(ref array, (int)from).Base ^ 0;
                        ref node n = ref Unsafe.Add(ref array, offset_);
                        if (n.Check != from)
                            return ErrorCode.NoValue;

                        result = GetNodeValue(ref n);
                        return ErrorCode.Success;
                    }

                    int to = Unsafe.Add(ref array, (int)from).Base ^ key_[pos];
                    if (Unsafe.Add(ref array, to).Check != from)
                        return ErrorCode.NoPath;

                    pos++;
                    from = to;
                }

                offset = -Unsafe.Add(ref array, (int)from).Base;
            }

            // switch to _tail to match suffix
            long pos_orig = pos; // start position in reading _tail


            ref byte tailPtr = ref u1.Tail[0];
            {
                ref byte tail = ref Unsafe.Add(ref tailPtr, (int) (offset - pos));

                if (pos < len)
                {
                    do
                    {
                        
                        if (key[pos] != Unsafe.Add(ref tail, (int)pos))
                            break;
                    }
                    while (++pos < len);

                    long moved = pos - pos_orig;
                    if (moved != 0)
                    {
                        from &= TAIL_OFFSET_MASK;
                        from |= (offset + moved) << 32;
                    }

                    if (pos < len)
                        return ErrorCode.NoPath; // input > tail, input != tail
                }

                if (Unsafe.Add(ref tail, (int)pos) != 0)
                    return ErrorCode.NoValue; // input < tail

                
                result = (T)(object)*(int*)Unsafe.AsPointer(ref Unsafe.Add(ref tail, len + 1));
                return ErrorCode.Success;
            }
        }

        public List<ValuePair<T>> CommonPrefixSearch(byte* key, int size, int count, long from = 0)
        {
            return CommonPrefixSearch<ValuePair<T>>(key, size, count, from);
        }

        public List<ValuePair<T>> CommonPrefixSearch(byte[] key, int count, long from = 0)
        {
            return CommonPrefixSearch<ValuePair<T>>(key, count, from);
        }

        public List<TResult> CommonPrefixSearch<TResult>(byte[] key, int count, long from = 0)
            where TResult : struct, ICedarResult<T>
        {
            fixed (byte* keyPtr = key)
                return CommonPrefixSearch<TResult>(keyPtr, key.Length, count, from);
        }

        public List<TResult> CommonPrefixSearch<TResult>(byte* key, int size, int count, long from = 0)
            where TResult : struct, ICedarResult<T>
        {
            var collection = new List<TResult>();

            int num = 0;
            for (long pos = 0; pos < size;)
            {
                T r;
                var errorCode = _find(key, ref from, ref pos, size, out r);

                if (errorCode == ErrorCode.NoValue)
                    continue;
                if (errorCode == ErrorCode.NoPath)
                    return collection;

                if (num >= count)
                    return collection;

                TResult item = default(TResult);
                item.SetResult(r, (int)pos, from);
                collection.Add(item);
            }

            return collection;
        }

        public List<ValuePair<T>> CommonPrefixPredict(byte* key, int size, int count, long from = 0)
        {
            return CommonPrefixPredict<ValuePair<T>>(key, size, count, from);
        }

        public List<ValuePair<T>> CommonPrefixPredict(byte[] key, int count, long from = 0)
        {
            return CommonPrefixPredict<ValuePair<T>>(key, count, from);
        }

        public List<TResult> CommonPrefixPredict<TResult>(byte[] key, int count, long from = 0)
            where TResult : struct, ICedarResult<T>
        {
            fixed (byte* keyPtr = key)
                return CommonPrefixPredict<TResult>(keyPtr, key.Length, count, from);
        }

        public List<TResult> CommonPrefixPredict<TResult>(byte* key, int size, int count, long from = 0)
            where TResult : struct, ICedarResult<T>
        {
            long pos = 0;
            long p = 0;

            var collection = new List<TResult>();

            T r;
            if (_find(key, ref from, ref pos, size, out r) == ErrorCode.NoPath)
                return collection;

            // From now contains the starting point. 
            long root = from;

            int num = 0;
            for (var b = Begin(ref from, ref p); b.Error != ErrorCode.NoPath; b = Next(ref from, ref p, root), num++)
            {
                if (num >= count)
                    return collection;

                TResult item = default(TResult);
                item.SetResult(b.Value, (int)p, from);
                collection.Add(item);
            }

            return collection;
        }

        public bool Remove(byte[] key)
        {
            fixed (byte* keyPtr = key)
                return Remove(keyPtr, key.Length);
        }

        public bool Remove(byte* key, int len, long from = 0)
        {
            //Console.WriteLine($"Begin Erase with len={len}");
            long pos = 0;

            T value;
            var i = _find(key, ref from, ref pos, len, out value);
            if (i != ErrorCode.Success)
                return false;

            if (from >> 32 != 0)
            {
                // leave tail as is
                from &= TAIL_OFFSET_MASK;
            }

            bool flag = _array[from].Base < 0; // have siblings
            int e = flag ? (int)from : _array[from].Base ^ 0;
            from = _array[e].Check;

            //Console.WriteLine($"flag={(flag ? 1 : 0)}, e={e}, from={from} (erase)");

            do
            {
                node n = _array[from];

                //Console.WriteLine($"n.Base={n.Base}, _ninfo[{from}].Child={_ninfo[from].Child} (erase)");
                //Console.WriteLine($"_ninfo[{(n.Base ^ _ninfo[from].Child)}].Sibling={_ninfo[n.Base ^ _ninfo[from].Child].Sibling} (erase)");

                flag = _ninfo[n.Base ^ _ninfo[from].Child].Sibling != 0;

                //Console.WriteLine($"flag={(flag ? 1 : 0)}, e={e}, from={from}, n.Base={n.Base}, n.Check={n.Check} (erase)");

                if (flag)
                    _pop_sibling(from, n.Base, (byte)(n.Base ^ e));

                _push_enode(e);
                e = (int)from;
                from = _array[from].Check;
            }
            while (!flag);

            //Console.WriteLine($"_ninfo[264] = [{_ninfo[264].Child},{_ninfo[264].Sibling}] (erase)");
            //Console.WriteLine($"End Erase with len={len}");

            return true;
        }

        public void Suffix(byte[] key, long to)
        {
            fixed (byte* keyPtr = key)
                Suffix(keyPtr, key.Length, to);
        }

        public void Suffix(byte* key, int len, long to)
        {
            key[len] = (byte)'\0';

            int offset = (int)(to >> 32);
            if (offset != 0)
            {
                fixed (byte* tail = u1.Tail)
                {
                    to &= TAIL_OFFSET_MASK;

                    int len_tail = strlen(tail + (-_array[to].Base));
                    if (len > len_tail)
                    {
                        len -= len_tail;
                    }
                    else
                    {
                        len_tail = len;
                        len = 0;
                    }

                    Unsafe.CopyBlock(key + len,  tail + offset - len_tail, (uint)len_tail);
                }

                while (len != 0)
                {
                    len--;

                    int from = _array[to].Check;
                    key[len] = (byte)(_array[from].Base ^ (int)to);
                    to = from;
                }
            }
        }

        private static int strlen(byte* str)
        {
            byte* current = str;
            while (*current != 0)
                current++;

            return (int)(current - str);
        }

        // test the validity of double array for debug
        internal void Test(long from = 0)
        {
            int @base = _array[from].Base;
            if (@base < 0)
            {
                // validate tail offset
                if (u1.Length < (int)(-@base + 1 + Unsafe.SizeOf<T>()))
                    throw new Exception($"Fail in tail offset {from}");

                return;
            }
            byte c = _ninfo[from].Child;
            do
            {
                if (from != 0)
                {
                    if (_array[@base ^ c].Check != from)
                        throw new Exception($"");
                }
                if (c != 0)
                {
                    Test(@base ^ c);
                }

                c = _ninfo[@base ^ c].Sibling;
            }
            while (c != 0);
        }

        public void Update(byte[] key, T value, long from = 0, long to = 0)
        {
            fixed (byte* keyPtr = key)
            {
                Update(keyPtr, key.Length, value, ref from, ref to);
            }
        }

        public void Update(byte* key, int len, T value, long from = 0, long to = 0)
        {
            Update(key, len, value, ref from, ref to);
        }

        private void Update(byte* key, int len, T value, ref long from, ref long pos)
        {
            if (len == 0 && from == 0)
                throw new ArgumentException("failed to insert zero-length key");

            try
            {
                //Console.WriteLine($"Start {nameof(Update)} with key-size: {len}");

                long offset = from >> 32;
                if (offset == 0)
                {
                    //Console.WriteLine("Begin 1");

                    for (byte* keyPtr = key; _array[from].Base >= 0; pos++)
                    {
                        if (pos == len)
                        {
                            int current = Follow(from, 0);
                            SetNodeValue(_array, current, value);
                            return;
                        }

                        from = Follow(from, key[pos]);
                    }

                    //Console.WriteLine("End 1");

                    offset = -_array[from].Base;
                }

                long pos_orig;
                int tailOffset;
                if (offset >= sizeof(int)) // go to _tail
                {
                    long moved;
                    pos_orig = pos;

                    tailOffset = (int)(0 + offset - pos);
                    while (pos < len && key[pos] == u1.Tail[tailOffset + pos])
                        pos++;

                    if (pos == len && u1.Tail[tailOffset + pos] == '\0')
                    {
                        // we found an exact match
                        moved = pos - pos_orig;
                        if (moved != 0)
                        {
                            // search end on tail
                            from &= TAIL_OFFSET_MASK;
                            from |= (offset + moved) << 32;
                        }

                        int ptrOffset = tailOffset + (len + 1);
                        Debug.Assert(ptrOffset + _tSize - 1 < u1.Tail.Length);

                        fixed (void* ptr = &u1.Tail[ptrOffset])
                        {
                            Unsafe.Write(ptr, value);

                            //Console.WriteLine($"_tail[{ptrOffset}] = {Unsafe.Read<T>(ptr)}");
                        }

                        return;
                    }

                    // otherwise, insert the common prefix in tail if any
                    if (from >> 32 != 0)
                    {
                        from &= TAIL_OFFSET_MASK; // reset to update tail offset
                        for (int offset_ = -_array[from].Base; offset_ < offset;)
                        {
                            from = Follow(from, u1.Tail[offset_]);
                            offset_++;
                        }

                        //Console.WriteLine();
                    }

                    //Console.WriteLine("Begin 2");

                    for (long pos_ = pos_orig; pos_ < pos; pos_++)
                        from = Follow(from, key[pos_]);

                    //Console.WriteLine("End 2");                    

                    moved = pos - pos_orig;
                    if (u1.Tail[tailOffset + pos] != 0)
                    {
                        // remember to move offset to existing tail
                        long to_ = Follow(from, u1.Tail[tailOffset + pos]);
                        moved++;

                        //Console.WriteLine($"_array[{to_}].Base = {-(int)(offset + moved)}");
                        _array[to_].Base = -(int)(offset + moved);

                        moved -= 1 + _tSize;  // keep record
                    }

                    moved += offset;
                    for (int i = (int)offset; i <= moved; i += 1 + _tSize)
                    {
                        u2.Length0 += 1;
                        if (_quota0 == u2.Length0)
                        {
                            _quota0 += u2.Length0 >= MAX_ALLOC_SIZE ? MAX_ALLOC_SIZE : u2.Length0;
                            // _quota0 += _quota0;

                            // Reallocating Tail0                        
                            u2 = new SizeUnion(Reallocate<int>(u2.Tail0, _quota0, u2.Length0));
                        }
                        u2.Tail0[u2.Length0] = i;
                    }
                    if (pos == len || u1.Tail[tailOffset + pos] == '\0')
                    {
                        long to = Follow(from, 0);
                        if (pos == len)
                        {
                            SetNodeValue(_array, (int)to, value);
                            return;
                        }
                        else
                        {
                            fixed (void* ptr = &u1.Tail[tailOffset + pos + 1])
                            {
                                T _toValue = Unsafe.Read<T>(ptr);
                                SetNodeValue(_array, (int)to, _toValue);
                            }
                        }
                    }

                    from = Follow(from, key[pos]);
                    pos++;
                }

                //
                int needed = (int)(len - pos + 1 + _tSize);
                if (pos == len && u2.Length0 != 0)
                {
                    int offset0 = u2.Tail0[u2.Length0];
                    u1.Tail[offset0] = 0;

                    //Console.WriteLine($"_array[{from}].Base = {-offset0}");
                    _array[from].Base = -offset0;
                    (u2.Length0)--;

                    fixed (void* ptr = &u1.Tail[offset0 + 1])
                    {
                        //Console.WriteLine($"_tail[{offset0 + 1}] = {value}");
                        Unsafe.Write(ptr, value);
                    }

                    return;
                }

                if (_quota < u1.Length + needed)
                {
                    if (needed > u1.Length || needed > MAX_ALLOC_SIZE)
                        _quota += needed;
                    else
                        _quota += (u1.Length >= MAX_ALLOC_SIZE) ? MAX_ALLOC_SIZE : u1.Length;

                    //_quota += _quota >= needed ? _quota : needed;

                    // Reallocating Tail.
                    u1 = new ElementUnion(Reallocate<byte>(u1.Tail, _quota, u1.Length));
                }

                //Console.WriteLine($"_array[{from}].Base = {-u1.Length}");
                _array[from].Base = -u1.Length;
                pos_orig = pos;

                tailOffset = (int)(u1.Length - pos);
                if (pos < len)
                {
                    do
                    {
                        //Console.WriteLine($"_tail[{tailOffset + pos}] = {key[pos]}");
                        u1.Tail[tailOffset + pos] = key[pos];
                    }
                    while (++pos < len);

                    from |= ((long)(u1.Length) + (len - pos_orig)) << 32;
                }

                u1.Length += needed;

                fixed (void* ptr = &u1.Tail[tailOffset + (len + 1)])
                {
                    Unsafe.Write(ptr, value);

                    //Console.WriteLine($"_tail[{tailOffset + (len + 1)}] = {Unsafe.Read<T>(ptr)}");
                }
            }
            finally
            {
                //Console.WriteLine($"End {nameof(Update)} with key-size: {len}");
            }

        }

        private int Follow(long from, byte label)
        {
            int to = 0;
            int @base = _array[from].Base;
            if (@base < 0 || _array[to = @base ^ label].Check < 0) // TODO: Check if the rules are the same here as in C++
            {
                to = _pop_enode(@base, label, (int)from);
                _push_sibling(from, to ^ label, label, @base >= 0);
            }
            else if (_array[to].Check != (int)from)
            {
                to = _resolve(from, @base, label);
            }

            //Console.WriteLine($"F->{to}");

            return to;
        }

        /// <summary>
        /// Resolve conflict on base_n ^ label_n = base_p ^ label_p
        /// </summary>
        private int _resolve(long from_n, int base_n, byte label_n)
        {
            //Console.WriteLine($"enters [{from_n}, {base_n}, {label_n}] (_resolve)");

            // examine siblings of conflicted nodes
            int to_pn = base_n ^ label_n;
            int from_p = _array[to_pn].Check;
            int base_p = _array[from_p].Base;

            // whether to replace siblings of newly added
            bool flag = _consult(base_n, base_p, _ninfo[from_n].Child, _ninfo[from_p].Child);

            byte* child = stackalloc byte[256];
            byte* first = child;
            byte* last = flag ? _set_child(first, base_n, _ninfo[from_n].Child, label_n) : _set_child(first, base_p, _ninfo[from_p].Child);

            int @base = (first == last ? _find_place() : _find_place(first, last)) ^ *first;

            // replace & modify empty list
            int from = flag ? (int)from_n : from_p;
            int base_ = flag ? base_n : base_p;

            //Console.WriteLine($"base_[{base_}], from[{from}], to_pn[{to_pn}], from_p[{from_p}], base_p[{base_p}] (_resolve)");

            if (flag && *first == label_n)
            {
                //Console.WriteLine($"_ninfo[{from}].Child = {label_n} (_resolve)");
                _ninfo[from].Child = label_n; // new child
            }


            //Console.WriteLine($"_array[{from}].Base = {@base} (_resolve)");
            _array[from].Base = @base; // new base

            for (byte* p = first; p <= last; p++)
            {
                // to_ => to
                int to = _pop_enode(@base, *p, from);
                int to_ = base_ ^ *p;

                //Console.WriteLine($"to[{to}], to_[{to_}] (_resolve)");

                //Console.WriteLine($"_ninfo[{to}].Sibling = {(byte)(p == last ? 0 : *(p + 1))} (_resolve)");
                _ninfo[to].Sibling = (byte)(p == last ? 0 : *(p + 1));

                if (flag && to_ == to_pn) // skip newcomer (no child)
                    continue;

                //Console.WriteLine($"_array[{to}].Base = {_array[to_].Base} (_resolve)");
                _array[to].Base = _array[to_].Base;
                if (_array[to_].Base > 0 && *p != 0)
                {
                    // copy base; bug fix
                    //Console.WriteLine($"_ninfo[{to}].Child = {_ninfo[to_].Child} (_resolve)");
                    byte c = _ninfo[to].Child = _ninfo[to_].Child;
                    do
                    {
                        int toBase = _array[to].Base ^ c;
                        //Console.WriteLine($"_array[{toBase}].Check = {to} (_resolve)");
                        _array[toBase].Check = to;
                        c = _ninfo[toBase].Sibling;
                    }
                    while (c != 0);
                }

                if (!flag && to_ == (int)from_n) // parent node moved
                    from_n = (long)to;

                if (!flag && to_ == to_pn)
                {
                    // the address is immediately used
                    _push_sibling(from_n, to_pn ^ label_n, label_n);

                    //Console.WriteLine($"_ninfo[{to_}].Child = 0 (_resolve)");
                    _ninfo[to_].Child = 0; // remember to reset child

                    if (label_n != 0)
                    {
                        //Console.WriteLine($"_array[{to_}].Base = -1 (_resolve)");
                        _array[to_].Base = -1;
                    }
                    else
                    {
                        ////Console.WriteLine($"_array[{to_}].Value = 0 (_resolve)");
                        SetNodeValue(_array, to_, default(T));
                    }

                    //Console.WriteLine($"_array[{to_}].Check = {(int)from_n} (_resolve)");
                    _array[to_].Check = (int)from_n;
                }
                else
                {
                    _push_enode(to_);
                }
            }

            //Console.WriteLine($"returns [{(flag ? @base ^ label_n : to_pn)}] (_resolve)");

            return flag ? @base ^ label_n : to_pn;
        }

        private void _push_enode(int e)
        {
            //Console.WriteLine($"enters [{e}] (_push_enode)");

            int bi = e >> 8;

            if (++_block[bi].Num == 1)
            {
                // Full to Closed
                _block[bi].Ehead = e;
                _array[e] = new node(-e, -e);
                //Console.WriteLine($"_array[{e}].Base = {_array[e].Base} (_push_enode)");
                //Console.WriteLine($"_array[{e}].Check = {_array[e].Check} (_push_enode)");
                if (bi != 0)
                    _transfer_block(bi, ref _bheadF, ref _bheadC); // Full to Closed
            }
            else
            {
                int prev = _block[bi].Ehead;
                int next = -_array[prev].Check;
                _array[e] = new node(-prev, -next);
                //Console.WriteLine($"_array[{e}].Base = {_array[e].Base} (_push_enode)");
                //Console.WriteLine($"_array[{e}].Check = {_array[e].Check} (_push_enode)");

                _array[prev].Check = _array[next].Base = -e;
                //Console.WriteLine($"_array[{prev}].Check = {_array[prev].Check} (_push_enode)");
                //Console.WriteLine($"_array[{next}].Base = {_array[next].Base} (_push_enode)");

                if (_block[bi].Num == 2 || _block[bi].Trial == _maxTrial)
                {
                    // Closed to Open
                    if (bi != 0)
                        _transfer_block(bi, ref _bheadC, ref _bheadO);
                }
                _block[bi].Trial = 0;
            }

            if (_block[bi].Reject < _reject[_block[bi].Num])
                _block[bi].Reject = _reject[_block[bi].Num];

            _ninfo[e] = new ninfo();
            //Console.WriteLine($"_ninfo[{e}] = [{_ninfo[e].Child},{_ninfo[e].Sibling}] (_push_enode)");
        }

        private int _find_place(byte* first, byte* last)
        {
            //Console.WriteLine($"enters [{*first},{*last}] (_find_place)");

            int bi = _bheadO;
            if (bi != 0)
            {
                int bz = _block[_bheadO].Prev;
                short nc = (short)(last - first + 1);
                while (true)
                {
                    //Console.WriteLine($"try [bi={bi},num={_block[bi].Num},nc={nc}] (_find_place)");

                    if (_block[bi].Num >= nc && nc < _block[bi].Reject) // explore configuration
                    {
                        int e = _block[bi].Ehead;
                        while (true)
                        {
                            int @base = e ^ *first;

                            //Console.WriteLine($"try [e={e},base={@base}] (_find_place)");
                            for (byte* p = first; _array[@base ^ *(++p)].Check < 0;)
                            {
                                if (p == last)
                                {
                                    _block[bi].Ehead = e;
                                    //Console.WriteLine($"returns: {e} (_find_place)");
                                    return e;
                                }
                            }

                            e = -_array[e].Check;
                            if (e == _block[bi].Ehead)
                                break;
                        }
                    }

                    _block[bi].Reject = nc;
                    if (_block[bi].Reject < _reject[_block[bi].Num])
                        _reject[_block[bi].Num] = _block[bi].Reject;

                    int bi_ = _block[bi].Next;
                    _block[bi].Trial++;
                    if (_block[bi].Trial == _maxTrial)
                        _transfer_block(bi, ref _bheadO, ref _bheadC);

                    Debug.Assert(_block[bi].Trial <= _maxTrial);

                    if (bi == bz)
                        break;

                    bi = bi_;
                }
            }

            int result = _add_block() << 8;
            //Console.WriteLine($"returns: {result} (_find_place)");
            return result;

        }

        private byte* _set_child(byte* p, int @base, byte c)
        {
            unchecked
            {
                return _set_child(p, @base, c, -1);
            };
        }

        private byte* _set_child(byte* p, int @base, byte c, int label)
        {
            //Console.WriteLine($"enters [{*p},{@base},{c},{label}] (_set_child)");

            p--;
            if (c == 0)
            {
                // 0 is a terminal character.
                p++;
                *p = c;
                c = _ninfo[@base ^ c].Sibling;
            }

            if (typeof(TOrdered) == typeof(Ordered))
            {
                while (c != 0 && c < label)
                {
                    p++;
                    *p = c;
                    c = _ninfo[@base ^ c].Sibling;
                }
            }

            if (label != -1)
            {
                p++;
                *p = (byte)label;
            }

            while (c != 0)
            {
                p++;
                *p = c;
                c = _ninfo[@base ^ c].Sibling;
            }

            return p;
        }

        private bool _consult(int base_n, int base_p, byte c_n, byte c_p)
        {
            //Console.WriteLine($"enters [{base_n},{base_p},{c_n},{c_p}] (_consult)");

            do
            {
                //Console.WriteLine($"\tc_n: _ninfo[{base_n ^ c_n}].sibling = {_ninfo[base_n ^ c_n].Sibling} (_consult)");
                c_n = _ninfo[base_n ^ c_n].Sibling;
                //Console.WriteLine($"\tc_p: _ninfo[{base_p ^ c_p}].sibling = {_ninfo[base_p ^ c_p].Sibling} (_consult)");
                c_p = _ninfo[base_p ^ c_p].Sibling;
            }
            while (c_n != 0 && c_p != 0);

            //Console.WriteLine($"returns: { (c_p != 0 ? 1 : 0)}  (_consult)");
            return c_p != 0;
        }

        private void _pop_sibling(long from, int @base, byte label)
        {
            //Console.WriteLine($"enters [{from},{@base},{(int)label}] (_pop_sibling)");

            // TODO: Review this and the push... the original uses pointers (and for a good reason) even though it is illegible what it is doing.

            bool changeChild = true;

            byte c = _ninfo[from].Child;
            while (c != label)
            {
                changeChild = false;

                from = @base ^ c;
                c = _ninfo[from].Sibling;
            }

            byte sibling = _ninfo[@base ^ label].Sibling;
            if (changeChild)
            {
                //Console.WriteLine($"\t_ninfo[{from}].Child = {sibling} (_pop_sibling)");
                _ninfo[from].Child = sibling;
            }
            else
            {
                //Console.WriteLine($"\t_ninfo[{@base ^ c}].Sibling = {sibling} (_pop_sibling)");
                _ninfo[from].Sibling = sibling;
            }
        }

        private void _push_sibling(long from, int @base, byte label, bool flag = true)
        {
            //Console.WriteLine($"enters [{from},{@base},{(int)label},{(flag ? 1 : 0)}] (_push_sibling)");

            bool changeChild = true;
            long current = from;
            byte c = _ninfo[current].Child;
            if (flag && ((typeof(TOrdered) == typeof(Ordered)) ? label > c : c == 0))
            {
                do
                {
                    changeChild = false;
                    current = @base ^ c;
                    c = _ninfo[current].Sibling;
                }
                while ((typeof(TOrdered) == typeof(Ordered)) && c != 0 && c < label);
            }

            //Console.WriteLine($"\t_ninfo[{ @base ^ label }].Sibling = {c.ToString()} (_push_sibling)");

            _ninfo[@base ^ label].Sibling = c;

            if (changeChild)
            {
                //Console.WriteLine($"\t_ninfo[{current}].Child = {label} (_push_sibling)");
                _ninfo[current].Child = label;
            }
            else
            {
                //Console.WriteLine($"\t_ninfo[{current}].Sibling = {label} (_push_sibling)");
                _ninfo[current].Sibling = label;
            }

        }

        private int _pop_enode(int @base, byte label, int from)
        {
            //Console.WriteLine($"enters [{@base},{label},{from}] (_pop_enode)");

            int e = @base < 0 ? _find_place() : @base ^ label;
            int bi = e >> 8;

            _block[bi].Num--;
            if (_block[bi].Num == 0)
            {
                if (bi != 0)
                    _transfer_block(bi, ref _bheadC, ref _bheadF); // Closed to Full
            }
            else // release empty node from empty ring
            {
                _array[-(_array[e].Base)].Check = _array[e].Check;

                //Console.WriteLine($"_array[{-(_array[e].Check)}].Base = {_array[e].Base}");
                _array[-(_array[e].Check)].Base = _array[e].Base;

                if (e == _block[bi].Ehead)
                    _block[bi].Ehead = -(_array[e].Check); // set ehead

                if (bi != 0 && _block[bi].Num == 1 && _block[bi].Trial != _maxTrial) // Open to Closed
                    _transfer_block(bi, ref _bheadO, ref _bheadC);
            }

            // initialize the released node
            if (label != 0)
            {
                //Console.WriteLine($"_array[{e}].Base = -1");
                _array[e].Base = -1;
            }
            else
            {
                SetNodeValue(_array, e, default(T));

                Debug.Assert(_array[e].Base == 0);
            }

            _array[e].Check = from;

            if (@base < 0)
            {
                _array[from].Base = e ^ label;
                //Console.WriteLine($"_array[{from}].Base = {e ^ label}");
            }

            //Console.WriteLine($"returns: {e} (_pop_enode)");
            return e;
        }

        private T GetNodeValue(ref node n)
        {
            return (T)(object)n.Base;
        }

        private void SetNodeValue(node[] n, int offset, T value)
        {
            //Console.WriteLine($"_array[{offset}].Value = {((int)(object)value)}");
            n[offset].Base = (int)(object)value;
        }

        private void _transfer_block(int bi, ref int head_in, ref int head_out)
        {
            //Console.WriteLine($"enters [{bi},{head_in},{head_out}] (_transfer_block)");

            _pop_block(bi, ref head_in, bi == _block[bi].Next);
            _push_block(bi, ref head_out, head_out == 0 && _block[bi].Num != 0);
        }

        private int _find_place()
        {
            //Console.WriteLine($"enters [] (_find_place)");

            if (_bheadC != 0)
            {
                //Console.WriteLine($"returns: {_block[_bheadC].Ehead} (_find_place)");
                return _block[_bheadC].Ehead;
            }

            if (_bheadO != 0)
            {
                //Console.WriteLine($"returns: {_block[_bheadO].Ehead} (_find_place)");
                return _block[_bheadO].Ehead;
            }

            int result = _add_block() << 8;
            //Console.WriteLine($"returns: {result} (_find_place)");
            return result;
        }

        private int _add_block()
        {
            //Console.WriteLine($"enters [] (_add_block)");

            if (Size == Capacity)
            {
                Capacity += Size >= MAX_ALLOC_SIZE ? MAX_ALLOC_SIZE : Size;

                _array = Reallocate<node>(_array, Capacity, Capacity);
                _ninfo = Reallocate<ninfo>(_ninfo, Capacity, Size);
                _block = Reallocate<block>(_block, Capacity >> 8, Size >> 8, block.Create());
            }

            _block[Size >> 8].Ehead = Size;
            _array[Size] = new node(-(Size + 255), -(Size + 1));
            for (int i = Size + 1; i < Size + 255; i++)
                _array[i] = new node(-(i - 1), -(i + 1));

            _array[Size + 255] = new node(-(Size + 254), -Size);
            _push_block(Size >> 8, ref _bheadO, _bheadO == 0);
            Size += 256;

            return (Size >> 8) - 1;
        }

        private void _pop_block(int bi, ref int head_in, bool last)
        {
            //Console.WriteLine($"enters [{bi},{head_in},{Convert.ToByte(last)}] (_pop_block)");

            if (last)
            {
                // last one poped; Closed or Open
                head_in = 0;
            }
            else
            {
                fixed (block* b = &_block[bi])
                {
                    _block[_block[bi].Prev].Next = _block[bi].Next;
                    //Console.WriteLine($"_block[{_block[bi].Prev}].Next = {_block[bi].Next} (_pop_block)");

                    _block[_block[bi].Next].Prev = _block[bi].Prev;
                    //Console.WriteLine($"_block[{_block[bi].Next}].Prev = {_block[bi].Prev} (_pop_block)");

                    if (bi == head_in)
                        head_in = b->Next;
                }
            }

            //Console.WriteLine($"returns [{head_in}] (_pop_block)");
        }

        private void _push_block(int bi, ref int head_out, bool empty)
        {
            // TODO: Ensure this can be inlined copying the parameter. 
            //Console.WriteLine($"enters [{bi},{head_out},{Convert.ToByte(empty)}] (_push_block)");

            fixed (block* b = &_block[bi])
            {
                if (empty)
                {
                    // the destination is empty
                    head_out = b->Prev = b->Next = bi;

                    //Console.WriteLine($"_block[{bi}].Next = {_block[bi].Next} (_push_block)");
                    //Console.WriteLine($"_block[{bi}].Prev = {_block[bi].Prev} (_push_block)");                    
                }
                else
                {
                    int tail_out = _block[head_out].Prev;
                    b->Prev = tail_out;
                    b->Next = head_out;

                    //Console.WriteLine($"_block[{bi}].Next = {tail_out} (_push_block)");
                    //Console.WriteLine($"_block[{bi}].Prev = {head_out} (_push_block)");
                    //Console.WriteLine($"_block[{tail_out}].Next = {bi} (_push_block)");
                    //Console.WriteLine($"_block[{head_out}].Prev = {bi} (_push_block)");

                    _block[tail_out].Next = bi;
                    _block[head_out].Prev = bi;
                    head_out = bi;
                }
            }

            //Console.WriteLine($"returns [{head_out}] (_push_block)");
        }


        struct IteratorValue
        {
            public T Value;
            public ErrorCode Error;
        }

        private IteratorValue Begin(ref long from, ref long len)
        {
            int @base = from >> 32 != 0 ? -(int)(from >> 32) : _array[from].Base;
            if (@base >= 0)
            {
                // on trie
                byte c = _ninfo[from].Child;
                if (from == 0)
                {
                    c = _ninfo[@base ^ c].Sibling;
                    if (c == 0) // no entry
                        return new IteratorValue { Error = ErrorCode.NoPath };
                }

                for (; c != 0 && @base >= 0; len++)
                {
                    from = @base ^ c;
                    @base = _array[from].Base;
                    c = _ninfo[from].Child;
                }

                if (@base >= 0) // it finishes in the trie
                    return new IteratorValue { Error = ErrorCode.Success, Value = GetNodeValue(ref _array[@base ^ c]) };
            }

            // we have a suffix to look for
            fixed (byte* tail = u1.Tail)
            {
                int len_ = strlen(tail - @base);
                from &= TAIL_OFFSET_MASK;
                from |= ((long)(-@base + len_)) << 32; // this must be long
                len += len_;

                return new IteratorValue { Error = ErrorCode.Success, Value = (T)(object)*(int*)(tail - @base + len_ + 1) };
            }
        }

        private IteratorValue Next(ref long from, ref long len, long root = 0)
        {
            // return the next child if any
            byte c = 0;

            int offset = (int)(from >> 32);
            if (offset != 0)
            {
                // on tail 
                if (root >> 32 != 0)
                    return new IteratorValue { Error = ErrorCode.NoPath };

                from &= TAIL_OFFSET_MASK;
                len -= offset - (-_array[from].Base);
            }
            else
            {
                c = _ninfo[_array[from].Base ^ 0].Sibling;
            }

            for (; c == 0 && from != root; len--)
            {
                c = _ninfo[from].Sibling;
                from = _array[from].Check;
            }

            if (c == 0)
                return new IteratorValue { Error = ErrorCode.NoPath };

            from = _array[from].Base ^ c;
            len++;

            return Begin(ref from, ref len);
        }

        private void Initialize()
        {
            // Original version
            _array = Reallocate<node>(_array, 256, 256);
            _ninfo = Reallocate<ninfo>(_ninfo, 256); // Marshal.Alloc doesn't ensure memory is zeroed out. 
            _block = Reallocate<block>(_block, 1, 0, block.Create()); // We need to call the constructor, not the default(block)

            _array[0] = new node(0, -1);
            for (int i = 1; i < 256; ++i)
                _array[i] = new node(i == 1 ? -255 : -(i - 1), i == 255 ? -1 : -(i + 1));

            Capacity = Size = 256;

            u1 = new ElementUnion(Reallocate<byte>(u1.Tail, sizeof(int)));
            u2 = new SizeUnion(Reallocate<int>(u2.Tail0, 1));

            _block[0].Ehead = 1; // bug fix for erase

            this._quota = u1.Length = sizeof(int);
            this._quota0 = 1;

            for (int i = 0; i < 256; i++)
                _reject[i] = (short)(i + 1);
        }

        W[] Reallocate<W>(W[] ptr, int size_n, int size_p = 0, W value = default(W)) where W : struct
        {
            // int wSize = Unsafe.SizeOf<W>();

            W[] tmp = new W[size_n];

            if (ptr == null)
            {
                ////Console.WriteLine($"allocating with elements to size: {size_n} zero from {size_p}");
            }
            else
            {
                Array.Copy(ptr, tmp, ptr.Length);

                ////Console.WriteLine($"moved with elements to size: {size_n} zero from {size_p}");
            }

            int count = size_n - size_p;
            for (int i = 0; i < count; i++)
                tmp[size_p + i] = value;

            return tmp;
        }

        #region IDisposable Support
        private bool disposedValue = false; // To detect redundant calls

        protected virtual void Dispose(bool disposing)
        {
            if (!disposedValue)
            {
                if (disposing)
                {
                    // TODO: dispose managed state (managed objects).
                }

                //SafeRelease(_array);
                //SafeRelease(_block);
                //SafeRelease(_ninfo);
                //SafeRelease(_trackingNode);
                //SafeRelease(u1.Ptr);
                //SafeRelease(u2.Ptr);

                disposedValue = true;
            }
        }

        private void SafeRelease(void* ptr)
        {
            if (ptr != null)
                Marshal.FreeHGlobal(new IntPtr(ptr));
        }

        ~CedarTrie()
        {
            Dispose(false);
        }

        public void Dispose()
        {
            // Do not change this code. Put cleanup code in Dispose(bool disposing) above.
            Dispose(true);
            GC.SuppressFinalize(this);
        }
        #endregion
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    struct node
    {
        public int Check; // negative means next empty index

        public int Base; // negative means prev empty index

        public node(int @base = 0, int check = 0)
        {
            this.Check = check;
            this.Base = @base;
        }
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    struct ninfo // x1.5 update speed; +.25 % memory (8n -> 10n)
    {
        public byte Sibling;  // right sibling (= 0 if not exist)
        public byte Child;    // first child

        public ninfo(byte sibling = 0, byte child = 0)
        {
            this.Sibling = sibling;
            this.Child = child;
        }
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    struct block // a block w/ 256 elements
    {
        public int Prev;   // prev block; 3 bytes
        public int Next;   // next block; 3 bytes
        public short Num;    // # empty elements; 0 - 256
        public short Reject; // minimum # branching failed to locate; soft limit
        public int Trial;  // # trial
        public int Ehead;  // first empty item

        public block(int prev, int next, short num, short reject, int trial, int ehead)
        {
            this.Prev = prev;
            this.Next = next;
            this.Num = num;
            this.Reject = reject;
            this.Trial = trial;
            this.Ehead = ehead;
        }

        public static block Create(int prev = 0, int next = 0, short num = 256, short reject = 257, int trial = 0, int ehead = 0)
        {
            return new block(prev, next, num, reject, trial, ehead);
        }
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    unsafe struct ElementUnion
    {
        public byte[] Tail;

        public int Length
        {
            get
            {
                fixed (byte* tail = Tail)
                {
                    return *((int*)tail);
                }
            }
            set
            {
                fixed (byte* tail = Tail)
                {
                    *((int*)tail) = value;
                }
            }
        }

        public ElementUnion(byte[] tail)
        {
            this.Tail = tail;
        }
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    unsafe struct SizeUnion
    {
        public int[] Tail0;

        public int Length0
        {
            get
            {
                fixed (int* tail = Tail0)
                {
                    return *tail;
                }
            }
            set
            {
                fixed (int* tail = Tail0)
                {
                    *tail = value;
                }
            }
        }

        public SizeUnion(int[] ptr)
        {
            this.Tail0 = ptr;
        }
    }
}
