﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;

namespace Voron.Data.BTrees
{

    /// <summary>
    /// The Cedar Branch Header is contained by the first page or any Cedar BTree Node
    /// </summary>
    [StructLayout(LayoutKind.Explicit, Pack = 1)]
    public unsafe struct CedarPageHeader
    {
        public bool IsValid => Flags == PageFlags.CedarTreePage && (TreeFlags == TreePageFlags.Branch || TreeFlags == TreePageFlags.Leaf);
        public bool IsBranchPage => TreeFlags == TreePageFlags.Branch;
        public bool IsLeafPage => TreeFlags == TreePageFlags.Leaf;
        
        public long BlocksPageNumber => PageNumber;
        public long TailPageNumber => PageNumber + DataPageCount;
        public long NodesPageNumber => PageNumber + DataPageCount + DataPageCount;

        /// <summary>
        /// This page number
        /// </summary>
        [FieldOffset(0)]
        public long PageNumber;

        /// <summary>
        /// Page size
        /// </summary>
        [FieldOffset(8)]
        public int OverflowSize;

        /// <summary>
        /// Page flags.
        /// </summary>
        [FieldOffset(12)]
        public PageFlags Flags;

        /// <summary>
        /// Tree pages flags. For this header the only valid value is <see cref="TreePageFlags.Branch"/> or <see cref="TreePageFlags.Leaf"/>
        /// </summary>
        [FieldOffset(13)]
        public TreePageFlags TreeFlags;

        /// <summary>
        /// The actual used size for the blocks storage.
        /// </summary>
        [FieldOffset(16)]
        public int Size;

        /// <summary>
        /// The total capacity for the blocks storage
        /// </summary>
        [FieldOffset(20)]
        public int Capacity;

        /// <summary>
        /// How many blocks pages are available to be used.
        /// </summary>
        [FieldOffset(24)]
        public int BlocksPageCount;

        [FieldOffset(28)]
        public int BlocksPerPage;

        /// <summary>
        /// How many tail pages are available to be used.
        /// </summary>
        [FieldOffset(32)]
        public int TailPageCount;

        [FieldOffset(36)]
        public int TailBytesPerPage;

        /// <summary>
        /// How many data nodes pages are available for this Node. 
        /// </summary>
        [FieldOffset(40)]
        public int DataPageCount;

        [FieldOffset(44)]
        public int DataNodesPerPage;

        /// <summary>
        /// The offset from the start of the <see cref="CedarPageHeader"/> where the blocks metadata is stored.
        /// </summary>
        [FieldOffset(48)]
        public int MetadataOffset;

        /// <summary>
        /// The offset from the start of the <see cref="CedarPageHeader"/> where the tail metadata is stored.
        /// </summary>
        [FieldOffset(52)]
        public int Tail0Offset;

        [FieldOffset(56)]
        public int _bheadF;  // first block of Full;   0
        [FieldOffset(60)]
        public int _bheadC;  // first block of Closed; 0 if no Closed
        [FieldOffset(64)]
        public int _bheadO;  // first block of Open;   0 if no Open

        [FieldOffset(68)]
        public fixed short Reject[257];
    }
}
