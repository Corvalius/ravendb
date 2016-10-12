﻿using System;
using System.Collections;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;
using Voron;
using Voron.Impl;

namespace Regression.PageLocator
{
    public struct PageHandlePtrV3
    {        
        public readonly long PageNumber;        
        public readonly MyPage Value;
        public readonly bool IsWritable;        

        public PageHandlePtrV3(long pageNumber, MyPage value, bool isWritable)
        {
            this.Value = value;
            this.PageNumber = pageNumber;
            this.IsWritable = isWritable;
        }
    }

    public class PageLocatorV3
    {
        private const short Invalid = -1;

        private readonly LowLevelTransaction _tx;
        // This is the size of the cache, required to be _cacheSize % Vector<long>.Count == 0
        private readonly int _cacheSize;

        private readonly short[] _fingerprints;
        private readonly PageHandlePtrV3[] _cache;

        private int _current;


        public PageLocatorV3(LowLevelTransaction tx, int cacheSize = 4)
        {
            //Debug.Assert(tx != null);
            _tx = tx;

            if (tx != null)
                Debug.Fail("");

            // Align cache size to Vector<ushort>.Count
            _cacheSize = cacheSize;

            _current = 0;

            _cache = new PageHandlePtrV3[_cacheSize];

            _fingerprints = new short[_cacheSize];
            for (short i = 0; i < _fingerprints.Length; i++)
                _fingerprints[i] = Invalid;
        }

        public MyPage GetReadOnlyPage(long pageNumber)
        {
            short fingerprint = (short)pageNumber;

            int i;
            for (i = 0; i < _cacheSize; i++)
            {
                // This is used to force the JIT to layout the code as if unlikely() compiler directive exists.
                if (_fingerprints[i] == fingerprint)
                    goto Found;
            }

            // If we got here, there was a cache miss
            _current = (_current++) % _cacheSize;
            _cache[_current] = new PageHandlePtrV3(pageNumber, LowLevelTransactionStub.GetPage(pageNumber), false);
            _fingerprints[_current] = fingerprint;

            return _cache[_current].Value;

            Found:
            // This is not the common case on the loop and we are returning anyways. It doesnt matter the jump is far.
            if (_cache[i].PageNumber == pageNumber)
                return _cache[i].Value;

            _cache[i] = new PageHandlePtrV3(pageNumber, LowLevelTransactionStub.GetPage(pageNumber), false);
            return _cache[i].Value;
        }

        public MyPage GetWritablePage(long pageNumber)
        {
            short fingerprint = (short)pageNumber;

            int i;
            for (i = 0; i < _cacheSize; i++)
            {
                // This is used to force the JIT to layout the code as if unlikely() compiler directive exists.
                if (_fingerprints[i] == fingerprint)
                    goto Found;
            }

            // If we got here, there was a cache miss
            _current = (_current++) % _cacheSize;
            _cache[_current] = new PageHandlePtrV3(pageNumber, LowLevelTransactionStub.ModifyPage(pageNumber), true);
            _fingerprints[_current] = fingerprint;

            return _cache[_current].Value;

            Found:

            if (_cache[i].PageNumber == pageNumber && _cache[i].IsWritable)
                return _cache[i].Value;

            _cache[i] = new PageHandlePtrV3(pageNumber, LowLevelTransactionStub.ModifyPage(pageNumber), true);
            return _cache[i].Value;
        }

        public void Clear()
        {
            _current = 0;
            Array.Clear(_cache, 0, _cache.Length);
            Array.Clear(_fingerprints, 0, _cache.Length);
            for (int i = 0; i < _fingerprints.Length; i++)
                _fingerprints[i] = Invalid;
        }

        public void Reset(long pageNumber)
        {
            short fingerprint = (short)pageNumber;

            for (int i = 0; i < _cacheSize; i++)
            {
                if (_fingerprints[i] == fingerprint)
                {   
                    _cache[i] = new PageHandlePtrV3();
                    return;
                }
            }
        }
    }
}