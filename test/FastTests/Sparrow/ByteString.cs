﻿using Sparrow;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Xunit;


namespace FastTests.Sparrow
{
    public unsafe class ByteStringTests
    {

        public void Lifecycle()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>())
            {
                ByteString byteString;
                context.Allocate(512, out byteString);

                Assert.Equal(512, byteString.Length);
                Assert.True(byteString.HasValue);
                Assert.True((ByteStringType.Mutable & byteString.Flags) != 0);
                Assert.True(byteString.IsMutable);
                Assert.Equal(1024, byteString._pointer->Size);

                ByteString byteStringWithExactSize;
                context.Allocate(1024 - sizeof(ByteStringStorage), out byteStringWithExactSize);

                Assert.True(byteStringWithExactSize.HasValue);
                Assert.Equal(1024 - sizeof(ByteStringStorage), byteStringWithExactSize.Length);
                Assert.True((ByteStringType.Mutable & byteStringWithExactSize.Flags) != 0);
                Assert.True(byteStringWithExactSize.IsMutable);
                Assert.Equal(1024, byteStringWithExactSize._pointer->Size);

                context.Release(ref byteString);
                Assert.False(byteString.HasValue);
                Assert.True(byteString._pointer == null);
            }
        }

        public void ConstructionInsideWholeSegment()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString byteStringInFirstSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage), out byteStringInFirstSegment);
                ByteString byteStringWholeSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage), out byteStringWholeSegment);
                ByteString byteStringNextSegment;
                context.Allocate(1, out byteStringNextSegment);

                long startLocation = (long)byteStringInFirstSegment._pointer;
                Assert.InRange((long)byteStringWholeSegment._pointer, startLocation, startLocation + ByteStringContext.MinBlockSizeInBytes);
                Assert.NotInRange((long)byteStringNextSegment._pointer, startLocation, startLocation + ByteStringContext.MinBlockSizeInBytes);
            }
        }

        public void ConstructionInsideWholeSegmentWithHistory()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                for (int i = 0; i < 10; i++)
                {
                    ByteString str;
                    context.Allocate(ByteStringContext.MinBlockSizeInBytes * 2, out str);
                }
            }
            using (new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString byteStringInFirstSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage), out byteStringInFirstSegment);
                ByteString byteStringWholeSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage), out byteStringWholeSegment);
                ByteString byteStringNextSegment;
                context.Allocate(1,out byteStringNextSegment);
               
                long startLocation = (long)byteStringInFirstSegment._pointer;
                Assert.InRange((long)byteStringWholeSegment._pointer, startLocation, startLocation + ByteStringContext.MinBlockSizeInBytes);
                Assert.NotInRange((long)byteStringNextSegment._pointer, startLocation, startLocation + ByteStringContext.MinBlockSizeInBytes);
            }
        }

        public void ConstructionReleaseForReuseTheLeftOver()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString byteStringInFirstSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage), out byteStringInFirstSegment);
                ByteString byteStringInNewSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage) + 1, out byteStringInNewSegment);
                ByteString byteStringInReusedSegment;
                context.Allocate((ByteStringContext.MinBlockSizeInBytes / 2) - sizeof(ByteStringStorage), out byteStringInReusedSegment);

                long startLocation = (long)byteStringInFirstSegment._pointer;
                Assert.NotInRange((long)byteStringInNewSegment._pointer, startLocation, startLocation + ByteStringContext.MinBlockSizeInBytes);
                Assert.InRange((long)byteStringInReusedSegment._pointer, startLocation, startLocation + ByteStringContext.MinBlockSizeInBytes);
            }
        }

        public void AllocateAndReleaseShouldReuse()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString byteStringInFirst;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out byteStringInFirst);
                ByteString byteStringInSecond;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out byteStringInSecond);

                long ptrLocation = (long)byteStringInFirst._pointer;
                Assert.InRange((long)byteStringInSecond._pointer, ptrLocation, ptrLocation + ByteStringContext.MinBlockSizeInBytes);

                context.Release(ref byteStringInFirst);

                ByteString byteStringReused;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out byteStringReused);

                Assert.InRange((long)byteStringReused._pointer, ptrLocation, ptrLocation + ByteStringContext.MinBlockSizeInBytes);
                Assert.Equal(ptrLocation, (long)byteStringReused._pointer);

                ByteString byteStringNextSegment;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out byteStringNextSegment);
                Assert.NotInRange((long)byteStringNextSegment._pointer, ptrLocation, ptrLocation + ByteStringContext.MinBlockSizeInBytes);
            }
        }

        public void AllocateAndReleaseShouldReuseAsSegment()
        {
            int allocationBlockSize = 2 * ByteStringContext.MinBlockSizeInBytes + 128 + sizeof(ByteStringStorage);
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(allocationBlockSize))
            {
                // Will be only 128 bytes left for the allocation unit.
                ByteString byteStringInFirst;
                context.Allocate(2 * ByteStringContext.MinBlockSizeInBytes - sizeof(ByteStringStorage), out byteStringInFirst);

                long ptrLocation = (long)byteStringInFirst._pointer;
                long nextPtrLocation = ptrLocation + byteStringInFirst._pointer->Size;

                context.Release(ref byteStringInFirst); // After the release the block should be reserved as a new segment. 

                // We use a different size to ensure we are not reusing a reuse bucket but big enough to avoid having space available. 
                ByteString byteStringReused;
                context.Allocate(512, out byteStringReused);

                Assert.InRange((long)byteStringReused._pointer, ptrLocation, ptrLocation + allocationBlockSize);
                Assert.Equal(ptrLocation, (long)byteStringReused._pointer); // We are the first in the segment.

                // This allocation will have an allocation unit size of 128 and fit into the rest of the initial segment, which should be 
                // available for an exact reuse bucket allocation. 
                ByteString byteStringReusedFromBucket;
                context.Allocate(64, out byteStringReusedFromBucket);

                Assert.Equal((long)byteStringReusedFromBucket._pointer, nextPtrLocation);
            }
        }

        public void AllocateAndReleaseShouldReuseRepeatedly()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString first;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out first);
                long ptrLocation = (long)first._pointer;
                context.Release(ref first);

                for (int i = 0; i < 100; i++)
                {
                    ByteString repeat;
                    context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out repeat);
                    Assert.Equal(ptrLocation, (long)repeat._pointer);
                    context.Release(ref repeat);
                }
            }
        }

#if VALIDATE
        public void ValidationKeyAfterAllocateAndReleaseReuseShouldBeDifferent()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString first;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out first);
                context.Release(ref first);

                ByteString repeat;
                context.Allocate(ByteStringContext.MinBlockSizeInBytes / 2 - sizeof(ByteStringStorage), out repeat);
                Assert.NotEqual(first.Key, repeat._pointer->Key);
                Assert.Equal(first.Key >> 32, repeat._pointer->Key >> 32);
                context.Release(ref repeat);
            }
        }

        public void FailValidationTryingToReleaseInAnotherContext()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            using (var otherContext = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString first;
                context.Allocate(1, out first);
                Assert.Throws<ByteStringValidationException>(() => otherContext.Release(ref first));
            }
        }

        public void FailValidationReleasingAnAliasAfterReleasingOriginal()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString first;
                context.Allocate(1, out first);
                var firstAlias = first;
                context.Release(ref first);

                Assert.Throws<InvalidOperationException>(() => context.Release(ref firstAlias));
            }
        }

        public void DetectImmutableChangeOnValidation()
        {
            using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
            {
                ByteString value;
                context.From("string", ByteStringType.Immutable, out value);
                value.Ptr[2] = (byte)'t';

                Assert.Throws<ByteStringValidationException>(() => context.Release(ref value));
            }
        }

        public void DetectImmutableChangeOnContextDispose()
        {
            Assert.Throws<ByteStringValidationException>(() =>
            {
                using (var context = new ByteStringContext<ByteStringDirectAllocator>(ByteStringContext.MinBlockSizeInBytes))
                {
                    ByteString value;
                    context.From("string", ByteStringType.Immutable, out value);
                    value.Ptr[2] = (byte)'t';
                }
            });
        }
#endif

    }
}
