﻿using System.Collections.Generic;
using System.Linq;
using BenchmarkDotNet.Attributes;
using Sparrow;
using Voron.Data.Tables;

namespace Voron.Benchmark.Table
{
    public class TableFillSequential : StorageBenchmark
    {
        private static readonly Slice TableNameSlice;
        private static readonly Slice SchemaPKNameSlice;
        private static readonly TableSchema Schema;

        /// <summary>
        /// We have one list per Transaction to carry out. Each one of these 
        /// lists has exactly the number of items we want to insert, with
        /// distinct keys for each one of them.
        /// 
        /// It is important for them to be lists, this way we can ensure the
        /// order of insertions remains the same throughout runs.
        /// </summary>
        private List<TableValueBuilder>[] _valueBuilders;

        static TableFillSequential()
        {
            Slice.From(Configuration.Allocator, "TableFillSequential", ByteStringType.Immutable, out TableNameSlice);
            Slice.From(Configuration.Allocator, "TableFillSequentialSchema", ByteStringType.Immutable, out SchemaPKNameSlice);

            Schema = new TableSchema()
                .DefineKey(new TableSchema.SchemaIndexDef
                {
                    StartIndex = 0,
                    Count = 0,
                    IsGlobal = false,
                    Name = SchemaPKNameSlice,
                    Type = TableIndexType.BTree
                });
        }

        [Setup]
        public override void Setup()
        {
            base.Setup();

            using (var tx = Env.WriteTransaction())
            {
                Schema.Create(tx, TableNameSlice, 16);
                tx.Commit();
            }

            var totalPairs = Utils.GenerateUniqueRandomSlicePairs(
                NumberOfTransactions * NumberOfRecordsPerTransaction,
                KeyLength,
                RandomSeed);

            // This will sort just the KEYS
            totalPairs.Sort((x, y) => SliceComparer.Compare(x.Item1, y.Item1));

            // Distribute keys in such a way that _valueBuilders[i][k] <
            // _valueBuilders[j][m] iff i < j, for all k and m.
            _valueBuilders = new List<TableValueBuilder>[NumberOfTransactions];

            for (int i = 0; i < NumberOfTransactions; i++)
            {
                var values = totalPairs.Take(NumberOfRecordsPerTransaction);
                totalPairs.RemoveRange(0, NumberOfRecordsPerTransaction);

                _valueBuilders[i] = new List<TableValueBuilder>();

                foreach (var pair in values)
                {
                    _valueBuilders[i].Add(new TableValueBuilder
                    {
                        pair.Item1,
                        pair.Item2
                    });
                }
            }
        }

        // TODO: Fix. See: https://github.com/PerfDotNet/BenchmarkDotNet/issues/258
        [Benchmark(OperationsPerInvoke = Configuration.RecordsPerTransaction * Configuration.Transactions)]
        public void FillRandomOneTransaction()
        {
            using (var tx = Env.WriteTransaction())
            {
                var table = tx.OpenTable(Schema, TableNameSlice);

                for (var i = 0; i < NumberOfTransactions; i++)
                {
                    foreach (var value in _valueBuilders[i])
                    {
                        table.Insert(value);
                    }
                }

                tx.Commit();
            }
        }

        // TODO: Fix. See: https://github.com/PerfDotNet/BenchmarkDotNet/issues/258
        [Benchmark(OperationsPerInvoke = Configuration.RecordsPerTransaction * Configuration.Transactions)]
        public void FillRandomMultipleTransactions()
        {
            for (var i = 0; i < NumberOfTransactions; i++)
            {
                using (var tx = Env.WriteTransaction())
                {
                    var table = tx.OpenTable(Schema, TableNameSlice);

                    foreach (var value in _valueBuilders[i])
                    {
                        table.Insert(value);
                    }

                    tx.Commit();
                }
            }
        }
    }
}