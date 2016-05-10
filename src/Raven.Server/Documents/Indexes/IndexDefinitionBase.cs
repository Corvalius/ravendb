﻿using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

using Raven.Abstractions.Data;
using Raven.Abstractions.Extensions;
using Raven.Abstractions.Indexing;
using Raven.Client.Indexing;
using Raven.Server.ServerWide.Context;

using Sparrow.Json;

using Voron;

namespace Raven.Server.Documents.Indexes
{
    public abstract class IndexDefinitionBase
    {
        protected const string MetadataFileName = "metadata";

        protected static readonly SliceArray DefinitionSlice = "Definition";

        private int? _cachedHashCode;

        protected IndexDefinitionBase(string name, string[] collections, IndexLockMode lockMode, IndexField[] mapFields)
        {
            Name = name;
            Collections = collections;
            MapFields = mapFields.ToDictionary(x => x.Name, x => x, StringComparer.OrdinalIgnoreCase);
            LockMode = lockMode;
        }

        public string Name { get; }

        public string[] Collections { get; }

        public Dictionary<string, IndexField> MapFields { get; }

        public IndexLockMode LockMode { get; set; }

        public void Persist(TransactionOperationContext context, StorageEnvironmentOptions options)
        {
            if (options is StorageEnvironmentOptions.DirectoryStorageEnvironmentOptions)
            {
                using (var stream = File.Open(Path.Combine(options.BasePath, MetadataFileName), FileMode.Create))
                using (var writer = new StreamWriter(stream, Encoding.UTF8))
                {
                    writer.Write(Name);
                    writer.Flush();
                }
            }

            var tree = context.Transaction.InnerTransaction.CreateTree("Definition");
            using (var stream = new MemoryStream())
            using (var writer = new BlittableJsonTextWriter(context, stream))
            {
                Persist(context, writer);

                writer.Flush();

                stream.Position = 0;
                tree.Add(DefinitionSlice, stream.ToArray());
            }
        }

        private void Persist(TransactionOperationContext context, BlittableJsonTextWriter writer)
        {
            writer.WriteStartObject();

            var collection = Collections.First();

            writer.WritePropertyName(context.GetLazyString(nameof(Collections)));
            writer.WriteStartArray();
            writer.WriteString(context.GetLazyString(collection));
            writer.WriteEndArray();
            writer.WriteComma();
            writer.WritePropertyName(context.GetLazyString(nameof(LockMode)));
            writer.WriteInteger((int)LockMode);
            writer.WriteComma();

            PersisFields(context, writer);

            writer.WriteEndObject();
        }

        protected abstract void PersisFields(TransactionOperationContext context, BlittableJsonTextWriter writer);

        protected void PersistMapFields(TransactionOperationContext context, BlittableJsonTextWriter writer)
        {
            writer.WritePropertyName(context.GetLazyString(nameof(MapFields)));
            writer.WriteStartArray();
            var first = true;
            foreach (var field in MapFields.Values)
            {
                if (first == false)
                    writer.WriteComma();

                writer.WriteStartObject();

                writer.WritePropertyName(context.GetLazyString(nameof(field.Name)));
                writer.WriteString(context.GetLazyString(field.Name));
                writer.WriteComma();

                writer.WritePropertyName(context.GetLazyString(nameof(field.Highlighted)));
                writer.WriteBool(field.Highlighted);
                writer.WriteComma();

                writer.WritePropertyName(context.GetLazyString(nameof(field.SortOption)));
                writer.WriteInteger((int)(field.SortOption ?? SortOptions.None));
                writer.WriteComma();

                writer.WritePropertyName(context.GetLazyString(nameof(field.MapReduceOperation)));
                writer.WriteInteger((int)(field.MapReduceOperation));

                writer.WriteEndObject();

                first = false;
            }
            writer.WriteEndArray();
        }

        public IndexDefinition ConvertToIndexDefinition(Index index)
        {
            var indexDefinition = new IndexDefinition();
            indexDefinition.IndexId = index.IndexId;
            indexDefinition.Name = index.Name;
            indexDefinition.Fields = MapFields.ToDictionary(
                x => x.Key,
                x => new IndexFieldOptions
                {
                    Sort = x.Value.SortOption,
                    TermVector = x.Value.Highlighted ? FieldTermVector.WithPositionsAndOffsets : (FieldTermVector?)null,
                    Analyzer = x.Value.Analyzer,
                    Indexing = x.Value.Indexing,
                    Storage = x.Value.Storage
                });

            indexDefinition.Type = index.Type;
            indexDefinition.LockMode = LockMode;

            indexDefinition.IndexVersion = -1; // TODO [ppekrol]      
            indexDefinition.IsSideBySideIndex = false; // TODO [ppekrol]
            indexDefinition.IsTestIndex = false; // TODO [ppekrol]       
            indexDefinition.MaxIndexOutputsPerDocument = null; // TODO [ppekrol]

            FillIndexDefinition(indexDefinition);

            return indexDefinition;
        }

        protected abstract void FillIndexDefinition(IndexDefinition indexDefinition);

        public bool ContainsField(string field)
        {
            if (field.EndsWith("_Range"))
                field = field.Substring(0, field.Length - 6);

            return MapFields.ContainsKey(field);
        }

        public IndexField GetField(string field)
        {
            if (field.EndsWith("_Range"))
                field = field.Substring(0, field.Length - 6);

            return MapFields[field];
        }

        public bool TryGetField(string field, out IndexField value)
        {
            if (field.EndsWith("_Range"))
                field = field.Substring(0, field.Length - 6);

            return MapFields.TryGetValue(field, out value);
        }

        public abstract bool Equals(IndexDefinitionBase indexDefinition, bool ignoreFormatting, bool ignoreMaxIndexOutputs);

        public override int GetHashCode()
        {
            if (_cachedHashCode != null)
                return _cachedHashCode.Value;

            unchecked
            {
                var hashCode = MapFields?.GetDictionaryHashCode() ?? 0;
                hashCode = (hashCode * 397) ^ (Name?.GetHashCode() ?? 0);
                hashCode = (hashCode * 397) ^ (Collections?.GetEnumerableHashCode() ?? 0);

                _cachedHashCode = hashCode;

                return hashCode;
            }
        }

        public static string TryReadName(DirectoryInfo directory)
        {
            var metadataFile = Path.Combine(directory.FullName, MetadataFileName);
            if (File.Exists(metadataFile) == false)
                return null;

            var name = File.ReadAllText(metadataFile, Encoding.UTF8);
            if (string.IsNullOrWhiteSpace(name))
                return null;

            return name;
        }
    }
}