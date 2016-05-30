﻿using System;
using System.Collections.Generic;

using Voron.Data;
using Voron.Data.BTrees;
using Voron.Data.Fixed;

namespace Voron.Impl
{
    public unsafe class Transaction : IDisposable
    {
        private Dictionary<Tuple<Tree, ISlice>, Tree> _multiValueTrees;
        private readonly LowLevelTransaction _lowLevelTransaction;

        public LowLevelTransaction LowLevelTransaction
        {
            get { return _lowLevelTransaction; }
        }

        private readonly Dictionary<string, Tree> _trees = new Dictionary<string, Tree>();
        private readonly HashSet<ICommittable> _participants = new HashSet<ICommittable>();

        public Transaction(LowLevelTransaction lowLevelTransaction)
        {
            _lowLevelTransaction = lowLevelTransaction;
        }

        public Tree ReadTree(string treeName)
        {
            Tree tree;
            if (_trees.TryGetValue(treeName, out tree))
                return tree;

            var header = (TreeRootHeader*)_lowLevelTransaction.RootObjects.DirectRead<SliceArray>(treeName);
            if (header != null)
            {
                if (header->RootObjectType != RootObjectType.VariableSizeTree)
                    throw new InvalidOperationException("Tried to opened " + treeName + " as a variable size tree, but it is actually a " + header->RootObjectType);

                tree = Tree.Open(_lowLevelTransaction, this, header);
                tree.Name = treeName;
                _trees.Add(treeName, tree);
                return tree;
            }

            _trees.Add(treeName, null);
            return null;
        }

        public IEnumerable<Tree> Trees
        {
            get { return _trees.Values; }
        }

        public void Commit()
        {
            if (_lowLevelTransaction.Flags != (TransactionFlags.ReadWrite))
                return; // nothing to do

            PrepareForCommit();
            _lowLevelTransaction.Commit();
        }

        public void Register(ICommittable participant)
        {
            _participants.Add(participant);
        }

        internal void PrepareForCommit()
        {
            if (_multiValueTrees != null)
            {
                foreach (var multiValueTree in _multiValueTrees)
                {
                    var parentTree = multiValueTree.Key.Item1;
                    var key = multiValueTree.Key.Item2;
                    var childTree = multiValueTree.Value;

                    var trh = (TreeRootHeader*)parentTree.DirectAdd(key, sizeof(TreeRootHeader), TreeNodeFlags.MultiValuePageRef);
                    childTree.State.CopyTo(trh);
                }
            }

            foreach (var tree in Trees)
            {
                if (tree == null)
                    continue;

                tree.State.InWriteTransaction = false;
                var treeState = tree.State;
                if (treeState.IsModified)
                {
                    var treePtr = (TreeRootHeader*)_lowLevelTransaction.RootObjects.DirectAdd<SliceArray>(tree.Name, sizeof(TreeRootHeader));
                    treeState.CopyTo(treePtr);
                }
            }

            foreach (var participant in _participants)
            {
                if (participant.RequiresParticipation)
                    participant.PrepareForCommit();
            }
        }


        internal void AddMultiValueTree<T>(Tree tree, T key, Tree mvTree)
            where T : ISlice
        {
            if (_multiValueTrees == null)
                _multiValueTrees = new Dictionary<Tuple<Tree, ISlice>, Tree>(new TreeAndSliceComparer());
            mvTree.IsMultiValueTree = true;
            _multiValueTrees.Add(Tuple.Create<Tree, ISlice>(tree, key), mvTree);
        }

        internal bool TryGetMultiValueTree<T>(Tree tree, T key, out Tree mvTree)
            where T : ISlice
        {
            mvTree = null;
            if (_multiValueTrees == null)
                return false;
            return _multiValueTrees.TryGetValue(Tuple.Create<Tree, ISlice>(tree, key), out mvTree);
        }

        internal bool TryRemoveMultiValueTree<T>(Tree parentTree, T key)
            where T : ISlice
        {
            var keyToRemove = Tuple.Create<Tree, ISlice>(parentTree, key);
            if (_multiValueTrees == null || !_multiValueTrees.ContainsKey(keyToRemove))
                return false;

            return _multiValueTrees.Remove(keyToRemove);
        }


        internal void AddTree(string name, Tree tree)
        {
            Tree value;
            if (_trees.TryGetValue(name, out value) && value != null)
            {
                throw new InvalidOperationException("Tree already exists: " + name);
            }
            _trees[name] = tree;
        }



        public void DeleteTree(string name)
        {
            if (_lowLevelTransaction.Flags == (TransactionFlags.ReadWrite) == false)
                throw new ArgumentException("Cannot create a new newRootTree with a read only transaction");

            Tree tree = ReadTree(name);
            if (tree == null)
                return;

            foreach (var page in tree.AllPages())
            {
                _lowLevelTransaction.FreePage(page);
            }

            _lowLevelTransaction.RootObjects.Delete<SliceArray>(name);

            _trees.Remove(name);
        }

        public void RenameTree(string fromName, string toName)
        {
            if (_lowLevelTransaction.Flags == (TransactionFlags.ReadWrite) == false)
                throw new ArgumentException("Cannot rename a new tree with a read only transaction");

            if (toName.Equals(Constants.RootTreeName, StringComparison.OrdinalIgnoreCase))
                throw new InvalidOperationException("Cannot create a tree with reserved name: " + toName);

            if (ReadTree(toName) != null)
                throw new ArgumentException("Cannot rename a tree with the name of an existing tree: " + toName);

            Tree fromTree = ReadTree(fromName);
            if (fromTree == null)
                throw new ArgumentException("Tree " + fromName + " does not exists");

            SliceArray key = toName;

            _lowLevelTransaction.RootObjects.Delete((SliceArray)fromName);
            var ptr = _lowLevelTransaction.RootObjects.DirectAdd(key, sizeof(TreeRootHeader));
            fromTree.State.CopyTo((TreeRootHeader*)ptr);
            fromTree.Name = toName;
            fromTree.State.IsModified = true;

            _trees.Remove(fromName);
            _trees.Remove(toName);

            AddTree(toName, fromTree);
        }

        public Tree CreateTree(string name)
        {
            Tree tree = ReadTree(name);
            if (tree != null)
                return tree;

            if (_lowLevelTransaction.Flags == (TransactionFlags.ReadWrite) == false)
                throw new InvalidOperationException("No such tree: '" + name + "' and cannot create trees in read transactions");

            SliceArray key = name;

            tree = Tree.Create(_lowLevelTransaction, this);
            tree.Name = name;
            var space = _lowLevelTransaction.RootObjects.DirectAdd(key, sizeof(TreeRootHeader));

            tree.State.CopyTo((TreeRootHeader*)space);
            tree.State.IsModified = true;
            AddTree(name, tree);

            return tree;
        }


        public void Dispose()
        {
            _lowLevelTransaction?.Dispose();
        }

        public FixedSizeTree FixedTreeFor(SliceArray treeName)
        {
            var valueSize = FixedSizeTree.GetValueSize(LowLevelTransaction, LowLevelTransaction.RootObjects, treeName);
            return FixedTreeFor(treeName, valueSize);
        }

        public FixedSizeTree FixedTreeFor(SliceArray treeName, ushort valSize)
        {
            return new FixedSizeTree(LowLevelTransaction, LowLevelTransaction.RootObjects, treeName, valSize);
        }

        public RootObjectType GetRootObjectType(SliceArray name)
        {
            var val = _lowLevelTransaction.RootObjects.DirectRead(name);
            if (val == null)
                return RootObjectType.None;

            return ((RootHeader*)val)->RootObjectType;
        }
    }

    public static class TransactionLegacyExtensions
    {
        public static TreePage GetReadOnlyTreePage(this LowLevelTransaction tx, long pageNumber)
        {
            return tx.GetPage(pageNumber).ToTreePage();
        }

        public static FixedSizeTreePage GetReadOnlyFixedSizeTreePage(this LowLevelTransaction tx, long pageNumber)
        {
            return tx.GetPage(pageNumber).ToFixedSizeTreePage();
        }
    }
}
