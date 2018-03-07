module Heap

%default total
%access private

public export
interface Heap (h : Type -> Type) where
  empty : Ord a => h a
  isEmpty : Ord a => h a -> Bool

  insert : Ord a => a -> h a -> h a
  merge : Ord a => h a -> h a -> h a

  findMin : Ord a => h a -> a
  deleteMin : Ord a => h a -> h a
