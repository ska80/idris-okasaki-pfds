module Sortable

%default total
%access private

public export
interface Sortable (s : Type -> Type) where
  empty : Ord a => s a
  add : Ord a => a -> s a -> s a
  sort : Ord a => s a -> List a
