module CatenableList

%default total
%access private

public export
interface CatenableList (c : Type -> Type) where
  empty : c a
  isEmpty : c a -> Bool

  cons : a -> c a -> c a
  snoc : c a -> a -> c a
  (++) : c a -> c a -> c a

  head : c a -> a
  tail : c a -> c a
