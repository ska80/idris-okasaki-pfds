module RandomAccessList

%default total
%access private

public export
interface RandomAccessList (r : Type -> Type) where
  empty : r a
  isEmpty : r a -> Bool

  cons : a -> r a -> r a
  head : r a -> a
  tail : r a -> r a

  lookup : Int -> r a -> a
  update : Int -> a -> r a -> r a
