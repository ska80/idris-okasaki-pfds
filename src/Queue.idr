module Queue

%default total
%access private

public export
interface Queue (q: Type -> Type) where
  empty : q a
  isEmpty : q a -> Bool

  snoc : q a -> a -> q a
  head : q a -> a
  tail : q a -> q a
