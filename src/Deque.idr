module Deque

%default total
%access private

public export
interface Deque (q : Type -> Type) where
  empty : q a
  isEmpty : q a -> Bool

  cons : a -> q a -> q a
  head : q a -> a
  tail : q a -> q a

  snoc : q a -> a -> q a
  last : q a -> a
  init : q a -> q a
