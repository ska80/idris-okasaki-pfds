module FiniteMap

%default total
%access private

public export
interface FiniteMap (m : Type -> Type -> Type) k where
  empty : m k a
  bind : k -> a -> m k a -> m k a
  lookup : k -> m k a -> Maybe a
