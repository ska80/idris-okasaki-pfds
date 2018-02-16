module Set

%default total
%access private

public export
interface Set (s : Type -> Type) a where
  empty : s a
  insert : a -> s a -> s a
  member : a -> s a -> Bool
