module CatenableDeque

import public Deque

%default total
%access private

public export
interface Deque d => CatenableDeque (d : Type -> Type) where
  (++) : d a -> d a -> d a
