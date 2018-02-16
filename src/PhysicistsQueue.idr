module PhysicistsQueue

import Queue

%default total
%access private

export
data PhysicistsQueue a = PQ (List a) Int (Lazy (List a)) Int (List a)

checkw : List a -> Int -> List a -> Int -> List a -> PhysicistsQueue a
checkw [] lenf f lenr r = PQ f lenf f lenr r
checkw w  lenf f lenr r = PQ w lenf f lenr r

check : List a -> Int -> List a -> Int -> List a -> PhysicistsQueue a
check w lenf f lenr r =
  if lenr <= lenf then checkw w lenf f lenr r
  else checkw f (lenf + lenr) (f ++ reverse r) 0 []

export
Queue PhysicistsQueue where
  empty = PQ [] 0 [] 0 []
  isEmpty (PQ w lenf f lenr r) = lenf == 0

  snoc (PQ w lenf f lenr r) x = check w lenf f (lenr + 1) (x :: r)

  head (PQ []       lenf f lenr r) = idris_crash "empty queue"
  head (PQ (x :: w) lenf f lenr r) = x

  tail (PQ []       lenf f lenr r) = idris_crash "empty queue"
  tail (PQ (x :: w) lenf f lenr r) = check w (lenf - 1) (Prelude.List.tail {ok = nef} f) lenr r
   where nef = believe_me "f = x :: w ++ _"
