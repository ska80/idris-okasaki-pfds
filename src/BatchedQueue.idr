module BatchedQueue

import Queue

%default total
%access private

export
data BatchedQueue a = BQ (List a) (List a)

check : List a -> List a -> BatchedQueue a
check [] r = BQ (reverse r) []
check f  r = BQ f           r

export
Queue BatchedQueue where
  empty = BQ [] []
  isEmpty (BQ f r) = isNil f

  snoc (BQ f r) x = check f (x :: r)

  head (BQ []       _) = idris_crash "empty queue"
  head (BQ (x :: f) r) = x

  tail (BQ []       _) = idris_crash "empty queue"
  tail (BQ (x :: f) r) = check f r
