module BootstrappedQueue

import Queue

%default total
%access private

export
data BootstrappedQueue a =
  E | Q Int (List a) (BootstrappedQueue (Lazy (List a))) Int (List a)

mutual
  checkF : Int -> List a -> BootstrappedQueue (Lazy (List a)) -> Int -> List a
        -> BootstrappedQueue a
  checkF lenfm [] E lenr r = E
  checkF lenfm [] m lenr r = Q lenfm (Force $ head m) (tail m) lenr r
  checkF lenfm f  m lenr r = Q lenfm f m lenr r

  checkQ : Int -> List a -> BootstrappedQueue (Lazy (List a)) -> Int -> List a
        -> BootstrappedQueue a
  checkQ lenfm f m lenr r =
    if lenr <= lenfm then checkF lenfm f m lenr r
    else checkF (lenfm + lenr) f (snoc m (reverse r)) 0 []

  export
  Queue BootstrappedQueue where
    empty = E -- Incorrect in original: Q 0 [] E 0 []
    isEmpty E = True
    isEmpty _ = False

    snoc E x = Q 1 [x] E 0 [] -- Incorrect in original: q 1 [x] E 0 []
    snoc (Q lenfm f m lenr r) x = checkQ lenfm f m (lenr + 1) (x :: r)

    head E                            = idris_crash "empty queue"
    head (Q lenfm (x :: f') m lenr r) = x
    head (Q _     []        _ _    _) = assert_unreachable

    tail E                            = idris_crash "empty queue"
    tail (Q lenfm (x :: f') m lenr r) = assert_total $ checkQ (lenfm - 1) f' m lenr r
    tail (Q _     []        _ _    _) = assert_unreachable
