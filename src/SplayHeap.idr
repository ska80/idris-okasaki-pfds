module SplayHeap

import Heap

%default total
%access private

export
data SplayHeap a = E | T (SplayHeap a) a (SplayHeap a)

partition : Ord a => a -> SplayHeap a -> (SplayHeap a, SplayHeap a)
partition pivot E = (E, E)
partition pivot t@(T a x b) =
  if x <= pivot then
    case b of
      E         => (t, E)
      T b1 y b2 =>
        if y <= pivot then
          let (small, big) = partition pivot $ assert_smaller t b2
          in (T (T a x b1) y small, big)
        else
          let (small, big) = partition pivot $ assert_smaller t b1
          in (T a x small, T big y b2)
  else
    case a of
      E         => (E, t)
      T a1 y a2 =>
        if y <= pivot then
          let (small, big) = partition pivot $ assert_smaller t a2
          in (T a1 y small, T big x b)
        else
          let (small, big) = partition pivot $ assert_smaller t a1
          in (small, T (T big y a2) x b)

export
Heap SplayHeap where
  empty = E
  isEmpty E = True
  isEmpty _ = False

  insert x t = let (a, b) = partition x t in T a x b

  merge E t = t
  merge (T a x b) t = let (ta, tb) = partition x t
    in T (assert_total $ merge ta a) x (assert_total $ merge tb b)

  findMin E = idris_crash "empty heap"
  findMin (T E x b) = x
  findMin (T a x b) = findMin a

  deleteMin E = idris_crash "empty heap"
  deleteMin (T E x b) = b
  deleteMin (T (T E x b) y c) = T b y c
  deleteMin (T (T a x b) y c) = T (deleteMin a) x (T b y c)
