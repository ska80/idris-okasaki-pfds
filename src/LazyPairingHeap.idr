module LazyPairingHeap

import Heap

%default total
%access private

export
data PairingHeap a = E | T a (PairingHeap a) (Lazy (PairingHeap a))

mutual
  link : Ord a => PairingHeap a -> PairingHeap a -> PairingHeap a
  link (T x E m) a = T x a m
  link (T x b m) a = T x E (assert_total $ merge (merge a b) m)
  link E         _ = assert_unreachable

  Heap PairingHeap where
    empty = E
    isEmpty E = True
    isEmpty _ = False

    insert x a = merge (T x E E) a

    merge a E = a
    merge E b = b
    merge a@(T x _ _) b@(T y _ _) = if x <= y then link a b else link b a

    findMin E = idris_crash "empty heap"
    findMin (T x a m) = x

    deleteMin E = idris_crash "empty heap"
    deleteMin (T x a m) = merge a m
