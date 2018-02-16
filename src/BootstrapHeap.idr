module BootstrapHeap

import Heap

%default total
%access private

export
data BootstrapHeap : (Type -> Type) -> Type -> Type where
  E : BootstrapHeap h a
  H : a -> h (BootstrapHeap h a) -> BootstrapHeap h a

Eq a => Eq (BootstrapHeap h a) where
  x == y = assert_total $ case x of
    (H x' _) => case y of
      (H y' _) => x' == y'

Ord a => Ord (BootstrapHeap h a) where
  compare x y = assert_total $ case x of
    (H x' _) => case y of
      (H y' _) => compare x' y'

Heap h => Heap (BootstrapHeap h) where
  empty = E
  isEmpty E = True
  isEmpty _ = False

  insert x h = merge (assert_total $ H x empty) h

  merge h1 h2 = assert_total $ case h1 of
    E        => h2
    (H x p1) => case h2 of
      E        => h1
      (H y p2) => if x <= y then H x (insert h2 p1) else H y (insert h1 p2)

  findMin h = assert_total $ case h of
    E       => idris_crash "empty heap"
    (H x p) => x

  deleteMin h = assert_total $ case h of
    E => idris_crash "empty heap"
    (H x p) =>
      if isEmpty p then E
      else let (H y p1) = findMin p
               p2 = deleteMin p
           in (H y (merge p1 p2))
