module ImplicitQueue

import Queue

%default total
%access private

data Digit a = Zero | One a | Two a a

export
data ImplicitQueue a =
    Shallow (Digit a)
  | Deep (Digit a) (Lazy (ImplicitQueue (a, a))) (Digit a)

export
Queue ImplicitQueue where
  empty = Shallow Zero
  isEmpty (Shallow Zero) = True
  isEmpty x              = False

  snoc (Shallow Zero) y = Shallow (One y)
  snoc (Shallow (One x)) y = Deep (Two x y) empty Zero
  snoc (Deep f m Zero) y = Deep f m (One y)
  snoc (Deep f m (One x)) y = Deep f (snoc m (x, y)) Zero
  snoc (Shallow (Two _ _)) _ = assert_unreachable
  snoc (Deep _ _ (Two _ _)) _ = assert_unreachable

  head (Shallow Zero   ) = idris_crash "empty queue"
  head (Shallow (One x)) = x
  head (Deep (One x)   m r) = x
  head (Deep (Two x y) m r) = x
  head (Shallow (Two _ _)) = assert_unreachable
  head (Deep Zero _ _) = assert_unreachable

  tail (Shallow Zero) = idris_crash "empty queue"
  tail (Shallow (One x)) = empty
  tail (Deep (Two x y) m r) = Deep (One y) m r
  tail (Deep (One x) m r) =
    if isEmpty m then Shallow r
    else let (y, z) = head m in Deep (Two y z) (tail m) r
  tail (Shallow (Two _ _)) = assert_unreachable
  tail (Deep Zero _ _) = assert_unreachable
