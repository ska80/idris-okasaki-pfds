module BinaryRandomAccessList

import RandomAccessList

%default total
%access private

data Tree a = Leaf a | Node Int (Tree a) (Tree a)
data Digit a = Zero | One (Tree a)

export
data BinaryList a = BL (List (Digit a))

size : Tree a -> Int
size (Leaf x) = 1
size (Node w t1 t2) = w

link : Tree a -> Tree a -> Tree a
link t1 t2 = Node (size t1 + size t2) t1 t2

consTree : Tree a -> List (Digit a) -> List (Digit a)
consTree t  []             = [One t]
consTree t  (Zero   :: ts) = One t :: ts
consTree t1 (One t2 :: ts) = Zero  :: consTree (link t1 t2) ts

unconsTree : List (Digit a) -> (Tree a, List (Digit a))
unconsTree [] = idris_crash "empty list"
unconsTree [One t] = (t, [])
unconsTree (One t :: ts) = (t, Zero :: ts)
unconsTree (Zero :: ts) = case unconsTree ts of
  (Node _ t1 t2, ts') => (t1, One t2 :: ts')
  (Leaf _      , _)   => assert_unreachable

export
RandomAccessList BinaryList where
  empty = BL []
  isEmpty (BL ts) = isNil ts

  cons x (BL ts) = BL (consTree (Leaf x) ts)
  head (BL ts) = assert_total $ let (Leaf x, _) = unconsTree ts in x
  tail (BL ts) = let (_, ts') = unconsTree ts in BL ts'

  lookup i (BL ts) = look i ts
   where
    lookTree : Int -> Tree a -> a
    lookTree 0 (Leaf x)       = x
    lookTree i (Leaf x)       = idris_crash "bad subscript"
    lookTree i (Node w t1 t2) = let hw = assert_total $ w `div` 2
      in if i < hw then lookTree i t1 else lookTree (i - hw) t2

    look i []            = idris_crash "bad subscript"
    look i (Zero  :: ts) = look i ts
    look i (One t :: ts) =
      if i < size t then lookTree i t else look (i - size t) ts

  update i y (BL ts) = BL (upd i ts)
   where
    updTree : Int -> Tree a -> Tree a
    updTree 0 (Leaf x)       = Leaf y
    updTree i (Leaf x)       = idris_crash "bad subscript"
    updTree i (Node w t1 t2) = let hw = assert_total $ w `div` 2 in
      if i < hw then Node w (updTree i t1) t2
      else Node w t1 (updTree (i - hw) t2)

    upd i []            = idris_crash "bad subscript"
    upd i (Zero  :: ts) = Zero :: upd i ts
    upd i (One t :: ts) =
      if i < size t then One (updTree i t) :: ts
      else One t :: upd (i - size t) ts
