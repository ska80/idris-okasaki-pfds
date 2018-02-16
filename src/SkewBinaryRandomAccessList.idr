module SkewBinaryRandomAccessList

import RandomAccessList

%default total
%access private

data Tree a = Leaf a | Node a (Tree a) (Tree a)

export
data SkewList a = SL (List (Int, Tree a))

ncCons : a -> List (Int, Tree a) -> SkewList a
ncCons x ts = SL ((1, Leaf x) :: ts)

export
RandomAccessList SkewList where
  empty = SL []
  isEmpty (SL ts) = isNil ts

  cons x (SL ts@((w1, t1) :: (w2, t2) :: tts)) =
    if w1 == w2 then SL ((1 + w1 + w2, Node x t1 t2) :: tts) else ncCons x ts
  cons x (SL ts) = ncCons x ts

  head (SL []) = idris_crash "empty list"
  head (SL ((_, Leaf x) :: ts)) = x
  head (SL ((w, Node x t1 t2) :: ts)) = x

  tail (SL []) = ?RandomAccessList_rhs_1
  tail (SL ((_, Leaf x) :: ts)) = SL ts
  tail (SL ((w, Node x t1 t2) :: ts)) = let hw = assert_total $ w `div` 2 in
    SL ((hw, t1) :: (hw, t2) :: ts)

  lookup i (SL ts) = look i ts
   where
    lookTree : Int -> Int -> Tree a -> a
    lookTree _ 0 (Leaf x) = x
    lookTree _ i (Leaf x) = idris_crash "bad subscript"
    lookTree w 0 (Node x t1 t2) = x
    lookTree w i (Node x t1 t2) = let w' = assert_total $ w `div` 2 in
      if i <= w' then lookTree w' (i - 1) t1 else lookTree w' (i - 1 - w') t2

    look i []             = idris_crash "bad subscript"
    look i ((w, t) :: ts) =
      if i < w then lookTree w i t else look (i - w) ts

  update i y (SL ts) = SL (upd i ts)
   where
    updTree : Int -> Int -> Tree a -> Tree a
    updTree _ 0 (Leaf x) = Leaf y
    updTree _ i (Leaf x) = idris_crash "bad subscript"
    updTree w 0 (Node x t1 t2) = Node y t1 t2
    updTree w i (Node x t1 t2) = let w' = assert_total $ w `div` 2 in
      if i <= w' then Node x (updTree w' (i - 1) t1) t2
      else Node x t1 (updTree w' (i - 1 - w') t2)

    upd i [] = idris_crash "bad subscript"
    upd i ((w, t) :: ts) =
      if i < w then (w, updTree w i t) :: ts else (w, t) :: upd (i - w) ts
