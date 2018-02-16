module SkewBinomialHeap

import Heap

%default total
%access private

data Tree a = Node Int a (List a) (List (Tree a))

export
data SkewBinomialHeap a = SBH (List (Tree a))

rank : Tree a -> Int
rank (Node r x xs c) = r

root : Tree a -> a
root (Node r x xs c) = x

link : Ord a => Tree a -> Tree a -> Tree a
link t1@(Node r x1 xs1 c1) t2@(Node _ x2 xs2 c2) =
  if x1 <= x2 then Node (r + 1) x1 xs1 (t2 :: c1)
  else Node (r + 1) x2 xs2 (t1 :: c2)

skewLink : Ord a => a -> Tree a -> Tree a -> Tree a
skewLink x t1 t2 =
  let Node r y ys c = link t1 t2
  in if x <= y then Node r x (y :: ys) c else Node r y (x :: ys) c

insTree : Ord a => Tree a -> List (Tree a) -> List (Tree a)
insTree t    []          = [t]
insTree t ts@(t' :: ts') =
  if rank t < rank t' then t :: ts else insTree (link t t') ts'

mrg : Ord a => List (Tree a) -> List (Tree a) -> List (Tree a)
mrg ts1                  []           = ts1
mrg     []           ts2              = ts2
mrg ts1@(t1 :: ts1') ts2@(t2 :: ts2') = case compare (rank t1) (rank t2) of
  LT => t1 :: mrg ts1' ts2
  GT => t2 :: mrg ts1 ts2'
  EQ => insTree (link t1 t2) (mrg ts1' ts2')

normalize : Ord a => List (Tree a) -> List (Tree a)
normalize []        = []
normalize (t :: ts) = insTree t ts

removeMinTree : Ord a => List (Tree a) -> (Tree a, List (Tree a))
removeMinTree [] = idris_crash "empty heap"
removeMinTree [t] = (t, [])
removeMinTree (t :: ts) = let (t', ts') = removeMinTree ts in
  if root t < root t' then (t, ts) else (t', t :: ts')

nlInsert : a -> List (Tree a) -> SkewBinomialHeap a
nlInsert x ts = SBH (Node 0 x [] [] :: ts)

export
Heap SkewBinomialHeap where
  empty = SBH []
  isEmpty (SBH ts) = isNil ts

  insert x (SBH ts@(t1 :: t2 :: ts')) =
    if rank t1 == rank t2 then SBH (skewLink x t1 t2 :: ts')
    else nlInsert x ts
  insert x (SBH ts) = nlInsert x ts

  merge (SBH ts1) (SBH ts2) = SBH (mrg (normalize ts1) (normalize ts2))

  findMin (SBH ts) = root (fst (removeMinTree ts))

  deleteMin (SBH ts) = let (Node _ x xs ts1, ts2) = removeMinTree ts
                           ts' = mrg (reverse ts1) (normalize ts2)
                       in foldr insert (SBH ts') xs
