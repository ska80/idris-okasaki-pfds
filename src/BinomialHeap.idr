module BinomialHeap

import Heap

%default total
%access private

data Tree a = Node Int a (List (Tree a))

export
data BinomialHeap a = BH (List (Tree a))

rank : Tree a -> Int
rank (Node r x c) = r

root : Tree a -> a
root (Node r x c) = x

link : Ord a => Tree a -> Tree a -> Tree a
link t1@(Node r x1 c1) t2@(Node _ x2 c2) =
  if x1 <= x2 then Node (r + 1) x1 (t2 :: c1) else Node (r + 1) x2 (t1 :: c2)

insTree : Ord a => Tree a -> List (Tree a) -> List (Tree a)
insTree t []             = [t]
insTree t ts@(t' :: ts') =
  if rank t < rank t' then t :: ts else insTree (link t t') ts'

mrg : Ord a => List (Tree a) -> List (Tree a) -> List (Tree a)
mrg ts1                  []           = ts1
mrg     []           ts2              = ts2
mrg ts1@(t1 :: ts1') ts2@(t2 :: ts2') = case compare (rank t1) (rank t2) of
  LT => t1 :: mrg ts1' ts2
  GT => t2 :: mrg ts1 ts2'
  EQ => insTree (link t1 t2) (mrg ts1' ts2')

removeMinTree : Ord a => List (Tree a) -> (Tree a, List (Tree a))
removeMinTree [] = idris_crash "empty heap"
removeMinTree [t] = (t, [])
removeMinTree (t :: ts) = let (t', ts') = removeMinTree ts in
  if root t < root t' then (t, ts) else (t', t :: ts')

Heap BinomialHeap where
  empty = BH []
  isEmpty (BH ts) = isNil ts

  insert x (BH ts) = BH (insTree (Node 0 x []) ts)

  merge (BH ts1) (BH ts2) = BH (mrg ts1 ts2)

  findMin (BH ts) = root (fst (removeMinTree ts))

  deleteMin (BH ts) = let (Node _ x ts1, ts2) = removeMinTree ts
    in BH (mrg (reverse ts1) ts2)
