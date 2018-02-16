module CatList

import CatenableList
import Queue

%default total
%access private

export
data CatList : (Type -> Type) -> Type -> Type where
  E : CatList q a
  C : a -> q (Lazy (CatList q a)) -> CatList q a

link : Queue q => CatList q a -> Lazy (CatList q a) -> CatList q a
link c s = assert_total $ case c of
  (C x q) => C x (snoc q s)
  E => assert_unreachable

linkAll : Queue q => CatList q a -> q (Lazy (CatList q a)) -> CatList q a
linkAll t q' =
  if isEmpty q'
   then t
   else link t (linkAll (Force $ head q') (assert_smaller q' $ tail q'))

export
Queue q => CatenableList (CatList q) where
  empty = E
  isEmpty E = True
  isEmpty _ = False

  xs ++ E  = xs
  E  ++ ys = ys
  xs ++ ys = link xs ys

  cons x xs = (assert_total $ C x empty) ++ xs
  snoc xs x = xs ++ (assert_total $ C x empty)

  head c = assert_total $ case c of
    E => idris_crash "empty list"
    (C x y) => x

  tail c = assert_total $ case c of
    E => idris_crash "empty list"
    (C x q) => if isEmpty q then E else linkAll (Force $ head q) (tail q)
