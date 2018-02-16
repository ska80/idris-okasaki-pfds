module AltRandomBinaryAccessList

import RandomAccessList

%default total
%access private

export
data BinaryList a = Nil | Zero (BinaryList (a, a)) | One a (BinaryList (a,a))

uncons : BinaryList a -> (a, BinaryList a)
uncons Nil = idris_crash "empty list"
uncons (One x Nil) = (x, Nil)
uncons (One x ps) = (x, Zero ps)
uncons (Zero ps) = let ((x, y), ps') = uncons ps in (x, One y ps')

mutual
  fupdate : (a -> a) -> Int -> BinaryList a -> BinaryList a
  fupdate f i Nil = idris_crash "bad subscript"
  fupdate f 0 (One x ps) = One (f x) ps
  fupdate f i (One x ps) = cons x (fupdate f (i - 1) (assert_smaller (One x ps) $ Zero ps))
  fupdate f i (Zero ps) = let i' = assert_total $ i `div` 2
                              r  = assert_total $ i `mod` 2
                              f' = \(x, y) => if 0 == r then (f x, y) else (x, f y)
                          in Zero (fupdate f' i' ps)

  export
  RandomAccessList BinaryList where
    empty = Nil
    isEmpty Nil = True
    isEmpty _   = False

    cons x Nil        = One x Nil
    cons x (Zero ps)  = One x ps
    cons x (One y ps) = Zero (cons (x, y) ps)

    head xs = fst (uncons xs)
    tail xs = snd (uncons xs)

    lookup i Nil = idris_crash "bad subscript"
    lookup 0 (One x ps) = x
    lookup i (One x ps) = lookup (i - 1) (assert_smaller (One x ps) $ Zero ps)
    lookup i (Zero ps) = let i' = assert_total $ i `div` 2
                             r  = assert_total $ i `mod` 2
                             (x, y) = lookup i' ps
                         in if 0 == r then x else y

    update i y xs = fupdate (\x => y) i xs
