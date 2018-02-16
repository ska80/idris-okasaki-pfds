module BottomUpMergeSort

import Sortable

%default total
%access private

export
data MergeSort a = MS Int (Lazy (List (List a)))

mrg : Ord a => List a -> List a -> List a
mrg    []         ys            = ys
mrg xs               []         = xs
mrg xs@(x :: xs') ys@(y :: ys') =
  if x <= y then x :: mrg xs' ys else y :: mrg xs ys'

addSeg : Ord a => List a -> List (List a) -> Int -> List (List a)
addSeg seg segs size = let size' = assert_total $ size `div` 2
                           r     = assert_total $ size `mod` 2 in
  if 0 == r then seg :: segs
            else addSeg (mrg seg (head segs {ok = segsNonEmpty}))
                        (tail segs {ok = segsNonEmpty})
                        (assert_smaller size size')
 where
  segsNonEmpty = believe_me "length segs = ceil lg size"

export
Sortable MergeSort where
  empty = MS 0 []
  add x (MS size segs) = MS (size + 1) (addSeg [x] segs size)
  sort (MS size segs) = foldl mrg [] segs
