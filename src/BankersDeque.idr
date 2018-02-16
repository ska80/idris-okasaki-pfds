module BankersDeque

import Deque

%default total
%access private

export
data BankersDeque a = BD Int (List a) Int (List a)

c : Int
c = 3

check : Int -> List a -> Int -> List a -> BankersDeque a
check lenf f lenr r =
  if lenf > c * lenr + 1 then
     let i = assert_total $ (lenf + lenr) `div` 2
         j = lenf + lenr - i
         f' = take (toNat i) f
         r' = r ++ reverse (drop (toNat i) f)
     in BD i f' j r'
  else if lenr > c * lenf + 1 then
    let j = assert_total $ (lenf + lenr) `div` 2
        i = lenf + lenr - j
        r' = take (toNat j) r
        f' = f ++ reverse (drop (toNat j) r)
    in BD i f' j r'
  else BD lenf f lenr r

export
Deque BankersDeque where
  empty = BD 0 [] 0 []
  isEmpty (BD lenf f lenr r) = lenf + lenr == 0

  cons x (BD lenf f lenr r) = check (lenf + 1) (x :: f) lenr r

  head (BD lenf []        lenr [x]) = x -- Missing in Haskell original
  head (BD lenf []        lenr r)   = idris_crash "empty deque"
  head (BD lenf (x :: f') lenr r)   = x

  tail (BD lenf []        lenr [x]) = empty -- Missing in Haskell original
  tail (BD lenf []        lenr r)   = idris_crash "empty deque"
  tail (BD lenf (x :: f') lenr r)   = check (lenf - 1) f' lenr r

  snoc (BD lenf f lenr r) x = check lenf f (lenr + 1) (x :: r)

  last (BD lenf [x] lenr [])        = x -- Missing in Haskell original
  last (BD lenf f   lenr [])        = idris_crash "empty deque"
  last (BD lenf f   lenr (x :: r')) = x

  init (BD lenf [x] lenr [])        = empty -- Missing in Haskell original
  init (BD lenf f   lenr [])        = idris_crash "empty deque"
  init (BD lenf f   lenr (x :: r')) = check lenf f (lenr - 1) r'
