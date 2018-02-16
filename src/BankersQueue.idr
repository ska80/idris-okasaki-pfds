module BankersQueue

import Queue
import OStream

%default total
%access private

export
data BankersQueue a = BQ Int (OStream a) Int (OStream a)

check : Int -> OStream a -> Int -> OStream a -> BankersQueue a
check lenf f lenr r =
  if lenr <= lenf then BQ lenf f lenr r
  else BQ (lenf+lenr) (OStream.append f (OStream.reverse r)) 0 []

export
Queue BankersQueue where
  empty = BQ 0 [] 0 []
  isEmpty (BQ lenf f lenr r) = lenf == 0

  snoc (BQ lenf f lenr r) x = check lenf f (lenr + 1) (x :: r)

  head (BQ lenf []        lenr r) = idris_crash "empty queue"
  head (BQ lenf (x :: f') lenr r) = x

  tail (BQ lenf []        lenr r) = idris_crash "empty queue"
  tail (BQ lenf (x :: f') lenr r) = check (lenf - 1) f' lenr r
