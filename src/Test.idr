import CatenableDeque
import FiniteMap

import BankersDeque
import ImplicitCatenableDeque

import Trie
import TrieOfTrees

data SizedD : (Type -> Type) -> Type -> Type where
  MkSized : (sz : Int) -> (d : dt a) -> SizedD dt a

ImplicitCatenableDeque.Sized (SizedD d) where
  size (MkSized sz _) = sz

subtract : Neg n => n -> n -> n
subtract y x = x - y

Deque d => Deque (SizedD d) where
  empty = MkSized 0 empty
  isEmpty (MkSized sz _) = 0 == sz
  cons x (MkSized sz d) = MkSized (1 + sz) (cons x d)
  head (MkSized _ d) = head d
  tail (MkSized sz d) = MkSized (subtract 1 sz) (tail d)
  snoc (MkSized sz d) x = MkSized (sz + 1) (snoc d x)
  last (MkSized _ d) = last d
  init (MkSized sz d) = MkSized (sz - 1) (init d)

CatenableDeque d => CatenableDeque (SizedD d) where
  (MkSized sz1 d1) ++ (MkSized sz2 d2) = MkSized (sz1 + sz2) (d1 ++ d2)

data BoolMap : Type -> Type -> Type where
  BM : (Maybe a, Maybe a) -> BoolMap Bool a

FiniteMap BoolMap Bool where
  empty = BM (Nothing, Nothing)
  bind False x (BM t) = BM (Just x, snd t)
  bind True x (BM t) = BM (fst t, Just x)
  lookup False (BM t) = fst t
  lookup True (BM t) = snd t
