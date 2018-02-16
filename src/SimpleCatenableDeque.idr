module SimpleCatenableDeque

import CatenableDeque

export
data SimpleCatDeque : (Type -> Type) -> Type -> Type where
  Shallow : d a -> SimpleCatDeque d a
  Deep : d a -> Lazy (SimpleCatDeque d (d a)) -> d a -> SimpleCatDeque d a

tooSmall : Deque d => d a -> Bool
tooSmall d = isEmpty d || isEmpty (tail d)

dappendL : Deque d => d a {- tooSmall -} -> d a -> d a
dappendL d1 d2 = if isEmpty d1 then d2 else cons (head d1) d2

dappendR : Deque d => d a -> d a {- tooSmall -} -> d a
dappendR d1 d2 = if isEmpty d2 then d1 else snoc d1 (head d2)

export
Deque d => Deque (SimpleCatDeque d) where
  empty = Shallow empty
  isEmpty (Shallow d) = isEmpty d
  isEmpty _           = False

  cons x (Shallow d)  = Shallow (cons x d)
  cons x (Deep f m r) = Deep (cons x f) m r

  head (Shallow d)  = head d
  head (Deep f m r) = head f

  tail (Shallow d)  = Shallow (tail d)
  tail (Deep f m r) = let f' = tail f in
    if not (tooSmall f') then Deep f' m r
    else if isEmpty m then Shallow (dappendL f' r)
    else Deep (dappendL f' (head m)) (tail m) r

  snoc (Shallow d) x  = Shallow (snoc d x)
  snoc (Deep f m r) x = Deep f m (snoc r x)

  last (Shallow d)  = last d
  last (Deep f m r) = last r

  init (Shallow d) = Shallow (init d)
  init (Deep f m r) = let r' = init r in
    if not (tooSmall r') then Deep f m r'
    else if isEmpty m then Shallow (dappendR f r')
    else Deep f (init m) (dappendR (last m) r')

export
Deque d => CatenableDeque (SimpleCatDeque d) where
  (Shallow d1) ++ (Shallow d2) =
    if tooSmall d1 then Shallow (dappendL d1 d2)
    else if tooSmall d2 then Shallow (dappendR d1 d2)
    else Deep d1 empty d2
  (Shallow d) ++ (Deep f m r) =
    if tooSmall d then Deep (dappendL d f) m r
    else Deep d (cons f m) r
  (Deep f m r) ++ (Shallow d) =
    if tooSmall d then Deep f m (dappendR r d)
    else Deep f (snoc m r) d
  (Deep f1 m1 r1) ++ (Deep f2 m2 r2) =
    let mf = assert_smaller (Deep f1 m1 r2) $ snoc m1 r1
        mr = assert_smaller (Deep f2 m2 r2) $ cons f2 m2
    in Deep f1 (mf ++ mr) r2
