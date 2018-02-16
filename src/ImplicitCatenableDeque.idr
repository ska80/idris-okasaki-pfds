module ImplicitCatenableDeque

import CatenableDeque

%default total
%access private

public export
interface Sized (d : Type -> Type) where
  size : d a -> Int

mutual
  export
  data ImplicitCatDeque : (Type -> Type) -> Type -> Type where
    Shallow : d a -> ImplicitCatDeque d a
    Deep : d a -> Lazy (ImplicitCatDeque d (CmpdElem d a)) -> d a
        -> Lazy (ImplicitCatDeque d (CmpdElem d a)) -> d a
        -> ImplicitCatDeque d a

  data CmpdElem : (Type -> Type) -> Type -> Type where
    Simple : d a -> CmpdElem d a
    Cmpd : d a -> Lazy (ImplicitCatDeque d (CmpdElem d a)) -> d a
        -> CmpdElem d a

dappendL : Deque d => d a {- size < 4 -} -> d a -> d a
dappendL d1 d2 =
  if isEmpty d1 then d2 else dappendL (assert_smaller d1 $ init d1) (cons (last d1) d2)

dappendR : Deque d => d a -> d a {- size < 4 -} -> d a
dappendR d1 d2 =
  if isEmpty d2 then d1 else dappendR (snoc d1 (head d2)) (assert_smaller d2 $ tail d2)

replaceHead : Deque d => a -> ImplicitCatDeque d a -> ImplicitCatDeque d a
replaceHead x (Shallow d) = Shallow (cons x (tail d))
replaceHead x (Deep f a m b r) = Deep (cons x (tail f)) a m b r

replaceLast : Deque d => ImplicitCatDeque d a -> a -> ImplicitCatDeque d a
replaceLast (Shallow d) x = Shallow (snoc (init d) x)
replaceLast (Deep f a m b r) x = Deep f a m b (snoc (init r) x)

share : Deque d => d a -> d a -> (d a, d a, d a)
share f r = let m = cons (last f) (cons (head r) empty) in (init f, m, tail r)

mutual
  export
  (Deque d, Sized d) => Deque (ImplicitCatDeque d) where
    empty = Shallow empty
    isEmpty (Shallow d) = isEmpty d
    isEmpty _ = False

    cons x (Shallow d) = Shallow (cons x d)
    cons x (Deep f a m b r) = Deep (cons x f) a m b r

    head (Shallow d) = head d
    head (Deep f a m b r) = head f

    tail (Shallow d) = Shallow (tail d)
    tail (Deep f a m b r) =
      if size f > 3 then Deep (tail f) a m b r
      else if not (isEmpty a) then
        case head a of
          (Simple d) => let f' = dappendL (tail f) d
                        in Deep f' (tail a) m b r
          (Cmpd f' c' r') => let f'' = dappendL (tail f) f'
                                 a'' = c' ++ replaceHead (Simple r') a
                             in Deep f'' a'' m b r
      else if not (isEmpty b) then
        case head b of
          (Simple d) => let f' = dappendL (tail f) m
                        in Deep f' empty d (tail b) r
          (Cmpd f' c' r') => let f'' = dappendL (tail f) m
                                 a'' = cons (Simple f') c'
                             in Deep f'' a'' r' (tail b) r
      else Shallow (dappendL (tail f) m) ++ Shallow r

    snoc (Shallow d) x = Shallow (snoc d x)
    snoc (Deep f a m b r) x = Deep f a m b (snoc r x)

    last (Shallow d) = last d
    last (Deep f a m b r) = last r

    init (Shallow d) = Shallow (init d)
    init (Deep f a m b r) =
      if size r > 3 then Deep f a m b (init r)
      else if not (isEmpty b) then
        case last b of
          (Simple d) => let r' = dappendR d (init r)
                        in Deep f a m (init b) r'
          (Cmpd f' c' r') => let r'' = dappendR r' (init r)
                                 b'' = replaceLast b (Simple f') ++ c'
                             in Deep f a m b'' r''
      else if not (isEmpty a) then
        case last a of
          (Simple d) => let r' = dappendR m (init r)
                        in Deep f (init a) d empty r'
          (Cmpd f' c' r') => let r'' = dappendR m (init r)
                                 b'' = snoc c' (Simple r')
                             in Deep f (init a) f' b'' r''
      else Shallow f ++ Shallow (dappendR m (init r))

  export
  (Deque d, Sized d) => CatenableDeque (ImplicitCatDeque d) where
    (Shallow d1) ++ (Shallow d2) =
      if size d1 < 4 then Shallow (dappendL d1 d2)
      else if size d2 < 4 then Shallow (dappendR d1 d2)
      else let (f, m, r) = share d1 d2 in Deep f empty m empty r
    (Shallow d) ++ (Deep f a m b r) =
      if size d < 4 then Deep (dappendL d f) a m b r
      else Deep d (cons (Simple f) a) m b r
    (Deep f a m b r) ++ (Shallow d) =
      if size d < 4 then Deep f a m b (dappendR r d)
      else Deep f a m (snoc b (Simple r)) d
    (Deep f1 a1 m1 b1 r1) ++ (Deep f2 a2 m2 b2 r2) =
      let (r1', m, f2') = share r1 f2
          a1' = snoc a1 (Cmpd m1 b1 r1')
          b2' = cons (Cmpd f2' a2 m2) b2
      in Deep f1 a1' m b2' r2
