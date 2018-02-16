module OStream -- If just "Stream", inrreconsilable conflict with names from PRelude.Stream

%default total
%access private

mutual
  public export
  data StreamCell a = Nil | (::) a (OStream a)
  infixr 7 ::

  {-
  I haven't figured out how define Stream at the top-level and not conflict with the version from
  Prelude.
  -}
  public export
  OStream : Type -> Type
  OStream a = Lazy (StreamCell a)

mutual
  append' : OStream a -> OStream a -> OStream a
  append' []       t = t
  append' (x :: s) t = x :: OStream.append s t
  -- elaborated Delayed prevents type-directed name resolution AND you can't qualify operators

  export
  append : OStream a -> OStream a -> OStream a
  append s t = Delay (Force (append' s t))

  export
  (++) : OStream a -> OStream a -> OStream a
  (++) = append

mutual
  take' : Int -> OStream a -> OStream a
  take' 0 s        = []
  take' n []       = []
  take' n (x :: s) = x :: OStream.take (n - 1) s
  -- elaborated Delayed prevents type-directed name resolution

  export
  take : Int -> OStream a -> OStream a
  take n s = Delay (Force (take' n s))

drop' : Int -> OStream a -> OStream a
drop' 0 s        = s
drop' n []       = []
drop' n (x :: s) = drop' (n - 1) s

export
drop : Int -> OStream a -> OStream a
drop n s = Delay (Force (drop' n s))

reverse' : OStream a -> OStream a -> OStream a
reverse' []       r = r
reverse' (x :: s) r = reverse' s (x :: r)

export
reverse : OStream a -> OStream a
reverse s = Delay (Force (reverse' s []))
