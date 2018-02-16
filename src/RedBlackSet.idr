module RedBlackSet

import Set

%default total
%access private

data Color = R | B

export
data RedBlackSet a = E | T Color (RedBlackSet a) a (RedBlackSet a)

balance : Color -> RedBlackSet a -> a -> RedBlackSet a -> RedBlackSet a
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance color a x b = T color a x b

export
Ord a => Set RedBlackSet a where
  empty = E

  member x E = False
  member x (T _ a y b) = case compare x y of
    LT => member x a
    GT => member x b
    EQ => True

  insert x s = assert_total $ let T _ a y b = ins s in T B a y b
   where
    ins : Ord a => RedBlackSet a -> RedBlackSet a
    ins E = T R E x E
    ins s'@(T color a y b) = case compare x y of
      LT => balance color (ins a) y b
      GT => balance color a y (ins b)
      EQ => s'
