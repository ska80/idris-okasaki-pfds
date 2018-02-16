module UnbalancedSet

import Set

%default total
%access private

export
data UnbalancedSet a = E | T (UnbalancedSet a) a (UnbalancedSet a)

export
Ord a => Set UnbalancedSet a where
  empty = E

  member x E = False
  member x (T a y b) = case compare x y of
    LT => member x a
    GT => member x b
    EQ => True

  insert x E = T E x E
  insert x s@(T a y b) = case compare x y of
    LT => T (insert x a) y b
    GT => T a y (insert x b)
    EQ => s
