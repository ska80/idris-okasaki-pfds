module TrieOfTrees

import FiniteMap

%default total
%access private

public export
data Tree a = E | T a (Tree a) (Tree a)

export
data Trie : (Type -> Type) -> Type -> Type -> Type where
  MkTrie : Maybe a -> mk (Trie mk ks (Trie mk ks a)) -> Trie mk ks a

export
FiniteMap m k => FiniteMap (Trie (m k)) (Tree k) where
  empty = assert_total $ MkTrie Nothing empty

  lookup E t = assert_total $ case t of
    MkTrie v m => v
  lookup (T k a b) t = assert_total $ case t of
    MkTrie v m => do
      m' <- lookup k m
      m'' <- lookup a m'
      lookup b m''

  bind E x t = assert_total $ case t of
    MkTrie v m => MkTrie (Just x) m
  bind (T k a b) x t = assert_total $ case t of
    MkTrie v m => let tt  = fromMaybe empty $ lookup k m
                      t   = fromMaybe empty $ lookup a tt
                      t'  = bind b x t
                      tt' = bind a t' tt
                  in MkTrie v (bind k tt' m)
