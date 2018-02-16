module Trie

import FiniteMap

%default total
%access private

export
data Trie : (Type -> Type) -> Type -> Type -> Type where
  MkTrie : Maybe a -> mk (Trie mk ks a) -> Trie mk ks a

export
FiniteMap m k => FiniteMap (Trie (m k)) (List k) where
  empty = assert_total $ MkTrie Nothing empty

  lookup [] t = assert_total $ case t of
    MkTrie b m => b
  lookup (k :: ks) t = assert_total $ case t of
    MkTrie b m => lookup k m >>= \m' => lookup ks m'

  bind [] x t = assert_total $ case t of
    MkTrie b m => MkTrie (Just x) m
  bind (k :: ks) x t = assert_total $ case t of
    MkTrie b m => let t = fromMaybe empty $ lookup k m
                      t' = bind ks x t
                  in MkTrie b (bind k t' m)
