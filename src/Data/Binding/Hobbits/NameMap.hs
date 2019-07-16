{-# LANGUAGE GADTs, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

-- |
-- Module      : Data.Binding.Hobbits.Mb
-- Copyright   : (c) 2019 Edwin Westbrook
--
-- License     : BSD3
--
-- Maintainer  : westbrook@galois.com
-- Stability   : experimental
-- Portability : GHC
--
-- Implements mappings from 'Name's to some associated data, using
-- 'Data.IntMap.Strict'. Note that these mappings are strict.

module Data.Binding.Hobbits.NameMap (
  NameMap(), NameAndElem(..)
  , empty, singleton, fromList
  , insert, delete, adjust, update, alter
  , lookup, (!), member, null, size
  , union, difference, (\\), intersection
  , map, foldr, foldl
  , assocs
  ) where

import Prelude hiding (lookup, null, map, foldr, foldl)
import qualified Prelude as Prelude (map)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Unsafe.Coerce

import Data.Binding.Hobbits.Internal.Name

-- | An element of a 'NameMap', where the name type @a@ is existentially
-- quantified
data NMElem (f :: k -> *) where
  NMElem :: f a -> NMElem f

-- | Coerce an @'NMElem' f@ to an @f a@ for a specific type @a@. This assumes we
-- know that this is the proper type to coerce it to, i.e., it is unsafe.
coerceNMElem :: NMElem f -> f a
coerceNMElem (NMElem x) = unsafeCoerce x

-- | A heterogeneous map from 'Name's of arbitrary type @a@ to elements of @f a@
newtype NameMap (f :: k -> *) =
  NameMap { unNameMap :: IntMap (NMElem f) }

mapNMap1 :: (IntMap (NMElem f) -> IntMap (NMElem f)) -> NameMap f -> NameMap f
mapNMap1 f (NameMap m) = NameMap $ f m

mapNMap2 :: (IntMap (NMElem f) -> IntMap (NMElem f) -> IntMap (NMElem f)) ->
            NameMap f -> NameMap f -> NameMap f
mapNMap2 f (NameMap m1) (NameMap m2) = NameMap $ f m1 m2


empty :: NameMap f
empty = NameMap IntMap.empty

singleton :: Name a -> f a -> NameMap f
singleton (MkName i) x = NameMap $ IntMap.singleton i $ NMElem x

data NameAndElem f where
  NameAndElem :: Name a -> f a -> NameAndElem f

fromList :: [NameAndElem f] -> NameMap f
fromList =
  NameMap . IntMap.fromList .
  Prelude.map (\ne ->
                case ne of
                  NameAndElem (MkName i) f -> (i, NMElem f))

insert :: Name a -> f a -> NameMap f -> NameMap f
insert (MkName i) f = mapNMap1 $ IntMap.insert i (NMElem f)

delete :: Name a -> NameMap f -> NameMap f
delete (MkName i) = mapNMap1 $ IntMap.delete i

adjust :: (f a -> f a) -> Name a -> NameMap f -> NameMap f
adjust f (MkName i) = mapNMap1 $ IntMap.adjust (NMElem . f . coerceNMElem) i

update :: (f a -> Maybe (f a)) -> Name a -> NameMap f -> NameMap f
update f (MkName i) = mapNMap1 $ IntMap.update (fmap NMElem . f . coerceNMElem) i

alter :: (Maybe (f a) -> Maybe (f a)) -> Name a -> NameMap f -> NameMap f
alter f (MkName i) =
  mapNMap1 $ IntMap.alter (fmap NMElem . f . fmap coerceNMElem) i

lookup :: Name a -> NameMap f -> Maybe (f a)
lookup (MkName i) (NameMap m) = fmap coerceNMElem $ IntMap.lookup i m

(!) :: NameMap f -> Name a -> f a
(NameMap m) ! (MkName i) = coerceNMElem $ m IntMap.! i

member :: Name a -> NameMap f -> Bool
member (MkName i) (NameMap m) = IntMap.member i m

null :: NameMap f -> Bool
null (NameMap m) = IntMap.null m

size :: NameMap f -> Int
size (NameMap m) = IntMap.size m

union :: NameMap f -> NameMap f -> NameMap f
union = mapNMap2 IntMap.union

difference :: NameMap f -> NameMap f -> NameMap f
difference = mapNMap2 IntMap.difference

(\\) :: NameMap f -> NameMap f -> NameMap f
(\\) = difference

intersection :: NameMap f -> NameMap f -> NameMap f
intersection = mapNMap2 IntMap.intersection

map :: (forall a. f a -> g a) -> NameMap f -> NameMap g
map f (NameMap m) =
  NameMap $ IntMap.map (\e -> case e of
                           NMElem x -> NMElem $ f x) m

foldr :: (forall a. f a -> b -> b) -> b -> NameMap f -> b
foldr f b (NameMap m) =
  IntMap.foldr (\e -> case e of
                   NMElem x -> f x) b m

foldl :: (forall b. a -> f b -> a) -> a -> NameMap f -> a
foldl f a (NameMap m) =
  IntMap.foldl (\a e -> case e of
                   NMElem x -> f a x) a m

assocs :: NameMap f -> [NameAndElem f]
assocs (NameMap m) =
  Prelude.map (\(i, e) -> case e of
                  NMElem f -> NameAndElem (MkName i) f) $
  IntMap.assocs m
