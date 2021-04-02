{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

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
--
-- All of the functions in this module operate in an identical manner as those
-- of the same name in the 'Data.IntMap.Strict' module.

module Data.Binding.Hobbits.NameMap (
  NameMap(), NameAndElem(..)
  , empty, singleton, fromList
  , insert, delete, adjust, update, alter
  , lookup, (!), member, null, size
  , union, difference, (\\), intersection
  , map, foldr, foldl
  , assocs
  , liftNameMap
  ) where

import Prelude hiding (lookup, null, map, foldr, foldl)
import qualified Prelude as Prelude (map)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Unsafe.Coerce

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.NuMatchingInstances ()
import Data.Binding.Hobbits.QQ

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
  NameMap (IntMap (NMElem f))

-- | Internal-only helper function for mapping a unary function on 'IntMap's to
-- a 'NameMap'
mapNMap1 :: (IntMap (NMElem f) -> IntMap (NMElem f)) -> NameMap f -> NameMap f
mapNMap1 f (NameMap m) = NameMap $ f m

-- | Internal-only helper function for mapping a binary function on 'IntMap's to
-- 'NameMap's
mapNMap2 :: (IntMap (NMElem f) -> IntMap (NMElem f) -> IntMap (NMElem f)) ->
            NameMap f -> NameMap f -> NameMap f
mapNMap2 f (NameMap m1) (NameMap m2) = NameMap $ f m1 m2

-- | The empty 'NameMap'
empty :: NameMap f
empty = NameMap IntMap.empty

-- | The singleton 'NameMap' with precisely one 'Name' and corresponding value
singleton :: Name a -> f a -> NameMap f
singleton (MkName i) x = NameMap $ IntMap.singleton i $ NMElem x

-- | A pair of a 'Name' of some type @a@ along with an element of type @f a@
data NameAndElem f where
  NameAndElem :: Name a -> f a -> NameAndElem f

-- | Build a 'NameMap' from a list of pairs of names and values they map to
fromList :: [NameAndElem f] -> NameMap f
fromList =
  NameMap . IntMap.fromList .
  Prelude.map (\ne ->
                case ne of
                  NameAndElem (MkName i) f -> (i, NMElem f))

-- | Insert a 'Name' and a value it maps to into a 'NameMap'
insert :: Name a -> f a -> NameMap f -> NameMap f
insert (MkName i) f = mapNMap1 $ IntMap.insert i (NMElem f)

-- | Delete a 'Name' and the value it maps to from a 'NameMap'
delete :: Name a -> NameMap f -> NameMap f
delete (MkName i) = mapNMap1 $ IntMap.delete i

-- | Apply a function to the value mapped to by a 'Name'
adjust :: (f a -> f a) -> Name a -> NameMap f -> NameMap f
adjust f (MkName i) = mapNMap1 $ IntMap.adjust (NMElem . f . coerceNMElem) i

-- | Update the value mapped to by a 'Name', possibly deleting it
update :: (f a -> Maybe (f a)) -> Name a -> NameMap f -> NameMap f
update f (MkName i) = mapNMap1 $ IntMap.update (fmap NMElem . f . coerceNMElem) i

-- | Apply a function to the optional value associated with a 'Name', where
-- 'Nothing' represents the 'Name' not being present in the 'NameMap'
alter :: (Maybe (f a) -> Maybe (f a)) -> Name a -> NameMap f -> NameMap f
alter f (MkName i) =
  mapNMap1 $ IntMap.alter (fmap NMElem . f . fmap coerceNMElem) i

-- | Look up the value associated with a 'Name', returning 'Nothing' if there is
-- none
lookup :: Name a -> NameMap f -> Maybe (f a)
lookup (MkName i) (NameMap m) = fmap coerceNMElem $ IntMap.lookup i m

-- | Synonym for 'lookup' with the argument order reversed
(!) :: NameMap f -> Name a -> f a
(NameMap m) ! (MkName i) = coerceNMElem $ m IntMap.! i

-- | Test if a 'Name' has a value in a 'NameMap'
member :: Name a -> NameMap f -> Bool
member (MkName i) (NameMap m) = IntMap.member i m

-- | Test if a 'NameMap' is empty
null :: NameMap f -> Bool
null (NameMap m) = IntMap.null m

-- | Return the number of 'Name's in a 'NameMap'
size :: NameMap f -> Int
size (NameMap m) = IntMap.size m

-- | Union two 'NameMap's
union :: NameMap f -> NameMap f -> NameMap f
union = mapNMap2 IntMap.union

-- | Remove all bindings in the first 'NameMap' for 'Name's in the second
difference :: NameMap f -> NameMap f -> NameMap f
difference = mapNMap2 IntMap.difference

-- | Infix synonym for 'difference'
(\\) :: NameMap f -> NameMap f -> NameMap f
(\\) = difference

-- | Intersect two 'NameMap's
intersection :: NameMap f -> NameMap f -> NameMap f
intersection = mapNMap2 IntMap.intersection

-- | Map a function across the values associated with each 'Name'
map :: (forall a. f a -> g a) -> NameMap f -> NameMap g
map f (NameMap m) =
  NameMap $ IntMap.map (\e -> case e of
                           NMElem x -> NMElem $ f x) m

-- | Perform a right fold across all values in a 'NameMap'
foldr :: (forall a. f a -> b -> b) -> b -> NameMap f -> b
foldr f b (NameMap m) =
  IntMap.foldr (\e -> case e of
                   NMElem x -> f x) b m

-- | Perform a left fold across all values in a 'NameMap'
foldl :: (forall b. a -> f b -> a) -> a -> NameMap f -> a
foldl f a (NameMap m) =
  IntMap.foldl (\a' e -> case e of
                   NMElem x -> f a' x) a m

-- | Return all 'Name's in a 'NameMap' with their associated values
assocs :: NameMap f -> [NameAndElem f]
assocs (NameMap m) =
  Prelude.map (\(i, e) -> case e of
                  NMElem f -> NameAndElem (MkName i) f) $
  IntMap.assocs m

$(mkNuMatching [t| forall f. NuMatchingAny1 f => NameAndElem f |])

-- | Lift a 'NameMap' out of a name-binding using a "partial lifting function"
-- that can lift some values in the 'NameMap' out of the binding. The resulting
-- 'NameMap' contains those names and associated values where the names were not
-- bound by the name-binding and the partial lifting function was able to lift
-- their associated values.
liftNameMap :: forall ctx f. NuMatchingAny1 f =>
               (forall a. Mb ctx (f a) -> Maybe (f a)) ->
               Mb ctx (NameMap f) -> NameMap f
liftNameMap lifter = helper . fmap assocs where
  helper :: Mb ctx [NameAndElem f] -> NameMap f
  helper mb_x = case mbMatch mb_x of
    [nuMP| [] |] -> empty
    [nuMP| (NameAndElem mb_n mb_f):mb_elems |]
      | Right n <- mbNameBoundP mb_n
      , Just f <- lifter mb_f
      -> insert n f (helper mb_elems)
    [nuMP| _:mb_elems |] -> helper mb_elems
