{-# LANGUAGE GADTs, DeriveDataTypeable, Rank2Types, ViewPatterns #-}

-- |
-- Module      : Data.Binding.Hobbits.Internal.Name
-- Copyright   : (c) 2014 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : westbrook@kestrel.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module defines the type @'Mb' ctx a@. In order to ensure
-- adequacy of the Hobbits name-binding approach, this representation
-- is hidden, and so this file should never be imported directly by
-- the user.
--

module Data.Binding.Hobbits.Internal.Mb where

import Data.Typeable
import Data.Proxy
import Data.Type.Equality

import Data.Type.List.Map
import Data.Binding.Hobbits.Internal.Name


{-|
  An @Mb ctx b@ is a multi-binding that binds one name for each type
  in @ctx@, where @ctx@ has the form @'Nil' ':>' t1 ':>' ... ':>' tn@.
  Internally, multi-bindings are represented either as "fresh
  functions", which are functions that quantify over all fresh names
  that have not been used before and map them to the body of the
  binding, or as "fresh pairs", which are pairs of a list of names
  that are guaranteed to be fresh along with a body. Note that fresh
  pairs must come with an 'MbTypeRepr' for the body type, to ensure
  that the names given in the pair can be relaced by fresher names.
-}
data Mb ctx b
    = MkMbFun (MapC Proxy ctx) (MapC Name ctx -> b)
    | MkMbPair (MbTypeRepr b) (MapC Name ctx) b
    deriving Typeable


{-|
   This type states that it is possible to replace free names with
   fresh names in an object of type @a@. This type essentially just
   captures a representation of the type a as either a Name type, a
   multi-binding, a function type, or a (G)ADT. In order to be sure
   that only the "right" proofs are used for (G)ADTs, however, this
   type is hidden from the user, and can only be constructed with
   'mkNuMatching'.
-}

data MbTypeRepr a where
    MbTypeReprName :: MbTypeRepr (Name a)
    MbTypeReprMb :: MbTypeRepr a -> MbTypeRepr (Mb ctx a)
    MbTypeReprFun :: MbTypeRepr a -> MbTypeRepr b -> MbTypeRepr (a -> b)
    MbTypeReprData :: MbTypeReprData a -> MbTypeRepr a

data MbTypeReprData a =
    MkMbTypeReprData (forall ctx. MapC Name ctx -> MapC Name ctx -> a -> a)


{-|
  The call @mapNamesPf data ns ns' a@ replaces each occurrence of a
  free name in @a@ which is listed in @ns@ by the corresponding name
  listed in @ns'@. This is similar to the name-swapping of Nominal
  Logic, except that the swapping does not go both ways.
-}
mapNamesPf :: MbTypeRepr a -> MapC Name ctx -> MapC Name ctx -> a -> a
mapNamesPf MbTypeReprName Nil Nil n = n
mapNamesPf MbTypeReprName (names :> m) (names' :> m') n =
    case cmpName m n of
      Just Refl -> m'
      Nothing -> mapNamesPf MbTypeReprName names names' n
mapNamesPf MbTypeReprName _ _ _ = error "Should not be possible! (in mapNamesPf)"
mapNamesPf (MbTypeReprMb tRepr) names1 names2 (ensureFreshFun -> (proxies, f)) =
    -- README: the fresh function created below is *guaranteed* to not
    -- be passed elements of either names1 or names2, since it should
    -- only ever be passed fresh names
    MkMbFun proxies (\ns -> mapNamesPf tRepr names1 names2 (f ns))
mapNamesPf (MbTypeReprFun tReprIn tReprOut) names names' f =
    (mapNamesPf tReprOut names names') . f . (mapNamesPf tReprIn names' names)
mapNamesPf (MbTypeReprData (MkMbTypeReprData mapFun)) names names' x =
    mapFun names names' x


-- | Ensures a multi-binding is in "fresh function" form
ensureFreshFun :: Mb ctx a -> (MapC Proxy ctx, MapC Name ctx -> a)
ensureFreshFun (MkMbFun proxies f) = (proxies, f)
ensureFreshFun (MkMbPair tRepr ns body) =
    (mapC (\_ -> Proxy) ns, \ns' -> mapNamesPf tRepr ns ns' body)

-- | Ensures a multi-binding is in "fresh pair" form
ensureFreshPair :: Mb ctx a -> (MapC Name ctx, a)
ensureFreshPair (MkMbPair _ ns body) = (ns, body)
ensureFreshPair (MkMbFun proxies f) =
    let ns = mapC (MkName . fresh_name) proxies in
    (ns, f ns)
