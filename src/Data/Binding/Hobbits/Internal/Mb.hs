{-# LANGUAGE GADTs, DeriveDataTypeable, ViewPatterns #-}
{-# LANGUAGE RankNTypes, DataKinds, PolyKinds #-}

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
import Data.Type.RList hiding (map)

import Data.Binding.Hobbits.Internal.Name


{-|
  An @Mb ctx b@ is a multi-binding that binds one name for each type
  in @ctx@, where @ctx@ has the form @'RNil' ':>' t1 ':>' ... ':>' tn@.
  Internally, multi-bindings are represented either as "fresh
  functions", which are functions that quantify over all fresh names
  that have not been used before and map them to the body of the
  binding, or as "fresh pairs", which are pairs of a list of names
  that are guaranteed to be fresh along with a body. Note that fresh
  pairs must come with an 'MbTypeRepr' for the body type, to ensure
  that the names given in the pair can be relaced by fresher names.
-}
data Mb (ctx :: RList k) b
    = MkMbFun (RAssign Proxy ctx) (RAssign Name ctx -> b)
    | MkMbPair (MbTypeRepr b) (RAssign Name ctx) b
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
    MkMbTypeReprData (forall ctx. NameRefresher -> a -> a)

{-|
  The call @mapNamesPf data ns ns' a@ replaces each occurrence of a
  free name in @a@ which is listed in @ns@ by the corresponding name
  listed in @ns'@. This is similar to the name-swapping of Nominal
  Logic, except that the swapping does not go both ways.
-}
mapNamesPf :: MbTypeRepr a -> NameRefresher -> a -> a
mapNamesPf MbTypeReprName refresher n = refreshName refresher n
mapNamesPf (MbTypeReprMb tRepr) refresher (ensureFreshFun -> (proxies, f)) =
    -- README: the fresh function created below is *guaranteed* to not
    -- be passed elements of either names1 or names2, since it should
    -- only ever be passed fresh names
    MkMbFun proxies (\ns -> mapNamesPf tRepr refresher (f ns))
mapNamesPf (MbTypeReprFun tReprIn tReprOut) refresher f =
    (mapNamesPf tReprOut refresher) . f . (mapNamesPf tReprIn refresher)
mapNamesPf (MbTypeReprData (MkMbTypeReprData mapFun)) refresher x =
    mapFun refresher x


-- | Ensures a multi-binding is in "fresh function" form
ensureFreshFun :: Mb ctx a -> (RAssign Proxy ctx, RAssign Name ctx -> a)
ensureFreshFun (MkMbFun proxies f) = (proxies, f)
ensureFreshFun (MkMbPair tRepr ns body) =
    (mapRAssign (\_ -> Proxy) ns, \ns' ->
      mapNamesPf tRepr (mkRefresher ns ns') body)

-- | Ensures a multi-binding is in "fresh pair" form
ensureFreshPair :: Mb ctx a -> (RAssign Name ctx, a)
ensureFreshPair (MkMbPair _ ns body) = (ns, body)
ensureFreshPair (MkMbFun proxies f) =
    let ns = mapRAssign (MkName . fresh_name) proxies in
    (ns, f ns)
