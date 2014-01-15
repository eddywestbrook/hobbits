{-# LANGUAGE GADTs, TypeOperators, RankNTypes #-}

-- |
-- Module      : Data.Type.List.Map
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- Vectors indexed by a type list

module Data.Type.List.Map where

import Data.Type.List.List
import Data.Type.List.Proof.Append (Append(..))
import Data.Type.List.Proof.Member (Member(..))
import Data.Proxy (Proxy(..))
--import Data.Typeable

import Data.Functor.Constant

-------------------------------------------------------------------------------
-- a vector of functor values, indexed by an List
-------------------------------------------------------------------------------

{-|
  A @MapC f c@ is a vector with exactly one element of type @f a@ for
  each type @a@ in the type list @c@.
-}
data MapC f c where
  Nil :: MapC f Nil -- Creates an empty vector
  (:>) :: MapC f c -> f a -> MapC f (c :> a) -- Appends an element to the end of a vector

-- | Create an empty 'MapC' vector.
empty :: MapC f Nil
empty = Nil

-- | Create a singleton 'MapC' vector.
singleton :: f a -> MapC f (Nil :> a)
singleton x = Nil :> x

-- | Look up an element of a 'MapC' vector using a 'Member' proof.
lookup :: Member c a -> MapC f c -> f a
lookup Member_Base (_ :> x) = x
lookup (Member_Step mem') (mc :> _) = Data.Type.List.Map.lookup mem' mc
lookup _ _ = error "Should not happen! (Map.lookup)"

-- | Map a function to all elements of a 'MapC' vector.
mapC :: (forall x. f x -> g x) -> MapC f c -> MapC g c
mapC _ Nil = Nil
mapC f (mc :> x) = mapC f mc :> f x

-- | Map a binary function to all pairs of elements of two 'MapC' vectors.
mapC2 :: (forall x. f x -> g x -> h x) -> MapC f c -> MapC g c -> MapC h c
mapC2 _ Nil Nil = Nil
mapC2 f (xs :> x) (ys :> y) = mapC2 f xs ys :> f x y

-- | Append two 'MapC' vectors.
append :: MapC f c1 -> MapC f c2 -> MapC f (c1 :++: c2)
append mc Nil = mc
append mc1 (mc2 :> x) = append mc1 mc2 :> x

-- | Append two 'MapC' vectors.
appendWithPf :: Append c1 c2 c -> MapC f c1 -> MapC f c2 -> MapC f c
appendWithPf Append_Base mc Nil = mc
appendWithPf (Append_Step app) mc1 (mc2 :> x) = appendWithPf app mc1 mc2 :> x

-- | Make an 'Append' proof from any 'MapC' vector for the second
-- argument of the append.
mkAppend :: MapC f c2 -> Append c1 c2 (c1 :++: c2)
mkAppend Nil = Append_Base
mkAppend (c :> _) = Append_Step (mkAppend c)

-- | A version of 'mkAppend' that takes in a 'Proxy' argument.
mkMonoAppend :: Proxy c1 -> MapC f c2 -> Append c1 c2 (c1 :++: c2)
mkMonoAppend _ = mkAppend

-- | Split a 'MapC' vector into two pieces.
split :: Append c1 c2 c -> MapC f c -> (MapC f c1, MapC f c2)
split Append_Base mc = (mc, Nil)
split (Append_Step app) (mc :> x) = (mc1, mc2 :> x)
  where (mc1, mc2) = split app mc
split _ _ = error "Should not happen! (Map.split)"

-- | Create a 'Proxy' object for the type list of a 'MapC' vector.
proxy :: MapC f c -> Proxy c
proxy _ = Proxy

-- | Create a vector of proofs that each type in @c@ is a 'Member' of @c@.
members :: MapC f c -> MapC (Member c) c
members Nil = Nil
members (c :> _) =
  mapC Member_Step (members c) :> Member_Base

-- | Replace a single element of a 'MapC' vector.
replace :: MapC f c -> Member c a -> f a -> MapC f c
replace (xs :> _) Member_Base y = xs :> y
replace (xs :> x) (Member_Step memb) y = replace xs memb y :> x

-- | Convert a MapC to a list
mapCToList :: MapC (Constant a) c -> [a]
mapCToList Nil = []
mapCToList (xs :> Constant x) = mapCToList xs ++ [x]

-- | A type-class which ensures that ctx is a valid context, i.e., has
-- | the form (Nil :> t1 :> ... :> tn) for some types t1 through tn
class TypeCtx ctx where
  typeCtxProxies :: MapC Proxy ctx

instance TypeCtx Nil where
  typeCtxProxies = Nil

instance TypeCtx ctx => TypeCtx (ctx :> a) where
  typeCtxProxies = typeCtxProxies :> Proxy
