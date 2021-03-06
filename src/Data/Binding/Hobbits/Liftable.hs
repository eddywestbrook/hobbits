{-# LANGUAGE GADTs, TypeOperators, FlexibleInstances, TemplateHaskell #-}
{-# LANGUAGE ViewPatterns, QuasiQuotes, DataKinds, PolyKinds #-}

-- |
-- Module      : Data.Binding.Hobbits.Mb
-- Copyright   : (c) 2014 Edwin Westbrook
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module defines the type-class Liftable for lifting
-- non-binding-related data out of name-bindings. Note that this code
-- is not "trusted", i.e., it is not part of the name-binding
-- abstraction: instead, it is all written using the primitives
-- exported by the Mb

module Data.Binding.Hobbits.Liftable where

import Data.Type.RList as RL
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.QQ
import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.NuMatchingInstances ()

import Data.Ratio
import Data.Proxy
import Numeric.Natural
import Data.Functor.Compose
import Data.Type.Equality


{-|
  The class @Liftable a@ gives a \"lifting function\" for a, which can
  take any data of type @a@ out of a multi-binding of type @'Mb' ctx a@.
-}
class NuMatching a => Liftable a where
    mbLift :: Mb ctx a -> a

{-|
  The class @LiftableAny1 f@ gives a family of lifting functions for the
  functor f, which can take any data of type @f a@ out of a multi-binding of
  type @'Mb' ctx (f a)@.
-}
class NuMatchingAny1 f => LiftableAny1 f where
  mbLiftAny1 :: Mb ctx (f a) -> f a


-------------------------------------------------------------------------------
-- * Lifting instances that must be defined inside the library abstraction boundary
-------------------------------------------------------------------------------

instance Liftable Char where
    mbLift (ensureFreshPair -> (_, c)) = c

instance Liftable Int where
    mbLift (ensureFreshPair -> (_, i)) = i

instance Liftable Integer where
    mbLift (ensureFreshPair -> (_, i)) = i

instance Liftable (Closed a) where
    mbLift (ensureFreshPair -> (_, c)) = c

instance Liftable Natural where
    mbLift (ensureFreshPair -> (_, i)) = i


-------------------------------------------------------------------------------
-- * Lifting instances and related functions that could be defined outside the library
-------------------------------------------------------------------------------

instance LiftableAny1 Proxy where
  mbLiftAny1 = mbLift

-- README: this requires overlapping instances, because it clashes
-- with Liftable2, but this instance is better because it does not
-- require c nor a to be liftable
instance Liftable (Member c a) where
  mbLift mb_x = case mbMatch mb_x of
    [nuMP| Member_Base |] -> Member_Base
    [nuMP| Member_Step m |] -> Member_Step (mbLift m)

-- | Lift a list (but not its elements) out of a multi-binding
mbList :: NuMatching a => Mb c [a] -> [Mb c a]
mbList mb_xs = case mbMatch mb_xs of
  [nuMP| [] |] -> []
  [nuMP| x : xs |] -> x : mbList xs

-- | Convert an 'RAssign' in a binding to an 'RAssign' of bindings
mbRAssign :: NuMatchingAny1 f => Mb ctx (RAssign f as) ->
             RAssign (Compose (Mb ctx) f) as
mbRAssign mb_xs = case mbMatch mb_xs of
  [nuMP| MNil |] -> MNil
  [nuMP| mb_xs' :>: mb_x |] -> mbRAssign mb_xs' :>: Compose mb_x

-- | Convert a 'Maybe' in a binding to a 'Maybe' of a binding
mbMaybe :: NuMatching a => Mb ctx (Maybe a) -> Maybe (Mb ctx a)
mbMaybe mb_x = case mbMatch mb_x of
  [nuMP| Just mb_a |] -> Just mb_a
  [nuMP| Nothing |] -> Nothing

instance (Integral a, Liftable a) => Liftable (Ratio a) where
  mbLift mb_r =
    (\(n,d) -> n%d) $ mbLift $ fmap (\r -> (numerator r, denominator r)) mb_r

instance Liftable a => Liftable [a] where
  mbLift mb_xs = case mbMatch mb_xs of
    [nuMP| [] |] -> []
    [nuMP| x : xs |] -> (mbLift x) : (mbLift xs)

instance LiftableAny1 f => Liftable (RAssign f ctx) where
  mbLift mb_xs = case mbMatch mb_xs of
    [nuMP| MNil |] -> MNil
    [nuMP| xs :>: x |] -> mbLift xs :>: mbLiftAny1 x

-- | Convert an 'RAssign' in a binding to an 'RAssign' of 'Proxy's
mbRAssignProxies :: Mb ctx (RAssign f as) -> RAssign Proxy as
mbRAssignProxies = mbLift . fmap (RL.map (const Proxy))

instance Liftable () where
  mbLift (mbMatch -> [nuMP| () |]) = ()

instance (Liftable a, Liftable b) => Liftable (a,b) where
  mbLift (mbMatch -> [nuMP| (x,y) |]) = (mbLift x, mbLift y)

instance Liftable Bool where
  mbLift mb_x = case mbMatch mb_x of
    [nuMP| True |] -> True
    [nuMP| False |] -> False

instance Liftable a => Liftable (Maybe a) where
  mbLift mb_x = case mbMatch mb_x of
    [nuMP| Nothing |] -> Nothing
    [nuMP| Just mb_a |] -> Just $ mbLift mb_a

instance (Liftable a, Liftable b) => Liftable (Either a b) where
  mbLift mb_x = case mbMatch mb_x of
    [nuMP| Left mb_a |] -> Left $ mbLift mb_a
    [nuMP| Right mb_b |] -> Right $ mbLift mb_b

instance Liftable (a :~: b) where
  mbLift (mbMatch -> [nuMP| Refl |]) = Refl

instance Liftable (Proxy (a :: k)) where
  mbLift (mbMatch -> [nuMP| Proxy |]) = Proxy



-- README: these lead to overlapping instances...

{-

{-|
  The class @Liftable1 f@ gives a lifting function for each type @f a@
  when @a@ itself is @Liftable@.
-}
class Liftable1 f where
    mbLift1 :: Liftable a => Mb ctx (f a) -> f a

instance (Liftable1 f, Liftable a) => Liftable (f a) where
    mbLift = mbLift1

instance Liftable1 [] where
    mbLift1 [nuP| [] |] = []
    mbLift1 [nuP| x : xs |] = (mbLift x) : (mbLift1 xs)

{-|
  The class @Liftable2 f@ gives a lifting function for each type @f a b@
  when @a@ and @b@ are @Liftable@.
-}
class Liftable2 f where
    mbLift2 :: (Liftable a, Liftable b) => Mb ctx (f a b) -> f a b

instance Liftable2 (,) where
    mbLift2 [nuP| (x,y) |] = (mbLift x, mbLift y)

instance (Liftable2 f, Liftable a) => Liftable1 (f a) where
    mbLift1 = mbLift2

-}
