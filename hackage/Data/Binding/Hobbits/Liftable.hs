{-# LANGUAGE GADTs, TypeOperators, FlexibleInstances, TemplateHaskell #-}
{-# LANGUAGE ViewPatterns, QuasiQuotes, DataKinds #-}

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

import Data.Type.RList
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.QQ
import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.NuMatching


{-|
  The class @Liftable a@ gives a \"lifting function\" for a, which can
  take any data of type @a@ out of a multi-binding of type @'Mb' ctx a@.
-}
class NuMatching a => Liftable a where
    mbLift :: Mb ctx a -> a

-------------------------------------------------------------------------------
-- Lifting instances that must be defined inside the library abstraction boundary
-------------------------------------------------------------------------------

instance Liftable Char where
    mbLift (ensureFreshPair -> (_, c)) = c

instance Liftable Int where
    mbLift (ensureFreshPair -> (_, i)) = i

instance Liftable Integer where
    mbLift (ensureFreshPair -> (_, i)) = i

instance Liftable (Closed a) where
    mbLift (ensureFreshPair -> (_, c)) = c


-------------------------------------------------------------------------------
-- Lifting instances and related functions that could be defined outside the library
-------------------------------------------------------------------------------

-- README: this requires overlapping instances, because it clashes
-- with Liftable2, but this instance is better because it does not
-- require c nor a to be liftable
instance Liftable (Member c a) where
    mbLift [nuP| Member_Base |] = Member_Base
    mbLift [nuP| Member_Step m |] = Member_Step (mbLift m)

-- | Lift a list (but not its elements) out of a multi-binding
mbList :: NuMatching a => Mb c [a] -> [Mb c a]
mbList [nuP| [] |] = []
mbList [nuP| x : xs |] = x : mbList xs


-------------------------------------------------------------------------------
-- Liftable1 and Liftable2
-------------------------------------------------------------------------------

instance Liftable a => Liftable [a] where
    mbLift [nuP| [] |] = []
    mbLift [nuP| x : xs |] = (mbLift x) : (mbLift xs)

instance Liftable () where
    mbLift [nuP| () |] = ()

instance (Liftable a, Liftable b) => Liftable (a,b) where
    mbLift [nuP| (x,y) |] = (mbLift x, mbLift y)

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