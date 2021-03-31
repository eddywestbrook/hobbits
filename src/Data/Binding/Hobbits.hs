{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : Data.Binding.Hobbits
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This library implements multi-bindings as described in the paper
-- E. Westbrook, N. Frisby, P. Brauner, \"Hobbits for Haskell: A Library for
-- Higher-Order Encodings in Functional Programming Languages\".

module Data.Binding.Hobbits (
  -- * Values under multi-bindings
  module Data.Binding.Hobbits.Mb,
  -- | The 'Data.Binding.Hobbits.Mb.Mb' type modeling multi-bindings is the
  -- central abstract type of the library

  -- * Closed terms
  module Data.Binding.Hobbits.Closed,
  -- | The 'Data.Binding.Hobbits.Closed.Cl' type models
  -- super-combinators, which are safe functions to apply under
  -- 'Data.Binding.Hobbits.Mb.Mb'.

  -- * Pattern-matching multi-bindings and closed terms
  module Data.Binding.Hobbits.QQ,
  -- | The 'Data.Binding.Hobbits.QQ.nuP' and 'Data.Binding.Hobbits.QQ.nuPM'
  -- quasiquoters allow safe pattern matching on 'Data.Binding.Hobbits.Mb.Mb'
  -- values.

  -- * Lifting values out of multi-bindings
  module Data.Binding.Hobbits.Liftable,

  -- * Ancilliary modules
  module Data.Proxy, module Data.Type.Equality,
  -- | Type lists track the types of bound variables.

  --module Data.Type.RList,
  RList, RNil, (:>), RAssign(..), Member(..), (:++:), Append(..),
  -- | The "Data.Binding.Hobbits.NuMatching" module exposes the NuMatching
  -- class, which allows pattern-matching on (G)ADTs in the bodies of
  -- multi-bindings
  module Data.Binding.Hobbits.NuMatching,
  module Data.Binding.Hobbits.NuMatchingInstances

                            ) where

import Data.Proxy
import Data.Type.Equality
import Data.Type.RList (RList, RNil, (:>), RAssign(..), Member(..), (:++:), Append(..))
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.QQ
import Data.Binding.Hobbits.Liftable
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.NuMatchingInstances()
