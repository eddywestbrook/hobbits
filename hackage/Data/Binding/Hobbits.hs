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
  -- | The 'Data.Binding.Hobbits.QQ.nuP' quasiquoter allows safe pattern
  -- matching on 'Data.Binding.Hobbits.Mb.Mb'
  -- values. 'Data.Binding.Hobbits.QQ.superCombP' is similar.

  -- * Lifting values out of multi-bindings
  module Data.Binding.Hobbits.Liftable,

  -- * Ancilliary modules
  module Data.Type.List,
  -- | Type lists track the types of bound variables.
  module Data.Binding.Hobbits.NuElim
  -- | The "Data.Binding.Hobbits.NuElim" module allows elimination of
  -- bindings and multi-bindings; NOTE: this module is not covered in
  -- the \"Hobbits for Haskell\" paper.
                            ) where

import Data.Type.List
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.QQ
import Data.Binding.Hobbits.Liftable
import Data.Binding.Hobbits.NuElim
