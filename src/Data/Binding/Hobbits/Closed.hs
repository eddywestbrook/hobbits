{-# LANGUAGE TemplateHaskell, ViewPatterns, PolyKinds #-}

-- |
-- Module      : Data.Binding.Hobbits.Closed
-- Copyright   : (c) 2014 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module uses Template Haskell to distinguish closed terms, so that the
-- library can trust such functions to not contain any @Name@ values in their
-- closure.

module Data.Binding.Hobbits.Closed (
  -- * Abstract types
  Closed(),
  -- * Operators involving 'Closed'
  unClosed, mkClosed, noClosedNames, clApply, clMbApply, clApplyCl,
  -- * Typeclass for inherently closed types
  Closable(..)
) where

import Data.Type.RList
import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.Internal.Closed
import Data.Binding.Hobbits.Mb

-- | @noClosedNames@ encodes the hobbits guarantee that no name can escape its
-- multi-binding.
noClosedNames :: Closed (Name a) -> b
noClosedNames (Closed n) =
  -- We compare n to itself to force evaluation, in case the body of
  -- the closed value is non-terminating...
  case cmpName n n of
    _ ->
      error $
      "... Clever girl!" ++
      "The `noClosedNames' invariant has somehow been violated."

-- | Closed terms are closed (sorry) under application.
clApply :: Closed (a -> b) -> Closed a -> Closed b
-- could be defined with cl were it not for the GHC stage restriction
clApply (Closed f) (Closed a) = Closed (f a)

-- | Closed multi-bindings are also closed under application.
clMbApply :: Closed (Mb ctx (a -> b)) -> Closed (Mb ctx a) ->
             Closed (Mb ctx b)
clMbApply (Closed f) (Closed a) = Closed (mbApply f a)

-- | When applying a closed function, the argument can be viewed as locally
-- closed
clApplyCl :: Closed (Closed a -> b) -> Closed a -> Closed b
clApplyCl (Closed f) a = Closed (f a)

-- | FIXME: this should not be possible!!
closeBug :: a -> Closed a
closeBug = $([| \x -> $(mkClosed [| x |]) |])

-- | Typeclass for inherently closed types
class Closable a where
  toClosed :: a -> Closed a

instance Closable (Member ctx a) where
  -- NOTE: this is actually definable with mkClosed, but this is more efficient
  toClosed memb = Closed memb
