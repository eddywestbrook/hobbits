{-# LANGUAGE TemplateHaskell, ViewPatterns #-}

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
-- This module defines the type @'Cl' a@ of closed objects of type
-- @a@. Note that, in order to ensure adequacy of the Hobbits
-- name-binding approach, this representation is hidden from the user,
-- and so this file should never be imported directly by the user.
--

module Data.Binding.Hobbits.Internal.Closed where

{-|
  The type @Cl a@ represents a closed term of type @a@,
  i.e., an expression of type @a@ with no free (Haskell) variables.
  Since this cannot be checked directly in the Haskell type system,
  the @Cl@ data type is hidden, and the user can only create
  closed terms using Template Haskell, through the 'cl' operator.
-}
newtype Cl a = Cl { unCl :: a }
