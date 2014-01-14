{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- |
-- Module      : Data.Type.List.List
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- The type-level constructors of type lists.

module Data.Type.List.List where

import Data.Proxy (Proxy(..))
import Data.Typeable

-------------------------------------------------------------------------------
-- type-level lists
-------------------------------------------------------------------------------

data Nil deriving Typeable
data r :> a deriving Typeable; infixl 5 :>

type family (r1 :++: r2); infixr 5 :++:
type instance r :++: Nil = r
type instance r1 :++: r2 :> a = (r1 :++: r2) :> a

proxyCons :: Proxy r -> f a -> Proxy (r :> a)
proxyCons _ _ = Proxy
