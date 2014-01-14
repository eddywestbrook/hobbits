{-# LANGUAGE TypeOperators, EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : Data.Type.List
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- A /type list/ contains types as elements. We use GADT proofs terms to
-- establish membership and append relations. A @Data.Type.List.Map.MapC@ @f@
-- is a vector indexed by a type list, where @f :: * -> *@ is applied to each
-- type element.

module Data.Type.List (
  module Data.Type.List.List, -- | Type-level nil, cons, and ++
  module Data.Type.List.Map, -- | Vectors parameterized by a @* -> *@ and indexed by a type list
  module Data.Type.List.Proof.Member, -- | Membership functions and proofs
  module Data.Type.List.Proof.Append, -- | Append functions and proofs
  module Data.Type.Equality,
  module Data.Proxy
  ) where

import Data.Type.List.List
import Data.Type.List.Map (MapC(..))
import Data.Type.List.Proof.Member (Member(..))
import Data.Type.List.Proof.Append (Append(..))

import Data.Type.Equality ((:=:)(..))
import Data.Proxy (Proxy(..))
