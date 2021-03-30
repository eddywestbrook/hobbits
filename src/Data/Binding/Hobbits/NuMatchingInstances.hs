{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Binding.Hobbits.NuMatchingInstances
-- Copyright   : (c) 2020 Edwin Westbrook
--
-- License     : BSD3
--
-- Maintainer  : westbrook@galois.com
-- Stability   : experimental
-- Portability : GHC
--
-- Provides a set of instances of 'NuMatching' for standard types using the
-- template Haskell 'mkNuMatching' function

module Data.Binding.Hobbits.NuMatchingInstances where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Constant
import Data.Functor.Product

import Data.Type.RList
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.NuMatching (NuMatching(..), NuMatchingAny1(..), mkNuMatching)
import Data.Binding.Hobbits.QQ (nuP)

$(mkNuMatching [t| forall a. NuMatching a => Maybe a |])
$(mkNuMatching [t| forall a b. (NuMatching a, NuMatching b) => Either a b |])
$(mkNuMatching [t| forall ctx a. Member ctx a |])
$(mkNuMatching [t| forall a. Proxy a |])
$(mkNuMatching [t| forall a b. a :~: b |])
$(mkNuMatching [t| forall a b. NuMatching a => Constant a b |])

$(mkNuMatching [t| forall f g a. (NuMatchingAny1 f,
                                  NuMatchingAny1 g) => Product f g a |])

instance (NuMatchingAny1 f,
          NuMatchingAny1 g) => NuMatchingAny1 (Product f g) where
  nuMatchingAny1Proof = nuMatchingProof
