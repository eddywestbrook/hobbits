{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Data.Binding.Hobbits.NuMatchingInstances where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Constant

import Data.Type.RList
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.NuMatching (NuMatching, NuMatchingAny1, mkNuMatching)
import Data.Binding.Hobbits.QQ (nuP)

$(mkNuMatching [t| forall a. NuMatching a => Maybe a |])
$(mkNuMatching [t| forall a b. (NuMatching a, NuMatching b) => Either a b |])
$(mkNuMatching [t| forall ctx a. Member ctx a |])
$(mkNuMatching [t| forall a. Proxy a |])
$(mkNuMatching [t| forall a b. a :~: b |])
$(mkNuMatching [t| forall a b. NuMatching a => Constant a b |])
