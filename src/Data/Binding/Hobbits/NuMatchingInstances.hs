{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Data.Binding.Hobbits.NuMatchingInstances where

import Data.Functor.Constant

import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.NameMap as NameMap
import Data.Binding.Hobbits.NuMatching (NuMatching, NuMatchingAny1, mkNuMatching)
import Data.Binding.Hobbits.QQ (nuP)

$(mkNuMatching [t| forall a b. NuMatching a => Constant a b |])

