{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Binding.Hobbits.NameSet where

import Data.Functor.Constant
import Data.Kind
import Data.Parameterized.Some

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.NameMap (NameAndElem(..), NameMap(..))
import qualified Data.Binding.Hobbits.NameMap as NM

import Data.Type.RList

type NameSet k = NameMap (Constant () :: k -> Type)

names :: NameSet k -> Some (MapRList (Name :: k -> Type))
names s =
  foldl (\(Some rets) (NameAndElem r _) -> Some (rets :>: r)) (Some MNil) $
  NM.assocs s
