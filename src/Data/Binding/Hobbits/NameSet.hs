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

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.NameMap (NameAndElem(..), NameMap(..))
import qualified Data.Binding.Hobbits.NameMap as NM

import Data.Type.RList

type NameSet k = NameMap (Constant () :: k -> Type)

data SomeNames (f :: k -> *) = forall x. SomeNames (f x)

names :: NameSet k -> SomeNames (MapRList (Name :: k -> Type))
names s =
  foldl (\(SomeNames rets) (NameAndElem r _) -> SomeNames (rets :>: r)) (SomeNames MNil) $
  NM.assocs s
