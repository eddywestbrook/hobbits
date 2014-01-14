{-# LANGUAGE Rank2Types #-}

module Data.Binding.Hobbits.InternalUtilities where

import qualified Data.Generics as SYB



everywhereButM :: Monad m =>
  SYB.GenericQ Bool -> SYB.GenericM m -> SYB.GenericM m
everywhereButM q f x
  | q x       = return x
  | otherwise = (SYB.gmapM (everywhereButM q f) x) >>= f
