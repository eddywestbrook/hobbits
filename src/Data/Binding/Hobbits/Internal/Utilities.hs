{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}

module Data.Binding.Hobbits.Internal.Utilities where

import qualified Data.Generics as SYB
import Language.Haskell.TH (Name, Pat(..))



everywhereButM :: Monad m =>
  SYB.GenericQ Bool -> SYB.GenericM m -> SYB.GenericM m
everywhereButM q f x
  | q x       = return x
  | otherwise = (SYB.gmapM (everywhereButM q f) x) >>= f

conPCompat :: Name -> [Pat] -> Pat
conPCompat n pats = ConP n
#if MIN_VERSION_template_haskell(2,18,0)
                           []
#endif
                           pats
