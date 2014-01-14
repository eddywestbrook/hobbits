{-# LANGUAGE GADTs, RankNTypes, TypeOperators, ViewPatterns, TypeFamilies, FlexibleInstances, FlexibleContexts, TemplateHaskell, UndecidableInstances, ScopedTypeVariables, NoMonomorphismRestriction #-}

module NuElimTest where

import Data.Binding.Hobbits


--
-- some helpers
--

proxies2 = Nil :> Proxy :> Proxy

nu2 :: (Name a1 -> Name a2 -> b) -> Mb (Nil :> a1 :> a2) b
nu2 f = nuMulti proxies2 $ \(Nil :> n1 :> n2) -> f n1 n2


--
-- test that mbApply works correctly for names in the argument
--

test1f :: Mb (Nil :> a :> a) (Name a -> Int)
test1f = nu2 $ \n1 n2 n ->
         case () of
           () | Just Refl <- cmpName n n1 -> 1
           () | Just Refl <- cmpName n n2 -> 2
           _ -> 3

test1a = test1f `mbApply` (nu2 $ \n1 n2 -> n1) -- body should be 1
test1b = test1f `mbApply` (nu2 $ \n1 n2 -> n2) -- body should be 2
test1c = nu (\n -> test1f `mbApply` (nu2 $ \n1 n2 -> n)) -- body should be 3



--
-- test that mbApply works correctly for names in the argument and the
-- return value
--

test2f :: Mb (Nil :> a :> a) (Name a -> Name a)
test2f = nu2 $ \n1 n2 n ->
         case () of
           () | Just Refl <- cmpName n n1 -> n2
           () | Just Refl <- cmpName n n2 -> n1
           _ -> n

test2a = test2f `mbApply` (nu2 $ \n1 n2 -> n1) -- should be Nu (n1,n2) n2
test2b = test2f `mbApply` (nu2 $ \n1 n2 -> n2) -- should be Nu (n1,n2) n1
test2c = nu (\n -> test2f `mbApply` (nu2 $ \n1 n2 -> n)) -- should be Nu (n) (Nu (n1,n2) n)
