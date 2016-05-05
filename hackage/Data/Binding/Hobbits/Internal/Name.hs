{-# LANGUAGE GADTs, DeriveDataTypeable, FlexibleInstances, TypeOperators #-}

-- |
-- Module      : Data.Binding.Hobbits.Internal.Name
-- Copyright   : (c) 2014 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : westbrook@kestrel.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module defines the type @'Name' a@ as a wrapper around a fresh
-- integer. Note that, in order to ensure adequacy of the Hobbits
-- name-binding approach, this representation is hidden from the user,
-- and so this file should never be imported directly by the user.
--

module Data.Binding.Hobbits.Internal.Name where

import Data.List
import Data.Functor.Constant
import Data.Typeable
import Data.Type.Equality ((:~:))
import Unsafe.Coerce (unsafeCoerce)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

import Data.Type.RList


-- | A @Name a@ is a bound name that is associated with type @a@.
newtype Name a = MkName Int deriving (Typeable, Eq)

instance Show (Name a) where
  showsPrec _ (MkName n) = showChar '#' . shows n . showChar '#'

instance Show (MapRList Name c) where
    show names = "[" ++ (concat $ intersperse "," $ mapRListToList $
                        mapMapRList (Constant . show) names) ++ "]"


-------------------------------------------------------------------------------
-- Externally visible operators
-------------------------------------------------------------------------------

{-|
  @cmpName n m@ compares names @n@ and @m@ of types @Name a@ and @Name b@,
  respectively. When they are equal, @Some e@ is returned for @e@ a proof
  of type @a :~: b@ that their types are equal. Otherwise, @None@ is returned.

  For example:

> nu $ \n -> nu $ \m -> cmpName n n   ==   nu $ \n -> nu $ \m -> Some Refl
> nu $ \n -> nu $ \m -> cmpName n m   ==   nu $ \n -> nu $ \m -> None
-}
cmpName :: Name a -> Name b -> Maybe (a :~: b)
cmpName (MkName n1) (MkName n2)
  | n1 == n2 = Just $ unsafeCoerce Refl
  | otherwise = Nothing



-------------------------------------------------------------------------------
-- Hidden, unsafe operators
-------------------------------------------------------------------------------


-- building an arbitrary InCtx proof with a given length
-- (this is used internally in HobbitLib)

data ExMember where ExMember :: Member c a -> ExMember

-- creating some Member proof of length i
memberFromLen :: Int -> ExMember
memberFromLen 0 = ExMember Member_Base
memberFromLen n = case memberFromLen (n - 1) of
  ExMember mem -> ExMember (Member_Step mem)

-- unsafely creating a *specific* member proof from length i;
-- this is for when we know the ith element of c must be type a
unsafeLookupC :: Int -> Member c a
unsafeLookupC n = case memberFromLen n of
  ExMember mem -> unsafeCoerce mem


-- building a proxy for each type in some unknown context
data ExProxy where ExProxy :: MapRList Proxy ctx -> ExProxy
proxyFromLen :: Int -> ExProxy
proxyFromLen 0 = ExProxy MNil
proxyFromLen n = case proxyFromLen (n - 1) of
                   ExProxy proxy -> ExProxy (proxy :>: Proxy)

-- -- unsafely building a proxy for each type in ctx from the length n
-- -- of ctx; this is only safe when we know the length of ctx = n
-- unsafeProxyFromLen :: Int -> MapC Proxy ctx
-- unsafeProxyFromLen n = case proxyFromLen n of
--                          ExProxy proxy -> unsafeCoerce proxy

-- -- unsafely convert a list of Ints, used to represent names, to
-- -- names of certain, given types; note that the first name in the
-- -- list becomes the last name in the output, with the same reversal
-- -- used in the Mb representation (see, e.g., mbCombine)
-- unsafeNamesFromInts :: [Int] -> MapC Name ctx
-- unsafeNamesFromInts [] = unsafeCoerce Nil
-- unsafeNamesFromInts (x:xs) =
--     unsafeCoerce $ unsafeNamesFromInts xs :> MkName x

-------------------------------------------------------------------------------
-- encapsulated impurity
-------------------------------------------------------------------------------

-- README: we *cannot* inline counter, because we want all uses
-- of counter to be the same IORef
counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

-- README: fresh_name takes a dummy argument that is used in a dummy
-- way to avoid let-floating its body (and thus getting a fresh name
-- exactly once)
-- README: it *is* ok to inline fresh_name because we don't care in
-- what order fresh names are created
fresh_name :: a -> Int
fresh_name a = unsafePerformIO $ do 
    dummyRef <- newIORef a
    x <- readIORef counter
    writeIORef counter (x+1)
    return x

-- -- make one fresh name for each name in a given input list
-- fresh_names :: MapC Name ctx -> MapC Name ctx
-- fresh_names Nil = Nil
-- fresh_names (names :> n) = fresh_names names :> MkName (fresh_name n)
