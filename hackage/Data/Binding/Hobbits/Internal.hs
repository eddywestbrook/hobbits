{-# LANGUAGE GADTs, DeriveDataTypeable #-}

-- |
-- Module      : Data.Binding.Hobbits.Internal
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module is internal to the Hobbits library, and should not be used
-- directly.

module Data.Binding.Hobbits.Internal where

import Data.Typeable
import Data.Type.HList
import Unsafe.Coerce (unsafeCoerce)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

-- | A @Name a@ is a bound name that is associated with type @a@.
newtype Name a = MkName Int deriving (Typeable, Eq)

{-|
  An @Mb ctx b@ is a multi-binding that binds exactly one name for each
  type in @ctx@, where @ctx@ has the form @'Nil' ':>' t1 ':>' ... ':>' tn@.
-}
data Mb ctx b
    = MkMbFun (MapC Proxy ctx) (MapC Name ctx -> b)
    | MkMbPair (MapC Name ctx) b
    deriving Typeable

{-
instance Typeable a => Typeable (Mb ctx a) where
    typeOf (MkMb _ x) = mkTyConApp (mkTyCon "Mb")
                          [mkTyConApp (mkTyCon "Nil") [], typeOf x]
-}


{-|
  The type @Cl a@ represents a closed term of type @a@,
  i.e., an expression of type @a@ with no free (Haskell) variables.
  Since this cannot be checked directly in the Haskell type system,
  the @Cl@ data type is hidden, and the user can only create
  closed terms using Template Haskell, through the 'mkClosed'
  operator.
-}
newtype Cl a = Cl { unCl :: a }



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
data ExProxy where ExProxy :: MapC Proxy ctx -> ExProxy
proxyFromLen :: Int -> ExProxy
proxyFromLen 0 = ExProxy Nil
proxyFromLen n = case proxyFromLen (n - 1) of
                   ExProxy proxy -> ExProxy (proxy :> Proxy)

-- unsafely building a proxy for each type in ctx from the length n
-- of ctx; this is only safe when we know the length of ctx = n
unsafeProxyFromLen :: Int -> MapC Proxy ctx
unsafeProxyFromLen n = case proxyFromLen n of
                         ExProxy proxy -> unsafeCoerce proxy

-- unsafely convert a list of Ints, used to represent names, to
-- names of certain, given types; note that the first name in the
-- list becomes the last name in the output, with the same reversal
-- used in the Mb representation (see, e.g., mbCombine)
unsafeNamesFromInts :: [Int] -> MapC Name ctx
unsafeNamesFromInts [] = unsafeCoerce Nil
unsafeNamesFromInts (x:xs) =
    unsafeCoerce $ unsafeNamesFromInts xs :> MkName x

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

-- make one fresh name for each name in a given input list
fresh_names :: MapC Name ctx -> MapC Name ctx
fresh_names Nil = Nil
fresh_names (names :> n) = fresh_names names :> MkName (fresh_name n)
