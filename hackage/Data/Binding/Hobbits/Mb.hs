{-# LANGUAGE GADTs, TypeOperators, FlexibleInstances #-}

-- |
-- Module      : Data.Binding.Hobbits.Mb
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module defines multi-bindings as the type 'Mb', as well as a number of
-- operations on multi-bindings. See the paper E. Westbrook, N. Frisby,
-- P. Brauner, \"Hobbits for Haskell: A Library for Higher-Order Encodings in
-- Functional Programming Languages\" for more information.

module Data.Binding.Hobbits.Mb (
  -- * Abstract types
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(),        -- hides MultiBind implementation
  -- * Multi-binding constructors
  nu, emptyMb, nuMulti,
  -- * Operations on multi-bindings
  elimEmptyMb, mbCombine, mbSeparate, mbToProxy, --mbRearrange,
  -- * Queries on names
  cmpName, mbCmpName, mbNameBoundP,
  -- * Special-purpose functions for lifting primitives out of bindings
  mbLiftChar, mbLiftInt, mbLiftInteger,
  -- * Synonyms
  nus
) where

import Data.Type.List
import Data.Type.List.Map
import qualified Data.Type.List.Proof.Member as Mem
--import qualified Data.Type.List.Proof.Append as App
import Data.Binding.Hobbits.Internal
--import qualified Data.Binding.Hobbits.Internal as I

import Data.List (intersperse)
import Data.Functor.Constant

import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- bindings
-------------------------------------------------------------------------------

-- | A @Binding@ is simply a multi-binding that binds one name
type Binding a = Mb (Nil :> a)

instance Show (Name a) where
  showsPrec _ (MkName n) = showChar '#' . shows n . showChar '#'

instance Show (MapC Name c) where
    show mapc = "[" ++ (concat $ intersperse "," $ mapCToList $
                        mapC (Constant . show) mapc) ++ "]"

-- note: we reverse l to show the inner-most bindings last
instance Show a => Show (Mb c a) where
  showsPrec p (MkMb names b) = showParen (p > 10) $
    showChar '#' . shows names . showChar '.' . shows b

-- README: we pass f to fresh_name to avoid let-floating the results
-- of fresh_name (which would always give the same name for each nu)
-- README: is *is* ok to do CSE on multiple copies of nu, because
-- the programmer cannot tell if two distinct (non-nested) nus get the
-- same fresh integer, and two nus that look the same to the CSE engine
-- cannot be nested
-- README: it *is* ok to inline nu because we don't care in
-- what order fresh names are created
{-|
  @nu f@ creates a binding which binds a fresh name @n@ and whose
  body is the result of @f n@.
-}
nu :: (Name a -> b) -> Binding a b
nu f = let n = fresh_name f in n `seq` MkMb (Nil :> MkName n) (f (MkName n))

-- README: inner-most bindings come FIRST
-- | Combines a binding inside another binding into a single binding.
mbCombine :: Mb c1 (Mb c2 b) -> Mb (c1 :++: c2) b
mbCombine (MkMb l1 (MkMb l2 b)) = MkMb (append l1 l2) b

{-|
  Separates a binding into two nested bindings. The first argument, of
  type @'Append' c1 c2 c@, is a \"phantom\" argument to indicate how
  the context @c@ should be split.
-}
mbSeparate :: Append c1 c2 c -> Mb c a -> Mb c1 (Mb c2 a)
mbSeparate app (MkMb l a) = MkMb d (MkMb t a) where
  (d, t) = split app l

-- | Returns a proxy object that enumerates all the types in ctx.
mbToProxy :: Mb ctx a -> MapC Proxy ctx
mbToProxy (MkMb l _) = mapC (\_ -> Proxy) l

{- README: this is unsafe, because the two bindings could share names
{- |
  Take a multi-binding inside another multi-binding and move the
  outer binding inside the ineer one.
-}
mbRearrange :: Mb ctx1 (Mb ctx2 a) -> Mb ctx2 (Mb ctx1 a)
mbRearrange (MkMb l1 (MkMb l2 a)) = MkMb l2 (MkMb l1 a)
-}

-- | Creates an empty binding that binds 0 names.
emptyMb :: a -> Mb Nil a
emptyMb t = MkMb Nil t

{-|
  The expression @nuMulti p f@ creates a multi-binding of zero or more
  names, one for each element of the vector @p@. The bound names are
  passed the names to @f@, which returns the body of the
  multi-binding.  The argument @p@, of type @'Mb' f ctx@, acts as a
  \"phantom\" argument, used to reify the list of types @ctx@ at the
  term level; thus it is unimportant what the type function @f@ is.
-}
nuMulti :: MapC f ctx -> (MapC Name ctx -> b) -> Mb ctx b
nuMulti Nil f = emptyMb $ f Nil
nuMulti (proxies :> proxy) f =
    mbCombine $ nuMulti proxies $ \names -> nu $ \n -> f (names :> n)

{-|
  Eliminates an empty binding, returning its body. Note that
  @elimEmptyMb@ is the inverse of @emptyMb@.
-}
elimEmptyMb :: Mb Nil a -> a
elimEmptyMb (MkMb Nil t) = t
--elimEmptyMb _ = error "Should not happen! (elimEmptyMb)"

{-|
  @cmpName n m@ compares names @n@ and @m@ of types @Name a@ and @Name b@,
  respectively. When they are equal, @Some e@ is returned for @e@ a proof
  of type @a :=: b@ that their types are equal. Otherwise, @None@ is returned.

  For example:

> nu $ \n -> nu $ \m -> cmpName n n   ==   nu $ \n -> nu $ \m -> Some Refl
> nu $ \n -> nu $ \m -> cmpName n m   ==   nu $ \n -> nu $ \m -> None
-}
cmpName :: Name a -> Name b -> Maybe (a :=: b)
cmpName (MkName n1) (MkName n2)
  | n1 == n2 = Just $ unsafeCoerce Refl
  | otherwise = Nothing

{-|
  Checks if a name is bound in a multi-binding, returning @Left mem@
  when the name is bound, where @mem@ is a proof that the type of the
  name is in the type list for the multi-binding, and returning
  @Right n@ when the name is not bound, where @n@ is the name.

  For example:

> nu $ \n -> mbNameBoundP (nu $ \m -> m)  ==  nu $ \n -> Left Member_Base
> nu $ \n -> mbNameBoundP (nu $ \m -> n)  ==  nu $ \n -> Right n
-}
mbNameBoundP :: Mb ctx (Name a) -> Either (Member ctx a) (Name a)
mbNameBoundP (MkMb names n) = helper names n where
    helper :: MapC Name c -> Name a -> Either (Member c a) (Name a)
    helper Nil n = Right n
    helper (names :> (MkName i)) (MkName j) | i == j = unsafeCoerce $ Left Member_Base
    helper (names :> _) n = case helper names n of
                              Left memb -> Left (Member_Step memb)
                              Right n -> Right n
-- old implementation with lists
{-
case elemIndex n names of
  Nothing -> Right (MkName n)
  Just i -> Left (I.unsafeLookupC i)
-}


{-|
  Compares two names inside bindings, taking alpha-equivalence into
  account; i.e., if both are the @i@th name, or both are the same name
  not bound in their respective multi-bindings, then they compare as
  equal. The return values are the same as for 'cmpName', so that
  @Some Refl@ is returned when the names are equal and @Nothing@ is
  returned when they are not.
-}
mbCmpName :: Mb c (Name a) -> Mb c (Name b) -> Maybe (a :=: b)
mbCmpName b1 b2 = case (mbNameBoundP b1, mbNameBoundP b2) of
  (Left mem1, Left mem2) -> Mem.same mem1 mem2
  (Right n1, Right n2) -> cmpName n1 n2
  _ -> Nothing

-- | Lifts a @Char@ out of a multi-binding
mbLiftChar :: Mb c Char -> Char
mbLiftChar (MkMb _ c) = c

-- | Lifts an @Int@ out of a multi-binding
mbLiftInt :: Mb c Int -> Int
mbLiftInt (MkMb _ c) = c

-- | Lifts an @Integer@ out of a multi-binding
mbLiftInteger :: Mb c Integer -> Integer
mbLiftInteger (MkMb _ c) = c

-- | @nus = nuMulti@
nus x = nuMulti x
