{-# LANGUAGE GADTs, TypeOperators, FlexibleInstances, ViewPatterns #-}

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
  nu, nuMulti, nus, emptyMb,
  -- * Queries on names
  cmpName, mbNameBoundP, mbCmpName,
  -- * Operations on multi-bindings
  elimEmptyMb, mbCombine, mbSeparate, mbToProxy, mbSwap, mbApply,
  -- * Eliminators for multi-bindings
  nuMultiWithElim, nuWithElim, nuMultiWithElim1, nuWithElim1
) where

import Control.Applicative
import Control.Monad.Identity

import Data.Type.Equality ((:~:)(..))
import Data.Proxy (Proxy(..))

import Unsafe.Coerce (unsafeCoerce)

import Data.Type.HList

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
--import qualified Data.Binding.Hobbits.Internal as I

-------------------------------------------------------------------------------
-- creating bindings
-------------------------------------------------------------------------------

-- | A @Binding@ is simply a multi-binding that binds one name
type Binding a = Mb (Nil :> a)

-- note: we reverse l to show the inner-most bindings last
instance Show a => Show (Mb c a) where
  showsPrec p (ensureFreshPair -> (names, b)) = showParen (p > 10) $
    showChar '#' . shows names . showChar '.' . shows b

{-|
  @nu f@ creates a binding which binds a fresh name @n@ and whose
  body is the result of @f n@.
-}
nu :: (Name a -> b) -> Binding a b
nu f = MkMbFun (Nil :> Proxy) (\(Nil :> n) -> f n)

{-|
  The expression @nuMulti p f@ creates a multi-binding of zero or more
  names, one for each element of the vector @p@. The bound names are
  passed the names to @f@, which returns the body of the
  multi-binding.  The argument @p@, of type @'HList' f ctx@, acts as a
  \"phantom\" argument, used to reify the list of types @ctx@ at the
  term level; thus it is unimportant what the type function @f@ is.
-}
nuMulti :: HList f ctx -> (HList Name ctx -> b) -> Mb ctx b
nuMulti proxies f = MkMbFun (mapHList (const Proxy) proxies) f

-- | @nus = nuMulti@
nus x = nuMulti x


-------------------------------------------------------------------------------
-- Queries on Names
-------------------------------------------------------------------------------

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
mbNameBoundP (ensureFreshPair -> (names, n)) = helper names n where
    helper :: HList Name c -> Name a -> Either (Member c a) (Name a)
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
mbCmpName :: Mb c (Name a) -> Mb c (Name b) -> Maybe (a :~: b)
mbCmpName b1 b2 = case (mbNameBoundP b1, mbNameBoundP b2) of
  (Left mem1, Left mem2) -> membersEq mem1 mem2
  (Right n1, Right n2) -> cmpName n1 n2
  _ -> Nothing


-------------------------------------------------------------------------------
-- Operations on multi-bindings
-------------------------------------------------------------------------------

-- | Creates an empty binding that binds 0 names.
emptyMb :: a -> Mb Nil a
emptyMb body = MkMbFun Nil (\_ -> body)

{-|
  Eliminates an empty binding, returning its body. Note that
  @elimEmptyMb@ is the inverse of @emptyMb@.
-}
elimEmptyMb :: Mb Nil a -> a
elimEmptyMb (ensureFreshPair -> (_, body)) = body


-- Extract the proxy objects from an Mb inside of a fresh function
freshFunctionProxies :: HList Proxy ctx1 -> (HList Name ctx1 -> Mb ctx2 a) ->
                        HList Proxy ctx2
freshFunctionProxies proxies1 f =
    case f (mapHList (const $ MkName 0) proxies1) of
      MkMbFun proxies2 _ -> proxies2
      MkMbPair _ ns _ -> mapHList (const Proxy) ns


-- README: inner-most bindings come FIRST
-- | Combines a binding inside another binding into a single binding.
mbCombine :: Mb c1 (Mb c2 b) -> Mb (c1 :++: c2) b
mbCombine (MkMbPair tRepr1 l1 (MkMbPair tRepr2 l2 b)) = MkMbPair tRepr2 (appendHList l1 l2) b
mbCombine (ensureFreshFun -> (proxies1, f1)) =
    -- README: we pass in Names with integer value 0 here in order to
    -- get out the proxies for the inner-most bindings; this is "safe"
    -- because these proxies should never depend on the names
    -- themselves
    let proxies2 = freshFunctionProxies proxies1 f1 in
    MkMbFun
    (appendHList proxies1 proxies2)
    (\ns ->
         let (ns1, ns2) = splitHList Proxy proxies2 ns in
         let (_, f2) = ensureFreshFun (f1 ns1) in
         f2 ns2)


{-|
  Separates a binding into two nested bindings. The first argument, of
  type @'HList' any c2@, is a \"phantom\" argument to indicate how
  the context @c@ should be split.
-}
mbSeparate :: HList any ctx2 -> Mb (ctx1 :++: ctx2) a ->
              Mb ctx1 (Mb ctx2 a)
mbSeparate c2 (MkMbPair tRepr ns a) =
    MkMbPair (MbTypeReprMb tRepr) ns1 (MkMbPair tRepr ns2 a) where
        (ns1, ns2) = splitHList Proxy c2 ns
mbSeparate c2 (MkMbFun proxies f) =
    MkMbFun proxies1 (\ns1 -> MkMbFun proxies2 (\ns2 -> f (appendHList ns1 ns2)))
        where
          (proxies1, proxies2) = splitHList Proxy c2 proxies


-- | Returns a proxy object that enumerates all the types in ctx.
mbToProxy :: Mb ctx a -> HList Proxy ctx
mbToProxy (MkMbFun proxies _) = proxies
mbToProxy (MkMbPair _ ns _) = mapHList (\_ -> Proxy) ns


{-|
  Take a multi-binding inside another multi-binding and move the
  outer binding inside the ineer one.
-}
mbSwap :: Mb ctx1 (Mb ctx2 a) -> Mb ctx2 (Mb ctx1 a)
mbSwap (ensureFreshFun -> (proxies1, f1)) =
    let proxies2 = freshFunctionProxies proxies1 f1 in
    MkMbFun proxies2
      (\ns2 ->
         MkMbFun proxies1
         (\ns1 ->
            snd (ensureFreshFun (f1 ns1)) ns2))

{-|
  Applies a function in a multi-binding to an argument in a
  multi-binding that binds the same number and types of names.
-}
mbApply :: Mb ctx (a -> b) -> Mb ctx a -> Mb ctx b
mbApply (ensureFreshFun -> (proxies, f_fun)) (ensureFreshFun -> (_, f_arg)) =
  MkMbFun proxies (\ns -> f_fun ns $ f_arg ns)


-------------------------------------------------------------------------------
-- Functor and Applicative instances
-------------------------------------------------------------------------------

instance Functor (Mb ctx) where
    fmap f mbArg =
        mbApply (nuMulti (mbToProxy mbArg) (\_ -> f)) mbArg

instance TypeCtx ctx => Applicative (Mb ctx) where
    pure x = nuMulti typeCtxProxies (const x)
    (<*>) = mbApply


-------------------------------------------------------------------------------
-- Eliminators for multi-bindings
-------------------------------------------------------------------------------

-- FIXME: add more examples!!
{-|
  The expression @nuWithElimMulti args f@ takes a sequence @args@ of
  zero or more multi-bindings, each of type @Mb ctx ai@ for the same
  type context @ctx@ of bound names, and a function @f@ and does the
  following:

  * Creates a multi-binding that binds names @n1,...,nn@, one name for
    each type in @ctx@;

  * Substitutes the names @n1,...,nn@ for the names bound by each
    argument in the @args@ sequence, yielding the bodies of the @args@
    (using the new name @n@); and then

  * Passes the sequence @n1,...,nn@ along with the result of
    substituting into @args@ to the function @f@, which then returns
    the value for the newly created binding.

  Note that the types in @args@ must each have a @NuMatching@ instance;
  this is represented with the @NuMatchingList@ type class.

  Here are some examples:

> (<*>) :: Mb ctx (a -> b) -> Mb ctx a -> Mb ctx b
> (<*>) f a =
>     nuWithElimMulti ('Nil' :> f :> a)
>                     (\_ ('Nil' :> 'Identity' f' :> 'Identity' a') -> f' a')
-}
nuMultiWithElim :: TypeCtx ctx =>
                   (HList Name ctx -> HList Identity args -> b) ->
                   HList (Mb ctx) args -> Mb ctx b
nuMultiWithElim f args =
  MkMbFun typeCtxProxies
          (\ns -> f ns $ mapHList (\arg -> Identity $ snd (ensureFreshFun arg) ns) args)


{-|
  Similar to 'nuMultiWithElim' but binds only one name.
-}
nuWithElim :: (Name a -> HList Identity args -> b) ->
              HList (Mb (Nil :> a)) args ->
              Binding a b
nuWithElim f args =
    nuMultiWithElim (\(Nil :> n) -> f n) args


{-|
  Similar to 'nuMultiWithElim' but takes only one argument
-}
nuMultiWithElim1 :: TypeCtx ctx => (HList Name ctx -> arg -> b) -> Mb ctx arg ->
                    Mb ctx b
nuMultiWithElim1 f arg =
    nuMultiWithElim (\names (Nil :> Identity arg) -> f names arg) (Nil :> arg)


{-|
  Similar to 'nuMultiWithElim' but takes only one argument that binds
  a single name.
-}
nuWithElim1 :: (Name a -> arg -> b) -> Binding a arg -> Binding a b
nuWithElim1 f arg =
  nuWithElim (\n (Nil :> Identity arg) -> f n arg) (Nil :> arg)
