{-# LANGUAGE GADTs, TypeOperators, FlexibleInstances, ViewPatterns, DataKinds #-}
{-# LANGUAGE RankNTypes, PolyKinds #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

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
  nu, nuMulti, nus, emptyMb, extMb, extMbMulti,
  -- * Queries on names
  cmpName, hcmpName, mbNameBoundP, mbCmpName,
  -- * Operations on multi-bindings
  elimEmptyMb, mbCombine, mbSeparate, mbToProxy, mbSwap, mbPure, mbApply,
  mbMap2, mbMap3, mbMap4,
  -- * Eliminators for multi-bindings
  nuMultiWithElim, nuWithElim, nuMultiWithElim1, nuWithElim1
) where

import Control.Monad.Identity

import Data.Type.Equality ((:~:)(..))
import Data.Proxy (Proxy(..))

import Unsafe.Coerce (unsafeCoerce)

import Data.Type.RList

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
--import qualified Data.Binding.Hobbits.Internal as I

-------------------------------------------------------------------------------
-- creating bindings
-------------------------------------------------------------------------------

-- | A @Binding@ is simply a multi-binding that binds one name
type Binding (a :: k) = Mb (RNil :> a)

-- note: we reverse l to show the inner-most bindings last
instance Show a => Show (Mb c a) where
  showsPrec p (ensureFreshPair -> (names, b)) = showParen (p > 10) $
    showChar '#' . shows names . showChar '.' . shows b

{-|
  @nu f@ creates a binding which binds a fresh name @n@ and whose
  body is the result of @f n@.
-}
nu :: forall k1 (a :: k1) (b :: *) . (Name a -> b) -> Binding a b
nu f = MkMbFun (MNil :>: Proxy) (\(MNil :>: n) -> f n)

{-|
  The expression @nuMulti p f@ creates a multi-binding of zero or more
  names, one for each element of the vector @p@. The bound names are
  passed the names to @f@, which returns the body of the
  multi-binding.  The argument @p@, of type @'RAssign' f ctx@, acts as a
  \"phantom\" argument, used to reify the list of types @ctx@ at the
  term level; thus it is unimportant what the type function @f@ is.
-}
nuMulti :: RAssign Proxy ctx -> (RAssign Name ctx -> b) -> Mb ctx b
nuMulti = MkMbFun

-- | @nus = nuMulti@
nus :: forall k (ctx :: RList k) b.
       RAssign Proxy ctx -> (RAssign Name ctx -> b) -> Mb ctx b
nus = nuMulti

-- | Extend the context of a name-binding by adding a single type
extMb :: Mb ctx a -> Mb (ctx :> tp) a
extMb = mbCombine typeCtxProxies . fmap (nu . const)

-- | Extend the context of a name-binding with multiple types
extMbMulti :: RAssign Proxy ctx2 -> Mb ctx1 a -> Mb (ctx1 :++: ctx2) a
extMbMulti ns mb = mbCombine ns (fmap (nuMulti ns . const) mb)


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
mbNameBoundP :: forall k1 k2 (a :: k1) (ctx :: RList k2).
                Mb ctx (Name a) -> Either (Member ctx a) (Name a)
mbNameBoundP (ensureFreshPair -> (names, n)) = helper names n where
    helper :: RAssign Name c -> Name a -> Either (Member c a) (Name a)
    helper MNil n' = Right n'
    helper (_ :>: (MkName i)) (MkName j)
      | i == j =
        unsafeCoerce $ Left Member_Base
    helper (names' :>: _) n' =
      case helper names' n' of
        Left memb -> Left (Member_Step memb)
        Right n'' -> Right n''
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
mbCmpName :: forall k1 k2 (a :: k1) (b :: k1) (c :: RList k2).
             Mb c (Name a) -> Mb c (Name b) -> Maybe (a :~: b)
mbCmpName (ensureFreshPair -> (names, n1)) (ensureFreshFun -> (_, f2)) =
  cmpName n1 (f2 names)


-------------------------------------------------------------------------------
-- Operations on multi-bindings
-------------------------------------------------------------------------------

-- | Creates an empty binding that binds 0 names.
emptyMb :: a -> Mb RNil a
emptyMb body = MkMbFun MNil (\_ -> body)

{-|
  Eliminates an empty binding, returning its body. Note that
  @elimEmptyMb@ is the inverse of @emptyMb@.
-}
elimEmptyMb :: Mb RNil a -> a
elimEmptyMb (ensureFreshPair -> (_, body)) = body

-- README: inner-most bindings come FIRST
-- | Combines a binding inside another binding into a single binding.
mbCombine ::
  forall k (c1 :: RList k) (c2 :: RList k) b.
  RAssign Proxy c2 ->
  Mb c1 (Mb c2 b) ->
  Mb (c1 :++: c2) b
mbCombine _ (MkMbPair (MbTypeReprMb tRepr2) l1 (ensureFreshPair -> (l2, b))) =
  MkMbPair tRepr2 (append l1 l2) b
mbCombine proxies2 (ensureFreshFun -> (proxies1, f1)) =
    -- README: we pass in Names with integer value 0 here in order to
    -- get out the proxies for the inner-most bindings; this is "safe"
    -- because these proxies should never depend on the names
    -- themselves
    MkMbFun
    (append proxies1 proxies2)
    (\ns ->
        case split Proxy proxies2 ns of
         (ns1, ns2) ->
           case ensureFreshFun (f1 ns1) of
             (_, f2) -> f2 ns2)

{-|
  Separates a binding into two nested bindings. The first argument, of
  type @'RAssign' any c2@, is a \"phantom\" argument to indicate how
  the context @c@ should be split.
-}
mbSeparate :: forall k (ctx1 :: RList k) (ctx2 :: RList k) (any :: k -> *) a.
              RAssign any ctx2 -> Mb (ctx1 :++: ctx2) a ->
              Mb ctx1 (Mb ctx2 a)
mbSeparate c2 (MkMbPair tRepr ns a) =
    MkMbPair (MbTypeReprMb tRepr) ns1 (MkMbPair tRepr ns2 a) where
        (ns1, ns2) = split Proxy c2 ns
mbSeparate c2 (MkMbFun proxies f) =
    MkMbFun proxies1 (\ns1 -> MkMbFun proxies2 (\ns2 -> f (append ns1 ns2)))
        where
          (proxies1, proxies2) = split Proxy c2 proxies


-- | Returns a proxy object that enumerates all the types in ctx.
mbToProxy :: forall k (ctx :: RList k) (a :: *) .
             Mb ctx a -> RAssign Proxy ctx
mbToProxy (MkMbFun proxies _) = proxies
mbToProxy (MkMbPair _ ns _) = mapRAssign (\_ -> Proxy) ns


{-|
  Take a multi-binding inside another multi-binding and move the
  outer binding inside the inner one.
-}
mbSwap :: RAssign Proxy ctx2 -> Mb ctx1 (Mb ctx2 a) -> Mb ctx2 (Mb ctx1 a)
mbSwap _ (MkMbPair _ names1 (MkMbPair aRepr names2 a)) =
  MkMbPair (MbTypeReprMb aRepr) names2 (MkMbPair aRepr names1 a)
mbSwap _ (MkMbPair (MbTypeReprMb aRepr) names1 (MkMbFun px2 f)) =
  MkMbFun px2 (\names2 -> MkMbPair aRepr names1 (f names2))
mbSwap proxies2 (ensureFreshFun -> (proxies1, f1)) =
    MkMbFun proxies2
      (\ns2 ->
         MkMbFun proxies1
         (\ns1 ->
            snd (ensureFreshFun (f1 ns1)) ns2))

-- | Put a value inside a multi-binding
mbPure :: RAssign Proxy ctx -> a -> Mb ctx a
mbPure prxs = nuMulti prxs . const

{-|
  Applies a function in a multi-binding to an argument in a
  multi-binding that binds the same number and types of names.
-}
mbApply :: Mb ctx (a -> b) -> Mb ctx a -> Mb ctx b
mbApply (MkMbPair (MbTypeReprFun _ bRepr) names1 f) (ensureFreshFun -> (_, mkA)) =
  MkMbPair bRepr names1 (f (mkA names1))
mbApply (ensureFreshFun -> (proxies, f_fun)) (ensureFreshFun -> (_, f_arg)) =
  MkMbFun proxies (\ns -> f_fun ns $ f_arg ns)


-- | Lift a binary function function to `Mb`s
mbMap2 :: (a -> b -> c) -> Mb ctx a -> Mb ctx b -> Mb ctx c
mbMap2 f mb1 mb2 = fmap f mb1 `mbApply` mb2

-- | Lift a ternary function function to `Mb`s
mbMap3 :: (a -> b -> c -> d) -> Mb ctx a -> Mb ctx b -> Mb ctx c -> Mb ctx d
mbMap3 f mb1 mb2 mb3 = mbMap2 f mb1 mb2 `mbApply` mb3

-- | Lift a quaternary function function to `Mb`s
mbMap4 :: (a -> b -> c -> d -> e) ->
          Mb ctx a -> Mb ctx b -> Mb ctx c -> Mb ctx d -> Mb ctx e
mbMap4 f mb1 mb2 mb3 mb4 = mbMap3 f mb1 mb2 mb3 `mbApply` mb4


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

  asdfasdf

  The expression @nuWithElimMulti args f@ takes a sequence @args@ of one or more
  multi-bindings (it is a runtime error to pass an empty sequence of arguments),
  each of type @Mb ctx ai@ for the same type context @ctx@ of bound names, and a
  function @f@ and does the following:

  * Creates a multi-binding that binds names @n1,...,nn@, one name for
    each type in @ctx@;

  * Substitutes the names @n1,...,nn@ for the names bound by each
    argument in the @args@ sequence, yielding the bodies of the @args@
    (using the new name @n@); and then

  * Passes the sequence @n1,...,nn@ along with the result of
    substituting into @args@ to the function @f@, which then returns
    the value for the newly created binding.

  For example, here is an alternate way to implement 'mbApply':

> mbApply' :: Mb ctx (a -> b) -> Mb ctx a -> Mb ctx b
> mbApply' f a =
>     nuWithElimMulti ('MNil' :>: f :>: a)
>                     (\_ ('MNil' :>: 'Identity' f' :>: 'Identity' a') -> f' a')
-}
nuMultiWithElim :: (RAssign Name ctx -> RAssign Identity args -> b) ->
                   RAssign (Mb ctx) args -> Mb ctx b
nuMultiWithElim f args =
  let proxies =
        case args of
          MNil -> error "nuMultiWithElim"
          (_ :>: arg1) -> mbToProxy arg1 in
  MkMbFun proxies
          (\ns ->
            f ns $ mapRAssign (\arg ->
                                Identity $ snd (ensureFreshFun arg) ns) args)

-- This should really be defined using 'mbLift', but doing so causes a
-- circular include
instance Eq a => Eq (Mb ctx a) where
  mb1 == mb2 =
    mbLiftBool $ nuMultiWithElim (\_ (_ :>: a1 :>: a2) ->
                                   a1 == a2) (MNil :>: mb1 :>: mb2)
    where -- the same as 'mbLift' for 'Bool'
          mbLiftBool :: Mb ctx Bool -> Bool
          mbLiftBool mb_b = case mbMatch mb_b of
            MatchedMb _ True -> True
            MatchedMb _ False -> False


{-|
  Similar to 'nuMultiWithElim' but binds only one name. Note that the argument
  list here is allowed to be empty.
-}
nuWithElim :: (Name a -> RAssign Identity args -> b) ->
              RAssign (Mb (RNil :> a)) args ->
              Binding a b
nuWithElim f MNil = nu $ \n -> f n MNil
nuWithElim f args =
    nuMultiWithElim (\(MNil :>: n) -> f n) args


{-|
  Similar to 'nuMultiWithElim' but takes only one argument
-}
nuMultiWithElim1 :: (RAssign Name ctx -> arg -> b) -> Mb ctx arg -> Mb ctx b
nuMultiWithElim1 f arg =
    nuMultiWithElim (\names (MNil :>: Identity arg') -> f names arg')
    (MNil :>: arg)


{-|
  Similar to 'nuMultiWithElim' but takes only one argument that binds
  a single name.
-}
nuWithElim1 :: (Name a -> arg -> b) -> Binding a arg -> Binding a b
nuWithElim1 f arg =
  nuWithElim (\n (MNil :>: Identity arg') -> f n arg') (MNil :>: arg)
