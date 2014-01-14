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
  nu, emptyMb, nuMulti,
  -- * Operations on multi-bindings
  elimEmptyMb, mbCombine, mbSeparate, mbToProxy, --mbRearrange,
  mbApply, mbMapAndSwap, mbRearrange,
  nuMultiWithElim, nuWithElim, nuMultiWithElim1, nuWithElim1,
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

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
--import qualified Data.Binding.Hobbits.Internal as I

import Data.List (intersperse)
import Data.Functor.Constant

import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- bindings
-------------------------------------------------------------------------------

-- | A @Binding@ is simply a multi-binding that binds one name
type Binding a = Mb (Nil :> a)

-- note: we reverse l to show the inner-most bindings last
instance Show a => Show (Mb c a) where
  showsPrec p (ensureFreshPair -> (names, b)) = showParen (p > 10) $
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
nu f = MkMbFun (Nil :> Proxy) (\(Nil :> n) -> f n)

-- Extract the proxy objects from an Mb inside of a fresh function
freshFunctionProxies :: MapC Proxy ctx1 -> (MapC Name ctx1 -> Mb ctx2 a) -> MapC Proxy ctx2
freshFunctionProxies proxies1 f =
    case f (mapC (const $ MkName 0) proxies1) of
      MkMbFun proxies2 _ -> proxies2
      MkMbPair _ ns _ -> mapC (const Proxy) ns


-- README: inner-most bindings come FIRST
-- | Combines a binding inside another binding into a single binding.
mbCombine :: Mb c1 (Mb c2 b) -> Mb (c1 :++: c2) b
mbCombine (MkMbPair tRepr1 l1 (MkMbPair tRepr2 l2 b)) = MkMbPair tRepr2 (append l1 l2) b
mbCombine (ensureFreshFun -> (proxies1, f1)) =
    -- README: we pass in Names with integer value 0 here in order to
    -- get out the proxies for the inner-most bindings; this is "safe"
    -- because these proxies should never depend on the names
    -- themselves
    let proxies2 = freshFunctionProxies proxies1 f1 in
    MkMbFun
    (append proxies1 proxies2)
    (\ns ->
         let (ns1, ns2) = split (mkAppend proxies2) ns in
         let (_, f2) = ensureFreshFun (f1 ns1) in
         f2 ns2)


{-|
  Separates a binding into two nested bindings. The first argument, of
  type @'Append' c1 c2 c@, is a \"phantom\" argument to indicate how
  the context @c@ should be split.
-}
mbSeparate :: Append c1 c2 c -> Mb c a -> Mb c1 (Mb c2 a)
mbSeparate app (MkMbPair tRepr ns a) =
    MkMbPair (MbTypeReprMb tRepr) ns1 (MkMbPair tRepr ns2 a) where
        (ns1, ns2) = split app ns
mbSeparate app (MkMbFun proxies f) =
    MkMbFun proxies1 (\ns1 -> MkMbFun proxies2 (\ns2 -> f (appendWithPf app ns1 ns2)))
        where
          (proxies1, proxies2) = split app proxies


-- | Returns a proxy object that enumerates all the types in ctx.
mbToProxy :: Mb ctx a -> MapC Proxy ctx
mbToProxy (MkMbFun proxies _) = proxies
mbToProxy (MkMbPair _ ns _) = mapC (\_ -> Proxy) ns


{-|
  Take a multi-binding inside another multi-binding and move the
  outer binding inside the ineer one.
-}
mbSwap :: Mb ctx1 (Mb ctx2 a) -> Mb ctx2 (Mb ctx1 a)
mbSwap (ensureFreshFun -> (proxies1, f1)) =
    let proxies2 = freshFunctionProxies proxies1 f1 in
    MkMbFun proxies2 (\ns2 ->
                          MkMbFun proxies1 (\ns1 ->
                                                snd (ensureFreshFun (f1 ns1)) ns2))

-- | Creates an empty binding that binds 0 names.
emptyMb :: a -> Mb Nil a
emptyMb body = MkMbFun Nil (\_ -> body)


{-


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


FIXME HERE: organize the below

{-|
  Applies a function in a multi-binding to an argument in a
  multi-binding that binds the same number and types of names.
-}
mbApply :: (NuMatching a, NuMatching b) => Mb ctx (a -> b) -> Mb ctx a -> Mb ctx b
mbApply (MkMb names f) (MkMb names' a) =
    let names'' = fresh_names names in
    MkMb names'' $ (mapNames names names'' f) (mapNames names' names'' a)

mbMapAndSwap :: NuMatching a => (Mb ctx1 a -> b) -> Mb ctx1 (Mb ctx2 a) -> Mb ctx2 b
mbMapAndSwap = undefined
{-
mbMapAndSwap (MkMb names f) (MkMb names' a) =
    MkMb names $ f $ mapNames names' names a
-}

{-|
  Take a multi-binding inside another multi-binding and move the
  outer binding inside the inner one.

  NOTE: This is not yet implemented.
-}
mbRearrange :: NuMatching a => Mb ctx1 (Mb ctx2 a) -> Mb ctx2 (Mb ctx1 a)
mbRearrange = mbMapAndSwap id



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

> commuteFun :: (NuMatching a, NuMatching b) => Mb ctx (a -> b) -> Mb ctx a -> Mb ctx b
> commuteFun f a =
>     nuWithElimMulti ('mbToProxy' f) ('Nil' :> f :> a)
>                     (\_ ('Nil' :> 'Identity' f' :> 'Identity' a') -> f' a')
-}
nuMultiWithElim :: (NuMatchingList args, NuMatching b) =>
                   MapC f ctx -> MapC (Mb ctx) args ->
                   (MapC Name ctx -> MapC Identity args -> b) -> Mb ctx b
nuMultiWithElim nameProxies args f =
    mbMultiApply (nuMulti nameProxies
                  (\names -> (mapCToAddArrows args (f names)))) args nuMatchingListProof where
        mapCToAddArrows :: MapC f args -> (MapC Identity args -> b) ->
                           AddArrows args b
        mapCToAddArrows Nil f = f Nil
        mapCToAddArrows (args :> _) f = mapCToAddArrows args (\args' x -> f (args' :> Identity x))
        mbMultiApply :: NuMatching b => Mb ctx (AddArrows args b) ->
                        MapC (Mb ctx) args -> MapC NuMatchingObj args -> Mb ctx b
        mbMultiApply mbF Nil Nil = mbF
        mbMultiApply mbF (args :> arg) (proofs :> NuMatchingObj ()) =
            mbApply (mbMultiApply mbF args proofs) arg


type family AddArrows ctx a
type instance AddArrows Nil a = a
type instance AddArrows (ctx :> b) a = AddArrows ctx (b -> a)

-- README: old implementation
{-
nuMultiWithElim nameProxies args f =
    nuMulti nameProxies $ \names -> f names (mapArgs nuMatchingListProof args names)
    where
      mapArgs :: MapC NuMatchingProof args -> MapC (Mb ctx) args ->
                 MapC Name ctx -> MapC Identity args
      mapArgs Nil Nil _ = Nil
      mapArgs (proofs :> proof) (args :> arg) names =
          mapArgs proofs args names :>
                      (Identity $ mapNamesSubst proof names arg)
      mapArgs _ _ _ = error "Should not be possible! (in mapArgs)"

      mapNamesSubst :: NuMatchingProof arg -> MapC Name ctx -> Mb ctx arg -> arg
      mapNamesSubst proof names (MkMb namesOld arg) =
          mapNamesPf proof namesOld names arg
-}

{-|
  Similar to 'nuMultiWithElim' but binds only one name.
-}
nuWithElim :: (NuMatchingList args, NuMatching b) => MapC (Mb (Nil :> a)) args ->
              (Name a -> MapC Identity args -> b) -> Binding a b
nuWithElim args f =
    nuMultiWithElim (Nil :> Proxy) args (\(Nil :> n) -> f n)


{-|
  Similar to 'nuMultiWithElim' but takes only one argument
-}
nuMultiWithElim1 :: (NuMatching arg, NuMatching b) => MapC f ctx -> Mb ctx arg ->
                    (MapC Name ctx -> arg -> b) -> Mb ctx b
nuMultiWithElim1 nameProxies arg f =
    nuMultiWithElim nameProxies (Nil :> arg)
                    (\names (Nil :> Identity arg) -> f names arg)


{-|
  Similar to 'nuMultiWithElim' but takes only one argument that binds
  a single name.
-}
nuWithElim1 :: (NuMatching arg, NuMatching b) => Binding a arg ->
               (Name a -> arg -> b) -> Binding a b
nuWithElim1 (MkMb namesOld arg) f =
    nu $ \n -> f n (mapNames namesOld (Nil :> n) arg)
{-
nuWithElim1 (MkMb _ arg) f =
    error "Internal error in nuWithElim1"
-}


-}
