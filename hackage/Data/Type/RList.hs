{-# LANGUAGE TypeOperators, EmptyDataDecls, RankNTypes #-}
{-# LANGUAGE TypeFamilies, DataKinds, KindSignatures #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : Data.Type.RList
-- Copyright   : (c) 2016 Edwin Westbrook
--
-- License     : BSD3
--
-- Maintainer  : westbrook@galois.com
-- Stability   : experimental
-- Portability : GHC
--
-- A /right list/, or 'RList', is a list where cons adds to the end, or the
-- right-hand side, of a list. This is useful conceptually for contexts of
-- name-bindings, where the most recent name-binding is intuitively at the end
-- of the context.

module Data.Type.RList where

import Data.Type.Equality ((:~:)(..))
import Data.Proxy (Proxy(..))
import Data.Functor.Constant
import Data.Typeable

-------------------------------------------------------------------------------
-- Right-lists as a datatype
-------------------------------------------------------------------------------

data RList a
  = RNil
  | (RList a) :> a

type family ((r1 :: RList *) :++: (r2 :: RList *)) :: RList *
infixr 5 :++:
type instance r :++: RNil = r
type instance r1 :++: r2 :> a = (r1 :++: r2) :> a

proxyCons :: Proxy r -> f a -> Proxy (r :> a)
proxyCons _ _ = Proxy


-------------------------------------------------------------------------------
-- proofs of membership in a type-level list
-------------------------------------------------------------------------------

{-|
  A @Member ctx a@ is a \"proof\" that the type @a@ is in the type
  list @ctx@, meaning that @ctx@ equals

>  t0 ':>' a ':>' t1 ':>' ... ':>' tn

  for some types @t0,t1,...,tn@.
-}
data Member ctx a where
  Member_Base :: Member (ctx :> a) a
  Member_Step :: Member ctx a -> Member (ctx :> b) a
  deriving Typeable

instance Show (Member r a) where showsPrec p = showsPrecMember (p > 10)

showsPrecMember :: Bool -> Member ctx a -> ShowS
showsPrecMember _ Member_Base = showString "Member_Base"
showsPrecMember p (Member_Step prf) = showParen p $
  showString "Member_Step" . showsPrec 10 prf

--toEq :: Member (Nil :> a) b -> b :~: a
--toEq Member_Base = Refl
--toEq _ = error "Should not happen! (toEq)"

weakenMemberL :: Proxy r1 -> Member r2 a -> Member (r1 :++: r2) a
weakenMemberL _ Member_Base = Member_Base
weakenMemberL tag (Member_Step mem) = Member_Step (weakenMemberL tag mem)

membersEq :: Member ctx a -> Member ctx b -> Maybe (a :~: b)
membersEq Member_Base Member_Base = Just Refl
membersEq (Member_Step mem1) (Member_Step mem2) = membersEq mem1 mem2
membersEq _ _ = Nothing


------------------------------------------------------------
-- proofs that one list equals the append of two others
------------------------------------------------------------

{-|
  An @Append ctx1 ctx2 ctx@ is a \"proof\" that @ctx = ctx1 ':++:' ctx2@.
-}
data Append ctx1 ctx2 ctx where
  Append_Base :: Append ctx RNil ctx
  Append_Step :: Append ctx1 ctx2 ctx -> Append ctx1 (ctx2 :> a) (ctx :> a)

-- -- | Appends two 'Append' proofs.
-- trans ::
--   Append ctx1 ctx2 ex_ctx -> Append ex_ctx ctx3 ctx -> Append ctx1 (ctx2 :++: ctx3) ctx
-- trans app Append_Base = app
-- trans app (Append_Step app') = Append_Step (trans app app')

-- -- | Returns a proof that ctx :~: ctx1 :++: ctx2
-- appendPf :: Append ctx1 ctx2 ctx -> (ctx :~: ctx1 :++: ctx2)
-- appendPf Append_Base = Refl
-- appendPf (Append_Step app) = case appendPf app of Refl -> Refl

-- -- | Returns the length of an 'Append' proof.
-- length :: Append ctx1 ctx2 ctx3 -> Int
-- length Append_Base = 0
-- length (Append_Step app) = 1 + Data.Type.List.Proof.Append.length app

-------------------------------------------------------------------------------
-- Heterogeneous lists
-------------------------------------------------------------------------------

{-|
  A @MapRList f r@ is a vector with exactly one element of type @f a@ for
  each type @a@ in the type 'RList' @r@.
-}
data MapRList f c where
  MNil :: MapRList f RNil
  (:>:) :: MapRList f c -> f a -> MapRList f (c :> a)

-- | Create an empty 'MapRList' vector.
empty :: MapRList f RNil
empty = MNil

-- | Create a singleton 'MapRList' vector.
singleton :: f a -> MapRList f (RNil :> a)
singleton x = MNil :>: x

-- | Look up an element of a 'MapRList' vector using a 'Member' proof.
mapRListLookup :: Member c a -> MapRList f c -> f a
mapRListLookup Member_Base (_ :>: x) = x
mapRListLookup (Member_Step mem') (mc :>: _) = mapRListLookup mem' mc
--mapRListLookup _ _ = error "Should not happen! (mapRListLookup)"

-- | Map a function on all elements of a 'MapRList' vector.
mapMapRList :: (forall x. f x -> g x) -> MapRList f c -> MapRList g c
mapMapRList _ MNil = MNil
mapMapRList f (mc :>: x) = mapMapRList f mc :>: f x

-- | Map a binary function on all pairs of elements of two 'MapRList' vectors.
mapMapRList2 :: (forall x. f x -> g x -> h x) ->
                MapRList f c -> MapRList g c -> MapRList h c
mapMapRList2 _ MNil MNil = MNil
mapMapRList2 f (xs :>: x) (ys :>: y) = mapMapRList2 f xs ys :>: f x y
mapMapRList2 _ _ _ =
  error "Something is terribly wrong in mapMapRList2: this case should not happen!"

-- | Append two 'MapRList' vectors.
appendMapRList :: MapRList f c1 -> MapRList f c2 -> MapRList f (c1 :++: c2)
appendMapRList mc MNil = mc
appendMapRList mc1 (mc2 :>: x) = appendMapRList mc1 mc2 :>: x

-- -- | Append two 'MapRList' vectors.
-- appendWithPf :: Append c1 c2 c -> MapRList f c1 -> MapRList f c2 -> MapRList f c
-- appendWithPf Append_Base mc Nil = mc
-- appendWithPf (Append_Step app) mc1 (mc2 :>: x) = appendWithPf app mc1 mc2 :>: x
-- appendWithPf  _ _ _ = error "Something is terribly wrong in appendWithPf: this case should not happen!"

-- | Make an 'Append' proof from any 'MapRList' vector for the second
-- argument of the append.
mkAppend :: MapRList f c2 -> Append c1 c2 (c1 :++: c2)
mkAppend MNil = Append_Base
mkAppend (c :>: _) = Append_Step (mkAppend c)

-- | A version of 'mkAppend' that takes in a 'Proxy' argument.
mkMonoAppend :: Proxy c1 -> MapRList f c2 -> Append c1 c2 (c1 :++: c2)
mkMonoAppend _ = mkAppend

-- | The inverse of 'mkAppend', that builds an 'MapRList' from an 'Append'
proxiesFromAppend :: Append c1 c2 c -> MapRList Proxy c2
proxiesFromAppend Append_Base = MNil
proxiesFromAppend (Append_Step a) = proxiesFromAppend a :>: Proxy

-- | Split an 'MapRList' vector into two pieces. The first argument is a
-- phantom argument that gives the form of the first list piece.
splitMapRList :: (c ~ (c1 :++: c2)) => Proxy c1 ->
                 MapRList any c2 -> MapRList f c -> (MapRList f c1, MapRList f c2)
splitMapRList _ MNil mc = (mc, MNil)
splitMapRList _ (any :>: _) (mc :>: x) = (mc1, mc2 :>: x)
  where (mc1, mc2) = splitMapRList Proxy any mc
--split _ _ = error "Should not happen! (Map.split)"

-- | Create a vector of proofs that each type in @c@ is a 'Member' of @c@.
members :: MapRList f c -> MapRList (Member c) c
members MNil = MNil
members (c :>: _) = mapMapRList Member_Step (members c) :>: Member_Base

-- -- | Replace a single element of a 'MapRList' vector.
-- replace :: MapRList f c -> Member c a -> f a -> MapRList f c
-- replace (xs :>: _) Member_Base y = xs :>: y
-- replace (xs :>: x) (Member_Step memb) y = replace xs memb y :>: x
-- replace _ _ _ = error "Should not happen! (Map.replace)"

-- | Convert an MapRList to a list
mapRListToList :: MapRList (Constant a) c -> [a]
mapRListToList MNil = []
mapRListToList (xs :>: Constant x) = mapRListToList xs ++ [x]

-- | A type-class which ensures that ctx is a valid context, i.e., has
-- | the form (RNil :> t1 :> ... :> tn) for some types t1 through tn
class TypeCtx ctx where
  typeCtxProxies :: MapRList Proxy ctx

instance TypeCtx RNil where
  typeCtxProxies = MNil

instance TypeCtx ctx => TypeCtx (ctx :> a) where
  typeCtxProxies = typeCtxProxies :>: Proxy
