{-# LANGUAGE TypeOperators, EmptyDataDecls, RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : Data.Type.HList
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : westbrook@galois.com
-- Stability   : experimental
-- Portability : GHC
--
-- A /type list/ contains types as elements. We use GADT proofs terms to
-- establish membership and append relations. A @Data.Type.HList.HList@ @f@
-- is a vector indexed by a type list, where @f :: * -> *@ is applied to each
-- type element.

module Data.Type.HList where

import Data.Type.Equality ((:~:)(..))
import Data.Proxy (Proxy(..))
import Data.Functor.Constant
import Data.Typeable

-------------------------------------------------------------------------------
-- type-level lists
-------------------------------------------------------------------------------

data Nil deriving Typeable
data r :> a deriving Typeable; infixl 5 :>

type family (r1 :++: r2); infixr 5 :++:
type instance r :++: Nil = r
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
  Append_Base :: Append ctx Nil ctx
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
  A @HList f c@ is a vector with exactly one element of type @f a@ for
  each type @a@ in the type list @c@.
-}
data HList f c where
  Nil :: HList f Nil -- Creates an empty vector
  (:>) :: HList f c -> f a -> HList f (c :> a) -- Appends an element to the end of a vector

-- | Create an empty 'HList' vector.
empty :: HList f Nil
empty = Nil

-- | Create a singleton 'HList' vector.
singleton :: f a -> HList f (Nil :> a)
singleton x = Nil :> x

-- | Look up an element of a 'HList' vector using a 'Member' proof.
hlistLookup :: Member c a -> HList f c -> f a
hlistLookup Member_Base (_ :> x) = x
hlistLookup (Member_Step mem') (mc :> _) = hlistLookup mem' mc
--hlistLookup _ _ = error "Should not happen! (hlistLookup)"

-- | Map a function on all elements of a 'HList' vector.
mapHList :: (forall x. f x -> g x) -> HList f c -> HList g c
mapHList _ Nil = Nil
mapHList f (mc :> x) = mapHList f mc :> f x

-- | Map a binary function on all pairs of elements of two 'HList' vectors.
mapHList2 :: (forall x. f x -> g x -> h x) -> HList f c -> HList g c -> HList h c
mapHList2 _ Nil Nil = Nil
mapHList2 f (xs :> x) (ys :> y) = mapHList2 f xs ys :> f x y
mapHList2 _ _ _ = error "Something is terribly wrong in mapHList2: this case should not happen!"

-- | Append two 'HList' vectors.
appendHList :: HList f c1 -> HList f c2 -> HList f (c1 :++: c2)
appendHList mc Nil = mc
appendHList mc1 (mc2 :> x) = appendHList mc1 mc2 :> x

-- -- | Append two 'HList' vectors.
-- appendWithPf :: Append c1 c2 c -> HList f c1 -> HList f c2 -> HList f c
-- appendWithPf Append_Base mc Nil = mc
-- appendWithPf (Append_Step app) mc1 (mc2 :> x) = appendWithPf app mc1 mc2 :> x
-- appendWithPf  _ _ _ = error "Something is terribly wrong in appendWithPf: this case should not happen!"

-- | Make an 'Append' proof from any 'HList' vector for the second
-- argument of the append.
mkAppend :: HList f c2 -> Append c1 c2 (c1 :++: c2)
mkAppend Nil = Append_Base
mkAppend (c :> _) = Append_Step (mkAppend c)

-- | A version of 'mkAppend' that takes in a 'Proxy' argument.
mkMonoAppend :: Proxy c1 -> HList f c2 -> Append c1 c2 (c1 :++: c2)
mkMonoAppend _ = mkAppend

-- | The inverse of 'mkAppend', that builds an 'HList' from an 'Append'
proxiesFromAppend :: Append c1 c2 c -> HList Proxy c2
proxiesFromAppend Append_Base = Nil
proxiesFromAppend (Append_Step a) = proxiesFromAppend a :> Proxy

-- | Split an 'HList' vector into two pieces. The first argument is a
-- phantom argument that gives the form of the first list piece.
splitHList :: (c ~ (c1 :++: c2)) => Proxy c1 -> HList any c2 -> HList f c -> (HList f c1, HList f c2)
splitHList _ Nil mc = (mc, Nil)
splitHList _ (any :> _) (mc :> x) = (mc1, mc2 :> x)
  where (mc1, mc2) = splitHList Proxy any mc
--split _ _ = error "Should not happen! (Map.split)"

-- | Create a vector of proofs that each type in @c@ is a 'Member' of @c@.
members :: HList f c -> HList (Member c) c
members Nil = Nil
members (c :> _) = mapHList Member_Step (members c) :> Member_Base

-- -- | Replace a single element of a 'HList' vector.
-- replace :: HList f c -> Member c a -> f a -> HList f c
-- replace (xs :> _) Member_Base y = xs :> y
-- replace (xs :> x) (Member_Step memb) y = replace xs memb y :> x
-- replace _ _ _ = error "Should not happen! (Map.replace)"

-- | Convert an HList to a list
hlistToList :: HList (Constant a) c -> [a]
hlistToList Nil = []
hlistToList (xs :> Constant x) = hlistToList xs ++ [x]

-- | A type-class which ensures that ctx is a valid context, i.e., has
-- | the form (Nil :> t1 :> ... :> tn) for some types t1 through tn
class TypeCtx ctx where
  typeCtxProxies :: HList Proxy ctx

instance TypeCtx Nil where
  typeCtxProxies = Nil

instance TypeCtx ctx => TypeCtx (ctx :> a) where
  typeCtxProxies = typeCtxProxies :> Proxy
