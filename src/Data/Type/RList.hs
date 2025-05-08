{-# LANGUAGE TypeOperators, EmptyCase, EmptyDataDecls, RankNTypes #-}
{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, KindSignatures #-}
{-# LANGUAGE GADTs, CPP, PatternGuards, ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ < 806
{-# LANGUAGE TypeInType #-}
#endif
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

module Data.Type.RList (
    RList, RNil, (:>), (:++:)
  , Member(..), weakenMemberL
  , Append(..), mkAppend, mkMonoAppend, proxiesFromAppend
  , RAssign(..), empty, singleton, get, HApply(..), hget, modify, set
  , memberElem, SplitAtMemberRet(..), memberSplitAt, map, mapRAssign
  , map2, head, tail, toList, mapToList, append, foldr, split
  , members, TypeCtx(..), appendAssoc, appendRNilConsEq, prependRNilEq, Eq1(..)
  ) where

import Prelude hiding (map, foldr, head, tail, any)
import Data.Kind
import Data.Type.Equality
import Data.Functor.Constant
import Data.Typeable

-------------------------------------------------------------------------------
-- * Right-lists as a datatype
-------------------------------------------------------------------------------

-- | A form of lists where elements are added to the right instead of the left
data RList a
  = RNil
  | (RList a) :> a
  deriving (Eq, Ord)

type RNil = 'RNil
type (:>) = '(:>)

-- | Append two 'RList's at the type level
type family ((r1 :: RList k) :++: (r2 :: RList k)) :: RList k
infixr 5 :++:
type instance (r :++: 'RNil) = r
type instance (r1 :++: (r2 ':> a)) = (r1 :++: r2) ':> a

-------------------------------------------------------------------------------
-- * Proofs of membership in a type-level list
-------------------------------------------------------------------------------

{-|
  A @Member ctx a@ is a \"proof\" that the type @a@ is in the type
  list @ctx@, meaning that @ctx@ equals

>  t0 ':>' a ':>' t1 ':>' ... ':>' tn

  for some types @t0,t1,...,tn@.
-}
data Member (ctx :: RList k1) (a :: k2) where
  Member_Base :: Member (ctx :> a) a
  Member_Step :: Member ctx a -> Member (ctx :> b) a
  deriving Typeable

instance Show (Member r a) where
  showsPrec p = showsPrecMember (p > 10) where
    showsPrecMember :: Bool -> Member ctx a -> ShowS
    showsPrecMember _ Member_Base = showString "Member_Base"
    showsPrecMember p' (Member_Step prf) = showParen p' $
      showString "Member_Step" . showsPrec 10 prf

instance TestEquality (Member ctx) where
  testEquality Member_Base Member_Base = Just Refl
  testEquality (Member_Step memb1) (Member_Step memb2)
    | Just Refl <- testEquality memb1 memb2
    = Just Refl
  testEquality _ _ = Nothing

instance Eq (Member ctx a) where
  Member_Base == Member_Base = True
  (Member_Step memb1) == (Member_Step memb2) = memb1 == memb2
  _ == _ = False

--toEq :: Member (Nil :> a) b -> b :~: a
--toEq Member_Base = Refl
--toEq _ = error "Should not happen! (toEq)"

-- | Weaken a 'Member' proof by prepending another context to the context it
-- proves membership in
weakenMemberL :: Proxy r1 -> Member r2 a -> Member (r1 :++: r2) a
weakenMemberL _ Member_Base = Member_Base
weakenMemberL tag (Member_Step mem) = Member_Step (weakenMemberL tag mem)


------------------------------------------------------------
-- * Proofs that one list equals the append of two others
------------------------------------------------------------

{-|
  An @Append ctx1 ctx2 ctx@ is a \"proof\" that @ctx = ctx1 ':++:' ctx2@.
-}
data Append ctx1 ctx2 ctx where
  Append_Base :: Append ctx RNil ctx
  Append_Step :: Append ctx1 ctx2 ctx -> Append ctx1 (ctx2 :> a) (ctx :> a)

-- | Make an 'Append' proof from any 'RAssign' vector for the second
-- argument of the append.
mkAppend :: RAssign f c2 -> Append c1 c2 (c1 :++: c2)
mkAppend MNil = Append_Base
mkAppend (c :>: _) = Append_Step (mkAppend c)

-- | A version of 'mkAppend' that takes in a 'Proxy' argument.
mkMonoAppend :: Proxy c1 -> RAssign f c2 -> Append c1 c2 (c1 :++: c2)
mkMonoAppend _ = mkAppend

-- | The inverse of 'mkAppend', that builds an 'RAssign' from an 'Append'
proxiesFromAppend :: Append c1 c2 c -> RAssign Proxy c2
proxiesFromAppend Append_Base = MNil
proxiesFromAppend (Append_Step a) = proxiesFromAppend a :>: Proxy


-------------------------------------------------------------------------------
-- * Contexts
-------------------------------------------------------------------------------

{-|
  An @RAssign f r@ an assignment of an @f a@ for each @a@ in the 'RList' @r@
-}
data RAssign (f :: k -> *) (c :: RList k) where
  MNil :: RAssign f RNil
  (:>:) :: RAssign f c -> f a -> RAssign f (c :> a)

-- | Create an empty 'RAssign' vector.
empty :: RAssign f RNil
empty = MNil

-- | Create a singleton 'RAssign' vector.
singleton :: f a -> RAssign f (RNil :> a)
singleton x = MNil :>: x

-- | Look up an element of an 'RAssign' vector using a 'Member' proof
get :: Member c a -> RAssign f c -> f a
get Member_Base (_ :>: x) = x
get (Member_Step mem') (mc :>: _) = get mem' mc

-- | Heterogeneous type application, including a proof that the input kind of
-- the function equals the kind of the type argument
data HApply (f :: k1 -> Type) (a :: k2) where
  HApply :: forall k (f :: k -> Type) (a :: k). f a -> HApply f a

-- | Look up an element of an 'RAssign' vector using a 'Member' proof at what
-- GHC thinks might be a different kind, i.e., heterogeneously
hget :: forall k1 k2 (f :: k1 -> Type) (c :: RList k1) (a :: k2).
        Member c a -> RAssign f c -> HApply f a
hget Member_Base (_ :>: x) = HApply x
hget (Member_Step mem') (mc :>: _) = hget mem' mc

-- | Modify an element of an 'RAssign' vector using a 'Member' proof.
modify :: Member c a -> (f a -> f a) -> RAssign f c -> RAssign f c
modify Member_Base f (xs :>: x) = xs :>: f x
modify (Member_Step mem') f (xs :>: x) = modify mem' f xs :>: x

-- | Set an element of an 'RAssign' vector using a 'Member' proof.
set :: Member c a -> f a -> RAssign f c -> RAssign f c
set memb x = modify memb (const x)

-- | Test if an object is in an 'RAssign', returning a 'Member' proof if it is
memberElem :: TestEquality f => f a -> RAssign f ctx -> Maybe (Member ctx a)
memberElem _ MNil = Nothing
memberElem x (_ :>: y) | Just Refl <- testEquality x y = Just Member_Base
memberElem x (xs :>: _) = fmap Member_Step $ memberElem x xs

-- | Existential return value from 'memberSplitAt'
data SplitAtMemberRet f ctx a where
  SplitAtMemberRet :: RAssign f ctx1 -> f a -> RAssign f ctx2 ->
                      SplitAtMemberRet f (ctx1 :> a :++: ctx2) a

-- | Split an assignment at the point specified by a 'Member' proof
memberSplitAt :: RAssign f ctx -> Member ctx a -> SplitAtMemberRet f ctx a
memberSplitAt MNil        member      = case member of {}
memberSplitAt (ctx :>: x) Member_Base = SplitAtMemberRet ctx x MNil
memberSplitAt (ctx :>: y) (Member_Step memb) =
  case memberSplitAt ctx memb of
    SplitAtMemberRet ctx1 x ctx2 -> SplitAtMemberRet ctx1 x (ctx2 :>: y)

-- | Map a function on all elements of an 'RAssign' vector.
map :: (forall x. f x -> g x) -> RAssign f c -> RAssign g c
map _ MNil = MNil
map f (mc :>: x) = map f mc :>: f x

-- | An alternate name for 'map' that does not clash with the prelude
mapRAssign :: (forall x. f x -> g x) -> RAssign f c -> RAssign g c
mapRAssign = map

-- | Map a binary function on all pairs of elements of two 'RAssign' vectors.
map2 :: (forall x. f x -> g x -> h x) ->
                RAssign f c -> RAssign g c -> RAssign h c
map2 _ MNil MNil = MNil
map2 f (xs :>: x) (ys :>: y) = map2 f xs ys :>: f x y

-- | Take the head of an 'RAssign'
head :: RAssign f (ctx :> a) -> f a
head (_ :>: x) = x

-- | Take the tail of an 'RAssign'
tail :: RAssign f (ctx :> a) -> RAssign f ctx
tail (xs :>: _) = xs

-- | Convert a monomorphic 'RAssign' to a list
toList :: RAssign (Constant a) c -> [a]
toList = mapToList getConstant

-- | Map a function with monomorphic output type across an 'RAssign' to create a
-- standard list:
--
-- > mapToList f = toList . map (Constant . f)
mapToList :: forall f ctx b. (forall a. f a -> b) -> RAssign f ctx -> [b]
mapToList f = go []
  where
    go :: forall d. [b] -> RAssign f d -> [b]
    go acc MNil       = acc
    go acc (xs :>: x) = go (f x : acc) xs

-- | Append two 'RAssign' vectors.
append :: RAssign f c1 -> RAssign f c2 -> RAssign f (c1 :++: c2)
append mc MNil = mc
append mc1 (mc2 :>: x) = append mc1 mc2 :>: x

-- | Perform a right fold across an 'RAssign'
foldr :: (forall a. f a -> r -> r) -> r -> RAssign f ctx -> r
foldr _ r MNil = r
foldr f r (xs :>: x) = f x $ foldr f r xs

-- | Split an 'RAssign' vector into two pieces. The first argument is a
-- phantom argument that gives the form of the first list piece.
split :: (c ~ (c1 :++: c2)) => prx c1 ->
                 RAssign any c2 -> RAssign f c -> (RAssign f c1, RAssign f c2)
split _ MNil mc = (mc, MNil)
split _ (any :>: _) (mc :>: x) =
  case split Proxy any mc of
      (mc1, mc2) -> (mc1, mc2 :>: x)

-- | Create a vector of proofs that each type in @c@ is a 'Member' of @c@.
members :: RAssign f c -> RAssign (Member c) c
members MNil = MNil
members (c :>: _) = map Member_Step (members c) :>: Member_Base

-- | A type-class which ensures that ctx is a valid context, i.e., has
-- | the form (RNil :> t1 :> ... :> tn) for some types t1 through tn
class TypeCtx ctx where
  typeCtxProxies :: RAssign Proxy ctx

instance TypeCtx 'RNil where
  typeCtxProxies = MNil

instance TypeCtx ctx => TypeCtx (ctx ':> a) where
  typeCtxProxies = typeCtxProxies :>: Proxy


-- | Proof that append on right-lists is associative
appendAssoc :: f1 ctx1 -> f2 ctx2 -> RAssign f3 ctx3 ->
               ctx1 :++: (ctx2 :++: ctx3) :~: (ctx1 :++: ctx2) :++: ctx3
appendAssoc _ _ MNil = Refl
appendAssoc c1 c2 (c3 :>: _) =
  case appendAssoc c1 c2 c3 of
    Refl -> Refl

-- | Proof that appending a right-list that starts with @a@ is the same as
-- consing @a@ and then appending
appendRNilConsEq :: prx1 ps1 -> prx_a a -> RAssign f ps2 ->
                    (ps1 :++: (RNil :> a :++: ps2)) :~: (ps1 :> a :++: ps2)
appendRNilConsEq _ _ MNil = Refl
appendRNilConsEq ps1 a (ps2 :>: _)
  | Refl <- appendRNilConsEq ps1 a ps2 = Refl

-- | Proof that prepending an empty 'RList' is the identity
prependRNilEq :: RAssign f ctx -> RNil :++: ctx :~: ctx
prependRNilEq MNil = Refl
prependRNilEq (ctx :>: _) | Refl <- prependRNilEq ctx = Refl


instance TestEquality f => TestEquality (RAssign f) where
  testEquality MNil MNil = Just Refl
  testEquality (xs1 :>: x1) (xs2 :>: x2)
    | Just Refl <- testEquality xs1 xs2
    , Just Refl <- testEquality x1 x2
    = Just Refl
  testEquality _ _ = Nothing

class Eq1 f where
  eq1 :: f a -> f a -> Bool

instance Eq1 f => Eq (RAssign f ctx) where
  MNil == MNil = True
  (xs1 :>: x1) == (xs2 :>: x2) = xs1 == xs2 && eq1 x1 x2
