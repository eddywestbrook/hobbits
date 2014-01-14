{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- |
-- Module      : Data.Type.List.Proof.Member
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- Proofs regarding membership of a type in a type list.

module Data.Type.List.Proof.Member (
  -- * Abstract data types
  Member(..),
  -- * Operators on 'Member' proofs
  toEq, weakenL, same, weakenR, split
  ) where

import Data.Type.List.List
import Data.Type.List.Proof.Append

import Data.Type.Equality ((:=:)(..))
import Data.Proxy (Proxy(..))
import Data.Typeable

import Unsafe.Coerce

-------------------------------------------------------------------------------
-- proof of membership
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

showsPrecMember _ Member_Base = showString "Member_Base"
showsPrecMember p (Member_Step prf) = showParen p $
  showString "Member_Step" . showsPrec 10 prf

toEq :: Member (Nil :> a) b -> b :=: a
toEq Member_Base = Refl
toEq _ = error "Should not happen! (toEq)"

weakenL :: Proxy r1 -> Member r2 a -> Member (r1 :++: r2) a
weakenL _    Member_Base = Member_Base
weakenL tag (Member_Step mem) = Member_Step (weakenL tag mem)

same :: Member r a -> Member r b -> Maybe (a :=: b)
same Member_Base Member_Base = Just $ unsafeCoerce Refl
same (Member_Step mem1) (Member_Step mem2) = same mem1 mem2
same _ _ = Nothing

-------------------------------------------------------------------------------
-- relations between Member and Append
-------------------------------------------------------------------------------

weakenR :: Member r1 a -> Append r1 r2 r -> Member r a
weakenR mem Append_Base = mem
weakenR mem (Append_Step app) = Member_Step (weakenR mem app)

split ::
  Append r1 r2 r -> Member r a -> Either (Member r1 a) (Member r2 a)
split app mem = case app of
  Append_Base -> Left mem
  Append_Step app' -> case mem of
    Member_Base -> Right Member_Base
    Member_Step mem' -> case split app' mem' of
      Left prf -> Left prf
      Right prf -> Right (Member_Step prf)
