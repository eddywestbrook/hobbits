{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : Data.Type.List.Proof.Append
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- Proofs regarding a type list as an append of two others.

module Data.Type.List.Proof.Append where

import Data.Type.List.List
import Data.Type.Equality ((:=:)(..))

------------------------------------------------------------
-- proofs about appended lists
------------------------------------------------------------

{-|
  An @Append ctx1 ctx2 ctx@ is a \"proof\" that @ctx = ctx1 ':++:' ctx2@.
-}
data Append ctx1 ctx2 ctx where
  Append_Base :: Append ctx Nil ctx
  Append_Step :: Append ctx1 ctx2 ctx -> Append ctx1 (ctx2 :> a) (ctx :> a)

-- | Appends two 'Append' proofs.
trans ::
  Append ctx1 ctx2 ex_ctx -> Append ex_ctx ctx3 ctx -> Append ctx1 (ctx2 :++: ctx3) ctx
trans app Append_Base = app
trans app (Append_Step app') = Append_Step (trans app app')

-- | Returns a proof that ctx :=: ctx1 :++: ctx2
appendPf :: Append ctx1 ctx2 ctx -> (ctx :=: ctx1 :++: ctx2)
appendPf Append_Base = Refl
appendPf (Append_Step app) = case appendPf app of Refl -> Refl

-- | Returns the length of an 'Append' proof.
length :: Append ctx1 ctx2 ctx3 -> Int
length Append_Base = 0
length (Append_Step app) = 1 + Data.Type.List.Proof.Append.length app
