{-# LANGUAGE TemplateHaskell, ViewPatterns #-}

-- |
-- Module      : Data.Binding.Hobbits.Closed
-- Copyright   : (c) 2014 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module uses Template Haskell to distinguish closed terms, so that the
-- library can trust such functions to not contain any @Name@ values in their
-- closure.

module Data.Binding.Hobbits.Closed (
  -- * Abstract types
  Cl(),
  -- * Operators involving 'Cl'
  cl, clApply, unCl, noClosedNames,
  -- * Synonyms
  mkClosed, Closed, unClosed
) where

import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.Internal.Closed
import Data.Binding.Hobbits.Mb

import Language.Haskell.TH (Q, Exp(..), Type(..))
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.ExpandSyns as TH

import qualified Data.Generics as SYB
import qualified Language.Haskell.TH.Syntax as TH


-- | @cl@ is used with Template Haskell quotations to create closed terms of
-- type 'Cl'. A quoted expression is closed if all of the names occuring in it
-- are
--
--   1) bound globally or
--   2) bound within the quotation or
--   3) also of type 'Cl'.
cl :: Q Exp -> Q Exp
cl e = AppE (ConE 'Cl) `fmap` e >>= SYB.everywhereM (SYB.mkM w) where
  w e@(VarE n@(TH.Name _ flav)) = case flav of
    TH.NameG {} -> return e -- bound globally
    TH.NameU {} -> return e -- bound locally within this quotation
    TH.NameL {} -> closed n >> return e -- bound locally outside this quotation
    _ -> fail $ "`cl' does not allow dynamically bound names: `"
      ++ show n ++ "'."
  w e = return e

  closed n = do
    i <- TH.reify n
    case i of
      TH.VarI _ ty _ _ -> TH.expandSyns ty >>= w
        where
          w (AppT (ConT m) _) | m == ''Cl = return ()
          w (ForallT _ _ ty) = w ty
          w _ = fail $ "`cl` requires non-global variables to have type `Cl'.\n\t`"
            ++ show (TH.ppr n) ++ "' does not. It's type is:\n\t `"
            ++ show (TH.ppr ty) ++ "'."
      _ -> fail $ "hobbits Panic -- could not reify `" ++ show n ++ "'."



-- | Closed terms are closed (sorry) under application.
clApply :: Cl (a -> b) -> Cl a -> Cl b
-- could be defined with cl were it not for the GHC stage restriction
clApply (Cl f) (Cl a) = Cl (f a)

-- | Closed multi-bindings are also closed under application.
clMbApply :: Cl (Mb ctx (a -> b)) -> Cl (Mb ctx a) ->
             Cl (Mb ctx b)
clMbApply (Cl f) (Cl a) = Cl (mbApply f a)

-- | @noClosedNames@ encodes the hobbits guarantee that no name can escape its
-- multi-binding.
noClosedNames :: Cl (Name a) -> b
noClosedNames _ = error $ "... Clever girl!" ++
  "The `noClosedNames' invariant has somehow been violated."

-- | @mkClosed = cl@
mkClosed = cl

-- | @Closed = Cl@
type Closed = Cl

-- | @unClosed = unCl@
unClosed x = unCl x
