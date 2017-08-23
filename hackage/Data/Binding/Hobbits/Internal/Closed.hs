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
-- This module defines the type @'Cl' a@ of closed objects of type
-- @a@. Note that, in order to ensure adequacy of the Hobbits
-- name-binding approach, this representation is hidden from the user,
-- and so this file should never be imported directly by the user.
--

module Data.Binding.Hobbits.Internal.Closed where

import Language.Haskell.TH (Q, Exp(..), Type(..))
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.ExpandSyns as TH

import qualified Data.Generics as SYB
import qualified Language.Haskell.TH.Syntax as TH

{-| The type @Closed a@ represents a closed term of type @a@, i.e., an expression
of type @a@ with no free (Haskell) variables.  Since this cannot be checked
directly in the Haskell type system, the @Closed@ data type is hidden, and the
user can only create closed terms using Template Haskell, through the 'mkClosed'
operator. -}
newtype Closed a = Closed { unClosed :: a }

-- | Extract the type of an 'Info' object
#if MIN_VERSION_template_haskell(2,11,0)
reifyNameType :: TH.Name -> Q Type
reifyNameType n =
  TH.reify n >>= \i ->
  case i of
    TH.VarI _ ty _ -> return ty
    _ -> fail $ "hobbits Panic -- could not reify `" ++ show n ++ "'."
#else
reifyNameType :: TH.Name -> Q Type
reifyNameType n =
  TH.reify n >>= \i ->
  case i of
    TH.VarI _ ty _ _ -> return ty
    _ -> fail $ "hobbits Panic -- could not reify `" ++ show n ++ "'."
#endif

-- | @mkClosed@ is used with Template Haskell quotations to create closed terms
-- of type 'Closed'. A quoted expression is closed if all of the names occuring in
-- it are either:
--
--   1) bound globally or
--   2) bound within the quotation or
--   3) also of type 'Closed'.
mkClosed :: Q Exp -> Q Exp
mkClosed e = AppE (ConE 'Closed) `fmap` e >>= SYB.everywhereM (SYB.mkM w) where
  w e@(VarE n@(TH.Name _ flav)) = case flav of
    TH.NameG {} -> return e -- bound globally
    TH.NameU {} -> return e -- bound locally within this quotation
    TH.NameL {} -> closed n >> return e -- bound locally outside this quotation
    _ -> fail $ "`mkClosed' does not allow dynamically bound names: `"
      ++ show n ++ "'."
  w e = return e

  closed n = do
    ty <- reifyNameType n
    TH.expandSyns ty >>= w ty
      where
        w _ (AppT (ConT m) _) | m == ''Closed = return ()
        w top_ty (ForallT _ _ ty') = w top_ty ty'
        w top_ty _ =
          fail $ "`mkClosed` requires non-global variables to have type `Closed'.\n\t`"
          ++ show (TH.ppr n) ++ "' does not. It's type is:\n\t `"
          ++ show (TH.ppr top_ty) ++ "'."
