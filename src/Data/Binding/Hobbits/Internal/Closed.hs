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

import Control.Monad (mapM_, unless)

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
newtype Closed a =
  Closed {
  -- | Extract the value of a 'Closed' object
  unClosed :: a
  }

-- | Extract the type of an 'Info' object
reifyNameType :: TH.Name -> Q Type
reifyNameType n =
  TH.reify n >>= \i ->
  case i of
    TH.VarI _ ty _ -> return ty
    _ -> fail $ "hobbits Panic -- could not reify `" ++ show n ++ "'."

-- | @mkClosed@ is used with Template Haskell quotations to create closed terms
-- of type 'Closed'. A quoted expression is closed if all of the names occuring in
-- it are either:
--
--   1) bound globally or
--   2) bound within the quotation or
--   3) also of type 'Closed'.
mkClosed :: TH.ExpQ -> TH.ExpQ
mkClosed e =
  do r <- TH.conE 'Closed `TH.appE` e
     let localNames = SYB.everything (++) (SYB.mkQ [] boundNames) r
     let allNames   = SYB.everything (++) (SYB.mkQ [] pure) r
     mapM_ (checkName localNames) allNames
     pure r

-- | Check that no local variables from outside of an expression are captured within it.
checkName :: [TH.Name] -> TH.Name -> Q ()
checkName env n@(TH.Name _ flav) =
  case flav of
    TH.NameG {} -> return () -- bound globally
    TH.NameL {} -> checkClosedType n  -- bound locally outside this quotation
    TH.NameU {} -> unless (n `elem` env)
                 $ fail $ "`mkClosed' found name from outer quotation: `"
                       ++ TH.nameBase n ++ "'."
    _ -> fail $ "`mkClosed' does not allow dynamically bound names: `"
             ++ show n ++ "'."

-- | Determine if a locally defined name has a type that is closed.
checkClosedType :: TH.Name -> Q ()
checkClosedType n =
  do ty <- reifyNameType n
     w ty =<< TH.expandSyns ty
      where
        w _ (ConT m `AppT` _) | m == ''Closed = return ()
        w top_ty (ForallT _ _ ty') = w top_ty ty'
        w top_ty _ =
          fail $ "`mkClosed` requires non-global variables to have type `Closed'.\n\t`"
          ++ show (TH.ppr n) ++ "' does not. It's type is:\n\t `"
          ++ show (TH.ppr top_ty) ++ "'."

-- | Find the names immediately bound by a particular pattern
boundNames :: TH.Pat -> [TH.Name]
boundNames (TH.VarP n  ) = [n]
boundNames (TH.AsP  n _) = [n]
boundNames _             = [ ]
