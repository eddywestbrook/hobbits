{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Data.Binding.Hobbits.Closed
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
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
  cl, clApply, unCl, mbApplyCl, mbLiftClosed, noClosedNames,
  -- * Synonyms
  mkClosed, Closed, unClosed
) where

import Data.Binding.Hobbits.Internal (Name, Mb(..), Cl(..))

import Data.Binding.Hobbits.NuElim

import Language.Haskell.TH (Q, Exp(..), Type(..))
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.ExpandSyns as TH

import qualified Data.Generics as SYB
import qualified Language.Haskell.TH.Syntax as TH




{-|
  The type @Cl a@ represents a closed term of type @a@,
  i.e., an expression of type @a@ with no free (Haskell) variables.
  Since this cannot be checked directly in the Haskell type system,
  the @Cl@ data type is hidden, and the user can only create
  closed terms using Template Haskell, through the 'mkClosed'
  operator.
-}
newtype Cl a = Cl { unCl :: a }



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
clMbApply :: (NuElim a, NuElim b) => Cl (Mb ctx (a -> b)) -> Cl (Mb ctx a) ->
             Cl (Mb ctx b)
clMbApply (Cl f) (Cl a) = Cl (mbApply f a)

-- | @mbLiftClosed@ is safe because closed terms don't contain names.
mbLiftClosed :: Mb ctx (Cl a) -> Cl a
mbLiftClosed (MkMb _ a) = a

-- | @noClosedNames@ encodes the hobbits guarantee that no name can escape its
-- multi-binding.
noClosedNames :: Cl (Name a) -> b
noClosedNames _ = error $ "... Clever girl!" ++
  "The `noClosedNames' invariant has somehow been violated."

-- | @mbApplyCl@ @f@ @b@ applies a closed function @f@ to the body of
-- multi-binding @b@. For example:
--
-- > mbApplyCl $(cl [| f |]) (nu $ \n -> n)   =   nu f
mbApplyCl :: Cl (a -> b) -> Mb ctx a -> Mb ctx b
mbApplyCl f (MkMb names i) = MkMb names (unCl f i)



-- | @mkClosed = cl@
mkClosed = cl

-- | @Closed = Cl@
type Closed = Cl

-- | @unClosed = unCl@
unClosed x = unCl x
