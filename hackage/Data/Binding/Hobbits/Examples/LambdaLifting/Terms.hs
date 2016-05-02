{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TemplateHaskell, Rank2Types, QuasiQuotes, ViewPatterns #-}
{-# LANGUAGE GADTs, KindSignatures #-}

-- |
-- Module      : Data.Binding.Hobbits.SuperComb
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--

module Data.Binding.Hobbits.Examples.LambdaLifting.Terms
  (L, D,
   Term(..), lam,
   DTerm(..), Decl(..), Decls(..)
  ) where

import Data.Binding.Hobbits
import qualified Data.Type.HList as C

-- dummy datatypes for distinguishing Decl names from Lam names
data L a
data D a

-- to make a function for HList (for pretty)
newtype StringF x = StringF String
unStringF (StringF str) = str


------------------------------------------------------------
-- source terms
------------------------------------------------------------

-- Term datatype; no Ds since there's no declarations yet
data Term :: * -> * where
  Var :: Name (L a) -> Term a
  Lam :: Binding (L b) (Term a) -> Term (b -> a)
  App :: Term (b -> a) -> Term b -> Term a

$(mkNuMatching [t| forall a . Term a |])

instance Show (Term a) where show = tpretty

-- helps to build terms without explicitly using nu or Var
lam :: (Term a -> Term b) -> Term (a -> b)
lam f = Lam $ nu (f . Var)

-- pretty print terms
tpretty :: Term a -> String
tpretty t = pretty' (emptyMb t) C.empty 0
  where pretty' :: Mb c (Term a) -> HList StringF c -> Int -> String
        pretty' [nuP| Var b |] varnames n =
            case mbNameBoundP b of
              Left pf  -> unStringF (C.hlistLookup pf varnames)
              Right n -> "(free-var " ++ show n ++ ")"
        pretty' [nuP| Lam b |] varnames n =
            let x = "x" ++ show n in
            "(\\" ++ x ++ "." ++ pretty' (mbCombine b) (varnames :> (StringF x)) (n+1) ++ ")"
        pretty' [nuP| App b1 b2 |] varnames n =
            "(" ++ pretty' b1 varnames n ++ " " ++ pretty' b2 varnames n ++ ")"

------------------------------------------------------------
-- target terms
------------------------------------------------------------

-- terms under declarations
data DTerm :: * -> * where
  TVar :: Name (L a) -> DTerm a
  TDVar :: Name (D a) -> DTerm a
  TApp :: DTerm (a -> b) -> DTerm a -> DTerm b

-- we use this type for a definiens instead of putting lambdas on the front
data Decl :: * -> * where
  Decl_One :: Binding (L a) (DTerm b) -> Decl (a -> b)
  Decl_Cons :: Binding (L a) (Decl b) -> Decl (a -> b)

-- top-level declarations with a return value
data Decls :: * -> * where
  Decls_Base :: DTerm a -> Decls a
  Decls_Cons :: Decl b -> Binding (D b) (Decls a) -> Decls a

$(mkNuMatching [t| forall a . DTerm a |])
$(mkNuMatching [t| forall a . Decl a |])
$(mkNuMatching [t| forall a . Decls a |])

instance Show (DTerm a) where show = pretty
instance Show (Decls a) where show = decls_pretty

------------------------------------------------------------
-- pretty printing
------------------------------------------------------------

-- pretty print terms
pretty :: DTerm a -> String
pretty t = mpretty (emptyMb t) C.empty

mpretty :: Mb c (DTerm a) -> HList StringF c -> String
mpretty [nuP| TVar b |] varnames =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuP| TDVar b |] varnames =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuP| TApp b1 b2 |] varnames =
    "(" ++ mpretty b1 varnames
        ++ " " ++ mpretty b2 varnames ++ ")"

mprettyName (Left pf) varnames = unStringF (C.hlistLookup pf varnames)
mprettyName (Right n) varnames = "(free-var " ++ (show n) ++ ")"
        

-- pretty print decls
decls_pretty :: Decls a -> String
decls_pretty decls =
    "let\n" ++ (mdecls_pretty (emptyMb decls) C.empty 0)

mdecls_pretty :: Mb c (Decls a) -> HList StringF c -> Int -> String
mdecls_pretty [nuP| Decls_Base t |] varnames n =
    "in " ++ (mpretty t varnames)
mdecls_pretty [nuP| Decls_Cons decl rest |] varnames n =
    let fname = "F" ++ show n in
    fname ++ " " ++ (mdecl_pretty decl varnames 0) ++ "\n"
    ++ mdecls_pretty (mbCombine rest) (varnames :> (StringF fname)) (n+1)

mdecl_pretty :: Mb c (Decl a) -> HList StringF c -> Int -> String
mdecl_pretty [nuP| Decl_One t|] varnames n =
  let vname = "x" ++ show n in
  vname ++ " = " ++ mpretty (mbCombine t) (varnames :> StringF vname)
mdecl_pretty [nuP| Decl_Cons d|] varnames n =
  let vname = "x" ++ show n in
  vname ++ " " ++ mdecl_pretty (mbCombine d) (varnames :> StringF vname) (n+1)
