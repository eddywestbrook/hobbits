{-# LANGUAGE QuasiQuotes, ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators, DataKinds #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- |
-- Module      : Data.Binding.Hobbits.Examples.LambdaLifting
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- The lambda lifting example from the paper E. Westbrook, N. Frisby,
-- P. Brauner, \"Hobbits for Haskell: A Library for Higher-Order Encodings in
-- Functional Programming Languages\".

-------------------------------------------------------------------------
-- lambda lifting for the lambda calculus with top-level declarations
-------------------------------------------------------------------------

module Data.Binding.Hobbits.Examples.LambdaLifting (
  -- * Term data types, using 'Data.Binding.Hobbits.Mb'
  module Data.Binding.Hobbits.Examples.LambdaLifting.Terms,
  -- * The lambda-lifting function
  lambdaLift, mbLambdaLift
  ) where

import Data.Binding.Hobbits
import qualified Data.Type.RList as C

import Data.Binding.Hobbits.Examples.LambdaLifting.Terms

-- imported for ease of use at terminal
import Data.Binding.Hobbits.Examples.LambdaLifting.Examples

import Control.Monad.Cont (Cont, runCont, cont)

------------------------------------------------------------
-- "peeling" lambdas off of a term
------------------------------------------------------------

data LType a where LType :: LType (L a)
type LC c = RAssign LType c

type family AddArrows (c :: RList *) b
type instance AddArrows RNil b = b
type instance AddArrows (c :> L a) b = AddArrows c (a -> b)

data PeelRet c a where
  PeelRet :: lc ~ (lc0 :> b) => LC lc -> Mb (c :++: lc) (Term a) ->
             PeelRet c (AddArrows lc a)

peelLambdas :: Mb c (Binding (L b) (Term a)) -> PeelRet c (b -> a)
peelLambdas b = peelLambdasH MNil LType (mbCombine b)

peelLambdasH ::
  lc ~ (lc0 :> b) => LC lc0 -> LType b -> Mb (c :++: lc) (Term a) ->
                     PeelRet c (AddArrows lc a)
peelLambdasH lc0 isl [nuP| Lam b |] =
  peelLambdasH (lc0 :>: isl) LType (mbCombine b)
peelLambdasH lc0 ilt t = PeelRet (lc0 :>: ilt) t




boundParams ::
  lc ~ (lc0 :> b) => LC lc -> (RAssign Name lc -> DTerm a) ->
                     Decl (AddArrows lc a)
boundParams (lc0 :>: LType) k = -- flagged as non-exhaustive, in spite of type
  freeParams lc0 (\ns -> Decl_One $ nu $ \n -> k (ns :>: n))

freeParams ::
  LC lc -> (RAssign Name lc -> Decl a) -> Decl (AddArrows lc a)
freeParams MNil k = k C.empty
freeParams (lc :>: LType) k =
    freeParams lc (\names -> Decl_Cons $ nu $ \x -> k (names :>: x))

------------------------------------------------------------
-- sub-contexts
------------------------------------------------------------

-- FIXME: use this type in place of functions
type SubC c' c = RAssign Name c -> RAssign Name c'

------------------------------------------------------------
-- operations on contexts of free variables
------------------------------------------------------------

data MbLName c a where
    MbLName :: Mb c (Name (L a)) -> MbLName c (L a)

type FVList c fvs = RAssign (MbLName c) fvs

-- unioning free variable contexts: the data structure
data FVUnionRet c fvs1 fvs2 where
    FVUnionRet :: FVList c fvs -> SubC fvs1 fvs -> SubC fvs2 fvs ->
                  FVUnionRet c fvs1 fvs2

fvUnion :: FVList c fvs1 -> FVList c fvs2 -> FVUnionRet c fvs1 fvs2
fvUnion MNil MNil = FVUnionRet MNil (\_ -> MNil) (\_ -> MNil)
fvUnion MNil (fvs2 :>: fv2) = case fvUnion MNil fvs2 of
  FVUnionRet fvs f1 f2 -> case elemMC fv2 fvs of
    Nothing -> FVUnionRet (fvs :>: fv2)
               (\(xs :>: _) -> f1 xs) (\(xs :>: x) -> f2 xs :>: x)
    Just idx -> FVUnionRet fvs f1 (\xs -> f2 xs :>: C.get idx xs)
fvUnion (fvs1 :>: fv1) fvs2 = case fvUnion fvs1 fvs2 of
  FVUnionRet fvs f1 f2 -> case elemMC fv1 fvs of
    Nothing -> FVUnionRet (fvs :>: fv1)
               (\(xs :>: x) -> f1 xs :>: x) (\(xs :>: _) -> f2 xs)
    Just idx -> FVUnionRet fvs (\xs -> f1 xs :>: C.get idx xs) f2

elemMC :: MbLName c a -> FVList c fvs -> Maybe (Member fvs a)
elemMC _ MNil = Nothing
elemMC mbLN@(MbLName n) (mc :>: MbLName n') = case mbCmpName n n' of
  Just Refl -> Just Member_Base
  Nothing -> fmap Member_Step (elemMC mbLN mc)

------------------------------------------------------------
-- deBruijn terms, i.e., closed terms
------------------------------------------------------------

data STerm c a where
    SWeaken :: SubC c1 c -> STerm c1 a -> STerm c a
    SVar :: Member c (L a) -> STerm c a
    SDVar :: Name (D a) -> STerm c a
    SApp :: STerm c (a -> b) -> STerm c a -> STerm c b

skelSubst :: STerm c a -> RAssign Name c -> DTerm a
skelSubst (SWeaken f db) names = skelSubst db $ f names
skelSubst (SVar inC) names = TVar $ C.get inC names
skelSubst (SDVar dTVar) _ = TDVar dTVar
skelSubst (SApp db1 db2) names = TApp (skelSubst db1 names) (skelSubst db2 names)

-- applying a STerm to a context of names
skelAppMultiNames ::
  STerm fvs (AddArrows fvs a) -> FVList c fvs -> STerm fvs a
skelAppMultiNames db args = skelAppMultiNamesH db args (C.members args) where
  skelAppMultiNamesH ::
    STerm fvs (AddArrows args a) -> FVList c args -> RAssign (Member fvs) args ->
    STerm fvs a
  skelAppMultiNamesH fvs MNil _ = fvs
  -- flagged as non-exhaustive, in spite of type
  skelAppMultiNamesH fvs (args :>: MbLName _) (inCs :>: inC) =
    SApp (skelAppMultiNamesH fvs args inCs) (SVar inC)

------------------------------------------------------------
-- STerms combined with their free variables
------------------------------------------------------------

data FVSTerm c lc a where
    FVSTerm :: FVList c fvs -> STerm (fvs :++: lc) a -> FVSTerm c lc a

fvSSepLTVars ::
  RAssign f lc -> FVSTerm (c :++: lc) RNil a -> FVSTerm c lc a
fvSSepLTVars lc (FVSTerm fvs db) = case fvSSepLTVarsH lc Proxy fvs of
  SepRet fvs' f -> FVSTerm fvs' (SWeaken f db)

data SepRet lc c fvs where
  SepRet :: FVList c fvs' -> SubC fvs (fvs' :++: lc) -> SepRet lc c fvs

-- | Create a 'Proxy' object for the type list of a 'RAssign' vector.
proxyOfRAssign :: RAssign f c -> Proxy c
proxyOfRAssign _ = Proxy

fvSSepLTVarsH ::
  RAssign f lc -> Proxy c -> FVList (c :++: lc) fvs -> SepRet lc c fvs
fvSSepLTVarsH _ _ MNil = SepRet MNil (\_ -> MNil)
fvSSepLTVarsH lc c (fvs :>: fv@(MbLName n)) = case fvSSepLTVarsH lc c fvs of
  SepRet m f -> case raiseAppName (C.mkMonoAppend c lc) n of
    Left idx ->
      SepRet m (\xs ->
                 f xs :>: C.get (C.weakenMemberL (proxyOfRAssign m) idx) xs)
    Right n ->
      SepRet (m :>: MbLName n)
      (\xs -> case C.split c' lc xs of
          (fvs' :>: fv', lcs) ->
            f (append fvs' lcs) :>: fv')
    where c' = proxyCons (proxyOfRAssign m) fv

raiseAppName ::
  Append c1 c2 (c1 :++: c2) -> Mb (c1 :++: c2) (Name a) -> Either (Member c2 a) (Mb c1 (Name a))
raiseAppName app n =
  case fmap mbNameBoundP (mbSeparate (proxiesFromAppend app) n) of
    [nuP| Left mem |] -> Left $ mbLift mem
    [nuP| Right n |] -> Right n

------------------------------------------------------------
-- lambda-lifting, woo hoo!
------------------------------------------------------------

type LLBodyRet b c a = Cont (Decls b) (FVSTerm c RNil a)

llBody :: LC c -> Mb c (Term a) -> LLBodyRet b c a
llBody _ [nuP| Var v |] =
  return $ FVSTerm (MNil :>: MbLName v) $ SVar Member_Base
llBody c [nuP| App t1 t2 |] = do
  FVSTerm fvs1 db1 <- llBody c t1
  FVSTerm fvs2 db2 <- llBody c t2
  FVUnionRet names sub1 sub2 <- return $ fvUnion fvs1 fvs2
  return $ FVSTerm names $ SApp (SWeaken sub1 db1) (SWeaken sub2 db2)
llBody c [nuP| Lam b |] = do
  PeelRet lc body <- return $ peelLambdas b
  llret <- llBody (C.append c lc) body
  FVSTerm fvs db <- return $ fvSSepLTVars lc llret
  cont $ \k ->
    Decls_Cons (freeParams (fvsToLC fvs) $ \names1 ->
                boundParams lc $ \names2 ->
                skelSubst db (C.append names1 names2))
      $ nu $ \d -> k $ FVSTerm fvs (skelAppMultiNames (SDVar d) fvs)
  where
    fvsToLC :: FVList c lc -> LC lc
    fvsToLC = C.mapRAssign mbLNameToProof where
      mbLNameToProof :: MbLName c a -> LType a
      mbLNameToProof (MbLName _) = LType

-- the top-level lambda-lifting function
lambdaLift :: Term a -> Decls a
lambdaLift t = runCont (llBody MNil (emptyMb t)) $ \(FVSTerm fvs db) ->
  Decls_Base (skelSubst db (C.mapRAssign (\(MbLName mbn) -> elimEmptyMb mbn) fvs))

mbLambdaLift :: Mb c (Term a) -> Mb c (Decls a)
mbLambdaLift = fmap lambdaLift
