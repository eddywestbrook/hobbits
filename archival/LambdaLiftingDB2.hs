{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses, RankNTypes, QuasiQuotes, TemplateHaskell, ViewPatterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-------------------------------------------------------------------------
-- lambda lifting for the lambda calculus with top-level declarations
-------------------------------------------------------------------------

module LambdaLifting2 where

import Ctx
import HobbitLibTH
import Data.List
import Control.Monad.Reader
import Control.Monad.Cont (Cont, ContT(..), runCont, cont)
import Control.Monad.Identity

------------------------------------------------------------
-- source terms
------------------------------------------------------------

-- Term datatype
data Term :: * -> * where
  Var :: Name (L a) -> Term a
  Lam :: Binding (L b) (Term a) -> Term (b -> a)
  App :: Term (b -> a) -> Term b -> Term a

instance Show (Term a) where show = tpretty

-- helper functions to build terms without explicitly using nu or Var
lam :: (Term a -> Term b) -> Term (a -> b)
lam f = Lam $ nu (f . Var)



-- pretty print terms
tpretty :: Term a -> String
tpretty t = pretty' (emptyMb t) emptyMC 0
  where pretty' :: Mb ctx (Term a) -> MapCtx StringF ctx -> Int -> String
        pretty' [nuQQ| Var b |] varnames n =
            case mbNameBoundP b of
              Left pf  -> unStringF (ctxLookup pf varnames)
              Right n -> "(free-var " ++ show n ++ ")"
        pretty' [nuQQ| Lam b |] varnames n =
            let x = "x" ++ show n in
            "(\\" ++ x ++ "." ++ pretty' (combineMb b) (varnames :> (StringF x)) (n+1) ++ ")"
        pretty' [nuQQ| App b1 b2 |] varnames n =
            "(" ++ pretty' b1 varnames n ++ " " ++ pretty' b2 varnames n ++ ")"


------------------------------------------------------------
-- target terms
------------------------------------------------------------

-- dummy datatypes for distinguishing Decl names from Lam names
data L a
data D a

data IsLType a where IsLType :: IsLType (L a)
type LCtx ctx = MapCtx IsLType ctx

data MbLName ctx a where
    MbLName :: Mb ctx (Name (L a)) -> MbLName ctx (L a)

-- terms with top-level names
data DTerm :: * -> * where
  TVar :: Name (L a) -> DTerm a
  TDVar :: Name (D a) -> DTerm a
  TApp :: DTerm (a -> b) -> DTerm a -> DTerm b

instance Show (DTerm a) where show = pretty

-- we use this type for a definiens instead of putting lambdas on the front
data Decl :: * -> * where
  DeclOne :: Binding (L a) (DTerm b) -> Decl (a -> b)
  DeclCons :: Binding (L a) (Decl b) -> Decl (a -> b)

-- top-level declarations with a return value
data Decls :: * -> * where
  DeclsBase :: DTerm a -> Decls a
  DeclsCons :: Decl b -> Binding (D b) (Decls a) -> Decls a

instance Show (Decls a) where show = decls_pretty

------------------------------------------------------------
-- pretty printing
------------------------------------------------------------

-- to make a function for MapCtx (for pretty)
newtype StringF x = StringF String
unStringF (StringF str) = str

-- pretty print terms
pretty :: DTerm a -> String
pretty t = mpretty (emptyMb t) emptyMC

mpretty :: Mb ctx (DTerm a) -> MapCtx StringF ctx -> String
mpretty [nuQQ| TVar b |] varnames =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuQQ| TDVar b |] varnames =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuQQ| TApp b1 b2 |] varnames =
    "(" ++ mpretty b1 varnames
        ++ " " ++ mpretty b2 varnames ++ ")"

mprettyName (Left pf) varnames = unStringF (ctxLookup pf varnames)
mprettyName (Right n) varnames = "(free-var " ++ (show n) ++ ")"
        

-- pretty print decls
decls_pretty :: Decls a -> String
decls_pretty decls =
    "let\n" ++ (mdecls_pretty (emptyMb decls) emptyMC 0)

mdecls_pretty :: Mb ctx (Decls a) -> MapCtx StringF ctx -> Int -> String
mdecls_pretty [nuQQ| DeclsBase t |] varnames n =
    "in " ++ (mpretty t varnames)
mdecls_pretty [nuQQ| DeclsCons decl rest |] varnames n =
    let fname = "F" ++ show n in
    fname ++ " " ++ (mdecl_pretty decl varnames 0) ++ "\n"
    ++ mdecls_pretty (combineMb rest) (varnames :> (StringF fname)) (n+1)

mdecl_pretty :: Mb ctx (Decl a) -> MapCtx StringF ctx -> Int -> String
mdecl_pretty [nuQQ| DeclOne t|] varnames n =
  let vname = "x" ++ show n in
  vname ++ " = " ++ mpretty (combineMb t) (varnames :> StringF vname)
mdecl_pretty [nuQQ| DeclCons d|] varnames n =
  let vname = "x" ++ show n in
  vname ++ " " ++ mdecl_pretty (combineMb d) (varnames :> StringF vname) (n+1)

------------------------------------------------------------
-- "peeling" lambdas off of a term
------------------------------------------------------------

type family AddArrows ctx b
type instance AddArrows CtxNil b = b
type instance AddArrows (CtxCons ctx (L a)) b = AddArrows ctx (a -> b)



data PeelRet ctx a where
    PeelRet :: lctx ~ CtxCons lctx0 b => LCtx lctx -> Mb (ctx :++: lctx) (Term a) ->
               PeelRet ctx (AddArrows lctx a)

peelLambdas :: Mb ctx (Binding (L b) (Term a)) ->
               PeelRet ctx (b -> a)
peelLambdas b =
  peelLambdasH EmptyMC IsLType (combineMb b)

peelLambdasH :: lctx ~ CtxCons lctx0 b =>
                LCtx lctx0 -> IsLType b -> Mb (ctx :++: lctx) (Term a) ->
                PeelRet ctx (AddArrows lctx a)
peelLambdasH lctx0 isl [nuQQ| Lam b |] =
    peelLambdasH (lctx0 :> isl) IsLType (combineMb b)
peelLambdasH lctx0 ilt t = PeelRet (lctx0 :> ilt) t




boundParams :: lctx ~ CtxCons lctx0 b =>
               LCtx lctx ->
               (MapCtx Name lctx -> DTerm a) ->
               Decl (AddArrows lctx a)
boundParams (lctx0 :> IsLType) k = -- flagged as non-exhaustive, but is because of type
  freeParams lctx0 (\ns -> DeclOne $ nu $ \n -> k (ns :> n))

freeParams :: LCtx lctx ->
              (MapCtx Name lctx -> Decl a) ->
              Decl (AddArrows lctx a)
freeParams EmptyMC k = k emptyMC
freeParams (lctx :> IsLType) k =
    freeParams lctx (\names -> DeclCons $ nu $ \x -> k (names :> x))





------------------------------------------------------------
-- sub-contexts
------------------------------------------------------------

-- FIXME: use this type in place of functions
type SubCtx ctx' ctx = MapCtx Name ctx -> MapCtx Name ctx'


------------------------------------------------------------
-- operations on contexts of free variables
------------------------------------------------------------

type FVList ctx fvs = MapCtx (MbLName ctx) fvs

-- unioning free variable contexts: the data structure
data FVUnionRet ctx fvs1 fvs2 where
    FVUnionRet :: FVList ctx fvs -> SubCtx fvs1 fvs -> SubCtx fvs2 fvs ->
                  FVUnionRet ctx fvs1 fvs2

fvUnion :: FVList ctx fvs1 -> FVList ctx fvs2 ->
                FVUnionRet ctx fvs1 fvs2
fvUnion EmptyMC EmptyMC =
    FVUnionRet EmptyMC (\_ -> EmptyMC) (\_ -> EmptyMC)
fvUnion EmptyMC (fvs2 :> fv2) =
    case fvUnion EmptyMC fvs2 of
      FVUnionRet fvs f1 f2 ->
          case elemMC fv2 fvs of
            Nothing -> FVUnionRet (fvs :> fv2) (\(xs :> x) -> f1 xs) (\(xs :> x) -> f2 xs :> x)
            Just idx -> FVUnionRet fvs f1 (\xs -> f2 xs :> ctxLookup idx xs)
fvUnion (fvs1 :> fv1) fvs2 =
    case fvUnion fvs1 fvs2 of
      FVUnionRet fvs f1 f2 ->
          case elemMC fv1 fvs of
            Nothing -> FVUnionRet (fvs :> fv1) (\(xs :> x) -> f1 xs :> x) (\(xs :> x) -> f2 xs)
            Just idx -> FVUnionRet fvs (\xs -> f1 xs :> ctxLookup idx xs) f2


elemMC :: MbLName ctx a -> FVList ctx fvs -> Maybe (InCtx fvs a)
elemMC _ EmptyMC = Nothing
elemMC mbLN@(MbLName n) (mc :> MbLName n') =
    case mbCmpName n n' of
      Just Refl -> Just InCtxBase
      Nothing -> fmap InCtxStep (elemMC mbLN mc)


------------------------------------------------------------
-- deBruijn terms, i.e., closed terms
------------------------------------------------------------

fvsToLCtx :: FVList ctx lctx -> LCtx lctx
fvsToLCtx = ctxMap mbLNameToProof where
    mbLNameToProof :: MbLName ctx a -> IsLType a
    mbLNameToProof (MbLName _) = IsLType

data STerm ctx a where
    SWeaken :: SubCtx ctx1 ctx -> STerm ctx1 a -> STerm ctx a
    SVar :: InCtx ctx (L a) -> STerm ctx a
    SDVar :: Name (D a) -> STerm ctx a
    SApp :: STerm ctx (a -> b) -> STerm ctx a -> STerm ctx b

skelSubst :: STerm ctx a -> MapCtx Name ctx -> DTerm a
skelSubst (SWeaken f db) names = skelSubst db $ f names
skelSubst (SVar inCtx) names = TVar $ ctxLookup inCtx names
skelSubst (SDVar dTVar) _ = TDVar dTVar
skelSubst (SApp db1 db2) names =
    TApp (skelSubst db1 names) (skelSubst db2 names)


-- applying a STerm to a context of names
skelAppMultiNames :: STerm fvs (AddArrows fvs a) -> FVList ctx fvs ->
                     STerm fvs a
skelAppMultiNames db args = skelAppMultiNamesH db args (ctxToInCtxs args)

skelAppMultiNamesH :: STerm fvs (AddArrows args a) ->
                      FVList ctx args -> MapCtx (InCtx fvs) args ->
                      STerm fvs a
skelAppMultiNamesH fun EmptyMC _ = fun
skelAppMultiNamesH fun (args :> MbLName _) (inCtxs :> inCtx) = -- flagged as non-exhaustive, but is because of type
    SApp (skelAppMultiNamesH fun args inCtxs) (SVar inCtx)


ctxToInCtxs :: MapCtx f ctx -> MapCtx (InCtx ctx) ctx
ctxToInCtxs EmptyMC = EmptyMC
ctxToInCtxs (ctx :> _) = ctxMap InCtxStep (ctxToInCtxs ctx) :> InCtxBase

------------------------------------------------------------
-- STerms combined with their free variables
------------------------------------------------------------



data FVSTerm ctx lctx a where
    FVSTerm :: FVList ctx fvs -> STerm (fvs :++: lctx) a ->
                FVSTerm ctx lctx a

fvSSepLTVars :: MapCtx f lctx -> FVSTerm (ctx :++: lctx) CtxNil a ->
                FVSTerm ctx lctx a
fvSSepLTVars lctx (FVSTerm fvs db) =
  case fvSSepLTVarsH lctx Tag fvs of
    SepRet fvs' f -> FVSTerm fvs' (SWeaken f db)


data SepRet lctx ctx fvs where
  SepRet :: FVList ctx fvs' -> SubCtx fvs (fvs' :++: lctx) ->
            SepRet lctx ctx fvs

fvSSepLTVarsH :: MapCtx f lctx -> Tag ctx -> FVList (ctx :++: lctx) fvs ->
                 SepRet lctx ctx fvs
fvSSepLTVarsH _ _ EmptyMC = SepRet EmptyMC (\_ -> EmptyMC)
fvSSepLTVarsH lctx ctx (fvs :> fv@(MbLName n)) =
    case fvSSepLTVarsH lctx ctx fvs of
      SepRet m f ->
          case raiseAppName (ctxAppendL ctx lctx) n of
            Left idx -> SepRet m (\xs -> f xs :> ctxLookup (weakenInCtxL (ctxTag m) idx) xs)
            Right n  ->
                SepRet (m :> MbLName n)
                       (\xs -> case mapCtxSplit (ctxAppendL (ctxConsTag (ctxTag m) fv) lctx) xs of
                                 (fvs' :> fv', lctxs) -> f (ctxAppend fvs' lctxs) :> fv')

raiseAppName :: IsAppend ctx1 ctx2 ctx -> Mb ctx (Name a) ->
                Either (InCtx ctx2 a) (Mb ctx1 (Name a))
raiseAppName isTApp n =
    case mbToplevel $(superComb [| mbNameBoundP |]) (separateMb isTApp n) of
      [nuQQ| Left inCtx |] -> Left $ mbInCtx inCtx
      [nuQQ| Right n |] -> Right n

------------------------------------------------------------
-- lambda-lifting, woo hoo!
------------------------------------------------------------


type LLBodyRet b ctx a = Cont (Decls b) (FVSTerm ctx CtxNil a)



llBody :: LCtx ctx -> Mb ctx (Term a) -> LLBodyRet b ctx a
llBody ctx [nuQQ| Var v |] =
  return $ FVSTerm (EmptyMC :> MbLName v) $ SVar InCtxBase
llBody ctx [nuQQ| App t1 t2 |] = do
  FVSTerm fvs1 db1 <- llBody ctx t1
  FVSTerm fvs2 db2 <- llBody ctx t2
  FVUnionRet names sub1 sub2 <- return $ fvUnion fvs1 fvs2
  return $ FVSTerm names $ SApp (SWeaken sub1 db1) (SWeaken sub2 db2)
llBody ctx [nuQQ| Lam b |] = do
  PeelRet lctx body <- return $ peelLambdas b
  llret <- llBody (ctxAppend ctx lctx) body
  FVSTerm fvs db <- return $ fvSSepLTVars lctx llret
  cont $ \k ->
    DeclsCons (freeParams (fvsToLCtx fvs) $ \names1 ->
               boundParams lctx $ \names2 ->
               skelSubst db (ctxAppend names1 names2))
      $ nu $ \d -> k $ FVSTerm fvs (skelAppMultiNames (SDVar d) fvs)



-- the top-level lambda-lifting function
lambdaLift :: Term a -> Decls a
lambdaLift t =
    runCont (llBody EmptyMC (emptyMb t))
              (\(FVSTerm fvs db) ->
                 let vs = ctxMap (\(MbLName mbn) -> elimEmptyMb mbn) fvs
                 in DeclsBase (skelSubst db vs))

------------------------------------------------------------
-- examples
------------------------------------------------------------

ex1 = lam (\f -> (lam $ \x -> App f x))
res1 = lambdaLift ex1

ex2 = lam (\f1 -> App f1 (lam (\f2 -> lam (\x -> App f2 x))))
res2 = lambdaLift ex2

ex3 = lam (\x -> lam (\f1 -> App f1 (lam (\f2 -> lam (\y -> f2 `App` x `App` y)))))
res3 = lambdaLift ex3

ex4 = lam (\x -> lam (\f1 -> App f1 (lam (\f2 -> lam (\y -> f2 `App` (f1 `App` x `App` y))))))
res4 = lambdaLift ex4

ex5 = lam (\f1 -> lam $ \f2 -> App f1 (lam $ \x -> App f2 x))
res5 = lambdaLift ex5

-- lambda-lift with a free variable
ex6 = nu (\f -> App (Var f) (lam $ \x -> x))
res6 = mbToplevel $(superComb [| lambdaLift |]) ex6

-- lambda-lift with a free variable as part of a lambda's environment
ex7 = nu (\f -> lam $ \y -> App y $ App (Var f) (lam $ \x -> x))
res7 = mbToplevel $(superComb [| lambdaLift |]) ex7

-- example from paper's Section 4
exP = lam $ \f -> lam $ \g -> App f $ lam $ \x -> App g $ App g x
resP = lambdaLift exP
