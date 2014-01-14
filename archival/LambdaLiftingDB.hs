{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses, RankNTypes, QuasiQuotes, TemplateHaskell, ViewPatterns #-}
-------------------------------------------------------------------------
-- lambda lifting for the lambda calculus with top-level declarations
-------------------------------------------------------------------------

module LambdaLifting where

import Ctx
import HobbitLibTH
import Data.List
import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.Identity


-- dummy datatypes for distinguishing Decl names from Lam names
data L a
data D a

-- terms with top-level names
data DTerm a where
  Var :: Name (L a) -> DTerm a
  DVar :: Name (D a) -> DTerm a
  Lam :: Binding (L a) (DTerm b) -> DTerm (a -> b)
  App :: DTerm (a -> b) -> DTerm a -> DTerm b

instance Show (DTerm a) where
    show = pretty

-- top-level declarations with a "return value"
data Decls a where
  DeclsBase :: DTerm a -> Decls a
  DeclsCons :: DTerm b -> Binding (D b) (Decls a) -> Decls a

instance Show (Decls a) where
    show = decls_pretty

-- helper functions to build terms without explicitly using nu or Var
lam :: (DTerm a -> DTerm b) -> DTerm (a -> b)
lam f = Lam $ nu (f . Var)


------------------------------------------------------------
-- pretty printing
------------------------------------------------------------

-- to make a function for MapCtx (for pretty)
newtype StringF x = StringF String
unStringF (StringF str) = str

-- pretty print terms
pretty :: DTerm a -> String
pretty t = mpretty (emptyMb t) emptyMC 0

mpretty :: Mb ctx (DTerm a) -> MapCtx StringF ctx -> Int -> String
mpretty [nuQQ| Var b |] varnames n =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuQQ| DVar b |] varnames n =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuQQ| Lam b |] varnames n =
    let x = "x" ++ show n in
    "(\\" ++ x ++ "." ++ mpretty (combineMb b) (varnames :> (StringF x)) (n+1) ++ ")"
mpretty [nuQQ| App b1 b2 |] varnames n =
    "(" ++ mpretty b1 varnames n
        ++ " " ++ mpretty b2 varnames n ++ ")"

mprettyName (Left pf) varnames = unStringF (ctxLookup pf varnames)
mprettyName (Right n) varnames = "##free var: " ++ (show n) ++ "##"
        

-- pretty print decls
decls_pretty :: Decls a -> String
decls_pretty decls =
    "[ decls:\n" ++ (mdecls_pretty (emptyMb decls) emptyMC 0) ++ "]"

mdecls_pretty :: Mb ctx (Decls a) -> MapCtx StringF ctx -> Int -> String
mdecls_pretty [nuQQ| DeclsBase t |] varnames n =
    (mpretty t varnames 0) ++ "\n"
mdecls_pretty [nuQQ| DeclsCons term rest |] varnames n =
    let fname = "F" ++ show n in
    fname ++ " = " ++ (mpretty term varnames 0) ++ "\n\n"
    ++ mdecls_pretty (combineMb rest) (varnames :> (StringF fname)) (n+1)


------------------------------------------------------------
-- "peeling" lambdas off of a term
------------------------------------------------------------

type family AddArrows ctx b
type instance AddArrows CtxNil b = b
type instance AddArrows (CtxCons ctx (L a)) b = AddArrows ctx (a -> b)

data PeelRet ctx a where
    PeelRet :: LCtx lam_ctx -> Mb (ctx :++: lam_ctx) (DTerm a) ->
               PeelRet ctx (AddArrows lam_ctx a)

peelLambdas :: LCtx lam_ctx -> Mb (ctx :++: lam_ctx) (DTerm a) ->
               PeelRet ctx (AddArrows lam_ctx a)
peelLambdas lctx [nuQQ| Lam b |] =
    peelLambdas (lctx :> IsLType) (combineMb b)
peelLambdas lctx [nuQQ| b |] = PeelRet lctx b


addLams :: LCtx lam_ctx -> (MapCtx Name lam_ctx -> DTerm a) ->
           DTerm (AddArrows lam_ctx a)
addLams EmptyMC k = k emptyMC
addLams (lam_ctx :> IsLType) k =
    addLams lam_ctx (\names -> Lam $ nu $ \x -> k (names :> x))


------------------------------------------------------------
-- sub-contexts
------------------------------------------------------------

-- FIXME: use this type in place of functions
type SubCtx ctx' ctx = MapCtx Name ctx -> MapCtx Name ctx'

subCtxConsBoth :: SubCtx ctx' ctx -> SubCtx (CtxCons ctx' a) (CtxCons ctx a)
subCtxConsBoth subCtx = \(ctx :> x) -> subCtx ctx :> x

subCtxConsR :: SubCtx ctx' ctx -> SubCtx ctx' (CtxCons ctx a)
subCtxConsR subCtx = \(ctx :> _) -> subCtx ctx


------------------------------------------------------------
-- operations on contexts of free variables
------------------------------------------------------------

{-
-- exists a sub-context of fvs
data ExSubFVs ctx fvs where
    ExSubFVs :: MapCtx (MbLName ctx) fvs' -> SubCtx fvs' fvs ->
                ExSubFVs ctx fvs

-- add an FV to an ExSubFVs
exSubFVsCons :: ExSubFVs ctx fvs -> MbLName ctx a -> ExSubFVs ctx (CtxCons fvs a)
exSubFVsCons (ExSubFVs fvs subCtx) n =
    ExSubFVs (fvs :> n) (subCtxConsBoth subCtx)

-- don't add the FV, just extend the type
exSubFVsWeaken :: ExSubFVs ctx fvs -> ExSubFVs ctx (CtxCons fvs a)
exSubFVsWeaken (ExSubFVs fvs subCtx) =
    ExSubFVs fvs (subCtxConsR subCtx)

-- removing a name from a context of fvs
remMbLName :: MapCtx (MbLName ctx) fvs -> MbLName ctx a -> ExSubFVs ctx fvs
remMbLName EmptyMC _ = ExSubFVs EmptyMC id
remMbLName (fvs :> MbLName fv) (MbLName n) =
    case mbCmpName fv n of
      Just _ -> exSubFVsWeaken $ remMbLName fvs (MbLName n)
      Nothing -> exSubFVsCons (remMbLName fvs (MbLName n)) (MbLName fv)
-}

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

data IsLType a where IsLType :: IsLType (L a)
type LCtx ctx = MapCtx IsLType ctx

data MbLName ctx a where
    MbLName :: Mb ctx (Name (L a)) -> MbLName ctx (L a)

fvsToLCtx :: FVList ctx lctx -> LCtx lctx
fvsToLCtx = ctxMap mbLNameToProof where
    mbLNameToProof :: MbLName ctx a -> IsLType a
    mbLNameToProof (MbLName _) = IsLType

data DBTerm ctx a where
    DBWeaken :: SubCtx ctx1 ctx -> DBTerm ctx1 a -> DBTerm ctx a
    DBVar :: InCtx ctx (L a) -> DBTerm ctx a
    DBDVar :: Name (D a) -> DBTerm ctx a
    DBApp :: DBTerm ctx (a -> b) -> DBTerm ctx a -> DBTerm ctx b

dbSubst :: DBTerm ctx a -> MapCtx Name ctx -> DTerm a
dbSubst (DBWeaken f db) names = dbSubst db $ f names
dbSubst (DBVar inCtx) names = Var $ ctxLookup inCtx names
dbSubst (DBDVar dVar) _ = DVar dVar
dbSubst (DBApp db1 db2) names =
    App (dbSubst db1 names) (dbSubst db2 names)


-- applying a DBTerm to a context of names
dbAppMultiNames :: DBTerm fvs (AddArrows fvs a) -> FVList ctx fvs ->
                   DBTerm fvs a
dbAppMultiNames db args = dbAppMultiNamesH db args (ctxToInCtxs args)

dbAppMultiNamesH :: DBTerm fvs (AddArrows args a) ->
                    FVList ctx args -> MapCtx (InCtx fvs) args ->
                    DBTerm fvs a
dbAppMultiNamesH fun EmptyMC _ = fun
dbAppMultiNamesH fun (args :> MbLName _) (inCtxs :> inCtx) =
    DBApp (dbAppMultiNamesH fun args inCtxs) (DBVar inCtx)


ctxToInCtxs :: MapCtx f ctx -> MapCtx (InCtx ctx) ctx
ctxToInCtxs EmptyMC = EmptyMC
ctxToInCtxs (ctx :> _) = ctxMap InCtxStep (ctxToInCtxs ctx) :> InCtxBase

------------------------------------------------------------
-- DBTerms combined with their free variables
------------------------------------------------------------

data FVDBTerm ctx lctx a where
    FVDBTerm :: FVList ctx fvs -> DBTerm (fvs :++: lctx) a ->
                FVDBTerm ctx lctx a

fvDBSepLVars :: MapCtx f lctx -> FVDBTerm (ctx :++: lctx) CtxNil a ->
                FVDBTerm ctx lctx a
fvDBSepLVars lctx (FVDBTerm fvs db) =
  case fvDBSepLVarsH lctx Tag fvs of
    SepRet fvs' f -> FVDBTerm fvs' (DBWeaken f db)


data SepRet lctx ctx fvs where
  SepRet :: FVList ctx fvs' -> SubCtx fvs (fvs' :++: lctx) ->
            SepRet lctx ctx fvs

fvDBSepLVarsH :: MapCtx f lctx -> Tag ctx -> FVList (ctx :++: lctx) fvs ->
                 SepRet lctx ctx fvs
fvDBSepLVarsH _ _ EmptyMC = SepRet EmptyMC (\_ -> EmptyMC)
fvDBSepLVarsH lctx ctx (fvs :> fv@(MbLName n)) =
    case fvDBSepLVarsH lctx ctx fvs of
      SepRet m f ->
          case raiseAppName (ctxAppendL ctx lctx) n of
            Left idx -> SepRet m (\xs -> f xs :> ctxLookup (weakenInCtxL (ctxTag m) idx) xs)
            Right n  ->
                SepRet (m :> MbLName n)
                       (\xs -> case mapCtxSplit (ctxAppendL (ctxConsTag (ctxTag m) fv) lctx) xs of
                                 (fvs' :> fv', lctxs) -> f (ctxAppend fvs' lctxs) :> fv')

raiseAppName :: IsAppend ctx1 ctx2 ctx -> Mb ctx (Name a) ->
                Either (InCtx ctx2 a) (Mb ctx1 (Name a))
raiseAppName isApp n =
    case mbToplevel $(superComb [| mbNameBoundP |]) (separateMb isApp n) of
      [nuQQ| Left inCtx |] -> Left $ mbInCtx inCtx
      [nuQQ| Right n |] -> Right n


{-
lowerFVs :: FVList ctx fvs -> MapCtx (MbLName (CtxCons ctx a)) fvs
lowerFVs EmptyMC = EmptyMC
lowerFVs (fvs :> MbLName n) =
    lowerFVs fvs :>
    MbLName (combineMb $ mbToplevel $(superComb [| nu . const |]) n)

lowerMultiL :: MapCtx f ctx -> a -> Mb ctx a
lowerMultiL EmptyMC x = emptyMb x
lowerMultiL (ctx :> _) x = combineMb $ lowerMultiL ctx $ nu $ \_ -> x

mkFV :: MapCtx f ctx -> MbLName (CtxCons ctx (L a)) (L a)
mkFV ctx = MbLName $ combineMb $ lowerMultiL ctx (nu $ \n -> n)

mkFVs :: LCtx ctx -> LCtx ctx2 -> MapCtx (MbLName (ctx :++: ctx2)) ctx2
mkFVs ctx EmptyMC = EmptyMC
mkFVs ctx (ctx2 :> IsLType) =
    lowerFVs (mkFVs ctx ctx2) :> (mkFV $ ctxAppend ctx ctx2)

raiseFVs :: Tag fvs -> LCtx lctx ->
            MapCtx (MbLName (ctx :++: lctx)) (fvs :++: lctx) ->
            FVList ctx fvs
raiseFVs = undefined

fvDBSepLVars :: LCtx ctx -> LCtx lctx -> FVDBTerm (ctx :++: lctx) CtxNil a ->
                FVDBTerm ctx lctx a
fvDBSepLVars ctx lctx (FVDBTerm fvs db) =
    undefined
-}
{-
    helper1 lctx db $ fvUnion fvs $ mkFVs ctx lctx where
        helper1 :: LCtx lctx -> DBTerm fvs a ->
                   FVUnionRet (ctx :++: lctx) fvs lctx ->
                   FVDBTerm ctx lctx a
        helper1 lctx db (FVUnionRet fvs' sub1 sub2) =
            FVDBTerm (raiseFVs tag lctx fvs') (DBWeaken sub1 db)
-}

------------------------------------------------------------
-- lambda-lifting, woo hoo!
------------------------------------------------------------

-- this cannot ever happen (there is no ctor for InCtx CtxNil a)
inCtxNil :: InCtx CtxNil a -> b
inCtxNil _ = undefined

dInLCtx :: LCtx ctx -> InCtx ctx (D a) -> b
dInLCtx EmptyMC inCtx = inCtxNil inCtx
dInLCtx (lctx :> IsLType) (InCtxStep inCtx) = dInLCtx lctx inCtx


type LLBodyRet b ctx a = Cont (Decls b) (FVDBTerm ctx CtxNil a)

felleisenC :: ((a -> Decls b) -> Decls b) -> Cont (Decls b) a
felleisenC f = ContT (\k -> Identity (f (runIdentity . k)))

llBody :: LCtx ctx -> Mb ctx (DTerm a) -> LLBodyRet b ctx a
llBody ctx [nuQQ| Var v |] =
    return $ FVDBTerm (EmptyMC :> MbLName v) $ DBVar InCtxBase

llBody ctx [nuQQ| DVar d |] =
    case mbNameBoundP d of
      Right d -> return $ FVDBTerm EmptyMC $ DBDVar d
      Left inCtx -> dInLCtx ctx inCtx

llBody ctx [nuQQ| App t1 t2 |] = do
  FVDBTerm fvs1 db1 <- llBody ctx t1
  FVDBTerm fvs2 db2 <- llBody ctx t2
  FVUnionRet names sub1 sub2 <- return $ fvUnion fvs1 fvs2
  return $ FVDBTerm names $ DBApp (DBWeaken sub1 db1) (DBWeaken sub2 db2)

llBody ctx lam @ [nuQQ| Lam _ |] = do
  PeelRet lctx body <- return $ peelLambdas EmptyMC lam
  llret <- llBody (ctxAppend ctx lctx) body
  FVDBTerm fvs db <- return $ fvDBSepLVars lctx llret
  felleisenC $ \k ->
      DeclsCons (addLams (fvsToLCtx fvs) $ \names1 ->
                 addLams lctx $ \names2 ->
                 dbSubst db (ctxAppend names1 names2))
        $ nu $ \d -> k $ FVDBTerm fvs (dbAppMultiNames (DBDVar d) fvs)


-- the top-level lambda-lifting function
lambdaLift :: DTerm a -> Decls a
lambdaLift t =
    runCont (llBody EmptyMC (emptyMb t))
              (\(FVDBTerm fvs db) ->
                 let none = ctxMap (\(MbLName mbn) -> elimEmptyMb mbn) fvs
                 in DeclsBase (dbSubst db none))

------------------------------------------------------------
-- lambda-lifting insde bindings
------------------------------------------------------------

mbLambdaLift :: Mb ctx (DTerm a) -> Mb ctx (Decls a)
mbLambdaLift = mbToplevel $(superComb [| lambdaLift |])

lambdaLiftDecls :: Decls a -> Decls a
lambdaLiftDecls (DeclsBase t) = lambdaLift t
lambdaLiftDecls (DeclsCons t rest) =
    DeclsCons t $ mbToplevel $(superComb [| lambdaLiftDecls |]) rest

-- modules
data Module a where
    Functor :: Binding (L a) (Module b) -> (Module b)
    Module :: Decls a -> Module a

lambdaLiftModule :: Module a -> Module a
lambdaLiftModule (Module d) = Module $ lambdaLiftDecls d
lambdaLiftModule (Functor b) =
    Functor $ mbToplevel $(superComb [| lambdaLiftModule |]) b


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

