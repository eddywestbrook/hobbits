{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses, QuasiQuotes, TemplateHaskell, ViewPatterns #-}

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


------------------------------------------------------------
-- misc helper operations
------------------------------------------------------------

data IsLType a where IsLType :: IsLType (L a)
type LCtx ctx = MapCtx IsLType ctx

data MbLName ctx a where
    MbLName :: (Mb ctx (Name (L a))) -> MbLName ctx (L a)

instance Eq (SomeLName ctx) where
    (SomeLName n1) == (SomeLName n2) =
        case mbCmpName n1 n2 of
          Just _ -> True
          Nothing -> False

instance Show (SomeLName ctx) where
    show (SomeLName n) = show n



mbMbNameBoundP :: Mb ctx1 (Mb ctx2 (Name a)) ->
                  Mb ctx1 (Either (InCtx ctx2 a) (Name a))
mbMbNameBoundP = mbToplevel $(superComb [| mbNameBoundP |])

-- testing if a name is the last one bound
cmpLastName :: Mb (CtxCons ctx b) (Name a) ->
                Maybe (Mb ctx (Name a))
cmpLastName n =
    case mbMbNameBoundP
           (separateMb
            (IsAppendStep IsAppendBase) n) of
      [nuQQ| Left _ |] -> Nothing
      [nuQQ| Right n |] -> Just n

-- adding a binding inside another
mbLower :: Mb ctx a -> Mb (CtxCons ctx b) a
mbLower = combineMb . mbToplevel $(superComb [| nu . const |])

lowerMulti :: Ctx ctx -> a -> Mb ctx a
lowerMulti EmptyMC a = emptyMb a
lowerMulti (ctx :> Tag) a = combineMb $ lowerMulti ctx (nu (\_ -> a))


------------------------------------------------------------
-- getting the free variables of a term
------------------------------------------------------------

-- some name of type (L a) with a hidden
data SomeLName ctx where
    SomeLName :: Mb ctx (Name (L a)) -> SomeLName ctx

-- free names with their types
data FVCtx ctx where
    FVCtx :: MapCtx (MbLName ctx) fvs -> FVCtx ctx

-- adding to a FVCtx
nameCtxCons :: SomeLName ctx -> FVCtx ctx -> FVCtx ctx
nameCtxCons (SomeLName n) (FVCtx mapC) = FVCtx (mapC :> MbLName n)

-- converting a list of SomeLNames into a FVCtx
fvsToFVCtx :: [SomeLName ctx] -> FVCtx ctx
fvsToFVCtx l = foldr nameCtxCons (FVCtx emptyMC) l

-- lift a list of SomeLNames out of a binding
liftSomeNames :: [SomeLName (CtxCons ctx b)] -> [SomeLName ctx]
liftSomeNames [] = []
liftSomeNames (SomeLName n : ns) =
    case cmpLastName n of
      Just n' -> SomeLName n' : liftSomeNames ns
      Nothing -> liftSomeNames ns

-- getting the free vars of a term in a context
freeVarsList :: Mb ctx (DTerm a) -> [SomeLName ctx]
freeVarsList [nuQQ| Var n |] = [SomeLName n]
freeVarsList [nuQQ| DVar _ |] = []
freeVarsList [nuQQ| App t1 t2 |] =
    union (freeVarsList t1) (freeVarsList t2)
freeVarsList [nuQQ| Lam b |] =
    liftSomeNames $ freeVarsList (combineMb b)

-- putting it all together
freeVars :: Mb ctx (DTerm a) -> FVCtx ctx
freeVars = fvsToFVCtx . freeVarsList

-- create a name mapping from names in empty multi-bindings
nilCtxMapApp :: FVCtx CtxNil -> [NameMap CtxNil] -> [NameMap CtxNil]
nilCtxMapApp (FVCtx EmptyMC) nmap = nmap
nilCtxMapApp (FVCtx (fvs :> MbLName mbN)) nmap =
    NameMap mbN (elimEmptyMb mbN) : nilCtxMapApp (FVCtx fvs) nmap

------------------------------------------------------------
-- MTerms = terms that require mapping their names to become DTerms
------------------------------------------------------------

-- a mapping from a name-in-context to a name
data NameMap ctx where
    NameMap :: (Mb ctx (Name a)) -> Name a -> NameMap ctx

mapName1 :: Maybe (a :=: b) -> Name a -> Maybe (Name b)
mapName1 Nothing _ = Nothing
mapName1 (Just Refl) n = Just n

mapName :: [NameMap ctx] -> Mb ctx (Name a) -> Maybe (Name a)
mapName [] n = Nothing
mapName (NameMap bound free : rest) n =
    case mapName1 (mbCmpName bound n) free of
      Nothing -> mapName rest n
      Just ret -> Just ret

nameMapLowerR :: NameMap ctx -> NameMap (CtxCons ctx b)
nameMapLowerR (NameMap mbN n) = NameMap (mbLower mbN) n

------------------------------------------------------------
-- binding monads
------------------------------------------------------------

class MonadBind m where
    nuM :: (Name a -> m ctx b) -> m ctx (Binding a b)
    strengthenM :: m (CtxCons ctx a) b -> m ctx b
    nuM' :: (Name a -> m (CtxCons ctx a) b) -> m ctx (Binding a b)
    nuM' f = nuM (strengthenM . f)

-- a trivial instance
newtype Proj2 ctx a = Proj2 { runProj2 :: a }
instance MonadBind Proj2 where
    nuM f = Proj2 $ nu $ runProj2 . f
    strengthenM (Proj2 m) = Proj2 m

-- our binding monad
newtype BindM ctx a = BindM { runBindM :: [NameMap ctx] -> a }

instance Monad (BindM ctx) where
    return x = BindM $ return x
    m >>= f = BindM $ (runBindM m) >>= \x -> runBindM (f x)

instance MonadReader [NameMap ctx] (BindM ctx) where
    ask = BindM $ \r -> r
    local f m = BindM $ \r -> runBindM m (f r)

instance MonadBind BindM where
    nuM m = BindM $ \nmap ->
        nu $ \n -> runBindM (m n) nmap
    strengthenM m = BindM $ \nmap -> runBindM m (map nameMapLowerR nmap)

-- perform a computation with an extended name map
withExtMap :: Mb ctx (Name a) -> Name a -> BindM ctx b -> BindM ctx b
withExtMap mbN n m = local (\nmap -> NameMap mbN n : nmap) m


------------------------------------------------------------
-- MTerms = terms that require mapping their names to become DTerms
------------------------------------------------------------

-- the MTerm type
type MTerm ctx a = BindM ctx (DTerm a)

-- perform the mapping
mapMTerm :: MTerm ctx a -> DTerm a
mapMTerm mt = runBindM mt []
-- mapMTerm :: MTerm ctx a -> [NameMap ctx] -> DTerm a
-- mapMTerm = runReader

-- a Var that needs lifting
mVar :: Mb ctx (Name (L a)) -> MTerm ctx a
mVar v =
    do nmap <- ask
       return $ case mapName nmap v of
                  Just n -> Var n
                  Nothing -> error $ "unexpected lambda-bound var: " ++ (show v)

-- a DVar that needs lifting
mDVar :: Mb ctx (Name (D a)) -> MTerm ctx a
mDVar d =
    case mbNameBoundP d of
      Left _ -> error "unexpected bound definition var!"
      Right n -> return $ DVar n

-- an App that needs lifting
mApp :: MTerm ctx (a -> b) -> MTerm ctx a -> MTerm ctx b
mApp mt1 mt2 =
    mt1 >>= \t1 ->
    mt2 >>= \t2 ->
    return (App t1 t2)

-- apply to zero or more names
mApplyToNames :: MTerm ctx (AddArrows lam_ctx a) ->
               MapCtx (MbLName ctx) lam_ctx -> MTerm ctx a
mApplyToNames mt EmptyMC = mt
mApplyToNames mt (args :> MbLName n) = mApp (mApplyToNames mt args) (mVar n)

-- lambda abstract over a bound name
mLam :: Mb ctx (Name (L a)) -> MTerm ctx b -> MTerm ctx (a -> b)
mLam mbN mt =
    nuM (\n -> withExtMap mbN n mt) >>= (return . Lam)

-- form multiple lambda abstractions from a free variable list
mLamMulti :: MapCtx (MbLName ctx) fvs -> MTerm ctx a -> MTerm ctx (AddArrows fvs a)
mLamMulti EmptyMC mt = mt
mLamMulti (fvs :> MbLName mbN) mt =
    mLamMulti fvs (mLam mbN mt)

-- make a bound name for the last name in the context
mkBoundName :: Ctx ctx -> Mb (CtxCons ctx a) (Name a)
mkBoundName ctx = combineMb (lowerMulti ctx (nu (\n -> n)))

-- add a lambda around an MTerm for the last variable in the binding
-- context, removing that variable from the context
mLam' :: Ctx ctx -> MTerm (CtxCons ctx (L b)) a -> MTerm ctx (b -> a)
mLam' ctx mt =
    nuM' (\n -> withExtMap (mkBoundName ctx) n mt) >>=
    (return . Lam)

ctxAppendLCtx :: Ctx ctx -> LCtx lctx -> Ctx (ctx :++: lctx)
ctxAppendLCtx ctx lctx = ctxAppend ctx (ctxMap (\_ -> Tag) lctx)

-- form multiple lambda abstractions from an LCtx
-- while removing inner bindings from the ctx
mLamMulti' :: Ctx ctx -> LCtx lam_ctx -> MTerm (ctx :++: lam_ctx) a ->
            MTerm ctx (AddArrows lam_ctx a)
mLamMulti' _ EmptyMC mt = mt
mLamMulti' ctx (lam_ctx :> IsLType) mt =
    mLamMulti' ctx lam_ctx (mLam' (ctxAppendLCtx ctx lam_ctx) mt)

mTermWithFVs :: FVCtx CtxNil -> MTerm CtxNil a -> MTerm CtxNil a
mTermWithFVs fvs = local (nilCtxMapApp fvs)

------------------------------------------------------------
-- lambda-lifting, woo hoo!
------------------------------------------------------------

type LLBodyRet b ctx a = Cont (Decls b) (MTerm ctx a)

felleisenC :: ((MTerm ctx a -> Decls b) -> Decls b) -> LLBodyRet b ctx a
felleisenC f = ContT (\ k -> Identity (f (runIdentity . k)))

llBody :: Ctx ctx -> Mb ctx (DTerm a) -> LLBodyRet b ctx a
llBody _ [nuQQ| Var v |] = return $ mVar v
llBody _ [nuQQ| DVar d |] = return $ mDVar d
llBody ctx [nuQQ| App t1 t2 |] =
    llBody ctx t1 >>= \mt1 ->
    llBody ctx t2 >>= \mt2 ->
    return $ mApp mt1 mt2
llBody ctx lam @ [nuQQ| Lam _ |] =
    llLambda ctx (peelLambdas EmptyMC lam) (freeVars lam)

llLambda :: Ctx ctx -> PeelRet ctx a -> FVCtx ctx -> LLBodyRet b ctx a
llLambda ctx (PeelRet lam_ctx body) (FVCtx fvs) =
    llBody (ctxAppendLCtx ctx lam_ctx) body >>= \b ->
    felleisenC $ \k ->
        DeclsCons (mapMTerm (mLamMulti fvs (mLamMulti' ctx lam_ctx b)))
                  (nu $ \d -> k $ mApplyToNames (return $ DVar d) fvs)

-- the top-level lambda-lifting function
lambdaLift :: DTerm a -> Decls a
lambdaLift t =
    runCont (llBody EmptyMC (emptyMb t))
            (\mt -> DeclsBase $ mapMTerm $
                    mTermWithFVs (freeVars (emptyMb t)) mt)

------------------------------------------------------------
-- lambda-lifting insde bindings
------------------------------------------------------------

-- lambda-lifting inside multi-bindings
mbLambdaLift :: Mb ctx (DTerm a) -> Mb ctx (Decls a)
mbLambdaLift = mbToplevel $(superComb [| lambdaLift |])

-- lambda-lifting for decls
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
res6 = mbLambdaLift ex6
