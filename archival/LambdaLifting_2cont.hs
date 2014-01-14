{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses, RankNTypes, QuasiQuotes, TemplateHaskell, ViewPatterns, FlexibleContexts, UndecidableInstances #-}

-------------------------------------------------------------------------
-- lambda lifting for the lambda calculus with top-level declarations
-------------------------------------------------------------------------

module LambdaLifting2 where

import Ctx
import HobbitLibTH
import Data.List
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Cont
import Control.Monad.Identity

-- Term datatype
data Term a where
  TVar :: Name (L a) -> Term a
  TLam :: Binding (L b) (Term a) -> Term (b -> a)
  TApp :: Term (b -> a) -> Term b -> Term a

instance Show (Term a) where
    show = tpretty

-- helper functions to build terms without explicitly using nu or Var
lam :: (Term a -> Term b) -> Term (a -> b)
lam f = TLam $ nu (f . TVar)



-- pretty print terms
tpretty :: Term a -> String
tpretty t = pretty' (emptyMb t) emptyMC 0
  where pretty' :: Mb ctx (Term a) -> MapCtx StringF ctx -> Int -> String
        pretty' [nuQQ| TVar b |] varnames n =
            case mbNameBoundP b of
              Left pf  -> unStringF (ctxLookup pf varnames)
              Right _ -> "free"
        pretty' [nuQQ| TLam b |] varnames n =
            let x = "x" ++ show n in
            "(\\" ++ x ++ "." ++ pretty' (combineMb b) (varnames :> (StringF x)) (n+1) ++ ")"
        pretty' [nuQQ| TApp b1 b2 |] varnames n =
            "(" ++ pretty' b1 varnames n ++ " " ++ pretty' b2 varnames n ++ ")"


data L a
data D a

data IsLType a where IsLType :: IsLType (L a)
type LCtx ctx = MapCtx IsLType ctx

data MbLName ctx a where
    MbLName :: Mb ctx (Name (L a)) -> MbLName ctx (L a)


-- terms with top-level names
data DTerm a where
  Var :: Name (L a) -> DTerm a
  DVar :: Name (D a) -> DTerm a
  App :: DTerm (a -> b) -> DTerm a -> DTerm b

instance Show (DTerm a) where
    show = pretty

-- we use this type for a definiens instead of putting lambdas back on the
-- front
data Decl :: * -> * where
  DeclOne :: Binding (L a) (DTerm b) -> Decl (a -> b)
  DeclCons :: Binding (L a) (Decl b) -> Decl (a -> b)

-- top-level declarations with a "return value"
data Decls a where
  DeclsBase :: DTerm a -> Decls a
  DeclsCons :: Decl b -> Binding (D b) (Decls a) -> Decls a

instance Show (Decls a) where
    show = decls_pretty

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
mpretty [nuQQ| Var b |] varnames =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuQQ| DVar b |] varnames =
    mprettyName (mbNameBoundP b) varnames
mpretty [nuQQ| App b1 b2 |] varnames =
    "(" ++ mpretty b1 varnames
        ++ " " ++ mpretty b2 varnames ++ ")"

mprettyName (Left pf) varnames = unStringF (ctxLookup pf varnames)
mprettyName (Right n) varnames = "##free var: " ++ (show n) ++ "##"
        

-- pretty print decls
decls_pretty :: Decls a -> String
decls_pretty decls =
    "[ decls:\n" ++ (mdecls_pretty (emptyMb decls) emptyMC 0) ++ "]"

mdecls_pretty :: Mb ctx (Decls a) -> MapCtx StringF ctx -> Int -> String
mdecls_pretty [nuQQ| DeclsBase t |] varnames n =
    (mpretty t varnames) ++ "\n"
mdecls_pretty [nuQQ| DeclsCons decl rest |] varnames n =
    let fname = "F" ++ show n in
    fname ++ " = " ++ (mdecl_pretty decl varnames 0) ++ "\n"
    ++ mdecls_pretty (combineMb rest) (varnames :> (StringF fname)) (n+1)

mdecl_pretty :: Mb ctx (Decl a) -> MapCtx StringF ctx -> Int -> String
mdecl_pretty [nuQQ| DeclOne t|] varnames n =
  let vname = "x" ++ show n in
  "\\" ++ vname ++ "." ++ mpretty (combineMb t) (varnames :> StringF vname)
mdecl_pretty [nuQQ| DeclCons d|] varnames n =
  let vname = "x" ++ show n in
  "\\" ++ vname ++ "." ++ mdecl_pretty (combineMb d) (varnames :> StringF vname) (n+1)

------------------------------------------------------------
-- "peeling" lambdas off of a term
------------------------------------------------------------

type family AddArrows ctx b
type instance AddArrows CtxNil b = b
type instance AddArrows (CtxCons ctx (L a)) b = AddArrows ctx (a -> b)


data NonEmpty lctx where
  NonEmpty :: NonEmpty (CtxCons lctx a)

data PeelRet ctx a where
    PeelRet :: NonEmpty lctx -> LCtx lctx -> Mb (ctx :++: lctx) (Term a) ->
               PeelRet ctx (AddArrows lctx a)

peelLambdas :: Tag ctx ->
               Mb ctx (Binding (L b) (Term a)) ->
               PeelRet ctx (b -> a)
peelLambdas ctx b =
  peelLambdasH ctx NonEmpty (EmptyMC :> IsLType) (combineMb b)

peelLambdasH :: Tag ctx -> NonEmpty lctx -> LCtx lctx -> Mb (ctx :++: lctx) (Term a) ->
                PeelRet ctx (AddArrows lctx a)
peelLambdasH ctx _ lctx [nuQQ| TLam b |] =
    peelLambdasH ctx NonEmpty (lctx :> IsLType) (combineMb b)
peelLambdasH _ ne lctx t = PeelRet ne lctx t




addLams :: LCtx (CtxCons lctx (L b)) ->
           (MapCtx Name (CtxCons lctx (L b)) -> DTerm a) ->
           Decl (AddArrows (CtxCons lctx (L b)) a)
addLams (lctx :> IsLType) k =
  addLamsH lctx (\ns -> DeclOne $ nu $ \n -> k (ns :> n))

addLamsH :: LCtx lctx ->
            (MapCtx Name lctx -> Decl a) ->
            Decl (AddArrows lctx a)
addLamsH EmptyMC k = k emptyMC
addLamsH (lctx :> IsLType) k =
    addLamsH lctx (\names -> DeclCons $ nu $ \x -> k (names :> x))





------------------------------------------------------------
-- sub-contexts
------------------------------------------------------------

-- FIXME: use this type in place of functions
type SubCtx ctx' ctx = MapCtx Name ctx -> MapCtx Name ctx'


------------------------------------------------------------
-- association lists from names in contexts to names
------------------------------------------------------------

--data SomeName ctx where SomeName :: Mb ctx (Name a) -> SomeName ctx

data NamePair ctx where NamePair :: Mb ctx (Name a) -> Name a -> NamePair ctx
type NameAList ctx = [NamePair ctx]

fvlookup :: NameAList ctx -> Mb ctx (Name a) -> Maybe (Name a)
fvlookup [] n = Nothing
fvlookup (NamePair mbn n : l') mbn' | Just Refl <- mbCmpName mbn mbn' = Just n
fvlookup (_ : l') mbn = fvlookup l' mbn

------------------------------------------------------------
-- lambda-lifting, woo hoo!
------------------------------------------------------------

newtype MbName ctx a = MbName (Mb ctx (Name a))

{-
data FVDeclPair ctx b where
    FVDeclPair :: MapCtx (MbName ctx) fvs -> Decl (AddArrows fvs b) ->
                  FVDeclPair ctx b

type FVM ctx b =
    StateT (NameAList ctx) (Cont (FVDeclPair ctx b))

type LLBodyRet b ctx a = Cont (Decls b) (FVM ctx b (DTerm a))
-}

{-
class Monad m => CMonad r m where
    felleisenC :: ((a -> r) -> r) -> m a

instance CMonad r (ContT r Identity) where
    felleisenC f = ContT (\k -> Identity (f (runIdentity . k)))

instance CMonad r m => CMonad r (StateT s m) where
    felleisenC f = StateT (\s -> felleisenC $ \k -> f (\x -> k (x, s)))
-}

{-
class Monad m => BindM n m where
    nuM :: (Name n -> m a) -> m a

instance Monad m => BindM (L n) (ContT (Decls b) m) where
    nuM f = contC $ \k -> DeclsCons $ nu $ \n -> runContT (f n) k
-}

{-
contC :: ((a -> r) -> r) -> Cont r a
contC f = ContT $ \k -> Identity (f (runIdentity . k))

stateContC :: (s -> ((a,s) -> r) -> r) -> StateT s (Cont r) a
stateContC f = StateT $ \s -> contC $ f s

llBody :: LCtx ctx -> Mb ctx (Term a) -> LLBodyRet b ctx a
llBody ctx [nuQQ| TApp t1 t2 |] =
    do m1 <- llBody ctx t1
       m2 <- llBody ctx t2
       return $
         do dt1 <- m1
            dt2 <- m2
            return $ App dt1 dt2

llBody ctx [nuQQ| TVar v |] =
    return $
      do fvlist <- get
         case fvlookup fvlist v of
           Just n -> return $ Var n
           Nothing ->
               stateContC $ \s -> \k ->
                   FVDeclPair () DeclCons $ nu $ \n ->
                       k (undefined, NamePair v n : s)
-}


FIXME: this doesn't seem to work!!


class Monad m => BindMonad r m where
    nuM :: ((Name n -> r) -> r) -> (Name n -> m a) -> m a

instance Monad m => BindMonad n r (ContT r Identity) where
    nuM bind f = ContT $ \k -> 


type FVM b1 b2 fvs ctx =
    ContT (Decl (AddArrows fvs b2)) (StateT (NameAList ctx) (Cont (Decls b1)))

data LLRet b1 b2 ctx a where
    LLRet :: MapCtx (MbName ctx) fvs ->
             FVM b1 b2 fvs ctx (DTerm a) -> LLRet b1 b2 ctx a
