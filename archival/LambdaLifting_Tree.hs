{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables, TypeOperators, EmptyDataDecls, PatternGuards, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, ViewPatterns, UndecidableInstances, QuasiQuotes #-}

-------------------------------------------------------------------------
-- lambda lifting for the lambda calculus with top-level declarations
-------------------------------------------------------------------------

module LambdaLifting_Tree where

import Ctx
import HobbitLibTH
import qualified Data.Set as Set
import Control.Monad.Reader


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
  DeclsCons :: String -> DTerm a -> Binding a (Decls a) -> Decls a

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
mpretty [$nuQQ| Var b |] varnames n =
    mprettyName (mbNameBoundP [$nuQQ| b |]) varnames
mpretty [$nuQQ| DVar b |] varnames n =
    mprettyName (mbNameBoundP [$nuQQ| b |]) varnames
mpretty [$nuQQ| Lam b |] varnames n =
    let x = "x" ++ show n in
    "(\\" ++ x ++ "." ++ mpretty (combineMb [$nuQQ| b |]) (varnames :> (StringF x)) (n+1) ++ ")"
mpretty [$nuQQ| App b1 b2 |] varnames n =
    "(" ++ mpretty [$nuQQ| b1 |] varnames n
        ++ " " ++ mpretty [$nuQQ| b2 |] varnames n ++ ")"

mprettyName (Left pf) varnames = unStringF (ctxLookup pf varnames)
mprettyName (Right _) varnames = "##free var##"
        

-- pretty print decls
decls_pretty :: Decls a -> String
decls_pretty decls =
    "[ decls:\n" ++ (mdecls_pretty (emptyMb decls) emptyMC) ++ "]"

mdecls_pretty :: Mb ctx (Decls a) -> MapCtx StringF ctx -> String
mdecls_pretty [$nuQQ| DeclsBase t |] varnames =
    (mpretty [$nuQQ| t |] varnames 0) ++ "\n"
mdecls_pretty [$nuQQ| DeclsCons b_fname term rest |] varnames =
    let fname = mbString [$nuQQ| b_fname |] in
    fname ++ " = " ++ (mpretty [$nuQQ| term |] varnames 0) ++ "\n\n"
    ++ mdecls_pretty (combineMb [$nuQQ| rest |]) (varnames :> (StringF fname))


------------------------------------------------------------
-- "peeling" lambdas off of a term
------------------------------------------------------------

type family AddLams ctx b
type instance AddLams CtxNil b = b
type instance AddLams (CtxCons ctx (L a)) b = AddLams ctx (a -> b)

data PeelRet ctx a where
    PeelRet :: Ctx lam_ctx -> Mb (ctx :++: lam_ctx) (DTerm a) ->
               PeelRet ctx (AddLams lam_ctx a)

peelLambdas :: Ctx lam_ctx -> Mb (ctx :++: lam_ctx) (DTerm a) ->
               PeelRet ctx (AddLams lam_ctx a)
peelLambdas ctx [$nuQQ| Lam b |] =
    peelLambdas (CtxCons ctx Tag) (combineMb [$nuQQ| b |])
peelLambdas ctx [$nuQQ| b |] =
    PeelRet ctx [$nuQQ| b |]


------------------------------------------------------------
-- lambda-lifting "skeletons" and hole lists
------------------------------------------------------------

data LSkel ctx holes a where
    LSVar :: Mb ctx (Name (L a)) -> LSkel ctx CtxNil a
    LSDVar :: Mb ctx (Name (D a)) -> LSkel ctx CtxNil a
    LSHole :: LSkel ctx (List1 a) a
    LSApp :: LSkel ctx holes1 (a -> b) -> LSkel ctx holes2 a ->
             LSkel ctx (holes1, holes2) b

data HoleList holes where
    HoleListNil :: HoleList CtxNil
    HoleListSingle :: HoleList holes' -> MapCtx (MbNameLF ctx) fvs ->
                      Ctx lam_ctx -> LSkel (ctx :++: lam_ctx) holes' a ->
                      HoleList (List1 (AddLams fvs (AddLams lam_ctx a)))
    HoleListApp :: HoleList holes1 -> HoleList holes2 ->
                   HoleList (holes1, holes2)

data SomeLSkel ctx a where
    SomeLSkel :: HoleList holes -> LSkel ctx holes a -> SomeLSkel ctx a


------------------------------------------------------------
-- helpers for constructing skeletons
------------------------------------------------------------

someLSkelApply :: SomeLSkel ctx (a -> b) -> SomeLSkel ctx a -> SomeLSkel ctx b
someLSkelApply (SomeLSkel holes1 lskel1) (SomeLSkel holes2 lskel2) =
    SomeLSkel (HoleListApp holes1 holes2) (LSApp lskel1 lskel2)

type family LskelTypeApply holes fvs
type instance LskelTypeApply holes CtxNil = holes
type instance LskelTypeApply holes (CtxCons fvs a) =
    (LskelTypeApply holes fvs, CtxNil)

lskelApplyToNames :: SomeLSkel ctx (AddLams fvs a) ->
                     MapCtx (MbNameLF ctx) fvs ->
                     SomeLSkel ctx a
lskelApplyToNames someLSkel EmptyMC = someLSkel
lskelApplyToNames someLSkel (mc :> (MbNameLF n)) =
    someLSkelApply (lskelApplyToNames someLSkel mc)
                   (SomeLSkel HoleListNil (LSVar n))
                        

------------------------------------------------------------
-- free variables of skeletons
------------------------------------------------------------

data SomeName ctx where
    SomeName :: Mb ctx (Name (L a)) -> SomeName ctx

instance Eq (SomeName ctx) where
    (SomeName n1) == (SomeName n2) = depEqBool n1 n2

instance Ord (SomeName ctx) where
    compare (SomeName n1) (SomeName n2) = depCompareOrd n1 n2

lskelFreeVars :: LSkel ctx holes a -> Set.Set (SomeName ctx)
lskelFreeVars (LSVar n) = Set.singleton (SomeName n)
lskelFreeVars (LSDVar _) = Set.empty
lskelFreeVars LSHole = Set.empty
lskelFreeVars (LSApp lskel1 lskel2) =
    Set.union (lskelFreeVars lskel1) (lskelFreeVars lskel2)


------------------------------------------------------------
-- removing the last free variables from a set
------------------------------------------------------------

data LiftNameTag
instance ToplevelFun LiftNameTag (Mb ctx (Name a)) where
    type ToplevelRes LiftNameTag (Mb ctx (Name a)) = Maybe (Name a)
    topFun _ n = case mbNameBoundP n of
                   Left _ -> Nothing
                   Right n -> Just n

liftName :: Tag ctx1 -> Ctx ctx2 -> SomeName (ctx1 :++: ctx2) ->
            Maybe (SomeName ctx1)
liftName tag ctx2 (SomeName n) =
    case mbToplevel (Tag :: Tag LiftNameTag) (separateMb tag ctx2 n) of
                  [$nuQQ| Just n |] -> Just (SomeName [$nuQQ| n |])
                  [$nuQQ| Nothing |] -> Nothing

butlastFVs :: Ctx last_ctx -> Set.Set (SomeName (ctx :++: last_ctx)) ->
              Set.Set (SomeName ctx)
butlastFVs last_ctx set =
    Set.fold (\n -> \set ->
                    case liftName Tag last_ctx n of
                      Just n' -> Set.insert n' set
                      Nothing -> set) Set.empty set

someLSkelButlastFVs :: Ctx lam_ctx -> SomeLSkel (ctx :++: lam_ctx) a ->
                       NameCtx ctx
someLSkelButlastFVs lam_ctx (SomeLSkel _ lskel) =
    fvsToNameCtx $ butlastFVs lam_ctx $ lskelFreeVars lskel


------------------------------------------------------------
-- extracting the type info from a set of names
------------------------------------------------------------

data MbNameLF ctx a where
    MbNameLF :: (Mb ctx (Name (L a))) -> MbNameLF ctx (L a)

data NameCtx ctx where
    NameCtx :: MapCtx (MbNameLF ctx) fvs -> NameCtx ctx

nameCtxCons :: SomeName ctx -> NameCtx ctx -> NameCtx ctx
nameCtxCons (SomeName n) (NameCtx mapC) = NameCtx (mapC :> MbNameLF n)

fvsToNameCtx :: Set.Set (SomeName ctx) -> NameCtx ctx
fvsToNameCtx set = Set.fold nameCtxCons (NameCtx emptyMC) set

------------------------------------------------------------
-- lambda-lifting a term into a skeleton and a list of "holes"
------------------------------------------------------------

llBody :: Mb ctx (DTerm a) -> SomeLSkel ctx a
llBody [$nuQQ| Var v |] = SomeLSkel HoleListNil $ LSVar [$nuQQ| v |]
llBody [$nuQQ| DVar f |] = SomeLSkel HoleListNil $ LSDVar [$nuQQ| f |]
llBody [$nuQQ| App t1 t2 |] =
    someLSkelApply (llBody [$nuQQ| t1 |]) (llBody [$nuQQ| t2 |])
llBody [$nuQQ| Lam b |] =
    helper $ peelLambdas (CtxCons CtxNil Tag) (combineMb [$nuQQ| b |])
    where helper :: PeelRet ctx a -> SomeLSkel ctx a
          helper (PeelRet lam_ctx body) =
              let llBodyRet = llBody body in
              helper2 lam_ctx (someLSkelButlastFVs lam_ctx llBodyRet) llBodyRet
          helper2 :: Ctx lam_ctx -> NameCtx ctx ->
                     SomeLSkel (ctx :++: lam_ctx) a ->
                     SomeLSkel ctx (AddLams lam_ctx a)
          helper2 lam_ctx (NameCtx fvs) (SomeLSkel holes lskel) =
              lskelApplyToNames
                  (SomeLSkel (HoleListSingle holes fvs lam_ctx lskel) LSHole)
                  fvs


------------------------------------------------------------
-- Next we need the HoleM monad, which is a reader with
-- a specialized "combine" operation
------------------------------------------------------------

data HoleNames holes where
    HoleNamesNil :: HoleNames CtxNil
    HoleNamesSingle :: Name (D a) -> HoleNames (List1 a)
    HoleNamesApp :: HoleNames holes1 -> HoleNames holes2 ->
                    HoleNames (holes1, holes2)

splitHoleNames :: HoleNames (holes1, holes2) ->
                  (HoleNames holes1, HoleNames holes2)
splitHoleNames (HoleNamesApp holes1 holes2) = (holes1, holes2)


type HoleM holes a = Reader (HoleNames holes) a

nameLookup :: HoleM (List1 a) (Name (D a))
nameLookup = Reader $ helper
             where helper :: HoleNames (List1 a) -> Name (D a)
                   helper (HoleNamesSingle n) = n

combine :: HoleM holes1 a -> HoleM holes2 b ->
           HoleM (holes1, holes2) (a, b)
combine m1 m2 =
    Reader $ \holes ->
        let (holes1, holes2) = splitHoleNames holes in
        (runReader m1 holes1, runReader m2 holes2)


------------------------------------------------------------
-- Finally, lambda-lifting!!
------------------------------------------------------------

lskelToTerm :: MapCtx Name ctx -> LSkel ctx holes a -> HoleM holes (DTerm a)
lskelToTerm bvs (LSVar n) =
    return $ case mbNameBoundP n of
               Left inCtx -> Var (ctxLookup inCtx bvs)
               Right n -> Var n
lskelToTerm bvs (LSDVar n) =
    return $ case mbNameBoundP n of
               Left inCtx -> DVar (ctxLookup inCtx bvs)
               Right n -> DVar n
lskelToTerm bvs LSHole = nameLookup >>= return . DVar
lskelToTerm bvs (LSApp fun arg) =
    combine (lskelToTerm bvs fun) (lskelToTerm bvs arg) >>= \(fun, arg) ->
        return $ App fun arg


lambdaLift :: DTerm a -> Decls a
lambdaLift t = undefined
