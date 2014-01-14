{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses, QuasiQuotes #-}

-------------------------------------------------------------------------
-- lambda lifting for the lambda calculus with top-level declarations
-------------------------------------------------------------------------

module LambdaLifting where

import Ctx
import HobbitLibTH
import qualified Data.Set as Set
import Control.Monad.Reader
import Control.Monad.Cont


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
  DeclsCons :: String -> DTerm b -> Binding (D b) (Decls a) -> Decls a

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
-- contexts that are guaranteed to have only L variables
------------------------------------------------------------

{-
data LCtx ctx where
    LCtxNil :: LCtx CtxNil
    LCtxCons :: LCtx ctx -> Tag (L a) -> LCtx (CtxCons ctx (L a))

lCtxToCtx :: LCtx ctx -> Ctx ctx
lCtxToCtx LCtxNil = CtxNil
lCtxToCtx (LCtxCons lctx tag) = CtxCons (lCtxToCtx lctx) tag

mapCtxToLCtx :: MapCtx (MbLName ctx) fvs -> LCtx fvs
mapCtxToLCtx EmptyMC = LCtxNil
mapCtxToLCtx (mc :> MbLName _) = LCtxCons (mapCtxToLCtx mc) Tag
-}

data IsLType a where IsLType :: IsLType (L a)
type LCtx ctx = MapCtx IsLType ctx

lCtxToCtx :: LCtx ctx -> Ctx ctx
lCtxToCtx = mapCtxToCtx

mapCtxToLCtx :: MapCtx (MbLName ctx) fvs -> LCtx fvs
mapCtxToLCtx = ctxMap (\(MbLName _) -> IsLType)



------------------------------------------------------------
-- "peeling" lambdas off of a term and adding them back again
------------------------------------------------------------

type family AddLams ctx b
type instance AddLams CtxNil b = b
type instance AddLams (CtxCons ctx (L a)) b = AddLams ctx (a -> b)

data PeelRet ctx a where
    PeelRet :: LCtx lam_ctx -> Mb (ctx :++: lam_ctx) (DTerm a) ->
               PeelRet ctx (AddLams lam_ctx a)

peelLambdas :: LCtx lam_ctx -> Mb (ctx :++: lam_ctx) (DTerm a) ->
               PeelRet ctx (AddLams lam_ctx a)
peelLambdas lctx [$nuQQ| Lam b |] =
    peelLambdas (lctx :> IsLType) (combineMb [$nuQQ| b |])
peelLambdas lctx [$nuQQ| b |] =
    PeelRet lctx [$nuQQ| b |]


addLams :: LCtx lam_ctx -> (MapCtx LName lam_ctx -> DTerm a) ->
           DTerm (AddLams lam_ctx a)
addLams EmptyMC k = k emptyMC
addLams (lam_ctx :> IsLType) k =
    addLams lam_ctx (\names -> Lam $ nu $ \x -> k (names :> LName x))


------------------------------------------------------------
-- lambda-lifting "skeletons" and hole lists
------------------------------------------------------------

data LSkel ctx holes a where
    LSVar :: Mb ctx (Name (L a)) -> LSkel ctx holes a
    LSDVar :: Mb ctx (Name (D a)) -> LSkel ctx holes a
    LSHole :: InCtx holes a -> LSkel ctx holes a
    LSApp :: LSkel ctx holes (a -> b) -> LSkel ctx holes a ->
             LSkel ctx holes b


data MbLName ctx a where
    MbLName :: (Mb ctx (Name (L a))) -> MbLName ctx (L a)

unMbLName :: MbLName CtxNil a -> Name a
unMbLName (MbLName n) = elimEmptyMb n


data HoleList holes where
    HoleListNil :: HoleList CtxNil
    HoleListCons :: HoleList holes -> MapCtx (MbLName ctx) fvs ->
                    LCtx lam_ctx -> LSkel (ctx :++: lam_ctx) holes a ->
                    HoleList (CtxCons holes (AddLams fvs (AddLams lam_ctx a)))

holeListLen :: HoleList holes -> Int
holeListLen HoleListNil = 0
holeListLen (HoleListCons holes _ _ _) = 1 + holeListLen holes

-- an LSkel and a HoleList with at least as many holes as holes
data MoreHoles ctx holes a where
    MoreHoles :: IsAppend holes1 holes2 holes -> HoleList holes ->
                 LSkel ctx holes a -> MoreHoles ctx holes1 a


-- FIXME: write fvsMunge and come up with a better name
newtype MaybeLName a = MaybeLName (Maybe (LName a))
data NamePair where
    NamePair :: Name a -> Name a -> NamePair

fvsMunge :: Ctx ctx -> LCtx lam_ctx -> MapCtx (MbLName ctx) fvs ->
            MapCtx Name fvs -> MapCtx Name lam_ctx ->
            ([NamePair], MapCtx MaybeLName (ctx :++: lam_ctx))
fvsMunge = undefined

------------------------------------------------------------
-- sets of free variables and simple ops on them
------------------------------------------------------------

data NameCtx ctx where
    NameCtx :: MapCtx (MbLName ctx) fvs -> NameCtx ctx

nameCtxCons :: SomeName ctx -> NameCtx ctx -> NameCtx ctx
nameCtxCons (SomeName n) (NameCtx mapC) = NameCtx (mapC :> MbLName n)

fvsToNameCtx :: Set.Set (SomeName ctx) -> NameCtx ctx
fvsToNameCtx set = Set.fold nameCtxCons (NameCtx emptyMC) set


------------------------------------------------------------
-- helpers for operating on skeletons
------------------------------------------------------------

weakenLSkelR :: LSkel ctx holes1 a -> IsAppend holes1 holes2 holes ->
                LSkel ctx holes a
weakenLSkelR (LSVar n) holes2 = LSVar n
weakenLSkelR (LSDVar n) holes2 = LSDVar n
weakenLSkelR (LSHole inCtx) holes2 = LSHole (weakenInCtxR inCtx holes2)
weakenLSkelR (LSApp t1 t2) holes2 =
    LSApp (weakenLSkelR t1 holes2) (weakenLSkelR t2 holes2)


--someLSkelApply :: SomeHoles ctx (a -> b) -> SomeHoles ctx a -> SomeHoles ctx b
--someLSkelApply (SomeHoles ctx1 holes1 lskel1) (SomeHoles ctx2 holes2 lskel2) =
--    SomeHoles (ctxAppend ctx1 ctx2)
--              (HoleListApp holes1 holes2) (LSApp lskel1 lskel2)
--someLSkelApply = undefined

--type family LskelTypeApply holes fvs
--type instance LskelTypeApply holes CtxNil = holes
--type instance LskelTypeApply holes (CtxCons fvs a) =
--    (LskelTypeApply holes fvs, CtxNil)


lskelApplyToNames :: LSkel ctx holes (AddLams fvs a) ->
                     MapCtx (MbLName ctx) fvs ->
                     LSkel ctx holes a
lskelApplyToNames lskel EmptyMC = lskel
lskelApplyToNames lskel (mc :> (MbLName n)) =
    LSApp (lskelApplyToNames lskel mc) (LSVar n)


-- apply a MoreHoles to a MoreHoles
{-
moreHolesApply :: (forall holes . HoleList holes -> MoreHoles ctx holes (a -> b)) ->
                  (forall holes . HoleList holes -> MoreHoles ctx holes a) ->
                  HoleList holes -> MoreHoles ctx holes b
moreHolesApply f1 f2 holes = funHelper (f1 holes) f2 where
    funHelper :: MoreHoles ctx holes (a -> b) ->
                 (forall holes . HoleList holes -> MoreHoles ctx holes a) ->
                 MoreHoles ctx holes b
    funHelper (MoreHoles isApp1 holes1 lskel1) f2 =
        argHelper isApp1 lskel1 (f2 holes1)
    argHelper :: IsAppend holes holes1 holes' -> LSkel ctx holes' (a -> b) ->
                 MoreHoles ctx holes' a -> MoreHoles ctx holes b
    argHelper isApp1 lskel1 (MoreHoles isApp2 holes2 lskel2) =
          MoreHoles (isAppendTrans isApp1 isApp2) holes2 $
                    LSApp (weakenLSkelR lskel1 isApp2) lskel2
-}

lskelApplyMH :: IsAppend holes1 h holes2 ->
                LSkel ctx holes2 (a -> b) -> MoreHoles ctx holes2 a ->
                MoreHoles ctx holes1 b
lskelApplyMH isApp1 lskel (MoreHoles isApp2 holes lskelArg) =
    MoreHoles (isAppendTrans isApp1 isApp2) holes
    $ LSApp (weakenLSkelR lskel isApp2) lskelArg

-- return a MoreHole whose LSkel is LSHole
moreHolesMkHole :: LCtx lam_ctx -> NameCtx ctx ->
                   MoreHoles (ctx :++: lam_ctx) holes a ->
                   MoreHoles ctx holes (AddLams lam_ctx a)
moreHolesMkHole lam_ctx (NameCtx fvs) (MoreHoles isApp holes lskel) =
    MoreHoles (IsAppendStep isApp)
              (HoleListCons holes fvs lam_ctx lskel)
              (lskelApplyToNames (LSHole InCtxBase) fvs)


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
lskelFreeVars (LSHole _) = Set.empty
lskelFreeVars (LSApp lskel1 lskel2) =
    Set.union (lskelFreeVars lskel1) (lskelFreeVars lskel2)


------------------------------------------------------------
-- removing the last free variables from a set
------------------------------------------------------------

data MbMbNameBoundP
instance ToplevelFun MbMbNameBoundP (Mb ctx (Name a)) where
    type ToplevelRes MbMbNameBoundP (Mb ctx (Name a)) =
        Either (InCtx ctx a) (Name a)
    topFun _ n = mbNameBoundP n

mbMbNameBoundP :: IsAppend ctx1 ctx2 ctx -> Mb ctx (Name a) ->
                  Mb ctx1 (Either (InCtx ctx2 a) (Name a))
mbMbNameBoundP isApp n =
    mbToplevel (Tag :: Tag MbMbNameBoundP) (separateMb isApp n)

liftName :: IsAppend ctx1 ctx2 ctx -> Mb ctx (Name a) ->
            Maybe (Mb ctx1 (Name a))
liftName isApp n =
    case mbMbNameBoundP isApp n of
      [$nuQQ| Left _ |] -> Nothing
      [$nuQQ| Right n |] -> Just [$nuQQ| n |]

liftSomeName :: IsAppend ctx1 ctx2 ctx -> SomeName ctx ->
                Maybe (SomeName ctx1)
liftSomeName isApp (SomeName n) =
    case liftName isApp n of
      Just n -> Just (SomeName n)
      Nothing -> Nothing

butlastFVs :: Ctx last_ctx -> Set.Set (SomeName (ctx :++: last_ctx)) ->
              Set.Set (SomeName ctx)
butlastFVs last_ctx set =
    Set.fold (\n -> \set ->
                    case liftSomeName (ctxAppendL Tag last_ctx) n of
                      Just n' -> Set.insert n' set
                      Nothing -> set) Set.empty set

someLSkelButlastFVs :: Ctx lam_ctx -> MoreHoles (ctx :++: lam_ctx) holes a ->
                       NameCtx ctx
someLSkelButlastFVs lam_ctx (MoreHoles _ _ lskel) =
    fvsToNameCtx $ butlastFVs lam_ctx $ lskelFreeVars lskel


------------------------------------------------------------
-- lambda-lifting a term into a skeleton and a list of "holes"
------------------------------------------------------------

llBody :: Mb ctx (DTerm a) -> HoleList holes -> MoreHoles ctx holes a
llBody [$nuQQ| Var v |] holes = MoreHoles IsAppendBase holes $ LSVar [$nuQQ| v |]
llBody [$nuQQ| DVar f |] holes = MoreHoles IsAppendBase holes $ LSDVar [$nuQQ| f |]
llBody [$nuQQ| App t1 t2 |] holes =
    helper (llBody [$nuQQ| t1 |] holes) [$nuQQ| t2 |] where
        helper :: MoreHoles ctx holes (a -> b) -> Mb ctx (DTerm a) ->
                  MoreHoles ctx holes b
        helper (MoreHoles isApp holes lskel) t2 =
            lskelApplyMH isApp lskel (llBody t2 holes)
llBody [$nuQQ| Lam b |] holes =
    llLambda (peelLambdas (EmptyMC :> IsLType) (combineMb [$nuQQ| b |])) holes

llLambda :: PeelRet ctx a -> HoleList holes -> MoreHoles ctx holes a
llLambda (PeelRet lam_ctx body) holes =
    let llBodyRet = llBody body holes in
    moreHolesMkHole lam_ctx
                    (someLSkelButlastFVs (lCtxToCtx lam_ctx) llBodyRet)
                    llBodyRet


------------------------------------------------------------
-- converting LSkels back to Decls
------------------------------------------------------------

newtype DName a = DName (Name (D a))

data LName a where
    LName :: Name (L a) -> LName (L a)

unLName :: LName a -> Name a
unLName (LName n) = n

-- helper for bvLookup
bvLookupH :: Maybe (Mb ctx (Name (L bv))
                    :=: Mb ctx (Name (L a))) ->
             Name (L bv) -> Maybe (Name (L a))
bvLookupH Nothing n = Nothing
bvLookupH (Just TEq) n = Just n

-- try to look up a bound name in a MapCtx of bound names, returning the
-- corresponding free name if the lookup succeeds
bvLookup :: MapCtx (MbLName ctx) fvs -> MapCtx Name fvs ->
            Mb ctx (Name (L a)) -> Name (L a)
bvLookup EmptyMC EmptyMC _ = error "unexpected variable!"
bvLookup (bvs :> MbLName bv) (new_bvs :> new_bv) n =
    case bvLookupH (depEq bv n) new_bv of
      Nothing -> bvLookup bvs new_bvs n
      Just new_n -> new_n

-- convert an LSkel into a DTerm
lskelToTerm :: Tag ctx -> (MapCtx (MbLName ctx) fvs, MapCtx Name fvs,
                           MapCtx LName lam_ctx) ->
               MapCtx DName holes -> LSkel (ctx :++: lam_ctx) holes a ->
               DTerm a
lskelToTerm tag (bvs, new_bvs, lam_names) hnames (LSVar n) =
    case mbMbNameBoundP (ctxAppendL tag lam_names) n of
      [$nuQQ| Left inCtx |] ->
          Var $ unLName $ ctxLookup (mbInCtx [$nuQQ| inCtx |]) lam_names
      [$nuQQ| Right n |] ->
          Var $ bvLookup bvs new_bvs [$nuQQ| n |]
lskelToTerm _ bvs hnames (LSDVar n) =
    case mbNameBoundP n of
      Left inCtx -> error "unexpected bound definition var!"
      Right n -> DVar n
lskelToTerm _ bvs hnames (LSHole inCtx) =
    case ctxLookup inCtx hnames of
      DName n -> DVar n
lskelToTerm tag bvs hnames (LSApp fun arg) =
    App (lskelToTerm tag bvs hnames fun) (lskelToTerm tag bvs hnames arg)

-- convert one element of a HoleList to a DTerm
holeToTerm :: Tag ctx -> MapCtx DName holes -> MapCtx (MbLName ctx) fvs ->
              LCtx lam_ctx -> LSkel (ctx :++: lam_ctx) holes a ->
              DTerm (AddLams fvs (AddLams lam_ctx a))
holeToTerm tag holeNames fvs lam_ctx lskel =
    addLams (mapCtxToLCtx fvs) $ \new_fvs ->
        addLams lam_ctx $ \names ->
            lskelToTerm tag (fvs, ctxMap unLName new_fvs, names) holeNames lskel


-- CPS-converted helper function
holesToDecls :: HoleList holes ->
                (MapCtx DName holes -> Decls a) -> Decls a
holesToDecls HoleListNil k = k emptyMC
holesToDecls (HoleListCons holes' fvs lam_ctx lskel) k =
    holesToDecls holes' $ \holeNames ->
        DeclsCons ("F" ++ (show (holeListLen holes')))
                  (holeToTerm Tag holeNames fvs lam_ctx lskel)
                  (nu $ \fname -> k (holeNames :> DName fname))

-- convert a HoleList into a Decl
holesLSkelToDecls :: HoleList holes -> LSkel CtxNil holes a ->
                     NameCtx CtxNil -> Decls a
holesLSkelToDecls holes lskel (NameCtx fvs) =
    holesToDecls holes $ \holeNames ->
        DeclsBase
        $ lskelToTerm (Tag :: Tag CtxNil)
              (fvs, ctxMap unMbLName fvs, emptyMC)
              holeNames lskel

------------------------------------------------------------
-- Finally, lambda-lifting!!
------------------------------------------------------------

lambdaLift :: DTerm a -> Decls a
lambdaLift t = helper $ llBody (emptyMb t) HoleListNil where
    helper :: MoreHoles CtxNil CtxNil a -> Decls a
    helper (MoreHoles _ holes lskel) =
        holesLSkelToDecls holes lskel $ fvsToNameCtx $ lskelFreeVars lskel

data LLToplevelTag
{-
instance ToplevelFun LLToplevelTag (DTerm a) where
    type ToplevelRes MbMbNameBoundP (DTerm a) = Decls a
    topFun _ n = lambdaLift n
-}
instance ToplevelFun LLToplevelTag (Decls a) where
    type ToplevelRes LLToplevelTag (Decls a) = Decls a
    topFun _ n = lambdaLiftDecls n

lambdaLiftDecls :: Decls a -> Decls a
lambdaLiftDecls (DeclsBase t) = lambdaLift t
lambdaLiftDecls (DeclsCons str t rest) =
    DeclsCons str t $ mbToplevel (Tag :: Tag LLToplevelTag) rest


------------------------------------------------------------
-- modules
------------------------------------------------------------

data Module a where
    Functor :: Binding (L a) (Module b) -> (Module b)
    Module :: Decls a -> Module a

instance ToplevelFun LLToplevelTag (Module a) where
    type ToplevelRes LLToplevelTag (Module a) = Module a
    topFun _ n = lambdaLiftModule n

lambdaLiftModule :: Module a -> Module a
lambdaLiftModule (Module d) = Module $ lambdaLiftDecls d
lambdaLiftModule (Functor b) =
    Functor $ mbToplevel (Tag :: Tag LLToplevelTag) b


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
