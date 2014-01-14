{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables, TypeOperators, EmptyDataDecls, PatternGuards, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, ViewPatterns, UndecidableInstances #-}

---------------------------------
-- an example : lambda calculus
---------------------------------

module Term where

import HobbitLib
import Control.Applicative
import Data.List
import Unsafe.Coerce(unsafeCoerce)
import Untyped
import Control.DeepSeq

-- Term datatype
data Term a where
  Var :: Name a -> Term a
  Lam :: Binding a (Term b) -> Term (a -> b)
  App :: Term (a -> b) -> Term a -> Term b

instance NFData (Term a) where
  rnf (Var i) = rnf i
  rnf (Lam b) = rnf b
  rnf (App t1 t2) = rnf t1 `seq` rnf t2

-- matching under binders
data BTerm ctx a where
  BVar :: Mb ctx (Name a) -> BTerm ctx a
  BLam :: Mb ctx (Binding a (Term b)) -> BTerm ctx (a -> b)
  BApp :: Mb ctx (Term (a -> b)) -> Mb ctx (Term a) -> BTerm ctx b

mbTerm :: Mb ctx (Term a) -> BTerm ctx a
mbTerm = mbMatch Tag

data TermCtors
type instance TFunApply TermCtors l =
    List3 (List1 (Name (First l)), Term (First l))
          (List1 (Binding (First l) (Term (Second l))), Term ((First l) -> (Second l)))
          (List2 (Term ((First l) -> (Second l))) (Term (First l)), Term (Second l))

data BTermF a
type instance TFunApply (BTermF a) ctx = BTerm ctx a

instance MbMatchable (Term a) where
    type CtorsFun (Term a) = TermCtors
    type MatchTpFun (Term a) = (BTermF a)

    toRepr (Var n) =
        Repr (Tag :: Tag (List1 a)) InListBase (ArgsCons n ArgsNil)
    toRepr (Lam b) =
        Repr (Tag :: Tag (List2 b1 b2)) (InListStep InListBase) (ArgsCons b ArgsNil)
    toRepr (App t1 t2) =
        Repr (Tag :: Tag (List2 b1 b2))
             (InListStep (InListStep InListBase))
             (ArgsCons t1 (ArgsCons t2 ArgsNil))

    mbCtor _ _ InListBase = BVar
    mbCtor _ _ (InListStep InListBase) = BLam
    mbCtor _ _ (InListStep (InListStep InListBase)) = BApp


-- helper functions to build terms without noticing the Fresh Monad
lam :: (Name a -> Term b) -> Term (a -> b)
lam f = Lam $ nu f

-- use a proof as an index
nth :: InList ctx b -> [a] -> a
nth InListBase (x:_) = x
nth (InListStep n) (_:xs) = nth n xs

-- pretty print terms
pretty :: Term a -> String
pretty t = pretty' (emptyMb t) emptyMC 0
  where pretty' :: Mb ctx (Term a) -> MapCtx StringF ctx -> Int -> String
        pretty' u varnames n =
          case mbTerm u of
            BVar b -> case mbCmpName b of
                        Left pf  -> unStringF (ctxLookup pf varnames)
                        Right _ -> "free"
            BLam b -> let x = showVar n in
                      "(\\" ++ x ++ "." ++ pretty' (combineMb b) (varnames |> (StringF x)) (n+1) ++ ")"
            BApp b1 b2 -> "(" ++ pretty' b1 varnames n ++ " " ++ pretty' b2 varnames n ++ ")"
          where showVar i = "x" ++ show i

-- to make a function for MapCtx (for pretty)
newtype StringF x = StringF String
unStringF (StringF str) = str

-- an example
ex1 = lam $ \x -> lam $ \f -> App (Var f) (Var x)
ex2 = lam $ \x -> Var x

zero = lam $ \z -> lam $ \s -> Var z
suc  = lam $ \n -> lam $ \z -> lam $ \s -> Var n `App` (Var s `App` Var z) `App` Var s
plus = lam $ \n -> lam $ \m -> Var n `App` Var m `App` suc

toChurch 0 = zero
toChurch n = suc `App` toChurch (n-1)

ex3 = plus `App` toChurch 3 `App` toChurch 4

-- printer for lambda-terms
instance Show (Term a) where
    show = pretty


-- calculating the size of terms
data SizeTag
instance ToplevelFun SizeTag (Term a) where
  type ToplevelRes SizeTag (Term a) = Int
  topFun _ = size

mbSize :: Mb ctx (Term a) -> Mb ctx Int
mbSize = mbToplevel (Tag :: Tag SizeTag)

size :: Term a -> Int
size (Var _) = 1
size (Lam b) = 1 + mbInt (mbSize b)
size (App b1 b2)= 1 + size b1 + size b2


-- multi-arity substitution
msubst :: MapCtx Term ctx -> Mb ctx (Term a) -> Term a
msubst ts b = 
    case mbTerm b of
      BApp b1 b2 -> App (msubst ts b1) (msubst ts b2)
      BLam b1 -> lam $ \n -> msubst (ts |> Var n) (combineMb b1)
      BVar bx -> case mbCmpName bx of
                   Left p  -> ctxLookup p ts
                   Right i -> Var i

subst :: Binding a (Term b) -> Term a -> Term b
subst b t = msubst (ctxSingle t) b

-- alpha equivalence
malpha :: (Mb ctx1 (Term a1)) -> (Mb ctx2 (Term a2)) -> Bool
malpha b1 b2 = 
    case (mbTerm b1, mbTerm b2) of
      (BVar bv1, BVar bv2)         -> 
          case (mbCmpName bv1, mbCmpName bv2) of 
            (Left p1, Left p2) -> inCtxSameLength p1 p2
            _                  -> error "ouch"
      (BLam bf1, BLam bf2)         -> malpha (combineMb bf1) (combineMb bf2)
      (BApp b11 b12, BApp b21 b22) -> malpha b11 b21 && malpha b12 b22
      _                            -> False

alpha :: Term a -> Term b -> Bool
alpha t u = malpha (emptyMb t) (emptyMb u)

-- TAPL small step cbv evaluator

eval1 :: Term a -> Maybe (Term a)
eval1 (Var _) = Nothing
eval1 (App (Lam t) u) = Just $ subst t u
eval1 (App t u) = case eval1 u of 
    Just u' -> Just (App t u')
    Nothing -> Nothing
eval1 _ = Nothing

eval :: Term a -> Term a
eval t = case eval1 t of 
    Just t' -> eval t' 
    Nothing -> t

--------------------------------------------------
-- cbn normalizer
--------------------------------------------------

-- cbn normalizer under bindings
data Norm1Tag
instance ToplevelFun Norm1Tag (Term a) where
  type ToplevelRes Norm1Tag (Term a) = Maybe (Term a)
  topFun _ = norm1

mbNorm1 :: Mb ctx (Term a) -> Mb ctx (Maybe (Term a))
mbNorm1 = mbToplevel (Tag :: Tag Norm1Tag)

norm1 :: Term a -> Maybe (Term a)
norm1 (Var _) = Nothing
norm1 (Lam b) =
    case mbMaybe (mbNorm1 b) of
      BNothing -> Nothing
      BJust b' -> Just (Lam b')
norm1 (App (Lam b) u) = Just $ subst b u
norm1 (App t u) =
    case norm1 t of
      Just t' -> Just $ App t' u
      Nothing -> case norm1 u of
                   Just u' -> Just $ App t u'
                   Nothing -> Nothing

-- top-level call to cbn normalizer
norm :: Term a -> Term a
norm t = case norm1 t of 
    Just t' -> norm t' 
    Nothing -> t


--------------------------------------------------
-- cbn big-step normalizer
--------------------------------------------------

{-
-- cbn normalizer under bindings
bigNorm1' :: Mb ctx (Term a) -> MapCtx Name ctx -> Term a
bigNorm1' b ns =
    case mbTerm b of
      BVar bn -> case mbCmpName bn of
                  Left p -> Var $ ctxLookup p ns
                  Right n -> Var n
      BLam b1 ->
          case mbMaybe (nu $ \n -> bigNorm1' (combineMb b1) (ns |> n)) of
            BNothing -> Nothing
            BJust b1' -> Just (Lam b1')
      BApp b1 b2
        | BLam b11 <- mbTerm b1 ->
            Just $ msubst ((ctxMap Var ns) |> (closeTerm b2 ns)) (combineMb b11)
        | otherwise ->
            case bigNorm1' b1 ns of
              Nothing -> Nothing
              Just t1 -> Just $ App t1 (closeTerm b2 ns)

bigNorm1 :: Term a -> Maybe (Term a)
bigNorm1 t = bigNorm1' (emptyMb t) emptyMC

-- top-level call to cbn normalizer
bigNorm :: Term a -> Term a
bigNorm t = case bigNorm1 t of 
    Just t' -> bigNorm t' 
    Nothing -> t
-}

--------------------------------------------------
-- lifting for various type constructs
--------------------------------------------------

-- Maybe
data BMaybe ctx a = BNothing | BJust (Mb ctx a)

data MaybeCtors
type instance TFunApply MaybeCtors a =
    List2 (List0, Maybe a)
          (List1 a, Maybe a)

data BMaybeF a
type instance TFunApply (BMaybeF a) ctx = BMaybe ctx a

instance MbMatchable (Maybe a) where
    type CtorsFun   (Maybe a) = MaybeCtors
    type MatchTpFun (Maybe a) = BMaybeF a

    toRepr Nothing  = Repr (Tag :: Tag a) InListBase ArgsNil
    toRepr (Just x) = Repr (Tag :: Tag a) (InListStep InListBase) (ArgsCons x ArgsNil)

    mbCtor _ _ InListBase = BNothing
    mbCtor _ _ (InListStep InListBase) = BJust

mbMaybe :: Mb ctx (Maybe a) -> BMaybe ctx a
mbMaybe = mbMatch Tag


-- pairs
type BPair ctx a b = (Mb ctx a, Mb ctx b)

data PairCtors a b
type instance TFunApply (PairCtors a b) l =
    List1 (List2 a b, (a, b))

data BPairF a b
type instance TFunApply (BPairF a b) ctx = BPair ctx a b

instance MbMatchable (a, b) where
    type CtorsFun   (a, b) = PairCtors a b
    type MatchTpFun (a, b) = BPairF a b

    toRepr (a, b) = Repr Tag InListBase (ArgsCons a (ArgsCons b ArgsNil))

-- README: causes a GHC panic!
--    mbCtor _ _ InListBase = \a -> \b -> (a,b)
    mbCtor _ _ InListBase = mkpair where
        mkpair a b = (a, b)

mbPair :: Mb ctx (a, b) -> BPair ctx a b
mbPair = mbMatch Tag


-- either
type BEither ctx a b = Either (Mb ctx a) (Mb ctx b)

data EitherCtors a b
type instance TFunApply (EitherCtors a b) l =
    List2 (List1 a, Either a b)
          (List1 b, Either a b)

data BEitherF a b
type instance TFunApply (BEitherF a b) ctx = BEither ctx a b

instance MbMatchable (Either a b) where
    type CtorsFun   (Either a b) = EitherCtors a b
    type MatchTpFun (Either a b) = BEitherF a b

    toRepr (Left x)  = Repr (Tag :: Tag a) InListBase (ArgsCons x ArgsNil)
    toRepr (Right x) = Repr (Tag :: Tag a) (InListStep InListBase) (ArgsCons x ArgsNil)

    mbCtor _ _ InListBase = Left
    mbCtor _ _ (InListStep InListBase) = Right

mbEither :: Mb ctx (Either a b) -> BEither ctx a b
mbEither = mbMatch Tag


-- lists
data BList ctx a = BNil | BCons (Mb ctx a) (Mb ctx [a])

data BListF a
type instance TFunApply (BListF a) ctx = BList ctx a

data ListCtors a
type instance TFunApply (ListCtors a) l =
    List2 (List0, [a])
          (List2 a [a], [a])

instance MbMatchable [a] where
    type CtorsFun   [a] = ListCtors a
    type MatchTpFun [a] = BListF a

    toRepr []  = Repr Tag InListBase ArgsNil
    toRepr (x:xs) = Repr Tag (InListStep InListBase) (ArgsCons x (ArgsCons xs ArgsNil))

    mbCtor _ _ InListBase = BNil
    mbCtor _ _ (InListStep InListBase) = BCons

mbList :: Mb ctx [a] -> BList ctx a
mbList = mbMatch Tag


-- InList
data BInList ctx l a where
  BInListBase :: BInList ctx (Cons a l) a
  BInListStep :: Mb ctx (InList l a) -> BInList ctx (Cons b l) a

data InListCtors
type instance TFunApply InListCtors l =
    List2 (List0, InList (Cons (First l) (Second l)) (First l))
          (List1 (InList (Second l) (First l)), InList (Cons (Third l) (Second l)) (First l))

data InListF l a
type instance TFunApply (InListF l a) ctx = BInList ctx l a

-- BUG: Haskell can't seem to type-check this inside MbMatchable instance...
inListToRepr :: InList l a -> Repr InListCtors (InList l a)
inListToRepr InListBase = (Repr (Tag :: Tag (List2 a l)) InListBase ArgsNil) :: Repr InListCtors (InList (Cons a l) a)
inListToRepr (InListStep pf) = Repr (Tag :: Tag (List3 a l b)) (InListStep InListBase) (ArgsCons pf ArgsNil)

instance MbMatchable (InList l a) where
    type CtorsFun   (InList l a) = InListCtors
    type MatchTpFun (InList l a) = InListF l a

    toRepr inlist = inListToRepr inlist

    mbCtor _ _ InListBase = BInListBase
    mbCtor _ _ (InListStep InListBase) = BInListStep


mbInList :: Mb ctx (InList l a) -> InList l a
mbInList b =
    case (mbMatch Tag b) of
      BInListBase -> InListBase
      BInListStep pf -> InListStep (mbInList pf)



---------------------------------
-- lambda-lifting
---------------------------------

data BZipper ctxOut ctxIn holes a where
    BZVarIn :: InCtx ctxIn a -> BZipper List0 ctxIn List0 a
    BZVarOut :: BZipper (List1 a) ctxIn List0 a
    BZVarFree :: Name a -> BZipper List0 ctxIn List0 a
    BZApp :: BZipper ctxOut1 ctxIn holes1 (a -> b) ->
             BZipper ctxOut2 ctxIn holes2 a ->
             SubCtx ctxOut1 ctxOut -> SubCtx ctxOut2 ctxOut ->
             BZipper ctxOut ctxIn (holes1 :++: holes2) b
    BZHole :: BZipper List0 ctxIn (List1 a) a

-- phantom type for context subsets; essentially a list of "exists a. InCtx ctx"
data SubCtx subCtx ctx where
    SubCtxNil :: SubCtx Nil ctx
    SubCtxStep :: InCtx ctx a -> SubCtx subCtx ctx -> SubCtx (Cons a subCtx) ctx

-- unioning SubCtx proofs
-- README: assumes both SubCtx proofs are sorted by cmpInCtx
data UnionRes ctx1 ctx2 ctx where
    UnionRes :: Ctx subCtx -> SubCtx ctx1 subCtx -> SubCtx ctx2 subCtx -> 
                SubCtx subCtx ctx -> UnionRes ctx1 ctx2 ctx

subCtxUnion :: SubCtx ctx1 ctx -> SubCtx ctx2 ctx -> UnionRes ctx1 ctx2 ctx
subCtxUnion SubCtxNil SubCtxNil = UnionRes CtxNil SubCtxNil SubCtxNil SubCtxNil
-- FIXME: finish this

-- terms to fill holes
data HoleFillers holes where
    HFNil :: HoleFillers List0
    HFCons :: Ctx holesNew -> BZipper ctxOut ctxIn holesNew a ->
              HoleFillers (holesNew :++: holesOld) ->
              HoleFillers (Cons (AbsCtx ctxOut (AbsCtx ctxIn a)) holes2)

holeFillersUnion :: HoleFillers holes1 -> HoleFillers holes2 ->
                    HoleFillers (holes1 :++: holes2)
holeFillersUnion hf1 HFNil = hf1
-- FIXME: finish this


-- liftLambdas result type; existentially quantifies fvs and holes
data LLRes ctxOut ctxIn a where
    LLRes :: SubCtx fvs ctxOut -> Ctx fvs -> Ctx holes ->
             BZipper fvs ctxIn holes a -> HoleFillers holes ->
             LLRes ctxOut ctxIn a

liftLambdas :: Ctx ctxOut -> Ctx ctxIn -> BTerm (ctxOut :++: ctxIn) a ->
               LLRes ctxOut ctxIn a
liftLambdas ctxOut ctxIn (BVar n) =
    case mbMbCmpName (separateMb ctxOut ctxIn n) of
      Left inInner -> LLRes SubCtxNil CtxNil CtxNil (BZVarIn inInner) HFNil
      Right (Left inOuter) ->
          LLRes (SubCtxStep inOuter SubCtxNil) (CtxCons Tag CtxNil) CtxNil
                BZVarOut HFNil
      Right (Right n) ->
          LLRes SubCtxNil CtxNil CtxNil (BZVarFree n) HFNil
liftLambdas ctxOut ctxIn (BApp b1 b2) =
    appLLRes (liftLambdas ctxOut ctxIn (mbTerm b1))
             (liftLambdas ctxOut ctxIn (mbTerm b2)) where
        appLLRes :: LLRes ctxOut ctxIn (a -> b) -> LLRes ctxOut ctxIn a ->
                    LLRes ctxOut ctxIn b
        appLLRes (LLRes subfvs1 fvs1 holes1 bz1 fillers1)
                 (LLRes subfvs2 fvs2 holes2 bz2 fillers2) =
                     helper (subCtxUnion subfvs1 subfvs2) fvs1 fvs2
                            holes1 holes2 bz1 bz2 fillers1 fillers2
        helper :: UnionRes fvs1 fvs2 ctxOut -> Ctx fvs1 -> Ctx fvs2 ->
                  Ctx holes1 -> Ctx holes2 ->
                  BZipper fvs1 ctxIn holes1 (a -> b) ->
                  BZipper fvs2 ctxIn holes2 a ->
                  HoleFillers holes1 -> HoleFillers holes2 ->
                  LLRes ctxOut ctxIn b
        helper (UnionRes newfvs subfvs1 subfvs2 subfvs) fvs1 fvs2 holes1 holes2
               bz1 bz2 fillers1 fillers2 =
                   LLRes subfvs newfvs (ctxAppend holes1 holes2)
                         (BZApp bz1 bz2 subfvs1 subfvs2)
                         (holeFillersUnion fillers1 fillers2)
liftLambdas ctxOut ctxIn (BLam b) =
    helper ctxOut ctxIn (liftLambdas' ctxOut ctxIn (BLam b))

liftLambdas' :: Ctx ctxOut -> Ctx ctxIn -> BTerm (ctxOut :++: ctxIn) a ->
                LLRes ctxOut ctxIn a
liftLambdas' ctxOut ctxIn 


-- mbCmpName inside bindings
data MbMbCmpNameTag
instance ToplevelFun MbMbCmpNameTag (Mb ctx (Name a)) where
  type ToplevelRes MbMbCmpNameTag (Mb ctx (Name a)) = Either (InCtx ctx a) (Name a)
  topFun _ = mbCmpName

mbMbCmpName :: Mb ctxOut (Mb ctxIn (Name a)) ->
               Either (InCtx ctxIn a) (Either (InCtx ctxOut a) (Name a))
mbMbCmpName b =
    case mbEither (mbToplevel (Tag :: Tag MbMbCmpNameTag) b) of
      Left b' -> Left (mbInList b')
      Right b' -> Right (mbCmpName b')



--------------------------------------------------
-- old stuff for lambda-lifting
--------------------------------------------------


--------------------------------------------------
-- representing arbitrary names and lifting them out of bindings
--------------------------------------------------

data SomeName where SomeName :: (Name a) -> SomeName
instance Eq SomeName where
    (SomeName a) == (SomeName b) = cmpNameBool a b
data BSomeName ctx where BSomeName :: (Mb ctx (Name a)) -> BSomeName ctx

data BSomeNameF
type instance TFunApply BSomeNameF ctx = BSomeName ctx

data SomeNameCtors
type instance TFunApply SomeNameCtors l =
    List1 (List1 (Name l), SomeName)

instance MbMatchable SomeName where
    type CtorsFun   SomeName = SomeNameCtors
    type MatchTpFun SomeName = BSomeNameF

    toRepr (SomeName n)  = Repr Tag InListBase (ArgsCons n ArgsNil)

    mbCtor _ _ InListBase = BSomeName

mbSomeName :: Mb ctx SomeName -> BSomeName ctx
mbSomeName = mbMatch Tag

mbNames :: Mb ctx [SomeName] -> [SomeName]
mbNames l = case mbList l of
              BNil -> []
              BCons b l' ->
                  case mbSomeName b of
                    BSomeName nb ->
                        (case mbCmpName nb of
                           Left _ -> []
                           Right n -> [SomeName n]) ++ mbNames l'


data NamePair where NamePair :: Name a -> Name a -> NamePair

swapNames :: [NamePair] -> Name a -> Name a
swapNames [] n = n
swapNames (NamePair n1 n2 : names) n =
    case cmpName n n1 of
      Just TEq -> n2
      Nothing -> swapNames names n


mbSubstSwap :: [NamePair] -> MapCtx Name ctxS -> Mb ctxS (Term a) -> Term a
mbSubstSwap names ts b =
    case mbTerm b of
      BVar bx -> case mbCmpName bx of
                   Left p  -> Var (ctxLookup p ts)
                   Right n -> Var (swapNames names n)
      BLam b1 -> lam $ \n -> mbSubstSwap names (ts |> n) (combineMb b1)
      BApp b1 b2 -> App (mbSubstSwap names ts b1) (mbSubstSwap names ts b2)

substSwap :: [NamePair] -> Term a -> Term a
substSwap pairs t = mbSubstSwap pairs emptyMC (emptyMb t)

abstractVars :: [SomeName] -> [NamePair] -> Term a -> Term a
abstractVars [] pairs t = substSwap pairs t
abstractVars ((SomeName n):names) pairs t =
    App (lam $ \m -> abstractVars names (NamePair n m:pairs) t) (Var n)

closeLams :: Term a -> ([SomeName], Term a)
closeLams (Var n) = ([SomeName n], Var n)
closeLams (App t u) =
    let ((vars1, t'), (vars2, u')) = (closeLams t, closeLams u) in
    (nub (vars1 ++ vars2), App t' u')
closeLams (Lam b) =
    let (vars, t) = closeLams' (Lam b) in
    (vars, abstractVars vars [] t)

closeLams' :: Term a -> ([SomeName], Term a)
closeLams' (Lam b) =
    let (namesb, resb) = mbPair $ mbToplevel (Tag :: Tag CloseLamsTag) b in
    (mbNames namesb, Lam resb)
closeLams' x = closeLams x

data CloseLamsTag
instance ToplevelFun CloseLamsTag (Term a) where
    type ToplevelRes CloseLamsTag (Term a) = ([SomeName], Term a)
    topFun _ = closeLams'


-- lifting closed terms is just a substitution
newtype UnitF x = UnitF ()
liftClosed :: MapCtx f ctx -> Mb ctx (Term a) -> Term a
liftClosed map b = msubst (ctxMap (\_ -> error "unclosed term!") map) b


-- semi-old way of doing things with zippers

data ZTerm ctx a where
  ZHole :: ZTerm (List1 a) a
  ZVar :: Name a -> ZTerm Nil a
  ZLam :: Binding a (ZTerm ctx b) -> ZTerm ctx (a -> b)
  ZApp :: ZTerm ctx1 (a -> b) -> ZTerm ctx2 a ->
          IsAppend ctx1 ctx2 ctx -> ZTerm ctx b

data Zipper a where
  Zipper :: MapCtx Zipper ctx -> ZTerm ctx a -> Zipper a

promoteTerm :: Term a -> ZTerm Nil a
promoteTerm (Var n) = ZVar n
promoteTerm (App t u) = ZApp (promoteTerm t) (promoteTerm u) IsAppendBase
promoteTerm (Lam b) = ZLam $ mbToplevel (Tag :: Tag PromoteTag) b

data PromoteTag
instance ToplevelFun PromoteTag (Term a) where
    type ToplevelRes PromoteTag (Term a) = ZTerm Nil a
    topFun _ = promoteTerm

-- FIXME HERE: don't promote BLams, lift their bodies!
{-
liftLamsZ :: MapCtx Name ctx -> Mb ctx (Term a) -> Zipper a
liftLamsZ names b =
    case mbTerm b of
      BVar bn -> case mbCmpName bn of
                   Left pf -> Zipper emptyMC (ZVar $ ctxLookup pf names)
                   Right n -> Zipper emptyMC (ZVar n)
      BLam _ -> let t = liftClosed names b in
                Zipper (ctxSingle (Zipper emptyMC (promoteTerm t))) ZHole
      BApp t u -> appZippers (liftLamsZ names t) (liftLamsZ names u)
    where
      appZippers (Zipper map1 z1) (Zipper map2 z2) =
          Zipper (map1 |++> map2) (ZApp z1 z2 (mkIsAppend map1 map2))
-}

{-
closeZTerm :: MapCtx Name ctx -> ZTerm ctx a -> Term a
closeZTerm (Empty :> n) (ZHole) = Var n
closeZTerm _ (ZVar n) = Var n
closeZTerm names (ZApp t u isApp) =
    let (names1, names2) = splitMapCtx names isApp in
    App (closeZTerm names1 t) (closeZTerm names1 u)
closeZTerm names (ZLam b) = Var n

letBindZipper :: Zipper a -> Term a
letBindZipper (Zipper ctx z)
-}

-- old (and incomplete) lambda-lifting code using zippers...

{-
data ZTerm ctx a where
  ZHole :: ZTerm (List1 a) a
  ZVar :: Name a -> ZTerm Nil a
  ZApp :: ZTerm ctx1 (a -> b) -> ZTerm ctx2 a ->
          IsAppend ctx1 ctx2 ctx -> ZTerm ctx b
-}

data FloatTree a where
  FTStep :: MapCtx MbFloatTree ctx -> ZTerm ctx a -> FloatTree a

data MbFloatTree a where
  MbFloatTree :: Mb ctx (FloatTree a) -> MbFloatTree (AbsCtx ctx a)

type family AbsCtx a b
type instance AbsCtx Nil a = a
type instance AbsCtx (Cons a l) b = AbsCtx l (a -> b)

data MbTerm a where
  MbTerm :: Mb ctx (Term a) -> MbTerm (AbsCtx ctx a)

--data FloatLamsRet a where
--  FloatLamsRet :: MapCtx MbTerm ctx -> ZTerm ctx a -> FloatLamsRet a

{-
floatLams :: Term a -> FloatTree a
floatLams (Var x) = FTStep emptyMC (ZVar x)
floatLams (App t1 t2) =
  case (floatLams t1, floatLams t2) of
    (FTStep mc1 z1, FTStep mc2 z2) ->
      FTStep (mc1 |++> mc2) (ZApp z1 z2 (mkIsAppend mc1 mc2))
floatLams (Lam b) =
    case compressLams b of
      MbTerm mb ->
          FTStep (ctxSingle
                  (MbFloatTree
                   (mbToplevel
                    (Tag :: Tag FloatLamsTag)
                    mb))) ZHole
  where
    compressLams :: Mb ctx (Term a) -> MbTerm (AbsCtx ctx a)
    compressLams t =
        case mbTerm t of
          BLam b' -> compressLams (combineMb b')
          _       -> MbTerm t

data FloatLamsTag
instance ToplevelFun FloatLamsTag (Term a) where
  type ToplevelRes FloatLamsTag (Term a) = FloatTree a
  topFun _ = floatLams
-}




-- getting the free vars of a Term

freeVars' :: Mb ctx (Term a) -> [SomeName]
freeVars' b = case mbTerm b of
      BVar v -> case mbCmpName v of
                  Left p  -> []
                  Right i -> [SomeName i]
      BLam bl -> freeVars' (combineMb bl)
      BApp b1 b2 -> union (freeVars' b1) (freeVars' b2)
freeVars t = freeVars' (emptyMb t)


-- abstracting names out of terms
{-
abstractVars :: [SomeName] -> Term a -> Term a
abstractVars [] t = t
abstractVars ((SomeName n):names) t = App (abstractVars names (Lam (mbRebind n t))) (Var n)

-- re-abstracting under a binding
data ApplyLamTag
instance ToplevelFun ApplyLamTag (Mb (List1 a) (Term b)) where
    type ToplevelRes ApplyLamTag (Mb (List1 a) (Term b)) = Term (a -> b)
    topFun _ = Lam
mbLam :: Mb ctx (Mb (List1 a) (Term b)) -> Mb ctx (Term (a -> b))
mbLam = mbToplevel (Tag :: Tag ApplyLamTag)

-- lifting for the case of nested lambdas
liftSomeNames :: Mb ctx [SomeName] -> [SomeName]
liftSomeNames (mbList -> BNil) = []
liftSomeNames (mbList -> BCons mbsname b') =
    case mbSomeName mbsname of
      BSomeName nb ->
          case mbCmpName nb of
            Left _  -> liftSomeNames b'
            Right nb -> (SomeName nb) : liftSomeNames b'

mbLambdaLift :: Mb ctx (Term a) -> ([SomeName], Mb ctx (Term a))
mbLambdaLift b = case mbTerm b of
                   BLam b' ->
                       let (snames, res) = mbLambdaLift (combineMb b') in
                       (snames, mbLam (separateMb res))
                   _ -> let (bsnames, res) = mbPair (mbToplevel (Tag :: Tag LambdaLiftTag) b) in
                        (liftSomeNames bsnames, res)


data LambdaLiftTag
instance ToplevelFun LambdaLiftTag (Term a) where
    type ToplevelRes LambdaLiftTag (Term a) = ([SomeName], Term a)
    topFun _ = lambdaLift'

lambdaLift' :: Term a -> ([SomeName], Term a)
lambdaLift' (Var n) = ([SomeName n], (Var n))
lambdaLift' (App t1 t2) =
    let (l1, t1') = lambdaLift' t1 in
    let (l2, t2') = lambdaLift' t2 in
    (union l1 l2, App t1' t2')
lambdaLift' (Lam b) = let (vars, bres) = mbLambdaLift b in
                      (vars, abstractVars vars (Lam b))

lambdaLift :: Term a -> Term a
lambdaLift t = let (_, res) = lambdaLift' t in res
-}

data Skel holes cvars bvars a where
  SHole :: Skel (Cons a Nil) nil bvars a
  SCVar :: Skel nil (Cons a Nil) bvars a
  SVar  :: Mb bvars (Name a)
        -> Skel nil nil bvars a
  SApp  :: Skel h1 c1 bv (a -> b)
        -> Skel h2 c2 bv a
        -> Skel (h1 :++: h2) (c1 :++: b2) bv b 

{-
data LLRes a =
  LLRes :: 

ll :: 
ll t = case mbTerm t of
         BLam b = undefined
         other  = ll' other
-}

--abstractVars (freeVars t) t

--exLL = lam $ \z -> lam $ \s -> return $ lambdaLift (App (Var s) (Var z))
-- FIXME: write example


-- CPS translation

type family Cps o a
type instance Cps o Int      = (Int -> o) -> o
type instance Cps o (a -> b) = ((a -> Cps o b) -> o) -> o

{-
cpsVal :: Mb ctx (Term a) -> ctx -> Term ((a -> o) -> o)
cpsVal b xs = 
    case mbTerm b of
      BVar bx -> case name_multi_bind_cmp bx of
                   Left p -> return . Var $ lookupCtx p xs

cps :: Mb ctx (Term a) -> Term (Cps o a)
cps = undefined
-}

-- Parser

-- MbMatchable instances and lift functions
data ParseResult where
  NoTerm :: ParseResult
  SomeTerm :: Term a -> Ty -> ParseResult

instance Show ParseResult where
  show NoTerm = "NoTerm"
  show (SomeTerm t ty) = "SomeTerm " ++ show t ++ " " ++ show ty

data BParseResult ctx where 
  BNoTerm   :: BParseResult ctx 
  BSomeTerm :: Mb ctx (Term a) -> Mb ctx Ty -> BParseResult ctx

data BParseResultF
type instance TFunApply BParseResultF ctx = BParseResult ctx

data ParseResultCtors
type instance TFunApply ParseResultCtors l =
    List2 (List0, ParseResult)
          (List2 (Term l) Ty, ParseResult) 

instance MbMatchable ParseResult where
    type CtorsFun   ParseResult = ParseResultCtors
    type MatchTpFun ParseResult = BParseResultF

    toRepr NoTerm          = Repr Tag InListBase ArgsNil
    toRepr (SomeTerm t ty) = Repr Tag (InListStep InListBase) (ArgsCons t (ArgsCons ty ArgsNil))

    mbCtor _ _ InListBase = BNoTerm
    mbCtor _ _ (InListStep InListBase) = BSomeTerm

mbParseResult :: Mb ctx ParseResult -> BParseResult ctx
mbParseResult = mbMatch Tag

-- lifting types

data BTy ctx = BBase (Mb ctx Int) | BArrow (Mb ctx Ty) (Mb ctx Ty)

data BTyF
type instance TFunApply BTyF ctx = BTy ctx

data TyCtors
type instance TFunApply TyCtors l =
    List2 (List1 Int, Ty)
          (List2 Ty Ty, Ty) 

instance MbMatchable Ty where
    type CtorsFun   Ty = TyCtors
    type MatchTpFun Ty = BTyF

    toRepr (Base i)        = Repr Tag InListBase (ArgsCons i ArgsNil)
    toRepr (Arrow ty1 ty2) = Repr Tag (InListStep InListBase) (ArgsCons ty1 (ArgsCons ty2 ArgsNil))

    mbCtor _ _ InListBase = BBase
    mbCtor _ _ (InListStep InListBase) = BArrow

liftTy :: Mb ctx Ty -> Ty
liftTy b = case mbMatch Tag b of
             BBase i -> Base (mbInt i)
             BArrow ty1 ty2 -> Arrow (liftTy ty1) (liftTy ty2)

-- now, the actual parser!
parse :: UTerm -> ParseResult
parse ut = parse' [] ut
  where parse' ctx (UVar x) = 
          case lookup x ctx of
            Nothing               -> NoTerm
            Just (SomeName n, ty) -> SomeTerm (Var n) ty
        parse' ctx (ULam x tyx uu) =
          case mbParseResult (nu (\n -> parse' ((x,(SomeName n,tyx)):ctx) uu)) of
            BNoTerm         -> NoTerm
            BSomeTerm b tyu -> SomeTerm (Lam b) (Arrow tyx (liftTy tyu))
        parse' ctx (UApp u1 u2) =
          case (parse' ctx u1, parse' ctx u2) of
            (SomeTerm t1 (Arrow ty1 ty2), SomeTerm t2 ty3) 
              -- FIXME
              | ty1 == ty3 -> SomeTerm (App (unsafeCoerce t1) t2) ty2
              | otherwise  -> NoTerm
            _ -> NoTerm

-- an example of substitution
test1 = nu (\x -> lam (\f -> App (Var f) (Var x)))
test2 = lam (\x -> (Var x))
ex4 = subst test1 test2


uex1 = ULam "x" (Base 0) $ ULam "f" (Base 1) $ UApp (UVar "f") (UVar "x")
uex2 = ULam "x" (Base 0) $ ULam "f" (Arrow (Base 0) (Base 1)) $ UApp (UVar "f") (UVar "x")

maintest = do
  print ex1
  print ex2
  print (eval (App ex1 ex2))
  print (norm ex3)
  print (parse uex1)
  print (parse uex2)



