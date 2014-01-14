{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables, TypeOperators, EmptyDataDecls, PatternGuards, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, ViewPatterns #-}

---------------------------------
-- an example : lambda calculus
---------------------------------

module Term where

import Hoas
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
        Repr (Tag :: Tag (List1 a)) InCtxtBase (ArgsCons n ArgsNil)
    toRepr (Lam b) =
        Repr (Tag :: Tag (List2 b1 b2)) (InCtxtStep InCtxtBase) (ArgsCons b ArgsNil)
    toRepr (App t1 t2) =
        Repr (Tag :: Tag (List2 b1 b2))
             (InCtxtStep (InCtxtStep InCtxtBase))
             (ArgsCons t1 (ArgsCons t2 ArgsNil))

    mbCtor _ _ InCtxtBase = BVar
    mbCtor _ _ (InCtxtStep InCtxtBase) = BLam
    mbCtor _ _ (InCtxtStep (InCtxtStep InCtxtBase)) = BApp


-- helper functions to build terms without noticing the Fresh Monad
var :: Name a -> Fresh (Term a)
var = pure . Var
lam :: (Name a -> Fresh (Term b)) -> Fresh (Term (a -> b))
lam f = Lam <$> nu f
app :: Fresh (Term (a -> b)) -> Fresh (Term a) -> Fresh (Term b)
app t1 t2 = App <$> t1 <*> t2

-- use a proof as an index
nth :: InCtxt ctx b -> [a] -> a
nth InCtxtBase (x:_) = x
nth (InCtxtStep n) (_:xs) = nth n xs

-- pretty print terms
pretty :: Term a -> String
pretty t = pretty' (emptyMb t) CtxtFListBase 0
  where pretty' :: Mb ctx (Term a) -> CtxtFList StringF ctx -> Int -> String
        pretty' u varnames n =
          case mbTerm u of
            BVar b -> case mbCmpName b of
                        Left pf  -> unStringF (lookupCtxFList pf varnames)
                        Right _ -> "free"
            BLam b -> let x = showVar n in
                      "(\\" ++ x ++ "." ++ pretty' (combineMb b) (varnames |> (StringF x)) (n+1) ++ ")"
            BApp b1 b2 -> "(" ++ pretty' b1 varnames n ++ " " ++ pretty' b2 varnames n ++ ")"
          where showVar i = "x" ++ show i

-- to make a function for CtxtFList (for pretty)
newtype StringF x = StringF String
unStringF (StringF str) = str

-- an example
ex1 = lam $ \x -> lam $ \f -> var f `app` var x
ex2 = lam $ \x -> var x

zero = lam $ \z -> lam $ \s -> var z
suc  = lam $ \n -> lam $ \z -> lam $ \s -> var n `app` (var s `app` var z) `app` var s
plus = lam $ \n -> lam $ \m -> var n `app` var m `app` suc

toChurch 0 = zero
toChurch n = suc `app` toChurch (n-1)

ex3 = plus `app` toChurch 3 `app` toChurch 4

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
msubst :: CtxtFList Term ctx -> Mb ctx (Term a) -> Fresh (Term a)
msubst ts b = 
    case mbTerm b of
      BApp b1 b2 -> app (msubst ts b1) (msubst ts b2)
      BLam b1 -> lam $ \n -> msubst (ts |> Var n) (combineMb b1)
      BVar bx -> case mbCmpName bx of
                   Left p  -> return $ lookupCtxFList p ts
                   Right i -> var i

subst :: Binding a (Term b) -> Term a -> Fresh (Term b)
subst b t = msubst (ctxtFListSingle t) b

-- alpha equivalence
sameLength :: InCtxt ctx1 a1 -> InCtxt ctx2 a2 -> Bool
sameLength InCtxtBase InCtxtBase           = True
sameLength (InCtxtStep p1) (InCtxtStep p2) = sameLength p1 p2
sameLength _               _               = False

malpha :: (Mb ctx1 (Term a1)) -> (Mb ctx2 (Term a2)) -> Bool
malpha b1 b2 = 
    case (mbTerm b1, mbTerm b2) of
      (BVar bv1, BVar bv2)         -> 
          case (mbCmpName bv1, mbCmpName bv2) of 
            (Left p1, Left p2) -> sameLength p1 p2
            _                  -> error "ouch"
      (BLam bf1, BLam bf2)         -> malpha (combineMb bf1) (combineMb bf2)
      (BApp b11 b12, BApp b21 b22) -> malpha b11 b21 && malpha b12 b22
      _                            -> False

alpha :: Term a -> Term b -> Bool
alpha t u = malpha (emptyMb t) (emptyMb u)

-- TAPL small step cbv evaluator

eval1 :: Term a -> Fresh (Maybe (Term a))
eval1 (Var _) = return $ Nothing
eval1 (App (Lam t) u) = Just <$> subst t u
eval1 (App t u) = do
  mu' <- eval1 u
  return $ case mu' of 
    Just u' -> Just (App t u')
    Nothing -> Nothing
eval1 _ = return $ Nothing

eval :: Term a -> Fresh (Term a)
eval t = do
  mt' <- eval1 t
  case mt' of 
    Just t' -> eval t' 
    Nothing -> return $ t

--------------------------------------------------
-- cbn normalizer
--------------------------------------------------

-- helper functions

closeTerm :: Mb ctx (Term a) -> CtxtFList Name ctx -> Fresh (Term a)
closeTerm b ns = 
    case mbTerm b of
      (BApp b1 b2) -> app (closeTerm b1 ns) (closeTerm b2 ns)
      (BLam b1)    -> lam $ \n -> closeTerm (combineMb b1) (ns |> n)
      (BVar bx)    -> case mbCmpName bx of
                        Left p  -> var $ lookupCtxFList p ns
                        Right i -> var i

convertCtx :: CtxtFList Name ctx -> CtxtFList Term ctx
convertCtx CtxtFListBase        = CtxtFListBase
convertCtx (CtxtFListStep x xs) = CtxtFListStep (Var x) (convertCtx xs)


-- cbn normalizer under bindings
norm1' :: Mb ctx (Term a) -> CtxtFList Name ctx -> Fresh (Maybe (Term a))
norm1' b ns = 
    case mbTerm b of
      BVar _ -> return $ Nothing
      BLam b1 -> do
        bmt1 <- nu $ \n -> norm1' (combineMb b1) (ns |> n)
        return $ case mbMaybe bmt1 of
          BNothing -> Nothing
          BJust b1' -> Just (Lam b1')
      BApp b1 b2
        | BLam b11 <- mbTerm b1 -> do
            t2 <- closeTerm b2 ns
            Just <$> msubst (convertCtx ns |> t2) (combineMb b11)
        | otherwise -> do
            mt1 <- norm1' b1 ns
            t2  <- closeTerm b2 ns
            return $ case mt1 of 
              Nothing -> Nothing
              Just t1 -> Just $ App t1 t2

norm1 :: Term a -> Fresh (Maybe (Term a))
norm1 t = norm1' (emptyMb t) CtxtFListBase

-- top-level call to cbn normalizer
norm :: Term a -> Fresh (Term a)
norm t = do
  mt' <- norm1 t
  case mt' of 
    Just t' -> norm t' 
    Nothing -> return $ t

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

    toRepr Nothing  = Repr (Tag :: Tag a) InCtxtBase ArgsNil
    toRepr (Just x) = Repr (Tag :: Tag a) (InCtxtStep InCtxtBase) (ArgsCons x ArgsNil)

    mbCtor _ _ InCtxtBase = BNothing
    mbCtor _ _ (InCtxtStep InCtxtBase) = BJust

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

    toRepr (a, b) = Repr Tag InCtxtBase (ArgsCons a (ArgsCons b ArgsNil))

-- README: causes a GHC panic!
--    mbCtor _ _ InCtxtBase = \a -> \b -> (a,b)
    mbCtor _ _ InCtxtBase = mkpair where
        mkpair a b = (a, b)

mbPair :: Mb ctx (a, b) -> BPair ctx a b
mbPair = mbMatch Tag


-- lists
data BList ctx a = BNil | BCons (Mb ctx a) (Mb ctx [a])

data BListF a
type instance TFunApply (BListF a) ctx = BList ctx a

data ListCtors a
type instance TFunApply (ListCtors a) l =
    List2 ((), [a])
          (List2 a [a], [a])

instance MbMatchable [a] where
    type CtorsFun   [a] = ListCtors a
    type MatchTpFun [a] = BListF a

    toRepr []  = Repr Tag InCtxtBase ArgsNil
    toRepr (x:xs) = Repr Tag (InCtxtStep InCtxtBase) (ArgsCons x (ArgsCons xs ArgsNil))

    mbCtor _ _ InCtxtBase = BNil
    mbCtor _ _ (InCtxtStep InCtxtBase) = BCons

mbList :: Mb ctx [a] -> BList ctx a
mbList = mbMatch Tag


--------------------------------------------------
-- representing arbitrary names and lifting them out of bindings
--------------------------------------------------

data SomeName where SomeName :: (Name a) -> SomeName
instance Eq SomeName where
    (SomeName a) == (SomeName b) = case cmpName a b of
                                   Nothing -> False
                                   Just _ -> True
data BSomeName ctx where BSomeName :: (Mb ctx (Name a)) -> BSomeName ctx

data BSomeNameF
type instance TFunApply BSomeNameF ctx = BSomeName ctx

data SomeNameCtors
type instance TFunApply SomeNameCtors l =
    List1 (List1 (Name l), SomeName)

instance MbMatchable SomeName where
    type CtorsFun   SomeName = SomeNameCtors
    type MatchTpFun SomeName = BSomeNameF

    toRepr (SomeName n)  = Repr Tag InCtxtBase (ArgsCons n ArgsNil)

    mbCtor _ _ InCtxtBase = BSomeName

mbSomeName :: Mb ctx SomeName -> BSomeName ctx
mbSomeName = mbMatch Tag

---------------------------------
-- lambda-lifting
---------------------------------

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
{-
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

--abstractVars (freeVars t) t

--exLL = lam $ \z -> lam $ \s -> return $ lambdaLift (App (Var s) (Var z))
-- FIXME: write example


-- CPS translation

type family Cps o a
type instance Cps o Int      = (Int -> o) -> o
type instance Cps o (a -> b) = ((a -> Cps o b) -> o) -> o

{-
cpsVal :: Mb ctx (Term a) -> ctx -> Fresh (Term ((a -> o) -> o))
cpsVal b xs = 
    case mbTerm b of
      BVar bx -> case name_multi_bind_cmp bx of
                   Left p -> return . Var $ lookupCtx p xs

cps :: Mb ctx (Term a) -> Fresh (Term (Cps o a))
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

    toRepr NoTerm          = Repr Tag InCtxtBase ArgsNil
    toRepr (SomeTerm t ty) = Repr Tag (InCtxtStep InCtxtBase) (ArgsCons t (ArgsCons ty ArgsNil))

    mbCtor _ _ InCtxtBase = BNoTerm
    mbCtor _ _ (InCtxtStep InCtxtBase) = BSomeTerm

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

    toRepr (Base i)        = Repr Tag InCtxtBase (ArgsCons i ArgsNil)
    toRepr (Arrow ty1 ty2) = Repr Tag (InCtxtStep InCtxtBase) (ArgsCons ty1 (ArgsCons ty2 ArgsNil))

    mbCtor _ _ InCtxtBase = BBase
    mbCtor _ _ (InCtxtStep InCtxtBase) = BArrow

liftTy :: Mb ctx Ty -> Ty
liftTy b = case mbMatch Tag b of
             BBase i -> Base (mbInt i)
             BArrow ty1 ty2 -> Arrow (liftTy ty1) (liftTy ty2)

-- now, the actual parser!
parse :: UTerm -> Fresh ParseResult
parse ut = parse' [] ut
  where parse' ctx (UVar x) = 
          return $ case lookup x ctx of
            Nothing               -> NoTerm
            Just (SomeName n, ty) -> SomeTerm (Var n) ty
        parse' ctx (ULam x tyx uu) = do
          mb <- nu (\n -> parse' ((x,(SomeName n,tyx)):ctx) uu)
          return $ case mbParseResult mb of
            BNoTerm         -> NoTerm
            BSomeTerm b tyu -> SomeTerm (Lam b) (Arrow tyx (liftTy tyu))
        parse' ctx (UApp u1 u2) = do
          mb1 <- parse' ctx u1
          mb2 <- parse' ctx u2
          return $ case (mb1,mb2) of
            (SomeTerm t1 (Arrow ty1 ty2), SomeTerm t2 ty3) 
              -- FIXME
              | ty1 == ty3 -> SomeTerm (App (unsafeCoerce t1) t2) ty2
              | otherwise  -> NoTerm
            _ -> NoTerm

-- an example of substitution
test1 = nu (\x -> lam (\f -> app (var f) (var x)))
test2 = lam (\x -> (var x))
ex4 = test1 >>= \x -> test2 >>= \y -> subst x y


uex1 = ULam "x" (Base 0) $ ULam "f" (Base 1) $ UApp (UVar "f") (UVar "x")
uex2 = ULam "x" (Base 0) $ ULam "f" (Arrow (Base 0) (Base 1)) $ UApp (UVar "f") (UVar "x")

maintest = do
  runFresh ex1 >>= print
  runFresh ex2 >>= print
  runFresh (ex1 `app` ex2 >>= eval) >>= print
  runFresh (ex3 >>= norm) >>= print
  runFresh (parse uex1) >>= print
  runFresh (parse uex2) >>= print
