{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables, TypeOperators, EmptyDataDecls, PatternGuards, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TemplateHaskell, QuasiQuotes, ViewPatterns #-}

---------------------------------
-- an example : lambda calculus
---------------------------------

module TermTH where

import Ctx
import HobbitLibTH
import Control.DeepSeq
import Untyped
import Unsafe.Coerce(unsafeCoerce)

-- Term datatype
data Term a where
  Var :: Name a -> Term a
  Lam :: Binding a (Term b) -> Term (a -> b)
  App :: Term (a -> b) -> Term a -> Term b

instance NFData (Term a) where
  rnf (Var i) = rnf i
  rnf (Lam b) = rnf b
  rnf (App t1 t2) = rnf t1 `seq` rnf t2

instance Show (Term a) where
    show = pretty

-- helper functions to build terms without explicitly using nu or Var
lam :: (Term a -> Term b) -> Term (a -> b)
lam f = Lam $ nu (f . Var)

----------------------------------------
-- some example terms
----------------------------------------

ex1 = lam $ \x -> lam $ \f -> App f x
ex2 = lam $ \x -> x

zero = lam $ \z -> lam $ \s -> z
suc  = lam $ \n -> lam $ \z -> lam $ \s -> n `App` (s `App` z) `App` s
plus = lam $ \n -> lam $ \m -> n `App` m `App` suc

toChurch 0 = zero
toChurch n = suc `App` toChurch (n-1)

ex3 = plus `App` toChurch 3 `App` toChurch 4


----------------------------------------
-- pretty printing
----------------------------------------

-- to make a function for MapCtx (for pretty)
newtype StringF x = StringF String
unStringF (StringF str) = str

-- pretty print terms
pretty :: Term a -> String
pretty t = pretty' (emptyMb t) emptyMC 0
  where pretty' :: Mb ctx (Term a) -> MapCtx StringF ctx -> Int -> String
        pretty' [nuQQ| Var b |] varnames n =
            case mbNameBoundP b of
              Left pf  -> unStringF (ctxLookup pf varnames)
              Right _ -> "free"
        pretty' [nuQQ| Lam b |] varnames n =
            let x = "x" ++ show n in
            "(\\" ++ x ++ "." ++ pretty' (combineMb b) (varnames :> (StringF x)) (n+1) ++ ")"
        pretty' [nuQQ| App b1 b2 |] varnames n =
            "(" ++ pretty' b1 varnames n ++ " " ++ pretty' b2 varnames n ++ ")"

----------------------------------------
-- simple operations
----------------------------------------

-- size of a lambda-term
msize :: Mb ctx (Term a) -> Int
msize [nuQQ| Var _ |] = 1
msize [nuQQ| App b1 b2 |] = 1 + (msize b1) + (msize b2)
msize [nuQQ| Lam b |] = 1 + (msize (combineMb b))

size :: Term a -> Int
size t = msize (emptyMb t)

-- multi-arity substitution
msubst :: MapCtx Term ctx -> Mb ctx (Term a) -> Term a
msubst ts [nuQQ| App b1 b2 |] =
    App (msubst ts b1) (msubst ts b2)
msubst ts [nuQQ| Lam b1 |] =
    lam $ \n -> msubst (ts :> n) (combineMb b1)
msubst ts [nuQQ| Var bx |] =
    case mbNameBoundP bx of
      Left p  -> ctxLookup p ts
      Right i -> Var i

subst :: Binding a (Term b) -> Term a -> Term b
subst b t = msubst (ctxSingle t) b

-- alpha equivalence
malpha :: (Mb ctx1 (Term a1)) -> (Mb ctx2 (Term a2)) -> Bool
malpha [nuQQ| Var bv1 |] [nuQQ| Var bv2 |] =
    case (mbNameBoundP bv1, mbNameBoundP bv2) of 
      (Left p1, Left p2) -> inCtxSameLength p1 p2
      (Right n1, Right n2) -> depEqBool n1 n2
      _                  -> False
malpha [nuQQ| Lam bf1 |] [nuQQ| Lam bf2 |] =
    malpha (combineMb bf1) (combineMb bf2)
malpha [nuQQ| App b11 b12 |] [nuQQ| App b21 b22 |] =
    malpha b11 b21 && malpha b12 b22
malpha _ _ = False

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
mbNorm1 :: Mb ctx (Term a) -> Mb ctx (Maybe (Term a))
mbNorm1 = mbToplevel $(superComb [| norm1 |])

norm1 :: Term a -> Maybe (Term a)
norm1 (Var _) = Nothing
norm1 (Lam b) =
    case mbNorm1 b of
      [nuQQ| Nothing |] -> Nothing
      [nuQQ| Just b' |] -> Just (Lam b')
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


--------------------------------------
-- parsing 
--------------------------------------
data ParseResult where
  NoTerm :: ParseResult
  SomeTerm :: Term a -> Ty -> ParseResult

data SomeName where SomeName :: (Name a) -> SomeName
instance Eq SomeName where
    (SomeName n1) == (SomeName n2) = depEqBool n1 n2

instance Show ParseResult where
  show NoTerm = "NoTerm"
  show (SomeTerm t ty) = "SomeTerm " ++ show t ++ " " ++ show ty

liftTy :: Mb ctx Ty -> Ty
liftTy [nuQQ| Base i |] = Base (mbInt i)
liftTy [nuQQ| Arrow ty1 ty2 |] =
    Arrow (liftTy ty1) (liftTy ty2)


-- now, the actual parser!
parse :: UTerm -> ParseResult
parse ut = parse' [] ut
  where parse' ctx (UVar x) = 
          case lookup x ctx of
            Nothing               -> NoTerm
            Just (SomeName n, ty) -> SomeTerm (Var n) ty
        parse' ctx (ULam x tyx uu) =
          case (nu (\n -> parse' ((x,(SomeName n,tyx)):ctx) uu)) of
            [nuQQ| NoTerm |]         -> NoTerm
            [nuQQ| SomeTerm b tyu |] ->
                SomeTerm (Lam b) (Arrow tyx (liftTy tyu))
        parse' ctx (UApp u1 u2) =
          case (parse' ctx u1, parse' ctx u2) of
            (SomeTerm t1 (Arrow ty1 ty2), SomeTerm t2 ty3) 
              -- FIXME
              | ty1 == ty3 -> SomeTerm (App (unsafeCoerce t1) t2) ty2
              | otherwise  -> NoTerm
            _ -> NoTerm
