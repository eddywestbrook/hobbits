module Bench.BigTerms where

import qualified Bench.LocallyNameless as LN
import qualified Bench.DeBruijn as DB
import Untyped


{-
  We define three forms of "big terms" parameterized by a natural number N:

  Exponential terms:
    \f:(a -> a) -> ((a -> a) -> a). \g:(a -> ... -> a -> a). EXP N []
  where
    EXP 0 [x1,...,xn] = g x1 ... xn
    EXP (k+1) xs = f (\xk:a. EXP k xk:xs) (\xk:a. EXP k xk:xs)


  Linear terms:
    \f:(a -> a) -> a. \g:(a -> ... -> a -> a).
      f (\x1:a. f (\x2:a. ... f (\xN:a. g xN ... x1)))

  Linear terms version 2:
    \f:(a -> a) -> (a -> a). \g:(a -> ... -> a -> a).
      f (\x1:a . f (\x2:a. ... (f (\xN:a. g xN ... x1) xN) ... x2) x1)

  Linear terms version 3:
    \f:(a -> a) -> (a -> a). \g:(a -> ... -> a -> a).
      f (\x1:a . f (\x2:a. ... (f (\xN:a. g xN ... xN) xN) ... x2) x1)

  Linear terms version 4:
    \f:(a -> a) -> (a -> a). \g:(a -> ... -> a -> a).
      f (\x1:a . f (\x2:a. ... (f (\xN:a. g x1 ... x1) xN) ... x2) x1)
-}

name i = "x" ++ show i

a = Base 0
infixr -->
a --> b = Arrow a b

-- the exponential one

{-
bigLN n = LN.Lam $ LN.Lam $ go n
  where go 0 = foldl (LN.:@) (LN.BVar n) (map LN.BVar [0..n-1])
        go i = let r = LN.Lam (go (i-1))
               in LN.BVar (n-i+1) LN.:@ r LN.:@ r

bigDB n = DB.Lam $ DB.Lam $ go n
  where go 0 = foldl (DB.:@) (DB.Var n) (map DB.Var [0..n-1])
        go i = let r = DB.Lam (go (i-1))
               in DB.Var (n-i+1) DB.:@ r DB.:@ r
-}

bigUntyped n = ULam "f" ((a --> a) --> (a --> a) --> a) $ ULam "g" (foldr (-->) a (replicate n a)) $ go n []
  where go 0 xs = foldl UApp (UVar "g") xs
        go i xs = let x = name i
                      r = ULam x a (go (i-1) (UVar x:xs))
                  in UVar "f" `UApp` r `UApp` r

-- a linear one

{-
bigLinearLN n = LN.Lam $ LN.Lam $ go n
  where go 0 = foldl (LN.:@) (LN.BVar n) (map LN.BVar [0..n-1])
        go i = let r = LN.Lam (go (i-1))
               in LN.BVar (n-i+1) LN.:@ r

bigLinearDB n = DB.Lam $ DB.Lam $ go n
  where go 0 = foldl (DB.:@) (DB.Var n) (map DB.Var [0..n-1])
        go i = let r = DB.Lam (go (i-1))
               in DB.Var (n-i+1) DB.:@ r
-}

bigLinearUntyped n = ULam "f" ((a --> a) --> a) $ ULam "g" (foldr (-->) a (replicate n a)) $ go n []
  where go 0 xs = foldl UApp (UVar "g") xs
        go i xs = let x = name i
                      r = ULam x a (go (i-1) (UVar x:xs))
                  in UVar "f" `UApp` r

-- linear version 2

{-
bigLinearLN2 n = LN.Lam $ LN.Lam $ LN.Lam $ go n
  where go 0 = foldl (LN.:@) (LN.BVar (n+1)) (map LN.BVar [0..n])
        go i = let r = LN.Lam (go (i-1))
               in LN.BVar (n-i+2) LN.:@ r LN.:@ LN.BVar 0

bigLinearDB2 n = DB.Lam $ DB.Lam $ DB.Lam $ go n
  where go 0 = foldl (DB.:@) (DB.Var (n+1)) (map DB.Var [0..n])
        go i = let r = DB.Lam (go (i-1))
               in DB.Var (n-i+2) DB.:@ r DB.:@ DB.Var 0
-}

bigLinearUntyped2 n = ULam "f" ((a --> a) --> a --> a) $ ULam "g" (foldr (-->) a (replicate (n+1) a)) $ ULam "x" a $ go n [UVar "x"]
  where go 0 xs = foldl UApp (UVar "g") xs
        go i xs = let x = name i
                      r = ULam x a (go (i-1) (UVar x:xs)) 
                  in UVar "f" `UApp` r `UApp` head xs

-- linear version 3

{-
bigLinearLN3 n = LN.Lam $ LN.Lam $ LN.Lam $ go n
  where go 0 = foldl (LN.:@) (LN.BVar (n+1)) (replicate (n+1) $ LN.BVar 0)
        go i = let r = LN.Lam (go (i-1))
               in LN.BVar (n-i+2) LN.:@ r LN.:@ LN.BVar 0

bigLinearDB3 n = DB.Lam $ DB.Lam $ DB.Lam $ go n
  where go 0 = foldl (DB.:@) (DB.Var (n+1)) (replicate (n+1) $ DB.Var 0)
        go i = let r = DB.Lam (go (i-1))
               in DB.Var (n-i+2) DB.:@ r DB.:@ DB.Var 0
-}

bigLinearUntyped3 n = ULam "f" ((a --> a) --> a --> a) $ ULam "g" (foldr (-->) a (replicate (n+1) a)) $ ULam "x" a $ go n (UVar "x")
  where go 0 lastX = foldl UApp (UVar "g") (replicate (n+1) lastX)
        go i lastX = let x = name i
                         r = ULam x a (go (i-1) $ UVar x)
                  in UVar "f" `UApp` r `UApp` lastX


-- linear version 4

bigLinearUntyped4 n = ULam "f" ((a --> a) --> a --> a) $ ULam "g" (foldr (-->) a (replicate (n+1) a)) $ ULam "x" a $ go n (UVar "x")
  where go 0 lastX = foldl UApp (UVar "g") (replicate (n+1) (UVar "x"))
        go i lastX = let x = name i
                         r = ULam x a (go (i-1) $ UVar x)
                     in UVar "f" `UApp` r `UApp` lastX

