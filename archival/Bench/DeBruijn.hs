{-# LANGUAGE FlexibleContexts, PackageImports #-}

module Bench.DeBruijn where

import Control.DeepSeq
import Data.List
import Untyped


-- lambda terms

data LTerm = Var Int 
           | Lam LTerm 
           | LTerm :@ LTerm
  deriving (Eq)

instance NFData LTerm where
  rnf (Var x) = rnf x
  rnf (Lam t)  = rnf t
  rnf (t :@ u) = rnf t `seq` rnf u

instance Show LTerm where
  show t = show' [] 0 t
    where show' ctx k (Var i)  = ctx !! i
          show' ctx k (Lam t)   = let x = showVar k in "(\\" ++ x ++ "." ++ show' (x:ctx) (k+1) t ++ ")"
          show' ctx k (t :@ u)  = "(" ++ show' ctx k t ++ " " ++ show' ctx k u ++ ")"
          showVar i = "x" ++ show i

size :: LTerm -> Int
size (Var _) = 1
size (Lam t) = 1 + size t
size (t1 :@ t2) = 1 + size t1 + size t2

-- substitution

tmmap onvar c t = walk c t
  where walk c (Var i)    = onvar c i
        walk c (Lam t1)   = Lam (walk (c+1) t1)
        walk c (t1 :@ t2) = walk c t1 :@ walk c t2 

shiftAbove d = tmmap (\c i -> if i >= c then Var (i+d) else Var i) 
shift d t = shiftAbove d 0 t
subst s t = tmmap (\c i -> if i == c then shift c s else Var i) 0 t
substTop s t = shift (-1) (subst (shift 1 s) t)

-- examples

zero = Lam (Lam (Var 1))
suc  = Lam (Lam (Lam (Var 2 :@ (Var 0 :@ Var 1) :@ Var 0)))
plus = Lam (Lam (Var 1 :@ Var 0 :@ suc))

toChurch 0 = zero
toChurch n = suc :@ toChurch (n-1)

ex1 = plus :@ toChurch 3 :@ toChurch 4

norm1 :: LTerm -> Maybe LTerm
norm1 (Lam t :@ u) = Just $ substTop u t
norm1 (t :@ u)     = case norm1 t of
                       Just t' -> Just $ t' :@ u
                       Nothing -> (t :@) `fmap` norm1 u
norm1 (Lam t)      = Lam `fmap` norm1 t
norm1 _            = Nothing

norm :: LTerm -> LTerm
norm t = case norm1 t of 
  Just t' -> norm t' 
  Nothing -> t

pret1 = Var 0
t1 = Lam pret1
t2 = t1 :@ t1


-- parsing

parse :: [String] -> UTerm -> LTerm
parse ctx (UVar x) = Var (unMaybe $ elemIndex x ctx) where
    unMaybe (Just x) = x
parse ctx (UApp t1 t2) = (parse ctx t1) :@ (parse ctx t2)
parse ctx (ULam x _ body) = Lam $ parse (x:ctx) body

parseTop = parse []
