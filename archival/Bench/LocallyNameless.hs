{-# LANGUAGE FlexibleContexts, PackageImports #-}

module Bench.LocallyNameless where

import Untyped
import Data.List
import Control.DeepSeq
import System.IO.Unsafe(unsafePerformIO)
import Data.IORef
import "mtl" Control.Monad.Reader

-- lambda terms

type Name = Int

data LTerm = FVar Name 
           | BVar Int 
           | Lam LTerm 
           | LTerm :@ LTerm
  deriving (Eq)

instance NFData LTerm where
  rnf (BVar x) = rnf x
  rnf (FVar x) = rnf x
  rnf (Lam t)  = rnf t
  rnf (t :@ u) = rnf t `seq` rnf u

lam x t = Lam $ abstract x t

instance Show LTerm where
  show t = show' [] 0 t
    where show' ctx k (FVar v)  = error "open term"
          show' ctx k (BVar i)  = ctx !! i
          show' ctx k (Lam t)   = let x = showVar k in "(\\" ++ x ++ "." ++ show' (x:ctx) (k+1) t ++ ")"
          show' ctx k (t :@ u)  = "(" ++ show' ctx k t ++ " " ++ show' ctx k u ++ ")"
          showVar i = "x" ++ show i

size :: LTerm -> Int
size (FVar _) = 1
size (BVar _) = 1
size (Lam t)  = 1 + size t
size (t1 :@ t2) = 1 + size t1 + size t2

abstract :: Name -> LTerm -> LTerm
abstract x t = abs 0 t where
  abs n (FVar y) | x==y      = BVar n
                 | otherwise = FVar y
  abs _ (BVar i)             = BVar i
  abs n (t :@ u)             = abs n t :@ abs n u
  abs n (Lam t)              = Lam (abs (n+1) t)

instanciate :: LTerm -> LTerm -> LTerm
instanciate u t = ins 0 t where
  ins n (BVar i) | n==i      = u
                 | otherwise = BVar i
  ins _ (FVar x)             = FVar x
  ins n (a :@ b)             = ins n a :@ ins n b
  ins n (Lam t)              = Lam (ins (n+1) t)

substitute :: LTerm -> Name -> LTerm -> LTerm 
substitute u x = instanciate u . abstract x

-- examples

zero = Lam (Lam (BVar 1))
suc  = Lam (Lam (Lam (BVar 2 :@ (BVar 0 :@ BVar 1) :@ BVar 0)))
plus = Lam (Lam (BVar 1 :@ BVar 0 :@ suc))
--zero = lam "x" $ lam "s" $ FVar "x"
--suc  = lam "n" $ lam "x" $ lam "s" $ FVar "n" :@ (FVar "s" :@ FVar "x") :@ FVar "s"
--plus = lam "n" $ lam "m" $ FVar "n" :@ FVar "m" :@ suc

toChurch 0 = zero
toChurch n = suc :@ toChurch (n-1)

ex1 = plus :@ toChurch 3 :@ toChurch 4

-- normalizer

type Fresh a = Reader Int a
runFresh f = runReader f 0

freshName :: (Name -> Fresh b) -> Fresh b
freshName f = local (+1) (ask >>= f)
{-
counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

fresh_int :: Fresh Int
fresh_int = do
  n <- readIORef counter
  () <- writeIORef counter (n+1)
  return n

type Fresh a = IO a
freshName f = do
  fresh_int >>= f

runFresh = id
-}

norm1 :: LTerm -> Fresh (Maybe LTerm)
norm1 (Lam t :@ u) = return . Just $ instanciate u t
norm1 (t :@ u)     = do mt' <- norm1 t
                        case mt' of
                          Nothing -> do mu' <- norm1 u
                                        return $ (t :@) `fmap` mu'
                          Just t' -> return . Just $ t' :@ u
norm1 (Lam t)      = freshName $ \n -> do
                       mt' <- norm1 (instanciate (FVar n) t)
                       return $ (lam n) `fmap` mt'
norm1 _            = return Nothing

norm :: LTerm -> Fresh LTerm
norm t = do
  mt' <- norm1 t
  case mt' of 
    Just t' -> norm t' 
    Nothing -> return t


-- parsing

parse :: [String] -> UTerm -> LTerm
parse ctx (UVar x) = BVar (unMaybe $ elemIndex x ctx) where
    unMaybe (Just x) = x
parse ctx (UApp t1 t2) = (parse ctx t1) :@ (parse ctx t2)
parse ctx (ULam x _ body) = Lam $ parse (x:ctx) body

parseTop = parse []
