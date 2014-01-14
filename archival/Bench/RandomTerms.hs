--module Bench.RandomTerms where

import Control.Applicative
import Control.Monad
import Test.QuickCheck
import Data.Maybe


import qualified Bench.LocallyNameless as LN
import qualified Bench.DeBruijn as DB
import Untyped

newtype MGen a = MGen { runMGen :: Gen (Maybe a) }

instance Monad MGen where
  return x = MGen $ return (Just x)
  MGen gma >>= f = MGen $ do ma <- gma
                             case ma of
                               Nothing -> return Nothing
                               Just x  -> runMGen $ f x

instance Functor MGen where
  fmap f mgx = do x <- mgx
                  return $ f x

instance Applicative MGen where
  pure    = return
  mgf <*> mgx = do f <- mgf
                   f <$> mgx

lift :: Gen a -> MGen a
lift ga = MGen $ Just <$> ga

cut :: MGen a 
cut = MGen (return Nothing)

moneof :: [MGen a] -> MGen a
moneof [] = cut
moneof xs = MGen $ oneof (map runMGen xs)

melements [] = cut
melements xs = lift (elements xs)

mfrequency :: [(Int, MGen a)] -> MGen a
mfrequency = MGen . frequency . map (\(x,y) -> (x, runMGen y))

try :: Int -> MGen a -> MGen a
try 0 mg = cut
try n mg = MGen $ do x <- runMGen mg
                     if isJust x then return x
                                 else runMGen $ try (n-1) mg

--retry mg = MGen (join <$> runMGen mg `suchThatMaybe` isJust)

genType = oneof [genBase, genArrow]
  where genBase = elements [nat, bool]  
        genArrow = Arrow <$> genType <*> genType

type Ctx = [(String, Ty)]

mgenTerm counter apps ctx ty = 
  moneof $ [ mgenVar ctx ty
           , mgenLam counter apps ctx ty]
           ++ if apps > 0
                then [ mgenIndir counter apps ctx ty
                     , mgenApp counter apps ctx ty]
                else []

{-
mgenTerm counter apps ctx ty = 
  mfrequency [ (4, mgenVar ctx ty)
             , (4, mgenLam counter apps ctx ty)
             , (4, mgenIndir counter apps ctx ty)
             , (1, mgenApp counter apps ctx ty) ]
-}

mgenVar ctx ty = UVar <$> melements candidates
  where candidates = [ x | (x,ty') <- ctx, ty == ty' ]

mgenLam counter apps ctx (Arrow ty1 ty2) = 
  ULam fresh ty1 <$> mgenTerm (counter+1) apps ((fresh,ty1):ctx) ty2
    where fresh = "x" ++ show counter
mgenLam _       _    _   _               = cut

mgenApp counter apps ctx ty = do
  (ty1, t1) <- try 2 $ do ty1 <- lift genType
                          t1 <- mgenTerm counter (apps-1) ctx (Arrow ty1 ty)
                          return $ (ty1, t1)
  t2 <- mgenTerm counter (apps-1) ctx ty1
  return $ UApp t1 t2

mgenIndir counter apps ctx ty = do
  (f,tys) <- melements [ (f,as) | (f,a) <- ctx
                                , let (ty', as) = peel a
                                , ty' == ty ]
  apply (UVar f) [try 2 $ mgenTerm counter (apps-1) ctx a | a <- tys] 
  where peel a = let (ty:tys) = reverse (peel' a) in (ty, tys)
        peel' ty@(Base _)     = [ty]
        peel' (Arrow ty1 ty2) = ty1:(peel' ty2)

        apply t [] = return t
        apply t (mx:mxs) = do x <- mx
                              apply (UApp t x) mxs

nat = Base 0
bool = Base 1
infixr -->
(-->) = Arrow
natCtx n = [ ("zero", nat)
           , ("succ", nat --> nat)
           , ("plus", nat --> nat --> nat) 
           , ("iszero", nat --> bool)
           , ("pred", nat --> nat) ] ++ ifs n

ifs n = [("if"++show i, bool --> t) | (i,t) <- zip [0..] (ifs' n)]
  where ifs' 0 = []
        ifs' n = nat:bool:[x --> y | x <- ifs' (n-1), y <- ifs' (n-1)]

close [] t = t
close ((f,ty):bs) t = ULam f ty (close bs t)

test n = fromJust <$> runMGen go `suchThat` hasJustDepth (length ctx+n)
  where go = close ctx <$> mgenTerm 0 n ctx nat

        isArrow (Arrow _ _) = True
        isArrow _           = False

        hasJustDepth n Nothing = False
        hasJustDepth n (Just t) = size t >= n

        size (UVar _) = 1
        size (UApp t1 t2) = size t1 `max` size t2
        size (ULam _ _ t) = 1 + size t
  
        ctx = natCtx 2

main = sample $ test 5

--genApp = undefined
