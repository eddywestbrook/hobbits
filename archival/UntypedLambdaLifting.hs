module UntypedLambdaLifting where

import Data.List

data Term = Var String | App Term Term | Lam String Term
  deriving(Show)

lams xs t = foldr Lam t xs
apps t us = foldl App t us

data Skel = SHole | SCVar String | SVar String | SApp Skel Skel

sapps t us = foldl SApp t us

type Ctx = [String]


-- cs is Gamma1
-- bs is Gamma2
ll :: Ctx -> Ctx -> Term -> ([Skel],Ctx,Skel)
ll cs bs (Lam x t) = ll cs (bs++[x]) t
ll cs bs t         = ll' cs bs t

ll' cs bs t = (llts ++ [lams (cvars++bs) skel], cvars, sapps SHole (map SVar cvars))
  where cvars = (fvt \\ bs) `intersect` cs
        (llts,skel,fvt) = ll'' (cs++bs) t

ll'' = undefined