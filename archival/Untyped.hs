module Untyped where

data Ty    = Base Int | Arrow Ty Ty deriving (Eq)
data UTerm = UApp UTerm UTerm | ULam String Ty UTerm | UVar String

instance Show Ty where
    show (Base i) = "a" ++ show i
    show (Arrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

instance Show UTerm where
    show (UVar x) = x
--    show (ULam x ty t) = "(\\" ++ x ++ ":" ++ show ty ++ "." ++ show t ++ ")"
    show (ULam x ty t) = "(\\" ++ x ++ ":_." ++ show t ++ ")"
    show (UApp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
