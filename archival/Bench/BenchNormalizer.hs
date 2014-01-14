{-# LANGUAGE CPP, GADTs #-}

--import qualified TermNoHack as HO1
--import qualified TermHack   as HO2
import qualified TermTH     as HO3

import Bench.BigTerms
import Bench.LocallyNameless as LN
import qualified Bench.DeBruijn as DB
import Untyped

import Test.BenchPress
import Control.Monad(forM_)
import System.IO
import Control.DeepSeq
import Unsafe.Coerce(unsafeCoerce)

-- bigTermHobbitNoHack n = 
--   case big of HO1.SomeTerm t _ -> (unsafeCoerce t) `HO1.App` idt
--   where big = HO1.parse $ bigLinearUntyped2 n
--         idt = HO1.lam $ \x -> HO1.Var x
-- bigTermHobbitHack n = 
--   case big of HO2.SomeTerm t _ -> (unsafeCoerce t) `HO2.App` idt
--   where big = HO2.parse $ bigLinearUntyped2 n
--         idt = HO2.lam $ \x -> HO2.Var x
bigTerm n = UApp (bigLinearUntyped2 n)
                 (ULam "x" (Arrow (Base 0) (Base 0)) $ UVar "x")
bigTermHobbitTH n = case HO3.parse (bigTerm n) of
                      HO3.SomeTerm t _ -> (unsafeCoerce t)
bigTermDb n = DB.parseTop $ bigTerm n
bigTermLn n = LN.parseTop $ bigTerm n

bigTerm3 n = UApp (bigLinearUntyped3 n)
                  (ULam "x" (Arrow (Base 0) (Base 0)) $ UVar "x")
bigTermHobbitTH3 n = case HO3.parse (bigTerm3 n) of
                       HO3.SomeTerm t _ -> (unsafeCoerce t)
bigTermDb3 n = DB.parseTop $ bigTerm3 n
bigTermLn3 n = LN.parseTop $ bigTerm3 n

bigTerm4 n = UApp (bigLinearUntyped4 n)
                  (ULam "x" (Arrow (Base 0) (Base 0)) $ UVar "x")
bigTermHobbitTH4 n = case HO3.parse (bigTerm4 n) of
                       HO3.SomeTerm t _ -> (unsafeCoerce t)
bigTermDb4 n = DB.parseTop $ bigTerm4 n
bigTermLn4 n = LN.parseTop $ bigTerm4 n


--bigChurchHobbitNoHack n = HO1.plus `HO1.App` HO1.toChurch n `HO1.App` HO1.toChurch n
--bigChurchHobbitHack   n = HO2.plus `HO2.App` HO2.toChurch n `HO2.App` HO2.toChurch n
bigChurchHobbitTH     n = HO3.plus `HO3.App` HO3.toChurch n `HO3.App` HO3.toChurch n
bigChurchLn n = LN.plus LN.:@ LN.toChurch n LN.:@ LN.toChurch n
bigChurchDb n = DB.plus DB.:@ DB.toChurch n DB.:@ DB.toChurch n

bigTerms = [(i, bigTermDb i, bigTermLn i, {- bigTermHobbitNoHack i, bigTermHobbitHack i, -} bigTermHobbitTH i) | i <- [10,20..400::Int]]
bigTerms3 = [(i, bigTermDb3 i, bigTermLn3 i, bigTermHobbitTH3 i) | i <- [10,20..400::Int]]
bigTerms4 = [(i, bigTermDb4 i, bigTermLn4 i, bigTermHobbitTH4 i) | i <- [10,20..400::Int]]
bigChurchs = [(i, bigChurchDb i, bigChurchLn i, {- bigChurchHobbitNoHack i, bigChurchHobbitHack i, -} bigChurchHobbitTH i) | i <- [1..50::Int]]

{-# NOINLINE mybench #-}
mybench action = do
  (stats, _) <- benchmark 10 (return ()) (const $ return ()) (const action)
  return $ median stats

putErr = hPutStr stderr
force x = x `deepseq` putErr ""

allTests terms = 
  terms `forM_` \(i,db,ln,{- ho1,ho2, -} ho3) -> do
    db `deepseq` ln `deepseq` {- ho1 `deepseq` ho2 `deepseq` -} ho3 `deepseq` do
      t0 <- mybench (force $ DB.norm db)
      t1 <- mybench (force $ LN.runFresh (LN.norm ln))
      {-
      t2 <- mybench (force (HO1.norm ho1))
      t3 <- mybench (force (HO2.norm ho2))
      -}
      t4 <- mybench (force (HO3.norm ho3))
      putStrLn $ show i ++ "\t" ++ show t0 ++ "\t" ++ show t1 ++ "\t" ++ {- show t2 ++ "\t" ++ show t3 ++ "\t" ++ -} show t4

main = do
  putStrLn "#church numerals"
  putStrLn "#size\tDB\tLN\thobbit_th" 
  allTests bigChurchs

  putStrLn "#big linear terms"
  putStrLn "#size\tDB\tLN\thobbit_th" 
  allTests bigTerms

  putStrLn "#big linear terms v3"
  putStrLn "#size\tDB\tLN\thobbit_th" 
  allTests bigTerms3

  putStrLn "#big linear terms v4"
  putStrLn "#size\tDB\tLN\thobbit_th" 
  allTests bigTerms4

