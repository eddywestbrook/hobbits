{-# LANGUAGE GADTs, ExistentialQuantification #-}

import Term as HO
import TermTree as HOTree
import TermFList as HOFList

{-
import HoasTreeIO as HOASTree
import HoasFList as HOASFList
-}

import Bench.LocallyNameless as LN
import qualified Bench.DeBruijn as DB

import Bench.BigTerms

import Test.BenchPress
import Control.Monad(forM_)
import System.IO
import Unsafe.Coerce(unsafeCoerce)
import Control.DeepSeq

data ATerm = forall a. Box (HO.Term a)

testHobbit :: ATerm -> HO.Term b
testHobbit (Box (HO.Lam b)) =
  HO.subst (unsafeCoerce b) placeHolder
  where placeHolder = HO.lam $ \x -> HO.Var x

{-
data ATermTree = forall a. BoxTree (HOTree.Term a)

testHoasTree :: ATermTree -> HOASTree.Fresh (HOTree.Term b)
testHoasTree (BoxTree (HOTree.Lam b)) = do
  ph <- placeHolder
  HOTree.subst (unsafeCoerce b) ph
  where placeHolder = HOTree.lam $ \x -> HOTree.var x

data ATermFList = forall a. BoxFList (HOFList.Term a)

testHoasFList :: ATermFList -> HOASFList.Fresh (HOFList.Term b)
testHoasFList (BoxFList (HOFList.Lam b)) = do
  ph <- placeHolder
  HOFList.subst (unsafeCoerce b) ph
  where placeHolder = HOFList.lam $ \x -> HOFList.var x
-}

testLn :: LTerm -> LTerm
testLn (LN.Lam t) = instanciate placeHolder t
  where placeHolder = LN.Lam (LN.BVar 0)

testDb :: DB.LTerm -> DB.LTerm
testDb (DB.Lam t) = DB.substTop placeHolder t
  where placeHolder = DB.Lam (DB.Var 0)

-- benchmarking action
mybench iters action = do
  (stats, _) <- benchmark iters (return ()) (const $ return ()) (const action)
  return $ median stats

-- main loop
main = do
  putStrLn "size\tDB\tLN\tHobbit" -- \tHOASTree\tHOASFList"
  [0,100..10000::Int] `forM_` \i -> do    
    let db = bigLinearDB i
    let ln = bigLinearLN i
    let ho = bigLinearUntyped i
    let pr = HO.parse ho
    {-
    pr_tree <- HOASTree.runFresh $ (HOTree.parse ho)
    pr_flist <- HOASFList.runFresh $ (HOFList.parse ho)
    -}
    case (pr {- , pr_tree, pr_flist -}) of 
      (HO.SomeTerm t _ {-, HOTree.SomeTerm t_tree _, HOFList.SomeTerm t_list _-}) ->
        db `deepseq` ln `deepseq` t `deepseq` {- t_tree `deepseq` t_list `deepseq` -} do 
          t0 <- mybench 1 $ do
            let t' = testDb db
            deepseq t' (hPutStr stderr "")
            --hPutStrLn stderr $ show (testDb db)
            --hPutStrLn stderr $ show (DB.size $ testDb db)
          t1 <- mybench 1 $ do
            let t' = testLn ln
            deepseq t' (hPutStr stderr "")
            --hPutStrLn stderr $ show (testLn ln)
            --hPutStrLn stderr $ show (LN.size $ testLn ln)
          t2 <- mybench 1 $ do
            let t' = testHobbit (Box t)
            deepseq t' (hPutStr stderr "")
            --hPutStrLn stderr $ show t'
            --hPutStrLn stderr $ show (HO.size t')
          {-
          t3 <- mybench 1 $ do
            t' <- HOASTree.runFresh $ (testHoasTree (BoxTree t_tree))
            deepseq t' (hPutStr stderr "")
            --hPutStrLn stderr $ show t'
            --hPutStrLn stderr $ show (HOTree.size t')
          t4 <- mybench 1 $ do
            t' <- HOASFList.runFresh $ (testHoasFList (BoxFList t_list))
            deepseq t' (hPutStr stderr "")
            --hPutStrLn stderr $ show t'
            --hPutStrLn stderr $ show (HOFList.size t')
          -}
          putStrLn $ show i ++ "\t" ++ show t0 ++ "\t" ++ show t1 
                     ++ "\t" ++ show t2 -- ++ "\t" ++ show t3 ++ "\t" ++ show t4
