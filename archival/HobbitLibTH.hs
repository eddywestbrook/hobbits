{-# LANGUAGE GADTs, TypeFamilies, EmptyDataDecls, MultiParamTypeClasses, TypeOperators, PackageImports, TemplateHaskell #-}

module HobbitLibTH (
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(), -- hides MultiBind implementation
  nu,
  mbNameBoundP, cmpName, mbCmpName,
  emptyMb,  elimEmptyMb, combineMb, separateMb, --mbRebind,
  mbInt, mbString, mbChar, mbInCtx,
  mbToplevel, SuperComb(), unSuperComb, superComb,

  -- things for using mbMatch
  --nApp,xformBody,pattVars,mbMatch,mbMatchRun,mbMatchFun,
  nuQQ
) where

import Unsafe.Coerce (unsafeCoerce)
import Data.List
import Data.Maybe
import Data.IORef
import System.IO.Unsafe(unsafePerformIO)
import Control.Applicative
import Language.Haskell.TH.Quote

-- we need template haskell, but we want to use Name ourselves
import Language.Haskell.TH hiding (Name)
import qualified Language.Haskell.TH as TH

import PattParser
import Ctx
    
import Control.DeepSeq
import "mtl" Control.Monad.Identity(Identity,runIdentity)
import Control.Monad

import qualified Data.Generics as SYB
import qualified Language.Haskell.TH.Syntax as TH
import qualified Control.Exception as CE

------------------------------------------------------------
-- fresh names
------------------------------------------------------------

type Nametype = Int

-- README: we *cannot* inline counter, because we want all uses
-- of counter to be the same IORef
counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

-- README: fresh_name takes a dummy argument that is used in a dummy
-- way to avoid let-floating its body (and thus getting a fresh name
-- exactly once)
-- README: it *is* ok to inline fresh_name because we don't care in
-- what order fresh names are created
fresh_name :: a -> Int
fresh_name a = unsafePerformIO $ do 
    dummyRef <- newIORef a
    x <- readIORef counter
    writeIORef counter (x+1)
    return x

------------------------------------------------------------
-- defining InCtx ctx a as the proofs that ctx has the form
-- (a1, (a2, ... (an, b))) where a = ai for some i
------------------------------------------------------------

------------------------------------------------------------
-- now we define our data-types
-- under the hood, names are just integers
------------------------------------------------------------

newtype Name a = MkName Int    deriving Eq
data Mb ctx b  = MkMb [Int] b
type Binding a = Mb (List1 a)

{-
instance Ord (Name a) where
    compare (MkName i) (MkName j) = compare i j

instance Ord b => Ord (Mb ctx b) where
    compare (MkMb _ b1) (MkMb _ b2) = compare b1 b2
-}

-- for benchmarking
instance NFData (Name a) where
    rnf (MkName i) = rnf i

-- for benchmarking
instance NFData a => NFData (Mb ctx a) where
    rnf (MkMb l x) = rnf l `seq` rnf x

------------------------------------------------------------
-- printing methods
------------------------------------------------------------

-- for printing things (debug only)
instance Show (Name a) where
  show (MkName n) = "#" ++ show n ++ "#"

-- note: we reverse l to show the inner-most bindings last
instance Show b => Show (Mb a b) where
  show (MkMb l b) = "#" ++ show (reverse l) ++ "." ++ show b

------------------------------------------------------------
-- simple operations for creating and manipulating bindings
------------------------------------------------------------

-- nu creates bindings
-- README: we pass f to fresh_name to avoid let-floating the results
-- of fresh_name (which would always give the same name for each nu)
-- README: is *is* ok to do CSE on multiple copies of nu, because
-- the programmer cannot tell if two distinct (non-nested) nus get the
-- same fresh integer, and two nus that look the same to the CSE engine
-- cannot be nested
-- README: it *is* ok to inline nu because we don't care in
-- what order fresh names are created
nu :: (Name a -> b) -> (Binding a b)
nu f = let n = fresh_name f in n `seq` MkMb [n] (f (MkName n))

-- combine binding of a binding into a single binding
-- README: inner-most bindings come FIRST
combineMb :: Mb ctx1 (Mb ctx2 b) -> Mb (ctx1 :++: ctx2) b
combineMb (MkMb l1 (MkMb l2 b)) = MkMb (l2++l1) b


-- separates inner-most binding
separateMb :: IsAppend ctx1 ctx2 ctx ->
              Mb ctx b -> Mb ctx1 (Mb ctx2 b)
separateMb isApp (MkMb l b) =
    MkMb (drop (isAppendLen isApp) l) (MkMb (take (isAppendLen isApp) l) b)

-- separates inner-most binding; old version
{-
separateMb :: Tag ctx1 -> Ctx ctx2 -> Mb (ctx1 :++: ctx2) b -> Mb ctx1 (Mb ctx2 b)
separateMb _ ctx (MkMb l b) =
    MkMb (drop (ctxLen ctx) l) (MkMb (take (ctxLen ctx) l) b)
-}

-- make an empty binding
emptyMb :: a -> Mb CtxNil a
emptyMb t = MkMb [] t

-- eliminate an empty binding
elimEmptyMb :: Mb CtxNil a -> a
elimEmptyMb (MkMb [] t) = t


------------------------------------------------------------
-- name-matching operations
------------------------------------------------------------

instance DepEq (Name a) (Name b) where
    depEq (MkName n1) (MkName n2) =
        if n1 == n2 then
            Just $ unsafeCoerce Refl
        else
            Nothing

instance DepOrd (Name a) (Name b) where
    depCompare (MkName n1) (MkName n2) =
        case compare n1 n2 of
          { LT -> DepLT ; GT -> DepGT ;
            EQ -> unsafeCoerce DepEQ }

-- README: these are WRONG because they do not consider alpha-equivalence
{-
instance DepEq a b => DepEq (Mb ctx a) (Mb ctx b) where
    depEq (MkMb _ n1) (MkMb _ n2) =
        case depEq n1 n2 of { Just eq -> Just (cong eq) ; Nothing -> Nothing }

instance DepOrd a b => DepOrd (Mb ctx a) (Mb ctx b) where
    depCompare (MkMb _ n1) (MkMb _ n2) =
        case depCompare n1 n2 of
          { DepLT -> DepLT ; DepGT -> DepGT ; DepEQ -> DepEQ }
-}

cmpName :: Name a -> Name b -> Maybe (a :=: b)
cmpName (MkName n1) (MkName n2) =
    if n1 == n2 then
        Just $ unsafeCoerce Refl
    else
        Nothing

-- this is for when we know the ith element of ctx must be type a
unsafeLookupCtx :: Int -> InCtx ctx a
unsafeLookupCtx n = helper $ inCtxFromLen n where
    helper :: ExInCtx -> InCtx ctx a
    helper (ExInCtx inCtx) = unsafeCoerce inCtx

-- mbNameBoundP checks if a name is bound in a multi-binding
mbNameBoundP :: Mb ctx (Name a) -> Either (InCtx ctx a) (Name a)
mbNameBoundP (MkMb names (MkName n)) =
  case (elemIndex n names) of
    Nothing -> Right (MkName n)
    Just i -> Left (unsafeLookupCtx i)

-- README: this can be defined outside of HobbitLib; it's here for convenience
mbCmpName :: Mb ctx (Name a) -> Mb ctx (Name b) -> Maybe (a :=: b)
mbCmpName b1 b2 =
    case (mbNameBoundP b1, mbNameBoundP b2) of
      (Left inCtx1, Left inCtx2) ->
          helper $ cmpInCtx inCtx1 inCtx2 where
              helper :: DepOrdering a b -> Maybe (a :=: b)
              helper DepEQ = Just Refl
              helper _ = Nothing
      (Right n1, Right n2) -> cmpName n1 n2
      _ -> Nothing


------------------------------------------------------------
-- re-binding names in terms
------------------------------------------------------------

-- FIXME: is this safe?
{-
mbRebind :: (Name a) -> b -> (Binding a b)
mbRebind (MkName i) b = MkMb [i] b
-}

------------------------------------------------------------
-- applying top-level functions under binders
------------------------------------------------------------

newtype SuperComb a = SuperComb { unSuperComb :: a }

-- | An quoted expression is a CAF if all of its names are bound globally or
-- within the quotation
isSuperComb :: Exp -> Bool
isSuperComb = SYB.everything (&&) (SYB.mkQ True nameOK) where
  nameOK (TH.Name _ flav) = case flav of
    TH.NameG {} -> True -- bound globally
    TH.NameU {} -> True -- bound within this same quotation
    _ -> False

superComb :: Q Exp -> Q Exp
superComb m = do
  e <- m
  if isSuperComb e then return (TH.AppE (TH.ConE 'SuperComb) e)
  else fail ("not a super combinator:\n\t" ++ TH.pprint e)

mbToplevel :: SuperComb (a -> b) -> Mb ctx a -> Mb ctx b
mbToplevel f (MkMb names i) = MkMb names (unSuperComb f i)


------------------------------------------------------------
-- special-purpose matching under binders
------------------------------------------------------------

mbInt :: Mb ctx Int -> Int
mbInt (MkMb _ i) = i

mbChar :: Mb ctx Char -> Char
mbChar (MkMb _ c) = c

mbString :: Mb ctx String -> String
mbString (MkMb _ str) = str

-- README: this could be defined outside HobbitLib in linear time,
-- but this does it in constant time (not that that matters anyway...)
mbInCtx :: Mb ctx (InCtx ctx2 a) -> InCtx ctx2 a
mbInCtx (MkMb _ inCtx) = inCtx

------------------------------------------------------------
-- generic matching under binders
------------------------------------------------------------
-- FIXME: this is all old stuff and should be removed

{-

-- dummy application operator to remove bindings; used to help
-- type inference for case expressions
nApp :: Mb ctx a -> x
nApp x = undefined

-- xformBody namesVar boundNames d  perofrms a generic traversal
-- of d to replace all occurrences of variables x in boundNames
-- by (MbMb namesVar x)
xformBody :: TH.Name -> [TH.Name] -> Data d => d -> d
xformBody namesVar boundNames d =
    case cast d of
      Just (VarE x) | elem x boundNames ->
          fromJust $ cast (AppE (ConE 'MkMb) $ AppE (VarE namesVar) $ VarE x)
      _ -> gmapT (xformBody namesVar boundNames) d

pattVars :: Data d => d -> [TH.Name]
pattVars d =
    case cast d of
      Just (VarP x) -> [x]
      _ -> gmapQl (++) [] pattVars d

addMkMbToPatt :: TH.Name -> Pat -> Pat
addMkMbToPatt n patt = ConP 'MkMb [VarP n, patt]

-- matching under bindings
mbMatch :: Q Exp -> Q Exp
mbMatch expQ =
    do exp <- expQ
       n <- newName "names"
       return $ helper n exp
    where helper n (CaseE (AppE (VarE app) scrut) cases) | app == 'nApp =
              CaseE scrut (map (case_helper n) cases)
          helper n _ = error "mbMatch can only be called on case expressions!"
          case_helper n (Match patt body decs) =
              Match (addMkMbToPatt n patt)
                    (xformBody n (pattVars patt) body) decs

mbMatchRun :: Q Exp -> IO Exp
mbMatchRun expQ = runQ (mbMatch expQ)

-- for top-level funs that match under bindings
mbMatchFun :: Q [Dec] -> Q [Dec]
mbMatchFun declsQ =
    do decls <- declsQ
       n <- newName "names"
       return $ map (helper n) decls
    where helper n (FunD f clauses) = FunD f (map (clause_helper n) clauses)
          helper n decl = decl
          clause_helper n (Clause patts body decls) =
              Clause (map (addMkMbToPatt n) patts)
                     (xformBody n (pattVars (head patts)) body) decls
-}

------------------------------------------------------------
-- matching under binders using a quasi-quoter
------------------------------------------------------------

hobbitNamesPattVar n = mkName $ "hobbit$$names" ++ (show n)

-- internPattVars replaces all subterms (VarP "x") with (MkMb ln -> VarP "x")
internPattVars :: TH.Name -> TH.Name -> Pat -> Pat
internPattVars mb ln = SYB.everywhere (SYB.mkT wrapVar) where
  wrapVar p = case p of
    VarP _ -> ViewP (InfixE
                     (Just $ VarE 'same_ctx `AppE` VarE mb)
                     (VarE '(.))
                     (Just $ ConE 'MkMb `AppE` VarE ln)) p
    _ -> p

syb_rnf :: SYB.Data a => a -> ()
syb_rnf = (`seq` ()) . rnf . SYB.gmapQ syb_rnf

same_ctx :: Mb ctx a -> Mb ctx b -> Mb ctx b
same_ctx _ x = x

nuQQPatt :: String -> Q Pat
nuQQPatt str = do
  mb <- newName "mb"
  ln <- newName "bs"
  pat <- runIO $ CE.evaluate (let x = parsePatt str in syb_rnf x `seq` x) `catch` \err ->
           (error $ "error parsing string |" ++ str ++ "|: " ++ show err)
  return $ AsP mb $ ConP 'MkMb [VarP ln, internPattVars mb ln pat]
        

nuQQ = QuasiQuoter (error "nuQQ Exp") nuQQPatt (error "nuQQ Type") (error "nuQQ Decs")
