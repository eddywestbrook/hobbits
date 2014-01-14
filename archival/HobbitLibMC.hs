{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, TypeFamilies, EmptyDataDecls, ScopedTypeVariables, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FlexibleInstances, ViewPatterns, ImplicitParams, TypeOperators, PackageImports #-}

module HobbitLibMC (
  InList (..),
  Nil,Cons,List0,List1,List2,List3,List4,List5,First,Second,Third,Tail,(:++:),
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(MkMb), -- shows MultiBind implementation (be very, very careful!)
  nu,
  cmpName, mbCmpName, InCtx(), sameLength, inCtxToPf,
  emptyMb, combineMb, --separateMb,
  mbInt, mbBool, mbString,
  mbToplevel, ToplevelFun, ToplevelRes, topFun,

  -- things for using mbMatch
  Tag(Tag),FTag(FTag),TFunApply,Repr(Repr),Args(ArgsNil,ArgsCons),ArgsMbMap,
  MbMatchable,toRepr,mbCtor,CtorsFun,MatchTpFun,
  mbMatch,

  -- things for CtxFLists
  MapCtx(), ctxSingle, emptyMC, (|>), (:|>), ctxLookup, ctxMap
) where

import Unsafe.Coerce
import Data.List
import Data.IORef
import System.IO.Unsafe(unsafePerformIO)
import Control.Applicative
    
--import Test.StrictBench
import Control.DeepSeq
import "mtl" Control.Monad.Identity(Identity,runIdentity)
import Control.Monad

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

------------------------------------------------------------
-- fresh names
------------------------------------------------------------

type Nametype = Int

counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

fresh_name :: () -> Int
{-# NOINLINE fresh_name #-}
fresh_name () = unsafePerformIO $ do 
    x <- readIORef counter
    writeIORef counter (x+1)
    return x

------------------------------------------------------------
-- manipulating lists of types
-- note: we do right on the outside for efficiency of
-- adding a single binder inside another one
------------------------------------------------------------

data Nil
data Cons a l

-- proofs that a type is in a tuple-list of types
data InList ctx a where
  InListBase :: InList (Cons a ctx) a
  InListStep :: InList ctx a -> InList (Cons b ctx) a

instance Eq (InList ctx a) where
  InListBase      == InListBase      = True 
  (InListStep p1) == (InListStep p2) = p1 == p2
  _               == _               = False


-- useful helper functions
type List0 = Nil
type List1 a = (Cons a Nil)
type List2 a b = (Cons a (Cons b Nil))
type List3 a b c = (Cons a (Cons b (Cons c Nil)))
type List4 a b c d = (Cons a (Cons b (Cons c (Cons d Nil))))
type List5 a b c d e = (Cons a (Cons b (Cons c (Cons d (Cons e Nil)))))

type family First a
type instance First (Cons a l) = a

type family Second a
type instance Second (Cons a1 (Cons a2 l)) = a2

type family Third a
type instance Third (Cons a1 (Cons a2 (Cons a3 l))) = a3

type family Tail a
type instance Tail (Cons a l) = l

type family (ctx1 :++: ctx2)
type instance ctx1 :++: () = ctx1
type instance ctx1 :++: (Cons a ctx2) = (Cons a (ctx1 :++: ctx2))

-- this is for when we know the ith element of ctx must be type a
unsafeLookupList :: Int -> InList ctx a
unsafeLookupList 0 = unsafeCoerce InListBase
unsafeLookupList n = unsafeCoerce (InListStep (unsafeLookupList (n-1)))

------------------------------------------------------------
-- now we define our data-types
-- under the hood, names are just integers
-- Mb ctx is just an integer giving the length of ctx, along with
-- an IntMap mapping names to where they are in ctx
-- note that this essentially is a deBruijn _level_ interpretation,
-- though the external interface (i.e. MapCtx) makes it look
-- like deBruijn indices
------------------------------------------------------------

data Name a    = MkName (Int)    deriving Eq
data Mb ctx b  = MkMb Int (IntMap Int) b  deriving Eq
type Binding a = Mb (List1 a)

-- for benchmarking
instance NFData (IORef a) where
    rnf ref = ref `seq` ()

instance NFData (Name a) where
    rnf (MkName i) = rnf i

-- for benchmarking
instance NFData a => NFData (Mb ctx a) where
    rnf (MkMb n map x) = rnf n `seq` rnf map `seq` rnf x

------------------------------------------------------------
-- printing methods
------------------------------------------------------------

-- for printing things (debug only)
{-
instance Show (Name a) where
  show (MkName n) = "#" ++ show n ++ "#"

instance Show b => Show (Mb a b) where
  show (MkMb l b) = "#" ++ show l ++ "." ++ show b
-}

instance Show b => Show (InList ctx b) where
  show InListBase      = "InListBase"
  show (InListStep pf) = "InListStep (" ++ show pf ++ ")"

------------------------------------------------------------
-- simple operations for creating and manipulating bindings
------------------------------------------------------------

-- nu creates bindings
nu :: (Name a -> b) -> (Binding a b)
nu f = let n = fresh_name () in
       MkMb 1 (IntMap.singleton n 0) (f (MkName n))

-- combine binding of a binding into a single binding
-- README: inner-most bindings come FIRST
combineMb :: Mb ctx1 (Mb ctx2 a) -> Mb (ctx1 :++: ctx2) a
combineMb (MkMb n1 map1 (MkMb n2 map2 a)) =
    MkMb (n1 + n2) (IntMap.foldWithKey (\k pos map -> IntMap.insert k (pos + n1) map) map1 map2) a

-- separates inner-most binding
--separateMb :: Mb (ctx :++: List1 a) b -> Mb ctx (Binding a b)
--separateMb (MkMb (a:l) b) = MkMb l (MkMb [a] b)

-- make an empty binding
emptyMb :: a -> Mb () a
emptyMb t = MkMb 0 IntMap.empty t

------------------------------------------------------------
-- name-matching operations
------------------------------------------------------------

data a :=: b where
  TEq :: (a ~ b) => a :=: b

cmpName :: Name a -> Name b -> Maybe (a :=: b)
cmpName (MkName n1) (MkName n2) =
    if n1 == n2 then
        Just $ unsafeCoerce TEq
    else
        Nothing

-- unsafe rep of an InCtx proof as an int specifying how long the proof ixs
data InCtx ctx a = InCtx Int
  deriving (Eq)

sameLength :: InCtx ctx1 a1 -> InCtx ctx2 a2 -> Bool
sameLength (InCtx i1) (InCtx i2) = i1 == i2

-- mbCmpName checks if a name is bound in a multi-binding
-- if so, it returns an opaque InCtx proof, which is just an
-- integer giving the deBruijn index of the name in the Mb;
-- note we must compute size - i - 1 to convert the deBruijn
-- levels in map to deBruijn indices
mbCmpName :: Mb ctx (Name a) -> Either (InCtx ctx a) (Name a)
mbCmpName (MkMb size map (MkName n)) =
    case IntMap.lookup n map of
      Just i -> Left (InCtx (size - i - 1))
      Nothing -> Right (MkName n)

-- in case anyone actually wants to build a proof
inCtxToPf :: InCtx ctx a -> InList ctx a
inCtxToPf (InCtx i) = unsafeLookupList i

------------------------------------------------------------
-- applying top-level functions under binders
------------------------------------------------------------

class ToplevelFun tag a where
    type ToplevelRes tag a
    topFun :: Tag tag -> a -> ToplevelRes tag a

mbToplevel :: ToplevelFun tag a => Tag tag -> Mb ctx a -> Mb ctx (ToplevelRes tag a)
mbToplevel tag (MkMb num map a) = MkMb num map (topFun tag a)


------------------------------------------------------------
-- special-purpose matching under binders
------------------------------------------------------------

mbInt :: Mb ctx Int -> Int
mbInt (MkMb _ _ i) = i

mbBool :: Mb ctx Bool -> Bool
mbBool (MkMb _ _ b) = b

mbString :: Mb ctx String -> String
mbString (MkMb _ _ str) = str


------------------------------------------------------------
-- generic matching under binders
------------------------------------------------------------

-- for supplying type arguments
data Tag a = Tag
data FTag (f :: * -> *) = FTag

-- user-extensible function for applying the type function ftag to args
type family TFunApply f targs

-- abstract representation of a (G)ADT
data Repr f a where
    Repr :: Tag z -> InList (TFunApply f z) (args, a) -> Args args -> Repr f a

-- this is essentially a value representation of a nested tuple type
data Args args where
    ArgsNil :: Args List0
    ArgsCons :: a -> Args args -> Args (Cons a args)

-- mapping (Mb ctx) over nested arrow types and replacing the ret value with ret
type family ArgsMbMap ctx args ret
type instance ArgsMbMap ctx List0 ret = ret
type instance ArgsMbMap ctx (Cons a args) ret = Mb ctx a -> ArgsMbMap ctx args ret

-- type class stating that FIXME
{-
class MbMatchable (f :: * -> *) where
    type CtorsFun f -- type function to get ctors list
    type MatchTpFun f :: * -> * -> * -- type function to get match result type
    toRepr :: f x -> Repr (CtorsFun f) (f x)
    mbCtor :: Tag z -> Tag ctx -> InList (TFunApply (CtorsFun f) z) (args, f x) ->
              ArgsMbMap ctx args (MatchTpFun f ctx x)
-}

class MbMatchable a where
    type CtorsFun a -- type function to get ctors list
    type MatchTpFun a -- type function to get match result type
    toRepr :: a -> Repr (CtorsFun a) a
    mbCtor :: Tag z -> Tag ctx -> InList (TFunApply (CtorsFun a) z) (args, a) ->
              ArgsMbMap ctx args (TFunApply (MatchTpFun a) ctx)

-- matching under bindings
mbMatch :: MbMatchable a => Tag ctx -> Mb ctx a -> TFunApply (MatchTpFun a) ctx
mbMatch ctxT (MkMb num map x) =
    case toRepr x of
      Repr zT in_ctors args ->
          argsMapApply ctxT Tag (MkMb num map) (mbCtor zT ctxT in_ctors) args

-- helper function for applying a function to arguments
argsMapApply :: Tag ctx -> Tag ret -> (forall x. x -> Mb ctx x) ->
                ArgsMbMap ctx args ret -> Args args -> ret
argsMapApply ctxT rT addMb f ArgsNil = f
argsMapApply ctxT rT addMb f (ArgsCons x args) = argsMapApply ctxT rT addMb (f (addMb x)) args


------------------------------------------------------------
-- lists of things that match the context
------------------------------------------------------------

data Ex f where Ex :: Tag x -> f x -> Ex f

type MapCtx f ctx = (Int, IntMap (Ex f))

emptyMC :: MapCtx f Nil
emptyMC = (0, IntMap.empty)

ctxSingle :: f a -> MapCtx f (List1 a)
ctxSingle x = (1, IntMap.singleton 0 (Ex Tag x))

type ctx :|> a = ctx :++: (List1 a)

(|>) :: MapCtx f ctx -> f a -> MapCtx f (ctx :|> a)
(num, map) |> x = (num+1, IntMap.insert num (Ex Tag x) map)

-- README: trickiness with ctxLookup: InCtx proofs here are essentially
-- deBruijn _indices_, but the IntMap in MapCtx maps deBruijn _levels_
-- (because these do not change on insert); to convert between the two
-- you subtract from the current size of the IntMap (and also subtract 1
-- because we are 0-based)
ctxLookup :: InCtx ctx a -> MapCtx f ctx -> f a
ctxLookup (InCtx i) (size, map) = unsafeUnEx (IntMap.lookup (size - i - 1) map) where
    unsafeUnEx (Just (Ex _ x)) = unsafeCoerce x
    unsafeUnEx Nothing = error "bad InCtx proof!"

ctxMap :: (forall x. f x -> g x) -> MapCtx f ctx -> MapCtx g ctx
ctxMap f (num, map) = (num, IntMap.map (exmap f) map) where
    exmap :: (forall x. f x -> g x) -> Ex f -> Ex g
    exmap f (Ex tag x) = Ex tag (f x)

--MapCtx f ctx1 -> MapCtx f ctx2 -> MapCtx f (ctx1 :++: ctx2)
