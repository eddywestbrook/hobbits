{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, TypeFamilies, EmptyDataDecls, ScopedTypeVariables, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FlexibleInstances, ViewPatterns, ImplicitParams, TypeOperators, UndecidableInstances #-}

module HoasFListIO (
  InList (..),InCtxt(),
  Cons,List0,List1,List2,List3,List4,List5,First,Second,Third,Tail,(:++:),
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(), -- hides MultiBind implementation
  nu,
  cmpName,cmpInCtxt,mbCmpName,inCtxtToPf,
  Fresh(),
  runFresh, unsafeRunFresh,
  emptyMb, combineMb, --separateMb,
  mbInt,  --mbRebind,
  mbToplevel, ToplevelFun, ToplevelRes, topFun,

  -- things related to All
  -- FIXME: use or remove
  --Compose(),MbF(),mbAll,

  -- things for using mbMatch
  Tag(Tag),FTag(FTag),TFunApply,Repr(Repr),Args(ArgsNil,ArgsCons),ArgsMbMap,
  MbMatchable,toRepr,mbCtor,CtorsFun,MatchTpFun,
  mbMatch,

  -- things for CtxtFLists
  CtxtFList,ctxtFListNil,ctxtFListSingle,(:|>:),(|>),
  lookupCtxtFList,ctxtFListMap
) where

import Unsafe.Coerce ( unsafeCoerce )
import Data.List ( elemIndex )
import Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import System.IO.Unsafe ( unsafePerformIO )
import Control.Applicative ( Applicative, (<$>) )
import Test.StrictBench ( NFData(..) )

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

------------------------------------------------------------
-- the fresh monad
------------------------------------------------------------
  
counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

newtype Fresh a = Fresh (IO a)
  deriving(Monad,Applicative,Functor)

runFresh :: Fresh a -> IO a
runFresh (Fresh m) = m

-- README: this should not really be used except for debugging; it is unsafe
unsafeRunFresh :: Fresh a -> a
unsafeRunFresh (Fresh m) = unsafePerformIO m

fresh_int :: Fresh Int
fresh_int = Fresh $ do
  n <- readIORef counter
  () <- writeIORef counter (n+1)
  return n

------------------------------------------------------------
-- manipulating lists of types
-- note: we do right on the outside for efficiency of
-- adding a single binder inside another one
------------------------------------------------------------

------------------------------------------------------------
-- manipulating lists of types
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
type instance Nil :++: ctx2 = ctx2
type instance (Cons a ctx1) :++: ctx2 = (Cons a (ctx1 :++: ctx2))

-- this is for when we know the ith element of ctx must be type a
unsafeLookupList :: Int -> InList ctx a
unsafeLookupList 0 = unsafeCoerce InListBase
unsafeLookupList n = unsafeCoerce (InListStep (unsafeLookupList (n-1)))

------------------------------------------------------------
-- now we define our data-types
-- under the hood, names are just integers
-- Mb ctx is just an integer giving the length of ctx, along with
-- an IntMap mapping names to where they are in ctx
------------------------------------------------------------

data Name a    = MkName Int    deriving Eq
data Mb ctx b  = MkMb Int (IntMap Int) b  deriving Eq
type Binding a = Mb (List1 a)

-- for benchmarking
instance NFData (Name a) where
    rnf (MkName n) = rnf n

-- for benchmarking
instance NFData a => NFData (Mb ctx a) where
    rnf (MkMb n map x) = rnf n `seq` rnf map `seq` rnf x

------------------------------------------------------------
-- printing methods
------------------------------------------------------------

-- for printing things (debug only)
instance Show (Name a) where
  show (MkName n) = "#" ++ show n ++ "#"

instance Show b => Show (Mb a b) where
  show (MkMb n map b) = "#" ++ show map ++ "." ++ show b

instance Show b => Show (InList ctx b) where
  show InListBase      = "InListBase"
  show (InListStep pf) = "InListStep (" ++ show pf ++ ")"

------------------------------------------------------------
-- simple operations for creating and manipulating bindings
------------------------------------------------------------

-- nu creates bindings
nu :: (Name a -> Fresh b) -> Fresh (Binding a b)
nu f = fresh_int >>= \n -> MkMb 1 (IntMap.singleton n 0) <$> (f $ MkName n) 

-- combine binding of a binding into a single binding
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

-- unsafe, hidden proofs that a type is in a context
data InCtxt ctx a = InCtxt Int deriving (Eq)

-- polymorphic equality testing
cmpInCtxt :: InCtxt ctx1 a1 -> InCtxt ctx2 a2 -> Bool
cmpInCtxt (InCtxt i1) (InCtxt i2) = i1 == i2

-- name_multi_bind_cmp checks if a name is bound in a multi-binding
mbCmpName :: Mb ctx (Name a) -> Either (InCtxt ctx a) (Name a)
mbCmpName (MkMb size map (MkName n)) =
    case IntMap.lookup n map of
      Just i -> Left (InCtxt i)
      Nothing -> Right (MkName n)

-- in case anyone actually wants to build a proof
inCtxtToPf :: InCtxt ctx a -> InList ctx a
inCtxtToPf (InCtxt i) = unsafeLookupList i


------------------------------------------------------------
-- re-binding names in terms
------------------------------------------------------------

--mbRebind :: (Name a) -> b -> (Binding a b)
--mbRebind (MkName i) b = MkMb [i] b


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
    mbCtor :: Tag z -> Tag ctx -> InCtxt (TFunApply (CtorsFun f) z) (args, f x) ->
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
-- this is an unsafe version, that is just a list
------------------------------------------------------------

data Ex f where Ex :: Tag x -> f x -> Ex f

type CtxtFList f ctx = (Int, IntMap (Ex f))

ctxtFListNil :: CtxtFList f Nil
ctxtFListNil = (0, IntMap.empty)

ctxtFListSingle :: f a -> CtxtFList f (List1 a)
ctxtFListSingle x = (1, IntMap.singleton 0 (Ex Tag x))

-- FIXME: I think this is now just Cons...
--type ctx :|> a = (Cons a ctx)
type ctx :|>: a = ctx :++: (List1 a)

(|>) :: CtxtFList f ctx -> f a -> CtxtFList f (ctx :|>: a)
(num, map) |> x = (num+1, IntMap.insert num (Ex Tag x) map)

lookupCtxtFList :: InCtxt ctx a -> CtxtFList f ctx -> f a
lookupCtxtFList (InCtxt i) (_, map) = unsafeUnEx (IntMap.lookup i map) where
    unsafeUnEx (Just (Ex _ x)) = unsafeCoerce x
    unsafeUnEx Nothing = error "bad InCtxt proof!"

ctxtFListMap :: (forall x. f x -> g x) -> CtxtFList f ctx -> CtxtFList g ctx
ctxtFListMap f (num, map) = (num, IntMap.map (exmap f) map) where
    exmap :: (forall x. f x -> g x) -> Ex f -> Ex g
    exmap f (Ex tag x) = Ex tag (f x)
