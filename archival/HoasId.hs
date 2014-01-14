{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, TypeFamilies, EmptyDataDecls, ScopedTypeVariables, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FlexibleInstances, ViewPatterns, ImplicitParams, TypeOperators, PackageImports #-}

module HoasId (
  InCtxt (..),
  Cons,List0,List1,List2,List3,List4,List5,First,Second,Third,Tail,(:++:),
  lookupCtx,
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(), -- hides MultiBind implementation
  nu,
  cmpName,mbCmpName,
  Fresh(Fresh),
  runFresh, unsafeRunFresh,
  emptyMb, combineMb, separateMb,
  mbInt,  mbRebind,
  mbToplevel, ToplevelFun, ToplevelRes, topFun,

  -- things for using mbMatch
  Tag(Tag),FTag(FTag),TFunApply,Repr(Repr),Args(ArgsNil,ArgsCons),ArgsMbMap,
  MbMatchable,toRepr,mbCtor,CtorsFun,MatchTpFun,
  mbMatch,

  -- things for CtxtFLists
  CtxtFList(CtxtFListBase,CtxtFListStep),ctxtFListSingle,(:|>),(|>),
  lookupCtxFList
) where

import Unsafe.Coerce
import Data.List
import Data.IORef
import System.IO.Unsafe(unsafePerformIO)
import Control.Applicative
    
import Test.StrictBench
import "mtl" Control.Monad.Identity(Identity,runIdentity)
import Control.Monad

------------------------------------------------------------
-- the fresh monad
------------------------------------------------------------
  
counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

newtype Fresh a = Fresh (Identity a)
  deriving (Monad,Functor)

instance Applicative Fresh where
  pure = return
  (<*>) = ap

runFresh :: Fresh a -> IO a
runFresh (Fresh m) = return $ runIdentity m

-- README: this is not actually unsafe for the Id monad
unsafeRunFresh :: Fresh a -> a
unsafeRunFresh (Fresh m) = runIdentity m

fresh_int :: () -> Fresh Int
{-# NOINLINE fresh_int #-}
fresh_int () = Fresh . return . unsafePerformIO $ do 
    x <- readIORef counter
    writeIORef counter (x+1)
    return x

------------------------------------------------------------
-- manipulating lists of types
-- note: we do right on the outside for efficiency of
-- adding a single binder inside another one
------------------------------------------------------------

type List0 = ()
type List1 a = ((), a)
type List2 a b = (((), b), a)
type List3 a b c = ((((), c), b), a)
type List4 a b c d = (((((), d), c), b), a)
type List5 a b c d e = ((((((), e), d), c), b), a)

type Cons a l = (l, a)

type family First a
type instance First (l, a) = a

type family Second a
type instance Second ((l, a2), a1) = a2

type family Third a
type instance Third (((l, a3), a2), a1) = a3

type family Tail a
type instance Tail (l, a) = l

type family (ctx1 :++: ctx2)
type instance ctx1 :++: () = ctx1
type instance ctx1 :++: (Cons a ctx2) = (Cons a (ctx1 :++: ctx2))

------------------------------------------------------------
-- defining InCtxt ctx a as the proofs that ctx has the form
-- (a1, (a2, ... (an, b))) where a = ai for some i
------------------------------------------------------------

-- proofs that a type is in a tuple-list of types
data InCtxt ctx a where
  InCtxtBase :: InCtxt (Cons a ctx) a
  InCtxtStep :: InCtxt ctx a -> InCtxt (Cons b ctx) a

instance Eq (InCtxt ctx a) where
  InCtxtBase      == InCtxtBase      = True 
  (InCtxtStep p1) == (InCtxtStep p2) = p1 == p2
  _               == _               = False

-- looking up a value in a tuple-list
lookupCtx :: InCtxt ctx a -> ctx -> a
lookupCtx InCtxtBase      (l, a) = a
lookupCtx (InCtxtStep pf) (l, a) = lookupCtx pf l

-- this is for when we know the ith element of ctx must be type a
unsafeLookupCtx :: Int -> InCtxt ctx a
unsafeLookupCtx 0 = unsafeCoerce InCtxtBase
unsafeLookupCtx n = unsafeCoerce (InCtxtStep (unsafeLookupCtx (n-1)))

------------------------------------------------------------
-- now we define our data-types
-- under the hood, names are just integers
------------------------------------------------------------

data Name a    = MkName Int    deriving Eq
data Mb ctx b  = MkMb [Int] b  deriving Eq
type Binding a = Mb (List1 a)

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

instance Show b => Show (Mb a b) where
  show (MkMb l b) = "#" ++ show l ++ "." ++ show b

instance Show b => Show (InCtxt ctx b) where
  show InCtxtBase      = "InCtxtBase"
  show (InCtxtStep pf) = "InCtxtStep (" ++ show pf ++ ")"

------------------------------------------------------------
-- simple operations for creating and manipulating bindings
------------------------------------------------------------

-- nu creates bindings
nu :: (Name a -> Fresh b) -> Fresh (Binding a b)
nu f = do
  i <- fresh_int () 
  i `seq` MkMb [i] <$> (f $ MkName i)

-- combine binding of a binding into a single binding
-- README: inner-most bindings come FIRST
combineMb :: Mb ctx1 (Mb ctx2 b) -> Mb (ctx1 :++: ctx2) b
combineMb (MkMb l1 (MkMb l2 b)) = MkMb (l2++l1) b

-- separates inner-most binding
separateMb :: Mb (ctx :++: List1 a) b -> Mb ctx (Binding a b)
separateMb (MkMb (a:l) b) = MkMb l (MkMb [a] b)

-- make an empty binding
emptyMb :: a -> Mb () a
emptyMb t = MkMb [] t

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

-- name_multi_bind_cmp checks if a name is bound in a multi-binding
mbCmpName 
  :: Mb ctx (Name a)
  -> Either (InCtxt ctx a) (Name a)

mbCmpName (MkMb names (MkName n)) =
  helper (elemIndex n names)
  where helper Nothing  = Right (MkName n)
        helper (Just i) = Left (unsafeLookupCtx i)


------------------------------------------------------------
-- re-binding names in terms
------------------------------------------------------------

mbRebind :: (Name a) -> b -> (Binding a b)
mbRebind (MkName i) b = MkMb [i] b


------------------------------------------------------------
-- applying top-level functions under binders
------------------------------------------------------------

class ToplevelFun tag a where
    type ToplevelRes tag a
    topFun :: Tag tag -> a -> ToplevelRes tag a

mbToplevel :: ToplevelFun tag a => Tag tag -> Mb ctx a -> Mb ctx (ToplevelRes tag a)
mbToplevel tag (MkMb names i) = MkMb names (topFun tag i)


------------------------------------------------------------
-- special-purpose matching under binders
------------------------------------------------------------

mbInt :: Mb ctx Int -> Int
mbInt (MkMb _ i) = i


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
    Repr :: Tag z -> InCtxt (TFunApply f z) (args, a) -> Args args -> Repr f a

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
    mbCtor :: Tag z -> Tag ctx -> InCtxt (TFunApply (CtorsFun a) z) (args, a) ->
              ArgsMbMap ctx args (TFunApply (MatchTpFun a) ctx)

-- matching under bindings
mbMatch :: MbMatchable a => Tag ctx -> Mb ctx a -> TFunApply (MatchTpFun a) ctx
mbMatch ctxT (MkMb names x) =
    case toRepr x of
      Repr zT in_ctors args ->
          argsMapApply ctxT Tag (MkMb names) (mbCtor zT ctxT in_ctors) args

-- helper function for applying a function to arguments
argsMapApply :: Tag ctx -> Tag ret -> (forall x. x -> Mb ctx x) ->
                ArgsMbMap ctx args ret -> Args args -> ret
argsMapApply ctxT rT addMb f ArgsNil = f
argsMapApply ctxT rT addMb f (ArgsCons x args) = argsMapApply ctxT rT addMb (f (addMb x)) args


------------------------------------------------------------
-- lists of things that match the context
------------------------------------------------------------

data CtxtFList f ctx where
    CtxtFListBase :: CtxtFList f ()
    CtxtFListStep :: f a -> CtxtFList f ctx -> CtxtFList f (Cons a ctx)

ctxtFListSingle :: f a -> CtxtFList f (List1 a)
ctxtFListSingle x = CtxtFListStep x CtxtFListBase

-- FIXME: I think this is now just Cons...
type ctx :|> a = (Cons a ctx)
--type ctx :|> a = ctx :++: (List1 a)

(|>) :: CtxtFList f ctx -> f a -> CtxtFList f (ctx :|> a)
l |> y = CtxtFListStep y l
--CtxtFListBase      |> y = single y
--CtxtFListStep x xs |> y = CtxtFListStep x (xs |> y)

lookupCtxFList :: InCtxt ctx a -> CtxtFList f ctx -> f a
lookupCtxFList InCtxtBase     (CtxtFListStep x _ ) = x
lookupCtxFList (InCtxtStep p) (CtxtFListStep _ xs) = lookupCtxFList p xs
--lookupCtxFList _                       _           = error "never happens"
