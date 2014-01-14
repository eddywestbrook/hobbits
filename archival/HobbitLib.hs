{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, TypeFamilies, EmptyDataDecls, ScopedTypeVariables, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FlexibleInstances, ViewPatterns, ImplicitParams, TypeOperators, PackageImports #-}

module HobbitLib (
  InList (..),
  Nil,Cons,List0,List1,List2,List3,List4,List5,First,Second,Third,Tail,(:++:),
  Ctx (CtxNil, CtxCons), ctxAppend, IsAppend (IsAppendBase,IsAppendStep),
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(), -- hides MultiBind implementation
  nu,
  cmpName, (:=:)(TEq), cmpNameBool, mbCmpName, InCtx, cmpInCtx, cmpInCtxBool,
  inCtxSameLength,
  emptyMb, combineMb, separateMb,
  mbInt, mbBool, mbString,
  mbToplevel, ToplevelFun, ToplevelRes, topFun,

  -- things for using mbMatch
  Tag(Tag),FTag(FTag),TFunApply,Repr(Repr),Args(ArgsNil,ArgsCons),ArgsMbMap,
  MbMatchable,toRepr,mbCtor,CtorsFun,MatchTpFun,
  mbMatch,

  -- things for CtxFLists
  MapCtx(..), emptyMC, ctxSingle, (|>), (:|>), ctxLookup, ctxMap, (|++>)
) where

import Unsafe.Coerce
import Data.List
import Data.IORef
import System.IO.Unsafe(unsafePerformIO)
import Control.Applicative
    
--import Test.StrictBench
import "mtl" Control.Monad.Identity(Identity,runIdentity)
import Control.Monad
import Control.DeepSeq

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

-- phantom type for type lists
data Ctx ctx where
    CtxNil :: Ctx Nil
    CtxCons :: Tag a -> Ctx l -> Ctx (Cons a l)

-- proofs that a tuple-list of types is the append of two others
data IsAppend ctx1 ctx2 ctx where
  IsAppendBase :: IsAppend ctx Nil ctx
  IsAppendStep :: IsAppend ctx1 ctx2 ctx -> IsAppend ctx1 (Cons x ctx2) (Cons x ctx)

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
type instance ctx1 :++: Nil = ctx1
type instance ctx1 :++: (Cons a ctx2) = (Cons a (ctx1 :++: ctx2))

-- appending two context representations
ctxAppend :: Ctx ctx1 -> Ctx ctx2 -> Ctx (ctx1 :++: ctx2)
ctxAppend ctx1 CtxNil = ctx1
ctxAppend ctx1 (CtxCons tag ctx2) = CtxCons tag (ctxAppend ctx1 ctx2)


-- this is for when we know the ith element of ctx must be type a
unsafeLookupList :: Int -> InList ctx a
unsafeLookupList 0 = unsafeCoerce InListBase
unsafeLookupList n = unsafeCoerce (InListStep (unsafeLookupList (n-1)))


------------------------------------------------------------
-- now we define our data-types
-- under the hood, names are just integers
------------------------------------------------------------

data Name a    = MkName (Nametype)    deriving Eq
data Mb ctx b  = MkMb [Nametype] b  deriving Eq
type Binding a = Mb (List1 a)

-- for benchmarking
instance NFData (IORef a) where
    rnf ref = ref `seq` ()

instance NFData (Name a) where
    rnf (MkName i) = rnf i

-- for benchmarking
instance NFData a => NFData (Mb ctx a) where
    rnf (MkMb l x) = rnf l `seq` rnf x

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
nu f = let n = fresh_name () in n `seq` MkMb [n] (f (MkName n))

-- combine binding of a binding into a single binding
-- README: inner-most bindings come FIRST
combineMb :: Mb ctx1 (Mb ctx2 b) -> Mb (ctx1 :++: ctx2) b
combineMb (MkMb l1 (MkMb l2 b)) = MkMb (l2++l1) b

-- separates inner-most binding
-- README: inner-most bindings come FIRST
separateMb :: Ctx ctxOut -> Ctx ctxIn ->
              Mb (ctxOut :++: ctxIn) a -> Mb ctxOut (Mb ctxIn a)
separateMb ctxOut ctxIn (MkMb l a) = MkMb lOut (MkMb lIn a)
    where (lIn, lOut) = splitAt (ctxLength ctxIn) l
          ctxLength :: Ctx ctx -> Int
          ctxLength CtxNil = 0
          ctxLength (CtxCons a ctx) = 1 + (ctxLength ctx)
{-
separateMb :: IsAppend ctx1 ctx2 ctx -> Mb ctx a -> Mb ctx1 (Mb ctx2 a)
separateMb isapp (MkMb l a) = MkMb l1 (MkMb l2 a)
    where (l1, l2) = splitAt (isAppLength isapp) l
          isAppLength :: IsAppend ctx1 ctx2 ctx -> Int
          isAppLength IsAppendBase = 0
          isAppLength (IsAppendStep isapp) = 1 + (isAppLength isapp)
-}

-- make an empty binding
emptyMb :: a -> Mb Nil a
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

cmpNameBool :: Name a -> Name b -> Bool
cmpNameBool (MkName n1) (MkName n2) = n1 == n2

-- in normal HobbitLib, InCtx = InList proofs
type InCtx ctx a = InList ctx a

-- comparing bound names using the ordering in the binding context
-- README: InCtxLT means a1 is bound inside of a2
data TpOrd a1 a2 where
    TpLT :: TpOrd a1 a2
    TpGT :: TpOrd a1 a2
    TpEQ :: TpOrd a a

cmpInCtx :: InCtx ctx a1 -> InCtx ctx a2 -> TpOrd a1 a2
cmpInCtx InListBase InListBase = TpEQ
cmpInCtx InListBase (InListStep _) = TpLT
cmpInCtx (InListStep _) InListBase = TpGT
cmpInCtx (InListStep in1) (InListStep in2) = cmpInCtx in1 in2

cmpInCtxBool :: InCtx ctx a1 -> InCtx ctx a2 -> Bool
cmpInCtxBool in1 in2 =
    case cmpInCtx in1 in2 of
      TpEQ -> True
      _ -> False

inCtxSameLength :: InCtx ctx1 a1 -> InCtx ctx2 a2 -> Bool
inCtxSameLength InListBase InListBase = True
inCtxSameLength (InListStep in1) (InListStep in2) = inCtxSameLength in1 in2
inCtxSameLength _ _ = False

-- name_multi_bind_cmp checks if a name is bound in a multi-binding
mbCmpName :: Mb ctx (Name a) -> Either (InCtx ctx a) (Name a)

mbCmpName (MkMb names (MkName n)) =
  helper (elemIndex n names)
  where helper Nothing  = Right (MkName n)
        helper (Just i) = Left (unsafeLookupList i)


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

mbBool :: Mb ctx Bool -> Bool
mbBool (MkMb _ b) = b

mbString :: Mb ctx String -> String
mbString (MkMb _ str) = str


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

data MapCtx f ctx where
    Empty :: MapCtx f Nil
    (:>) :: MapCtx f ctx -> f a -> MapCtx f (Cons a ctx)

emptyMC = Empty
(|>) = (:>)

ctxSingle :: f a -> MapCtx f (List1 a)
ctxSingle x = Empty :> x

type ctx :|> a = (Cons a ctx)

ctxLookup :: InCtx ctx a -> MapCtx f ctx -> f a
ctxLookup InListBase     (_ :> x)  = x
ctxLookup (InListStep p) (xs :> _) = ctxLookup p xs

ctxMap :: (forall x. f x -> g x) -> MapCtx f ctx -> MapCtx g ctx
ctxMap f Empty = Empty
ctxMap f (xs :> x) = (ctxMap f xs) :> (f x)

(|++>) :: MapCtx f ctx1 -> MapCtx f ctx2 -> MapCtx f (ctx1 :++: ctx2)
mc |++> Empty = mc
mc |++> (mc2 :> x) = (mc |++> mc2) :> x
