{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, TypeFamilies, EmptyDataDecls, ScopedTypeVariables, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FlexibleInstances, ViewPatterns, ImplicitParams, TypeOperators, UndecidableInstances #-}

module HoasTreeIO (
  InTree (..), InList (..),
  Cons,List0,List1,List2,List3,List4,List5,First,Second,Third,Tail,(:++:),
  Name(),      -- hides Name implementation
  Binding(),   -- hides Binding implementation
  Mb(), -- hides MultiBind implementation
  nu,
  cmpName,mbCmpName,
  Fresh(),
  runFresh, unsafeRunFresh,
  emptyMb, combineMb, --separateMb,
  mbInt, mbBool, --mbRebind,
  mbToplevel, ToplevelFun, ToplevelRes, topFun,

  -- things related to All
  -- FIXME: use or remove
  --Compose(),MbF(),mbAll,

  -- things for using mbMatch
  Tag(Tag),FTag(FTag),TFunApply,Repr(Repr),Args(ArgsNil,ArgsCons),ArgsMbMap,
  MbMatchable,toRepr,mbCtor,CtorsFun,MatchTpFun,
  mbMatch,

  -- things for CtxtFTrees
  CtxtFTree(..),ctxtFListSingle,(:|>),(|>),(|*>),
  lookupCtxFTree, ctxtFTreeMap
) where

import Unsafe.Coerce
import Data.List
import Data.IORef
import System.IO.Unsafe(unsafePerformIO)
import Control.Applicative
    
import Test.StrictBench

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
--import Data.Map (Map)
--import qualified Data.Map as Map

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
-- useful miscellany
------------------------------------------------------------

-- for supplying type arguments
data Tag a = Tag
data FTag (f :: * -> *) = FTag


------------------------------------------------------------
-- manipulating lists of types
------------------------------------------------------------

data Nil
data Cons a l

data ListRep l where
    Nil :: ListRep Nil
    Cons :: Tag a -> Int -> ListRep l -> ListRep (Cons a l)

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

-- interleaving lists, i.e. repeatedly taking one from each
type family Interleave l1 l2
type instance Interleave Nil l = l
type instance Interleave l Nil = l
type instance Interleave (Cons a1 l1) (Cons a2 l2) =
    Cons a1 (Cons a2 (Interleave l1 l2))

listInterleave :: ListRep l1 -> ListRep l2-> ListRep (Interleave l1 l2)
listInterleave l1 Nil = l1
listInterleave Nil l2 = l2
listInterleave (Cons tag1 i1 l1) (Cons tag2 i2 l2) =
    Cons tag1 i1 (Cons tag2 i2 (listInterleave l1 l2))


------------------------------------------------------------
-- manipulating trees of types
------------------------------------------------------------

-- for building trees of types
data TreeNil
data TreeNode l a r s

-- selectors to say which way to add next
data L
data R

type family Opp s
type instance Opp L = R
type instance Opp R = L

-- adding to a tree
-- README: would be nice to have inductive kinds here...
type family AddToTree t a
type instance AddToTree TreeNil a = TreeNode TreeNil a TreeNil L
type instance AddToTree (TreeNode l b r s) a = TreeNode (AddToTree l a) b r (Opp s)

-- making a singleton tree
type TreeSingle a = TreeNode TreeNil a TreeNil L
treeSingle :: Tag a -> Int -> TreeRep (TreeSingle a)
treeSingle tag i = TreeNode TreeNil tag i TreeNil L

-- term representation of L/R selectors
data Selector s where
    L :: Selector L
    R :: Selector R

opp :: Selector s -> Selector (Opp s)
opp L = R
opp R = L

-- term representation of trees of types, also containing Int tags at the nodes
data TreeRep t where
    TreeNil :: TreeRep TreeNil
    TreeNode :: TreeRep l -> Tag a -> Int -> TreeRep r -> Selector s ->
                TreeRep (TreeNode l a r s)

-- proofs that a type is in a tree of types
data InTree t a where
  InTreeBase :: InTree (TreeNode l a r s) a
  InTreeL :: InTree l a -> InTree (TreeNode l b r s) a
  InTreeR :: InTree r a -> InTree (TreeNode l b r s) a

-- equality on proofs
instance Eq (InTree t a) where
  InTreeBase      == InTreeBase      = True 
  (InTreeL p1) == (InTreeL p2) =     p1 == p2
  (InTreeR p1) == (InTreeR p2) =     p1 == p2
  _               == _               = False

-- adding an Int to a tree
addToTree :: TreeRep t -> Tag a -> Int -> (TreeRep (AddToTree t a),
                                           InTree (AddToTree t a) a)
addToTree TreeNil tag i = (TreeNode TreeNil tag i TreeNil L, InTreeBase)
addToTree (TreeNode l tagb j r s) tag i =
    let (rep, pf) = addToTree l tag i in
    (TreeNode rep tagb j r (opp s), InTreeL pf)

-- turning trees into lists
type family TreeToList t1
type instance TreeToList TreeNil = Nil
type instance TreeToList (TreeNode l a r s) =
    Cons a (Interleave (TreeToList l) (TreeToList r))

-- appending trees at the type level
type t1 :|>: t2 = TreeAppendList t1 (TreeToList t2)
-- special case for adding one type
type ctx :|> a = ctx :|>: (TreeSingle a)

type family TreeAppendList t l
type instance TreeAppendList t Nil = t
type instance TreeAppendList t (Cons a l) = TreeAppendList (AddToTree t a) l

-- reflecting append at the term level
treeAppend :: TreeRep t1 -> TreeRep t2 -> TreeRep (t1 :|>: t2)
treeAppend t1 t2 = treeAppendList t1 (treeToList t2)

treeAppendList :: TreeRep t -> ListRep l -> TreeRep (TreeAppendList t l)
treeAppendList t1 Nil = t1
treeAppendList t1 (Cons tag i l) = treeAppendList (fst $ addToTree t1 tag i) l

treeToList :: TreeRep t -> ListRep (TreeToList t)
treeToList TreeNil = Nil
treeToList (TreeNode l tag i r s) =
    Cons tag i (listInterleave (treeToList l) (treeToList r))

-- just to trust that we did everything correctly...
treeAppendOK :: TreeRep t1 -> TreeRep t2 ->
                ((TreeToList t1) :++: (TreeToList t2))
                :=:
                (TreeToList (t1 :|>: t2))
treeAppendOK = undefined
-- FIXME!!!

------------------------------------------------------------
-- generic map interface, so we can change it out
------------------------------------------------------------

type SomeTreeMap = IntMap InSomeTree

mapEmpty = IntMap.empty
mapSingleton = IntMap.singleton
mapLookup = IntMap.lookup
mapInsert = IntMap.insert

{-
type SomeTreeMap = Map Int InSomeTree

mapEmpty = Map.empty
mapSingleton = Map.singleton
mapLookup = Map.lookup
mapInsert = Map.insert
-}

------------------------------------------------------------
-- now we define our data-types
-- under the hood, names are just integers
------------------------------------------------------------

data Name a    = MkName Int    deriving Eq
data Mb ctx b  = MkMb (TreeRep ctx) SomeTreeMap b  --deriving Eq
type Binding a = Mb (TreeSingle a)
-- FIXME: does Mb have to derive Eq?

data InSomeTree where InSomeTree :: InTree t a -> InSomeTree

-- for benchmarking
instance NFData (Name a) where
    rnf (MkName i) = rnf i

-- for benchmarking
instance NFData a => NFData (Mb ctx a) where
    rnf (MkMb t map x) = rnf t `seq` rnf map `seq` rnf x

instance NFData (TreeRep t) where
    rnf (TreeNode l Tag i r s) = rnf l `seq` rnf i `seq` rnf r
    rnf TreeNil = ()

instance NFData InSomeTree where
    rnf (InSomeTree pf) = rnf pf

instance NFData (InTree t a) where
    rnf InTreeBase = ()
    rnf (InTreeL pf) = rnf pf
    rnf (InTreeR pf) = rnf pf

------------------------------------------------------------
-- printing methods
------------------------------------------------------------

-- for printing things (debug only)
instance Show (Name a) where
  show (MkName n) = "#" ++ show n ++ "#"

instance Show b => Show (Mb a b) where
  show (MkMb t _ b) = "#" ++ show (listInts (treeToList t)) ++ "." ++ show b

listInts :: ListRep t -> [Int]
listInts Nil = []
listInts (Cons _ i l) = i : (listInts l)

instance Show a => Show (InTree t a) where
  show InTreeBase      = "InTreeBase"
  show (InTreeL pf) = "InTreeL (" ++ show pf ++ ")"
  show (InTreeR pf) = "InTreeR (" ++ show pf ++ ")"

------------------------------------------------------------
-- simple operations for creating and manipulating bindings
------------------------------------------------------------

-- nu creates bindings
nu :: (Name a -> Fresh b) -> Fresh (Binding a b)
nu f = fresh_int >>= \n -> MkMb (treeSingle Tag n) (mapSingleton n (InSomeTree InTreeBase)) <$> (f $ MkName n) 

-- combine binding of a binding into a single binding
combineMb :: Mb ctx1 (Mb ctx2 a) -> Mb (ctx1 :|>: ctx2) a
combineMb (MkMb t1 map1 (MkMb t2 _ a)) =
    let (t, map) = treeAppendWithPfs t1 map1 t2 in
    MkMb t map a

treeAppendWithPfs :: TreeRep t1 -> SomeTreeMap -> TreeRep t2 ->
                     (TreeRep (t1 :|>: t2), SomeTreeMap)
treeAppendWithPfs t1 map t2 = treeAppendListWithPfs t1 map (treeToList t2)
treeAppendListWithPfs :: TreeRep t -> SomeTreeMap -> ListRep l ->
                         (TreeRep (TreeAppendList t l), SomeTreeMap)
treeAppendListWithPfs t1 map Nil = (t1, map)
treeAppendListWithPfs t1 map (Cons tag i l) =
    let (t, pf) = (addToTree t1 tag i) in
    treeAppendListWithPfs t (mapInsert i (InSomeTree pf) map) l


-- separates inner-most binding
{- FIXME
separateMb :: Mb (ctx :|> a) b -> Mb ctx (Binding a b)
separateMb (MkMb t map b) = MkMb l (MkMb [a] b)

treeRemoveLast
-}

-- make an empty binding
emptyMb :: a -> Mb TreeNil a
emptyMb a = MkMb TreeNil mapEmpty a

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
mbCmpName :: Mb ctx (Name a) -> Either (InTree ctx a) (Name a)

mbCmpName (MkMb _ map (MkName n)) =
    case mapLookup n map of
      Just (InSomeTree pf) -> Left $ unsafeCoerce pf
      Nothing -> Right $ MkName n


------------------------------------------------------------
-- re-binding names in terms
------------------------------------------------------------

mbRebind :: (Name a) -> b -> (Binding a b)
mbRebind (MkName n) b =
    MkMb (treeSingle Tag n) (mapSingleton n (InSomeTree InTreeBase)) b

------------------------------------------------------------
-- applying top-level functions under binders
------------------------------------------------------------

class ToplevelFun tag a where
    type ToplevelRes tag a
    topFun :: Tag tag -> a -> ToplevelRes tag a

mbToplevel :: ToplevelFun tag a => Tag tag -> Mb ctx a -> Mb ctx (ToplevelRes tag a)
mbToplevel tag (MkMb t map i) = MkMb t map (topFun tag i)


------------------------------------------------------------
-- special-purpose matching under binders
------------------------------------------------------------

mbInt :: Mb ctx Int -> Int
mbInt (MkMb _ _ i) = i

mbBool :: Mb ctx Bool -> Bool
mbBool (MkMb _ _ b) = b


------------------------------------------------------------
-- generic matching under binders
------------------------------------------------------------

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
mbMatch ctxT (MkMb t map x) =
    case toRepr x of
      Repr zT in_ctors args ->
          argsMapApply ctxT Tag (MkMb t map) (mbCtor zT ctxT in_ctors) args

-- helper function for applying a function to arguments
argsMapApply :: Tag ctx -> Tag ret -> (forall x. x -> Mb ctx x) ->
                ArgsMbMap ctx args ret -> Args args -> ret
argsMapApply ctxT rT addMb f ArgsNil = f
argsMapApply ctxT rT addMb f (ArgsCons x args) = argsMapApply ctxT rT addMb (f (addMb x)) args


------------------------------------------------------------
-- lists of things that match the context
------------------------------------------------------------

data CtxtFTree f ctx where
    CtxtFTreeNil :: CtxtFTree f TreeNil
    CtxtFTreeNode :: f a -> CtxtFTree f ctx1 -> CtxtFTree f ctx2 ->
                     Selector s ->
                     CtxtFTree f (TreeNode ctx1 a ctx2 s)

ctxtFListSingle :: f a -> CtxtFTree f (TreeSingle a)
ctxtFListSingle x = CtxtFTreeNode x CtxtFTreeNil CtxtFTreeNil L

(|>) :: CtxtFTree f ctx -> f a -> CtxtFTree f (ctx :|> a)
CtxtFTreeNil          |> y = ctxtFListSingle y
CtxtFTreeNode x l r s |> y = CtxtFTreeNode x (l |> y) r (opp s)

(|*>) :: CtxtFTree f ctx -> (Tag a, f a) -> CtxtFTree f (ctx :|> a)
l |*> (_, x) = l |> x

lookupCtxFTree :: InTree ctx a -> CtxtFTree f ctx -> f a
lookupCtxFTree InTreeBase  (CtxtFTreeNode x _ _ _) = x
lookupCtxFTree (InTreeL p) (CtxtFTreeNode _ l _ _) = lookupCtxFTree p l
lookupCtxFTree (InTreeR p) (CtxtFTreeNode _ _ r _) = lookupCtxFTree p r
--lookupCtxFList _                       _           = error "never happens"

ctxtFTreeMap :: (forall x. f x -> g x) -> CtxtFTree f ctx -> CtxtFTree g ctx
ctxtFTreeMap f CtxtFTreeNil = CtxtFTreeNil
ctxtFTreeMap f (CtxtFTreeNode x l r s) =
    CtxtFTreeNode (f x) (ctxtFTreeMap f l) (ctxtFTreeMap f r) s
