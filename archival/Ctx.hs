{-# LANGUAGE GADTs, TypeFamilies, EmptyDataDecls, RankNTypes, MultiParamTypeClasses, TypeOperators #-}

------------------------------------------------------------
-- library for manipulating contexts of types
-- README: contexts are represented right-to-left, i.e., the
-- right-most element comes first; this is to make it
-- easy to add to the inside of a context
------------------------------------------------------------

module Ctx where


------------------------------------------------------------
-- manipulating lists of types
-- note: we do right on the outside for efficiency of
-- adding a single binder inside another one
------------------------------------------------------------

data CtxNil
data CtxCons l a


------------------------------------------------------------
-- helpers for constructing and destructing contexts
------------------------------------------------------------

type List0 = CtxNil
type List1 a = (CtxCons CtxNil a)
type List2 a b = (CtxCons (CtxCons CtxNil b) a)
type List3 a b c = (CtxCons (CtxCons (CtxCons CtxNil c) b) a)
type List4 a b c d = (CtxCons (CtxCons (CtxCons (CtxCons CtxNil d) c) b) a)
type List5 a b c d e = (CtxCons (CtxCons (CtxCons (CtxCons (CtxCons CtxNil e) d) c) b) a)

type family First a
type instance First (CtxCons l a) = a

type family Second a
type instance Second (CtxCons (CtxCons l a2) a1) = a2

type family Third a
type instance Third (CtxCons (CtxCons (CtxCons l a3) a2) a1) = a3

type family Tail a
type instance Tail (CtxCons l a) = l

type family (ctx1 :++: ctx2)
type instance ctx1 :++: CtxNil = ctx1
type instance ctx1 :++: (CtxCons ctx2 a) = (CtxCons (ctx1 :++: ctx2) a)

------------------------------------------------------------
-- the Ctx type, which reifies contexts at the term level
------------------------------------------------------------

data Tag a = Tag
data FTag (f :: * -> *) = FTag

type Ctx ctx = MapCtx Tag ctx

ctxTag :: MapCtx f ctx -> Tag ctx
ctxTag _ = Tag

ctxConsTag :: Tag ctx -> f a -> Tag (CtxCons ctx a)
ctxConsTag _ _ = Tag

ctxLen :: Ctx ctx -> Int
ctxLen EmptyMC = 0
ctxLen (ctx :> _) = 1 + (ctxLen ctx)

ctxAppend :: MapCtx f ctx1 -> MapCtx f ctx2 -> MapCtx f (ctx1 :++: ctx2)
ctxAppend ctx1 EmptyMC = ctx1
ctxAppend ctx1 (ctx2 :> tag) = (ctxAppend ctx1 ctx2) :> tag

------------------------------------------------------------
-- proofs that a type is in a tuple-list of types
------------------------------------------------------------

data InCtx ctx a where
  InCtxBase :: InCtx (CtxCons ctx a) a
  InCtxStep :: InCtx ctx a -> InCtx (CtxCons ctx b) a

instance Show b => Show (InCtx ctx b) where
  show InCtxBase      = "InCtxBase"
  show (InCtxStep pf) = "InCtxStep (" ++ show pf ++ ")"

instance Eq (InCtx ctx a) where
  InCtxBase      == InCtxBase      = True 
  (InCtxStep p1) == (InCtxStep p2) = p1 == p2
  _               == _               = False

{-
weakenInCtxR :: InCtx ctx1 a -> Ctx ctx2 -> InCtx (ctx1 :++: ctx2) a
weakenInCtxR inCtx CtxNil = inCtx
weakenInCtxR inCtx (CtxCons ctx2 _) = InCtxStep (weakenInCtxR inCtx ctx2)
-}

inCtxToEq :: InCtx (CtxCons CtxNil a) b -> b :=: a
inCtxToEq InCtxBase = Refl

------------------------------------------------------------
-- lists of things that match the context
------------------------------------------------------------

data MapCtx f ctx where
    EmptyMC :: MapCtx f CtxNil
    (:>) :: MapCtx f ctx -> f a -> MapCtx f (CtxCons ctx a)

emptyMC = EmptyMC

ctxSingle :: f a -> MapCtx f (List1 a)
ctxSingle x = EmptyMC :> x

type ctx :|> a = (CtxCons ctx a)

ctxLookup :: InCtx ctx a -> MapCtx f ctx -> f a
ctxLookup InCtxBase     (_ :> x)  = x
ctxLookup (InCtxStep p) (xs :> _) = ctxLookup p xs

ctxMap :: (forall x. f x -> g x) -> MapCtx f ctx -> MapCtx g ctx
ctxMap f EmptyMC = EmptyMC
ctxMap f (xs :> x) = (ctxMap f xs) :> (f x)

(|++>) :: MapCtx f ctx1 -> MapCtx f ctx2 -> MapCtx f (ctx1 :++: ctx2)
mc |++> EmptyMC = mc
mc |++> (mc2 :> x) = (mc |++> mc2) :> x

mapCtxToCtx :: MapCtx f ctx -> Ctx ctx
mapCtxToCtx = ctxMap (\_ -> Tag)

------------------------------------------------------------
-- proofs that a tuple-list of types is the append of two others
------------------------------------------------------------

data IsAppend ctx1 ctx2 ctx where
  IsAppendBase :: IsAppend ctx CtxNil ctx
  IsAppendStep :: IsAppend ctx1 ctx2 ctx -> IsAppend ctx1 (CtxCons ctx2 x) (CtxCons ctx x)

mkIsAppend :: MapCtx f ctx2 -> IsAppend ctx1 ctx2 (ctx1 :++: ctx2)
mkIsAppend EmptyMC = IsAppendBase
mkIsAppend (ctx :> _) = IsAppendStep $ mkIsAppend ctx

isAppendLen :: IsAppend ctx1 ctx2 ctx -> Int
isAppendLen IsAppendBase = 0
isAppendLen (IsAppendStep isApp) = 1 + (isAppendLen isApp)

ctxAppendL :: Tag ctx1 -> MapCtx f ctx2 -> IsAppend ctx1 ctx2 (ctx1 :++: ctx2)
ctxAppendL tag EmptyMC = IsAppendBase
ctxAppendL tag (ctx2 :> _) = IsAppendStep (ctxAppendL tag ctx2)

isAppendTrans :: IsAppend ctx1 ctx2 ctx' -> IsAppend ctx' ctx3 ctx ->
                 IsAppend ctx1 (ctx2 :++: ctx3) ctx
isAppendTrans isApp IsAppendBase = isApp
isAppendTrans isApp (IsAppendStep isApp') =
    IsAppendStep (isAppendTrans isApp isApp')


mapCtxSplit :: IsAppend ctx1 ctx2 ctx -> MapCtx f ctx ->
            (MapCtx f ctx1, MapCtx f ctx2)
mapCtxSplit IsAppendBase mc = (mc, emptyMC)
mapCtxSplit (IsAppendStep isA) (mc :> elem) =
    let (mc1, mc2) = mapCtxSplit isA mc in
    (mc1, mc2 :> elem)


inCtxSplit :: IsAppend ctx1 ctx2 ctx -> InCtx ctx a ->
              Either (InCtx ctx1 a) (InCtx ctx2 a)
inCtxSplit IsAppendBase inCtx = Left inCtx
inCtxSplit (IsAppendStep isApp) InCtxBase = Right InCtxBase
inCtxSplit (IsAppendStep isApp) (InCtxStep inCtx) =
    case inCtxSplit isApp inCtx of
      Left inCtx1 -> Left inCtx1
      Right inCtx2 -> Right $ InCtxStep inCtx2


weakenInCtxR :: InCtx ctx1 a -> IsAppend ctx1 ctx2 ctx -> InCtx ctx a
weakenInCtxR inCtx IsAppendBase = inCtx
weakenInCtxR inCtx (IsAppendStep isApp) = InCtxStep (weakenInCtxR inCtx isApp)

weakenInCtxL :: Tag ctx1 -> InCtx ctx2 a -> InCtx (ctx1 :++: ctx2) a
weakenInCtxL tag InCtxBase = InCtxBase
weakenInCtxL tag (InCtxStep inCtx) = InCtxStep (weakenInCtxL tag inCtx)

------------------------------------------------------------
-- dependent equality and comparison
------------------------------------------------------------

data a :=: b where
  Refl :: a :=: a

cong :: a :=: b -> f a :=: f b
cong Refl = Refl

data DepOrdering a b where
    DepLT :: DepOrdering a b
    DepGT :: DepOrdering a b
    DepEQ :: DepOrdering a a

class DepEq a b where
    depEq :: a -> b -> Maybe (a :=: b)
    depEqBool :: a -> b -> Bool
    depEqBool a b = case depEq a b of { Just _ -> True ; Nothing -> False }

class DepEq a b => DepOrd a b where
    depCompare :: a -> b -> DepOrdering a b
    depCompareOrd :: a -> b -> Ordering
    depCompareOrd a b = case depCompare a b of
                          { DepLT -> LT ; DepGT -> GT ; DepEQ -> EQ }

{- FIXME: causes overlapping instance errors
instance DepEq f => Eq (f a) where
    a1 == a2 = case depEq a1 a2 of { Just _ -> True ; Nothing -> False }

instance DepOrd f => Ord (f a) where
    compare a1 a2 = case depCompare a1 a2 of
                      { DepLT -> LT ; DepGT -> GT ; DepEQ _ -> EQ }
-}

{-
depEqToEq :: (f a -> f a -> Maybe (a :=: a)) -> (f a -> f a -> Bool)
depEqToEq f =
    \x1 -> \x2 -> case f x1 x2 of { Just _ -> True ; Nothing -> False }

depCmpToCmp :: (f a -> f a -> DepOrdering (f a) (f a)) -> (f a -> f a -> Ordering)
depCmpToCmp f =
    \x1 -> \x2 -> case f x1 x2 of { DepLT -> LT ; DepGT -> GT ; DepEQ _ -> EQ }
-}


cmpInCtx :: InCtx ctx a1 -> InCtx ctx a2 -> DepOrdering a1 a2
cmpInCtx InCtxBase InCtxBase = DepEQ
cmpInCtx InCtxBase (InCtxStep _) = DepLT
cmpInCtx (InCtxStep _) InCtxBase = DepGT
cmpInCtx (InCtxStep in1) (InCtxStep in2) = cmpInCtx in1 in2

instance DepEq (InCtx ctx a1) (InCtx ctx a2) where
    depEq in1 in2 = helper $ cmpInCtx in1 in2
        where helper :: DepOrdering a1 a2 -> Maybe (InCtx ctx a1 :=: InCtx ctx a2)
              helper DepEQ = Just Refl
              helper _ = Nothing

instance DepOrd (InCtx ctx a1) (InCtx ctx a2) where
    depCompare in1 in2 = helper $ cmpInCtx in1 in2
        where helper :: DepOrdering a1 a2 -> DepOrdering (InCtx ctx a1) (InCtx ctx a2)
              helper DepEQ = DepEQ
              helper DepLT = DepLT
              helper DepGT = DepGT


inCtxSameLength :: InCtx ctx1 a1 -> InCtx ctx2 a2 -> Bool
inCtxSameLength InCtxBase InCtxBase = True
inCtxSameLength (InCtxStep in1) (InCtxStep in2) = inCtxSameLength in1 in2
inCtxSameLength _ _ = False


------------------------------------------------------------
-- building an arbitrary InCtx proof with a given length
-- (this is used internally in HobbitLib)
------------------------------------------------------------

data ExInCtx where
    ExInCtx :: InCtx ctx a -> ExInCtx

inCtxFromLen :: Int -> ExInCtx
inCtxFromLen 0 = ExInCtx InCtxBase
inCtxFromLen n = exInCtxCons (inCtxFromLen (n-1)) where
    exInCtxCons :: ExInCtx -> ExInCtx
    exInCtxCons (ExInCtx inCtx) = ExInCtx $ InCtxStep inCtx


------------------------------------------------------------
-- sub-contexts
------------------------------------------------------------

-- FIXME: come back to this...
{-
data SubCtx sub ctx where
    SubCtxNil :: SubCtx CtxNil
    SubCtxY :: SubCtx sub ctx -> SubCtx (CtxCons sub a) (CtxCons ctx a)
    SubCtxN :: SubCtx sub ctx -> SubCtx sub (CtxCons ctx a)


subCtxAppendL :: IsAppend ctx1 ctx2 ctx -> SubCtx ctx1 ctx
subCtxAppendR :: IsAppend ctx1 ctx2 ctx -> SubCtx ctx2 ctx

inSubCtx :: SubCtx sub ctx -> InCtx sub a -> InCtx ctx a
inSubCtx SubCtxBase inCtx = inCtx
inSubCtx (SubCtxL isApp sub) inCtx = inCtx
-}

