{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Data.Binding.Hobbits.NuMatching
-- Copyright   : (c) 2014 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : westbrook@kestrel.edu
-- Stability   : experimental
-- Portability : GHC
--
-- This module defines the typeclass @'NuMatching' a@, which allows
-- pattern-matching on the bodies of multi-bindings when their bodies
-- have type a. To ensure adequacy, the actual machinery of how this
-- works is hidden from the user, but, for any given (G)ADT @a@, the
-- user can use the Template Haskell function 'mkNuMatching' to
-- create a 'NuMatching' instance for @a@.
--


module Data.Binding.Hobbits.NuMatching (
  NuMatching(..), mkNuMatching,
  MbTypeRepr(), isoMbTypeRepr, unsafeMbTypeRepr,
  NuMatchingAny1
) where

import Prelude hiding (exp)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
--import Data.Typeable
import Language.Haskell.TH hiding (Name, Type(..), cxt, clause)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype.TyVarBndr
import Control.Monad (forM)
import Numeric.Natural
import Data.Kind as DK
import Data.Word
--import Control.Monad.Identity

import Data.Type.RList hiding (map)
import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.Internal.Closed
import Data.Binding.Hobbits.Internal.Utilities


{-| Just like 'mapNamesPf', except uses the NuMatching class. -}
mapNames :: NuMatching a => NameRefresher -> a -> a
mapNames = mapNamesPf nuMatchingProof

matchDataDecl :: Dec -> Maybe (Cxt, TH.Name, [TyVarBndrVis], [Con])
matchDataDecl (DataD cxt name tyvars _ constrs _) =
  Just (cxt, name, tyvars, constrs)
matchDataDecl (NewtypeD cxt name tyvars _ constr _) =
  Just (cxt, name, tyvars, [constr])
matchDataDecl _ = Nothing


mkInstanceD :: Cxt -> TH.Type -> [Dec] -> Dec
mkInstanceD = InstanceD Nothing

{-|
  Instances of the @'NuMatching' a@ class allow pattern-matching on
  multi-bindings whose bodies have type @a@, i.e., on multi-bindings
  of type @'Mb' ctx a@. The structure of this class is mostly hidden
  from the user; see 'mkNuMatching' to see how to create instances
  of the @NuMatching@ class.
-}
class NuMatching a where
    nuMatchingProof :: MbTypeRepr a

-- | Build an 'MbTypeRepr' for type @a@ by using an isomorphism with an
-- already-representable type @b@. This is useful for building 'NuMatching'
-- instances for, e.g., 'Integral' types, by mapping to and from 'Integer',
-- without having to define instances for each one in this module.
isoMbTypeRepr :: NuMatching b => (a -> b) -> (b -> a) -> MbTypeRepr a
isoMbTypeRepr f_to f_from =
  MbTypeReprData $ MkMbTypeReprData $ \refresher a ->
  f_from $ mapNames refresher (f_to a)

-- | Builds an 'MbTypeRepr' proof for use in a 'NuMatching' instance. This proof
-- is unsafe because it does no renaming of fresh names, so should only be used
-- for types that are guaranteed not to contain any 'Name' or 'Mb' values.
unsafeMbTypeRepr :: MbTypeRepr a
unsafeMbTypeRepr = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching (Name a) where
    nuMatchingProof = MbTypeReprName

instance NuMatching (Closed a) where
    -- no need to map free variables in a Closed object
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance (NuMatching a, NuMatching b) => NuMatching (a -> b) where
    nuMatchingProof = MbTypeReprFun nuMatchingProof nuMatchingProof

instance NuMatching a => NuMatching (Mb ctx a) where
    nuMatchingProof = MbTypeReprMb nuMatchingProof

instance NuMatching Bool where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Int where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Integer where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Char where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Natural where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Float where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Double where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Word where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Word8 where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Word16 where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Word32 where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching Word64 where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance NuMatching () where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\_ -> id))

instance (NuMatching a, NuMatching b) => NuMatching (a,b) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ \r (a,b) ->
                                       (mapNames r a, mapNames r b))

instance (NuMatching a, NuMatching b, NuMatching c) => NuMatching (a,b,c) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ \r (a,b,c) ->
                                       (mapNames r a, mapNames r b, mapNames r c))

instance (NuMatching a, NuMatching b,
          NuMatching c, NuMatching d) => NuMatching (a,b,c,d) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ \r (a,b,c,d) ->
                                       (mapNames r a, mapNames r b,
                                        mapNames r c, mapNames r d))

instance NuMatching a => NuMatching [a] where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\r -> map (mapNames r)))

instance NuMatching a => NuMatching (Vector a) where
    nuMatchingProof =
      MbTypeReprData (MkMbTypeReprData $ (\r -> Vector.map (mapNames r)))


{-
type family NuMatchingListProof args
type instance NuMatchingListProof Nil = ()
type instance NuMatchingListProof (args :> arg) = (NuMatchingListProof args, MbTypeReprData arg)

-- the NuMatchingList class, for saying that NuMatching holds for a context of types
class NuMatchingList args where
    nuMatchingListProof :: NuMatchingListProof args

instance NuMatchingList Nil where
    nuMatchingListProof = ()

instance (NuMatchingList args, NuMatching a) => NuMatchingList (args :> a) where
    nuMatchingListProof = (nuMatchingListProof, nuMatchingProof)
-}

{-
-- | An object-level reification of the 'NuMatching' class
data NuMatchingObj a = NuMatching a => NuMatchingObj ()

class NuMatchingList args where
    nuMatchingListProof :: RAssign NuMatchingObj args

instance NuMatchingList RNil where
    nuMatchingListProof = MNil

instance (NuMatchingList args, NuMatching a) => NuMatchingList (args :> a) where
    nuMatchingListProof = nuMatchingListProof :>: NuMatchingObj ()


class NuMatching1 f where
    nuMatchingProof1 :: NuMatching a => NuMatchingObj (f a)
-}

-- README: deriving NuMatching from NuMatching1 leads to overlapping instances
-- for, e.g., Name a
{-
instance (NuMatching1 f, NuMatching a) => NuMatching (f a) where
    nuMatchingProof = nuMatchingProof1 nuMatchingProof
-}

{-
instance {-# OVERLAPPABLE #-} (NuMatching1 f, NuMatchingList ctx) =>
                              NuMatching (RAssign f ctx) where
    nuMatchingProof = MbTypeReprData $ MkMbTypeReprData $ helper nuMatchingListProof where
        helper :: NuMatching1 f =>
                  RAssign NuMatchingObj args -> NameRefresher ->
                  RAssign f args -> RAssign f args
        helper MNil r MNil = MNil
        helper (proofs :>: NuMatchingObj ()) r (elms :>: (elm :: f a)) =
            case nuMatchingProof1 :: NuMatchingObj (f a) of
              NuMatchingObj () ->
                  (helper proofs r elms) :>:
                  mapNames r elm
-}

-- | An alias for a 'NuMatching' constraint on a functor of arbitrary kind that
-- does not require any constraints on the input type. We define this as a
-- class, rather than a type synonym, so that downstream users do not have to
-- enable @QuantifiedConstraints@ just to be able to use it.
class    (forall a. NuMatching (f a)) => NuMatchingAny1 (f :: k -> Type)
instance (forall a. NuMatching (f a)) => NuMatchingAny1 (f :: k -> Type)

instance {-# OVERLAPPABLE #-} NuMatchingAny1 f => NuMatching (RAssign f ctx) where
    nuMatchingProof = MbTypeReprData $ MkMbTypeReprData helper where
        helper :: NuMatchingAny1 f => NameRefresher -> RAssign f args ->
                  RAssign f args
        helper _ MNil = MNil
        helper r (elms :>: elm) = helper r elms :>: mapNames r elm

-- now we define some TH to create NuMatchings

natsFrom :: Integer -> [Integer]
natsFrom i = i : natsFrom (i+1)

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

-- snd3 :: (a,b,c) -> b
-- snd3 (_,y,_) = y

thd3 :: (a,b,c) -> c
thd3 (_,_,z) = z


type Names = (TH.Name, TH.Name, TH.Name)

mapNamesType :: TypeQ -> TypeQ
mapNamesType a = [t| NameRefresher -> $a -> $a |]

{-|
  Template Haskell function for creating NuMatching instances for (G)ADTs.
  Typical usage is to include the following line in the source file for
  (G)ADT @T@ (here assumed to have two type arguments):

> $(mkNuMatching [t| forall a b . T a b |])

  The 'mkNuMatching' call here will create an instance declaration for
  @'NuMatching' (T a b)@. It is also possible to include a context in the
  forall type; for example, if we define the 'ID' data type as follows:

> data ID a = ID a

  then we can create a 'NuMatching' instance for it like this:

> $( mkNuMatching [t| NuMatching a => ID a |])

  Note that, when a context is included, the Haskell parser will add
  the @forall a@ for you.
-}
mkNuMatching :: Q TH.Type -> Q [Dec]
mkNuMatching tQ =
    do t <- tQ
       (cxt, cType, tName, constrs, tyvars) <- getMbTypeReprInfoTop t
       fName <- newName "f"
       refrName <- newName "_refresher"
       clauses <- getClauses (tName, fName, refrName) constrs
       mapNamesT <- mapNamesType (return cType)
       return [mkInstanceD
               cxt (TH.AppT (TH.ConT ''NuMatching) cType)
               [ValD (VarP 'nuMatchingProof)
                (NormalB
                 $ AppE (ConE 'MbTypeReprData)
                   $ AppE (ConE 'MkMbTypeReprData)
                         $ LetE [SigD fName
                                 $ TH.ForallT (map plainTVSpecified tyvars) cxt mapNamesT,
                                 FunD fName clauses]
                               (VarE fName)) []]]

       {-
       return (LetE
               [SigD fName
                     (TH.ForallT tyvars reqCxt
                     $ foldl TH.AppT TH.ArrowT
                           [foldl TH.AppT (TH.ConT conName)
                                      (map tyVarToType tyvars)]),
                FunD fname clauses]
               (VarE fname))
        -}
    where
      -- fail for getMbTypeReprInfo
      getMbTypeReprInfoFail t extraMsg =
          fail ("mkMbTypeRepr: " ++ show t
                ++ " is not a type constructor for a (G)ADT applied to zero or more distinct type variables" ++ extraMsg)

      -- get info for conName (top-level call)
      getMbTypeReprInfoTop t = getMbTypeReprInfo [] [] t t

      -- get info for conName
      getMbTypeReprInfo ctx tyvars topT (TH.ConT tName) =
          do info <- reify tName
             case info of
               TyConI (matchDataDecl -> Just (_, _, tyvarsReq, constrs)) ->
                 success tyvarsReq constrs
               _ -> getMbTypeReprInfoFail topT (": info for " ++ (show tName) ++ " = " ++ (show info))
          where
            success tyvarsReq constrs =
                let tyvarsRet = if tyvars == [] && ctx == []
                                then map tvName tyvarsReq
                                else tyvars in
                return (ctx,
                        foldl TH.AppT (TH.ConT tName) (map TH.VarT tyvars),
                        tName, constrs, tyvarsRet)

      getMbTypeReprInfo ctx tyvars topT (TH.AppT f (TH.VarT argName)) =
          if elem argName tyvars then
              getMbTypeReprInfoFail topT ""
          else
              getMbTypeReprInfo ctx (argName:tyvars) topT f

      getMbTypeReprInfo ctx tyvars topT (TH.ForallT _ ctx' t) =
          getMbTypeReprInfo (ctx ++ ctx') tyvars topT t

      getMbTypeReprInfo _ _ topT _ = getMbTypeReprInfoFail topT ""

      -- get the name from a data type
      getTCtor t = getTCtorHelper t t []
      getTCtorHelper (TH.ConT tName) topT tyvars = Just (topT, tName, tyvars)
      getTCtorHelper (TH.AppT t1 (TH.VarT var)) topT tyvars =
          getTCtorHelper t1 topT (tyvars ++ [var])
      getTCtorHelper (TH.SigT t1 _) topT tyvars = getTCtorHelper t1 topT tyvars
      getTCtorHelper _ _ _ = Nothing

      -- get a list of Clauses, one for each constructor in constrs
      getClauses :: Names -> [Con] -> Q [Clause]
      getClauses _ [] = return []

      getClauses names (NormalC cName cTypes : constrs) =
        do clause <-
             getClauseHelper names (map snd cTypes) (natsFrom 0)
             (\l -> conPCompat cName (map (VarP . fst3) l))
             (\l -> foldl AppE (ConE cName) (map fst3 l))
           clauses <- getClauses names constrs
           return $ clause : clauses

      getClauses names (RecC cName cVarTypes : constrs) =
        do clause <-
             getClauseHelper names (map thd3 cVarTypes) (map fst3 cVarTypes)
             (\l -> RecP cName (map (\(var,_,field) -> (field, VarP var)) l))
             (\l -> RecConE cName (map (\(exp,_,field) -> (field, exp)) l))
           clauses <- getClauses names constrs
           return $ clause : clauses

      getClauses names (InfixC cType1 cName cType2 : constrs) =
        do clause <-
             getClauseHelper names (map snd [cType1, cType2]) (natsFrom 0)
             (\l -> conPCompat cName (map (VarP . fst3) l))
             (\l -> foldl AppE (ConE cName) (map fst3 l))
           clauses <- getClauses names constrs
           return $ clause : clauses

      getClauses names (GadtC cNames cTypes _ : constrs) =
        do clauses1 <-
             forM cNames $ \cName ->
             getClauseHelper names (map snd cTypes) (natsFrom 0)
             (\l -> conPCompat cName (map (VarP . fst3) l))
             (\l -> foldl AppE (ConE cName) (map fst3 l))
           clauses2 <- getClauses names constrs
           return (clauses1 ++ clauses2)

      getClauses names (RecGadtC cNames cVarTypes _ : constrs) =
        do clauses1 <-
             forM cNames $ \cName ->
             getClauseHelper names (map thd3 cVarTypes) (map fst3 cVarTypes)
             (\l -> RecP cName (map (\(var,_,field) -> (field, VarP var)) l))
             (\l -> RecConE cName (map (\(exp,_,field) -> (field, exp)) l))
           clauses2 <- getClauses names constrs
           return (clauses1 ++ clauses2)

      getClauses names (ForallC _ _ constr : constrs) =
        getClauses names (constr : constrs)

      getClauseHelper :: Names -> [TH.Type] -> [a] ->
                         ([(TH.Name,TH.Type,a)] -> Pat) ->
                         ([(Exp,TH.Type,a)] -> Exp) ->
                         Q Clause
      getClauseHelper names@(_, _, refrName) cTypes cData pFun eFun =
          do varNames <- mapM (newName . ("x" ++) . show . fst)
                         $ zip (natsFrom 0) cTypes
             let varsTypesData = zip3 varNames cTypes cData
             let expsTypesData = map (mkExpTypeData names) varsTypesData
             return $ Clause [(VarP refrName), (pFun varsTypesData)]
                        (NormalB $ eFun expsTypesData) []

      mkExpTypeData :: Names -> (TH.Name,TH.Type,a) -> (Exp,TH.Type,a)
      mkExpTypeData (tName, fName, refrName)
                    (varName, getTCtor -> Just (t, tName', _), cData)
          | tName == tName' =
              -- the type of the arg is the same as the (G)ADT we are
              -- recursing over; apply the recursive function
              (foldl AppE (VarE fName)
                         [(VarE refrName), (VarE varName)],
               t, cData)
      mkExpTypeData (_, _, refrName) (varName, t, cData) =
          -- the type of the arg is not the same as the (G)ADT; call mapNames
          (foldl AppE (VarE 'mapNames)
                     [(VarE refrName), (VarE varName)],
           t, cData)

{-
-- FIXME: old stuff below

type CxtStateQ a = StateT Cxt Q a

-- create a MkMbTypeReprData for a (G)ADT
mkMkMbTypeReprDataOld :: Q TH.Name -> Q Exp
mkMkMbTypeReprDataOld conNameQ =
    do conName <- conNameQ
       (cxt, name, tyvars, constrs) <- getMbTypeReprInfo conName
       (clauses, reqCxt) <- runStateT (getClauses cxt name tyvars [] constrs) []
       fname <- newName "f"
       return (LetE
               [SigD fname
                     (TH.ForallT tyvars reqCxt
                     $ foldl TH.AppT TH.ArrowT
                           [foldl TH.AppT (TH.ConT conName)
                                      (map tyVarToType tyvars)]),
                FunD fname clauses]
               (VarE fname))
    where
      -- convert a TyVar to a Name
      tyVarToType (PlainTV n) = TH.VarT n
      tyVarToType (KindedTV n _) = TH.VarT n

      -- get info for conName
      getMbTypeReprInfo conName =
          reify conName >>= \info ->
              case info of
                TyConI (matchDataDecl -> Just (cxt, name, tyvars, constrs)) ->
                    return (cxt, name, tyvars, constrs)
                _ -> fail ("mkMkMbTypeReprData: " ++ show conName
                           ++ " is not a (G)ADT")
      {-
      -- report failure
      getMbTypeReprInfoFail t =
          fail ("mkMkMbTypeReprData: " ++ show t
                ++ " is not a fully applied (G)ADT")

      getMbTypeReprInfo (TH.ConT conName) topT =
          reify conName >>= \info ->
              case info of
                TyConI (DataD cxt name tyvars constrs _) ->
                    return (cxt, name, tyvars, constrs)
                _ -> getMbTypeReprInfoFail topT
      getMbTypeReprInfo (TH.AppT t _) topT = getMbTypeReprInfo t topT
      getMbTypeReprInfo (TH.SigT t _) topT = getMbTypeReprInfo t topT
      getMbTypeReprInfo _ topT = getMbTypeReprInfoFail topT
       -}

      -- get a list of Clauses, one for each constructor in constrs
      getClauses :: Cxt -> TH.Name -> [TyVarBndr] -> [TyVarBndr] -> [Con] ->
                    CxtStateQ [Clause]
      getClauses cxt name tyvars locTyvars [] = return []

      getClauses cxt name tyvars locTyvars (NormalC cName cTypes : constrs) =
        do clause <-
             getClauseHelper cxt name tyvars locTyvars (map snd cTypes)
             (natsFrom 0)
             (\l -> conPCompat cName (map (VarP . fst3) l))
             (\l -> foldl AppE (ConE cName) (map (VarE . fst3) l))
           clauses <- getClauses cxt name tyvars locTyvars constrs
           return (clause : clauses)

      getClauses cxt name tyvars locTyvars (RecC cName cVarTypes : constrs) =
        do clause <-
             getClauseHelper cxt name tyvars locTyvars (map thd3 cVarTypes)
             (map fst3 cVarTypes)
             (\l -> RecP cName (map (\(var,_,field) -> (field, VarP var)) l))
             (\l -> RecConE cName (map (\(var,_,field) -> (field, VarE var)) l))
           clauses <- getClauses cxt name tyvars locTyvars constrs
           return (clause : clauses)

      getClauses cxt name tyvars locTyvars (InfixC cType1 cName cType2 : _) =
        undefined -- FIXME

      getClauses cxt name tyvars locTyvars (ForallC tyvars2 cxt2 constr
                                            : constrs) =
        do clauses1 <-
             getClauses (cxt ++ cxt2) name tyvars (locTyvars ++ tyvars2) [constr]
           clauses2 <- getClauses cxt name tyvars locTyvars constrs
           return (clauses1 ++ clauses2)

      getClauses cxt name tyvars locTyvars (GadtC cNames cTypes _ : constrs) =
        do clauses1 <-
             forM cNames $ \cName ->
             getClauseHelper cxt name tyvars locTyvars (map snd cTypes)
             (natsFrom 0) (\l -> conPCompat cName (map (VarP . fst3) l))
             (\l -> foldl AppE (ConE cName) (map (VarE . fst3) l))
           clauses2 <- getClauses cxt name tyvars locTyvars constrs
           return (clauses1 ++ clauses2)

      getClauses cxt name tyvars locTyvars (RecGadtC cNames cVarTypes _
                                            : constrs) =
        do clauses1 <-
             forM cNames $ \cName ->
             getClauseHelper cxt name tyvars locTyvars
             (map thd3 cVarTypes) (map fst3 cVarTypes)
             (\l -> RecP cName (map (\(var,_,field) -> (field, VarP var)) l))
             (\l -> RecConE cName (map (\(var,_,field) -> (field, VarE var)) l))
           clauses2 <- getClauses cxt name tyvars locTyvars constrs
           return (clauses1 ++ clauses2)

      getClauseHelper :: Cxt -> TH.Name -> [TyVarBndr] -> [TyVarBndr] ->
                         [TH.Type] -> [a] ->
                         ([(TH.Name,TH.Type,a)] -> Pat) ->
                         ([(TH.Name,TH.Type,a)] -> Exp) ->
                         CxtStateQ Clause
      getClauseHelper cxt name tyvars locTyvars cTypes cData pFun eFun =
          do varNames <- mapM (lift . newName . ("x" ++) . show . fst)
                         $ zip (natsFrom 0) cTypes
             () <- ensureCxt cxt locTyvars cTypes
             let varsTypesData = zip3 varNames cTypes cData
             return $ Clause [(pFun varsTypesData)]
                        (NormalB $ eFun varsTypesData) []

      -- ensure that MbTypeRepr a holds for each type a in cTypes
      ensureCxt :: Cxt -> [TyVarBndr] -> [TH.Type] -> CxtStateQ ()
      ensureCxt cxt locTyvars cTypes =
          foldM (const (ensureCxt1 cxt locTyvars)) () cTypes

      -- FIXME: it is not possible (or, at least, not easy) to determine
      -- if MbTypeRepr a is implied from a current Cxt... so we just add
      -- everything we need to the returned Cxt, except for
      ensureCxt1 :: Cxt -> [TyVarBndr] -> TH.Type -> CxtStateQ ()
      ensureCxt1 cxt locTyvars t = undefined
      {-
      ensureCxt1 cxt locTyvars t = do
        curCxt = get
        let fullCxt = cxt ++ curCxt
        isOk <- isMbTypeRepr fullCxt

      isMbTypeRepr
       -}
-}
