{-# LANGUAGE GADTs, RankNTypes, TypeOperators, ViewPatterns, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, DataKinds #-}

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
  NuMatching(..), mkNuMatching, NuMatchingList(..), NuMatching1(..),
  MbTypeRepr()
) where

--import Data.Typeable
import Language.Haskell.TH hiding (Name)
import qualified Language.Haskell.TH as TH
import Control.Monad.State
--import Control.Monad.Identity

import Data.Type.RList
import Data.Binding.Hobbits.Internal.Name
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.Internal.Closed


{-| Just like 'mapNamesPf', except uses the NuMatching class. -}
mapNames :: NuMatching a => MapRList Name ctx -> MapRList Name ctx -> a -> a
mapNames = mapNamesPf nuMatchingProof


{-|
  Instances of the @'NuMatching' a@ class allow pattern-matching on
  multi-bindings whose bodies have type @a@, i.e., on multi-bindings
  of type @'Mb' ctx a@. The structure of this class is mostly hidden
  from the user; see 'mkNuMatching' to see how to create instances
  of the @NuMatching@ class.
-}
class NuMatching a where
    nuMatchingProof :: MbTypeRepr a

instance NuMatching (Name a) where
    nuMatchingProof = MbTypeReprName

instance NuMatching (Cl a) where
    -- no need to map free variables in a Closed object
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> id))

instance (NuMatching a, NuMatching b) => NuMatching (a -> b) where
    nuMatchingProof = MbTypeReprFun nuMatchingProof nuMatchingProof

instance NuMatching a => NuMatching (Mb ctx a) where
    nuMatchingProof = MbTypeReprMb nuMatchingProof

instance NuMatching Int where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> id))

instance NuMatching Integer where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> id))

instance NuMatching Char where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> id))

instance NuMatching () where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> id))

instance (NuMatching a, NuMatching b) => NuMatching (a,b) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 (a,b) -> (mapNames c1 c2 a, mapNames c1 c2 b)))

instance (NuMatching a, NuMatching b, NuMatching c) => NuMatching (a,b,c) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 (a,b,c) -> (mapNames c1 c2 a, mapNames c1 c2 b, mapNames c1 c2 c)))

instance (NuMatching a, NuMatching b, NuMatching c, NuMatching d) => NuMatching (a,b,c,d) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 (a,b,c,d) -> (mapNames c1 c2 a, mapNames c1 c2 b, mapNames c1 c2 c, mapNames c1 c2 d)))

instance (NuMatching a, NuMatching b) => NuMatching (Either a b) where
    nuMatchingProof = MbTypeReprData
                  (MkMbTypeReprData
                   $ (\c1 c2 x -> case x of
                                    Left l -> Left (mapNames c1 c2 l)
                                    Right r -> Right (mapNames c1 c2 r)))

instance NuMatching a => NuMatching [a] where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> map (mapNames c1 c2)))

instance NuMatching (Member c a) where
    nuMatchingProof = MbTypeReprData (MkMbTypeReprData $ (\c1 c2 -> id))


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

data NuMatchingObj a = NuMatching a => NuMatchingObj ()

-- the NuMatchingList class, for saying that NuMatching holds for a context of types
class NuMatchingList args where
    nuMatchingListProof :: MapRList NuMatchingObj args

instance NuMatchingList RNil where
    nuMatchingListProof = MNil

instance (NuMatchingList args, NuMatching a) => NuMatchingList (args :> a) where
    nuMatchingListProof = nuMatchingListProof :>: NuMatchingObj ()


class NuMatching1 f where
    nuMatchingProof1 :: NuMatching a => NuMatchingObj (f a)

-- README: deriving NuMatching from NuMatching1 leads to overlapping instances
-- for, e.g., Name a
{-
instance (NuMatching1 f, NuMatching a) => NuMatching (f a) where
    nuMatchingProof = nuMatchingProof1 nuMatchingProof
-}

instance (NuMatching1 f, NuMatchingList ctx) => NuMatching (MapRList f ctx) where
    nuMatchingProof = MbTypeReprData $ MkMbTypeReprData $ helper nuMatchingListProof where
        helper :: NuMatching1 f =>
                  MapRList NuMatchingObj args -> MapRList Name ctx1 ->
                  MapRList Name ctx1 -> MapRList f args -> MapRList f args
        helper MNil c1 c2 MNil = MNil
        helper (proofs :>: NuMatchingObj ()) c1 c2 (elems :>: (elem :: f a)) =
            case nuMatchingProof1 :: NuMatchingObj (f a) of
              NuMatchingObj () ->
                  (helper proofs c1 c2 elems) :>:
                  mapNames c1 c2 elem


-- now we define some TH to create NuMatchings

natsFrom i = i : natsFrom (i+1)

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

snd3 :: (a,b,c) -> b
snd3 (_,y,_) = y

thd3 :: (a,b,c) -> c
thd3 (_,_,z) = z


type Names = (TH.Name, TH.Name, TH.Name, TH.Name)

mapNamesType a = [t| forall ctx. MapRList Name ctx -> MapRList Name ctx -> $a -> $a |]

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
mkNuMatching :: Q Type -> Q [Dec]
mkNuMatching tQ =
    do t <- tQ
       (cxt, cType, tName, constrs, tyvars) <- getMbTypeReprInfoTop t
       fName <- newName "f"
       x1Name <- newName "x1"
       x2Name <- newName "x2"
       clauses <- mapM (getClause (tName, fName, x1Name, x2Name)) constrs
       mapNamesT <- mapNamesType (return cType)
       return [InstanceD
               cxt (AppT (ConT ''NuMatching) cType)
               [ValD (VarP 'nuMatchingProof)
                (NormalB
                 $ AppE (ConE 'MbTypeReprData)
                   $ AppE (ConE 'MkMbTypeReprData)
                         $ LetE [SigD fName
                                 $ ForallT (map PlainTV tyvars) cxt mapNamesT,
                                 FunD fName clauses]
                               (VarE fName)) []]]

       {-
       return (LetE
               [SigD fName
                     (ForallT tyvars reqCxt
                     $ foldl AppT ArrowT
                           [foldl AppT (ConT conName)
                                      (map tyVarToType tyvars)]),
                FunD fname clauses]
               (VarE fname))
        -}
    where
      -- extract the name from a TyVarBndr
      tyBndrToName (PlainTV n) = n
      tyBndrToName (KindedTV n _) = n

      -- fail for getMbTypeReprInfo
      getMbTypeReprInfoFail t extraMsg =
          fail ("mkMbTypeRepr: " ++ show t
                ++ " is not a type constructor for a (G)ADT applied to zero or more distinct type variables" ++ extraMsg)

      -- get info for conName (top-level call)
      getMbTypeReprInfoTop t = getMbTypeReprInfo [] [] t t

      -- get info for conName
      getMbTypeReprInfo ctx tyvars topT (ConT tName) =
          do info <- reify tName
             case info of
               TyConI (DataD _ _ tyvarsReq constrs _) ->
                   success tyvarsReq constrs
               TyConI (NewtypeD _ _ tyvarsReq constr _) ->
                   success tyvarsReq [constr]
               _ -> getMbTypeReprInfoFail topT (": info for " ++ (show tName) ++ " = " ++ (show info))
          where
            success tyvarsReq constrs =
                let tyvarsRet = if tyvars == [] && ctx == []
                                then map tyBndrToName tyvarsReq
                                else tyvars in
                return (ctx,
                        foldl AppT (ConT tName) (map VarT tyvars),
                        tName, constrs, tyvarsRet)

      getMbTypeReprInfo ctx tyvars topT (AppT f (VarT argName)) =
          if elem argName tyvars then
              getMbTypeReprInfoFail topT ""
          else
              getMbTypeReprInfo ctx (argName:tyvars) topT f

      getMbTypeReprInfo ctx tyvars topT (ForallT _ ctx' t) =
          getMbTypeReprInfo (ctx ++ ctx') tyvars topT t

      getMbTypeReprInfo ctx tyvars topT t = getMbTypeReprInfoFail topT ""

      -- get the name from a data type
      getTCtor t = getTCtorHelper t t []
      getTCtorHelper (ConT tName) topT tyvars = Just (topT, tName, tyvars)
      getTCtorHelper (AppT t1 (VarT var)) topT tyvars =
          getTCtorHelper t1 topT (tyvars ++ [var])
      getTCtorHelper (SigT t1 _) topT tyvars = getTCtorHelper t1 topT tyvars
      getTCtorHelper _ _ _ = Nothing

      -- get a list of Clauses, one for each constructor in constrs
      getClauses :: Names -> [Con] -> Q [Clause]
      getClauses names constrs = mapM (getClause names) constrs

      getClause :: Names -> Con -> Q Clause
      getClause names (NormalC cName cTypes) =
          getClauseHelper names (map snd cTypes)
                          (natsFrom 0)
                          (\l -> ConP cName (map (VarP . fst3) l))
                          (\l -> foldl AppE (ConE cName) (map fst3 l))

      getClause names (RecC cName cVarTypes) =
          getClauseHelper names (map thd3 cVarTypes)
                         (map fst3 cVarTypes)
                         (\l -> RecP cName
                                (map (\(var,_,field) -> (field, VarP var)) l))
                         (\l -> RecConE cName
                                (map (\(exp,_,field) -> (field, exp)) l))

      getClause names (InfixC cType1 cName cType2) =
          undefined -- FIXME

      getClause names (ForallC _ _ con) =  getClause names con

      getClauseHelper :: Names -> [Type] -> [a] ->
                         ([(TH.Name,Type,a)] -> Pat) ->
                         ([(Exp,Type,a)] -> Exp) ->
                         Q Clause
      getClauseHelper names@(tName, fName, x1Name, x2Name) cTypes cData pFun eFun =
          do varNames <- mapM (newName . ("x" ++) . show . fst)
                         $ zip (natsFrom 0) cTypes
             let varsTypesData = zip3 varNames cTypes cData
             let expsTypesData = map (mkExpTypeData names) varsTypesData
             return $ Clause [(VarP x1Name), (VarP x2Name), (pFun varsTypesData)]
                        (NormalB $ eFun expsTypesData) []

      mkExpTypeData :: Names -> (TH.Name,Type,a) -> (Exp,Type,a)
      mkExpTypeData (tName, fName, x1Name, x2Name)
                    (varName, getTCtor -> Just (t, tName', _), cData)
          | tName == tName' =
              -- the type of the arg is the same as the (G)ADT we are
              -- recursing over; apply the recursive function
              (foldl AppE (VarE fName)
                         [(VarE x1Name), (VarE x2Name), (VarE varName)],
               t, cData)
      mkExpTypeData (tName, fName, x1Name, x2Name) (varName, t, cData) =
          -- the type of the arg is not the same as the (G)ADT; call mapNames
          (foldl AppE (VarE 'mapNames)
                     [(VarE x1Name), (VarE x2Name), (VarE varName)],
           t, cData)

-- FIXME: old stuff below

type CxtStateQ a = StateT Cxt Q a

-- create a MkMbTypeReprData for a (G)ADT
mkMkMbTypeReprDataOld :: Q TH.Name -> Q Exp
mkMkMbTypeReprDataOld conNameQ =
    do conName <- conNameQ
       (cxt, name, tyvars, constrs) <- getMbTypeReprInfo conName
       (clauses, reqCxt) <- runStateT (getClauses cxt name tyvars constrs) []
       fname <- newName "f"
       return (LetE
               [SigD fname
                     (ForallT tyvars reqCxt
                     $ foldl AppT ArrowT
                           [foldl AppT (ConT conName)
                                      (map tyVarToType tyvars)]),
                FunD fname clauses]
               (VarE fname))
    where
      -- convert a TyVar to a Name
      tyVarToType (PlainTV n) = VarT n
      tyVarToType (KindedTV n _) = VarT n

      -- get info for conName
      getMbTypeReprInfo conName =
          reify conName >>= \info ->
              case info of
                TyConI (DataD cxt name tyvars constrs _) ->
                    return (cxt, name, tyvars, constrs)
                _ -> fail ("mkMkMbTypeReprData: " ++ show conName
                           ++ " is not a (G)ADT")
      {-
      -- report failure
      getMbTypeReprInfoFail t =
          fail ("mkMkMbTypeReprData: " ++ show t
                ++ " is not a fully applied (G)ADT")

      getMbTypeReprInfo (ConT conName) topT =
          reify conName >>= \info ->
              case info of
                TyConI (DataD cxt name tyvars constrs _) ->
                    return (cxt, name, tyvars, constrs)
                _ -> getMbTypeReprInfoFail topT
      getMbTypeReprInfo (AppT t _) topT = getMbTypeReprInfo t topT
      getMbTypeReprInfo (SigT t _) topT = getMbTypeReprInfo t topT
      getMbTypeReprInfo _ topT = getMbTypeReprInfoFail topT
       -}

      -- get a list of Clauses, one for each constructor in constrs
      getClauses :: Cxt -> TH.Name -> [TyVarBndr] -> [Con] -> CxtStateQ [Clause]
      getClauses cxt name tyvars constrs =
          mapM (getClause cxt name tyvars []) constrs

      getClause :: Cxt -> TH.Name -> [TyVarBndr] -> [TyVarBndr] -> Con ->
                   CxtStateQ Clause
      getClause cxt name tyvars locTyvars (NormalC cName cTypes) =
          getClauseHelper cxt name tyvars locTyvars (map snd cTypes)
                          (natsFrom 0)
                          (\l -> ConP cName (map (VarP . fst3) l))
                          (\l -> foldl AppE (ConE cName) (map (VarE . fst3) l))

      getClause cxt name tyvars locTyvars (RecC cName cVarTypes) =
          getClauseHelper cxt name tyvars locTyvars (map thd3 cVarTypes)
                         (map fst3 cVarTypes)
                         (\l -> RecP cName
                                (map (\(var,_,field) -> (field, VarP var)) l))
                         (\l -> RecConE cName
                                (map (\(var,_,field) -> (field, VarE var)) l))

      getClause cxt name tyvars locTyvars (InfixC cType1 cName cType2) =
          undefined -- FIXME

      getClause cxt name tyvars locTyvars (ForallC tyvars2 cxt2 con) =
          getClause (cxt ++ cxt2) name tyvars (locTyvars ++ tyvars2) con

      getClauseHelper :: Cxt -> TH.Name -> [TyVarBndr] -> [TyVarBndr] ->
                         [Type] -> [a] ->
                         ([(TH.Name,Type,a)] -> Pat) ->
                         ([(TH.Name,Type,a)] -> Exp) ->
                         CxtStateQ Clause
      getClauseHelper cxt name tyvars locTyvars cTypes cData pFun eFun =
          do varNames <- mapM (lift . newName . ("x" ++) . show . fst)
                         $ zip (natsFrom 0) cTypes
             () <- ensureCxt cxt locTyvars cTypes
             let varsTypesData = zip3 varNames cTypes cData
             return $ Clause [(pFun varsTypesData)]
                        (NormalB $ eFun varsTypesData) []

      -- ensure that MbTypeRepr a holds for each type a in cTypes
      ensureCxt :: Cxt -> [TyVarBndr] -> [Type] -> CxtStateQ ()
      ensureCxt cxt locTyvars cTypes =
          foldM (const (ensureCxt1 cxt locTyvars)) () cTypes

      -- FIXME: it is not possible (or, at least, not easy) to determine
      -- if MbTypeRepr a is implied from a current Cxt... so we just add
      -- everything we need to the returned Cxt, except for 
      ensureCxt1 :: Cxt -> [TyVarBndr] -> Type -> CxtStateQ ()
      ensureCxt1 cxt locTyvars t = undefined
      {-
      ensureCxt1 cxt locTyvars t = do
        curCxt = get
        let fullCxt = cxt ++ curCxt
        isOk <- isMbTypeRepr fullCxt 

      isMbTypeRepr 
       -}
