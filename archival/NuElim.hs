{-# LANGUAGE GADTs, Rank2Types, TypeOperators, ViewPatterns #-}

module NuElim (
  NuElimProof(..),
  NuElimDataProof(),
  NuElim(..), mkNuElimData,
  mapNames
) where

--import Data.Data
import Data.Binding.Hobbits
import Language.Haskell.TH hiding (Name)
import qualified Language.Haskell.TH as TH
--import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.State


-- "proofs" that type a is an allowed type for nu-elimination; i.e.,
-- that the multi-binding of an Mb ctx a can be eliminated by nuWithElim
data NuElimProof a where
    NuElimName :: NuElimProof (Name a)
    NuElimMb :: NuElimProof a -> NuElimProof (Mb ctx a)
    NuElimFun :: NuElimProof a -> NuElimProof b -> NuElimProof (a -> b)
    NuElimData :: NuElimDataProof a -> NuElimProof a

data NuElimDataProof a =
    NuElimDataProof (forall ctx. MapC Name ctx -> MapC Name ctx -> a -> a)


-- the NuElim class and some useful instances
class NuElim a where
    nuElimProof :: NuElimProof a

instance NuElim (Name a) where
    nuElimProof = NuElimName

instance (NuElim a, NuElim b) => NuElim (a -> b) where
    nuElimProof = NuElimFun nuElimProof nuElimProof

instance NuElim a => NuElim (Mb ctx a) where
    nuElimProof = NuElimMb nuElimProof

instance NuElim a => NuElim [a] where
    nuElimProof = NuElimData (NuElimDataProof $ (\c1 c2 -> map (mapNames c1 c2)))


-- map the names in one MapC to the corresponding ones in another
mapNamesPf :: NuElimProof a -> MapC Name ctx -> MapC Name ctx -> a -> a
mapNamesPf NuElimName Nil Nil n = n
mapNamesPf NuElimName (names :> m) (names' :> m') n =
    case cmpName m n of
      Just Refl -> m'
      Nothing -> mapNamesPf NuElimName names names' n
mapNamesPf (NuElimMb nuElim) names names' x = undefined -- FIXME!
mapNamesPf (NuElimFun nuElimIn nuElimOut) names names' f =
    (mapNamesPf nuElimOut names names') . f . (mapNamesPf nuElimIn names' names)
mapNamesPf (NuElimData (NuElimDataProof mapFun)) names names' x =
    mapFun names names' x


-- just like mapNamesPf, except use the NuElim class
mapNames :: NuElim a => MapC Name ctx -> MapC Name ctx -> a -> a
mapNames = mapNamesPf nuElimProof


-- now we define some TH to create NuElimDataProofs

natsFrom i = i : natsFrom (i+1)

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

snd3 :: (a,b,c) -> b
snd3 (_,y,_) = y

thd3 :: (a,b,c) -> c
thd3 (_,_,z) = z


type Names = (TH.Name, TH.Name, TH.Name, TH.Name)

mapNamesType a = [t| forall ctx. MapC Name ctx -> MapC Name ctx -> $a -> $a |]

mkNuElimData :: Q [Dec] -> Q [Dec]
mkNuElimData declsQ =
    do decls <- declsQ
       (cxt, cType, tName, constrs, tyvars) <- getNuElimInfo decls
       fName <- newName "f"
       x1Name <- newName "x1"
       x2Name <- newName "x2"
       clauses <- mapM (getClause (tName, fName, x1Name, x2Name)) constrs
       mapNamesT <- mapNamesType (return cType)
       return [InstanceD
               cxt (AppT (ConT ''NuElim) cType)
               [ValD (VarP 'nuElimProof)
                (NormalB
                 $ AppE (ConE 'NuElimData)
                   $ AppE (ConE 'NuElimDataProof)
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
      -- get the name from a data type
      getTCtor t = getTCtorHelper t t []
      getTCtorHelper (ConT tName) topT tyvars = Just (topT, tName, tyvars)
      getTCtorHelper (AppT t1 (VarT var)) topT tyvars =
          getTCtorHelper t1 topT (tyvars ++ [var])
      getTCtorHelper (SigT t1 _) topT tyvars = getTCtorHelper t1 topT tyvars
      getTCtorHelper _ _ _ = Nothing

      -- fail for getNuElimInfo
      getNuElimInfoFail t =
          fail ("mkNuElimData: " ++ show t
                ++ " is not a NuElim instance for a (G)ADT applied to 0 or more type vars")

      -- get info for conName
      getNuElimInfo topT@[InstanceD cxt
                          (AppT (ConT nuElim)
                           (getTCtor -> Just (t, tName, tyvars))) _]
          | nuElim == ''NuElim =
              reify tName >>= \info ->
                  case info of
                    TyConI (DataD _ _ _ constrs _) ->
                        return (cxt, t, tName, constrs, tyvars)
                    _ -> getNuElimInfoFail topT

      getNuElimInfo t = getNuElimInfoFail t

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

-- create a NuElimDataProof for a (G)ADT
mkNuElimDataProofOld :: Q TH.Name -> Q Exp
mkNuElimDataProofOld conNameQ =
    do conName <- conNameQ
       (cxt, name, tyvars, constrs) <- getNuElimInfo conName
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
      getNuElimInfo conName =
          reify conName >>= \info ->
              case info of
                TyConI (DataD cxt name tyvars constrs _) ->
                    return (cxt, name, tyvars, constrs)
                _ -> fail ("mkNuElimDataProof: " ++ show conName
                           ++ " is not a (G)ADT")
      {-
      -- report failure
      getNuElimInfoFail t =
          fail ("mkNuElimDataProof: " ++ show t
                ++ " is not a fully applied (G)ADT")

      getNuElimInfo (ConT conName) topT =
          reify conName >>= \info ->
              case info of
                TyConI (DataD cxt name tyvars constrs _) ->
                    return (cxt, name, tyvars, constrs)
                _ -> getNuElimInfoFail topT
      getNuElimInfo (AppT t _) topT = getNuElimInfo t topT
      getNuElimInfo (SigT t _) topT = getNuElimInfo t topT
      getNuElimInfo _ topT = getNuElimInfoFail topT
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

      -- ensure that NuElim a holds for each type a in cTypes
      ensureCxt :: Cxt -> [TyVarBndr] -> [Type] -> CxtStateQ ()
      ensureCxt cxt locTyvars cTypes =
          foldM (const (ensureCxt1 cxt locTyvars)) () cTypes

      -- FIXME: it is not possible (or, at least, not easy) to determine
      -- if NuElim a is implied from a current Cxt... so we just add
      -- everything we need to the returned Cxt, except for 
      ensureCxt1 :: Cxt -> [TyVarBndr] -> Type -> CxtStateQ ()
      ensureCxt1 cxt locTyvars t = undefined
      {-
      ensureCxt1 cxt locTyvars t = do
        curCxt = get
        let fullCxt = cxt ++ curCxt
        isOk <- isNuElim fullCxt 

      isNuElim 
       -}
