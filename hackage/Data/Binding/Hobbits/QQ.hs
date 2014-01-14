{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Data.Binding.Hobbits.QQ
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- Defines a quasi-quoter for writing patterns that match the bodies of 'Mb'
-- multi-bindings. Uses the haskell-src-exts parser. @[nuP| P ]@ defines a
-- pattern that will match a multi-binding whose body matches @P@. Any
-- variables matched by @P@ will remain inside the binding; thus, for example,
-- in the pattern @[nuP| x |]@, @x@ matches the entire multi-binding.
--
-- Examples:
--
-- > case (nu Left) of [nuP| Left x |] -> x  ==  nu id
--
-- [clP| P |] does the same for the Cl type, and [clNuP| P |] works for
-- both simultaneously: Cl (Mb ctx a).

module Data.Binding.Hobbits.QQ (nuP, clP, clNuP) where

import qualified Data.Binding.Hobbits.InternalUtilities as IU
import Data.Binding.Hobbits.Internal (Mb(..), Cl(..))
import Data.Binding.Hobbits.PatternParser (parsePattern)

import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Ppr as TH
import Language.Haskell.TH.Quote

import qualified Data.Generics as SYB
import Control.Monad.Writer (runWriterT, tell)
import Data.Monoid (Any(..))





compose :: Exp -> Exp -> Exp
compose f g = VarE '(.) `AppE` f `AppE` g

patQQ n pat = QuasiQuoter (err "Exp") pat (err "Type") (err "Decs")
  where err s = error $ "QQ `" ++ n ++ "' is for patterns, not " ++ s ++ "."





data WrapKit =
  -- _add adds structure just before binding the name (i.e. on VarP)
  -- _rm  removes structure that was added for the @ patterns
  -- _top removes structure at the top of the whole pattern
  WrapKit {_add :: Exp, _rm :: Pat -> Pat, _top :: Bool -> Pat -> Pat}

outsideKit (WrapKit {_add = addO, _rm = rmO, _top = topO})
           (WrapKit {_add = addI, _rm = rmI, _top = topI}) =
  WrapKit {_add = addO `compose` addI,
           _rm = rmO . rmI,
           _top = \b -> topO b . topI b}

-- wrapVars changes the types of names bound in a pattern
wrapVars :: Monad m => WrapKit -> Pat -> m Pat
wrapVars (WrapKit {_add = add, _rm = rm, _top = top}) pat = do
  (pat', Any usedAdd) <- runWriterT m
  return $ top usedAdd pat'
  where
    m = IU.everywhereButM (SYB.mkQ False isExp) (SYB.mkM w) pat
      where isExp :: Exp -> Bool
            -- don't recur into the expression part of view patterns
            isExp _ = True

    -- this should be called if the 'add' function is ever used
    hit x = tell (Any True) >> return x

    -- wraps up bound names
    w p@VarP{} = hit $ ViewP add p
    -- wraps for the bound name, then immediately unwraps
    -- for the rest of the pattern
    w (AsP v p) = hit $ ViewP add $ AsP v $ rm p
    -- requires the expression to be closed
    w (ViewP (VarE n) p) = return $ ViewP (VarE 'unCl `AppE` VarE n) p
    w (ViewP e _) = fail $ "view function must be a single name: `" ++ show (TH.ppr e) ++ "'"
    w p = return p





parseHere :: String -> Q Pat
parseHere s = do
  fn <- loc_filename `fmap` location
  case parsePattern fn s of
    Left e -> error $ "Parse error: `" ++ e ++
      "'\n\n\t when parsing pattern: `" ++ s ++ "'."
    Right p -> return p





same_ctx :: Mb ctx a -> Mb ctx b -> Mb ctx b
same_ctx _ x = x

nuKit mb ln = WrapKit {_add = add, _rm = rm, _top = top} where
  add = (VarE 'same_ctx `AppE` VarE mb) `compose`
        (ConE 'MkMb     `AppE` VarE ln)

  rm p = ConP 'MkMb [WildP, p]

  top b p = if b then AsP mb $ ConP 'MkMb [VarP ln, p] else rm p





nuP = patQQ "nuP" $ \s -> do
  mb <- newName "mb"
  ln <- newName "bs"

  parseHere s >>= wrapVars (nuKit mb ln)





clKit = WrapKit {_add = ConE 'Cl, _rm = rm, _top = const rm}
  where rm p = ConP 'Cl [p]

clP = patQQ "clP" $ (>>= wrapVars clKit) . parseHere





clNuP = patQQ "clNuP" $ \s -> do
  mb <- newName "mb"
  ln <- newName "bs"

  parseHere s >>= wrapVars (clKit `outsideKit` nuKit mb ln)
