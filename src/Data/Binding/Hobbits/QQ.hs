{-# LANGUAGE TemplateHaskell, FlexibleContexts, PolyKinds #-}

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
-- @[clP| P |]@ does the same for the 'Closed' type, and @[clNuP| P |]@ works
-- for both simultaneously: @'Closed' ('Mb' ctx a)@.

module Data.Binding.Hobbits.QQ (nuP, clP, clNuP) where

import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Ppr as TH
import Language.Haskell.TH.Quote

import qualified Data.Generics as SYB
import Control.Monad.Writer (runWriterT, tell)
import Data.Monoid (Any(..))

import qualified Data.Binding.Hobbits.Internal.Utilities as IU
import Data.Binding.Hobbits.Internal.Mb
import Data.Binding.Hobbits.Internal.Closed
import Data.Binding.Hobbits.PatternParser (parsePattern)
import Data.Binding.Hobbits.NuMatching


-- | Helper function to apply an expression to multiple arguments
appEMulti :: Exp -> [Exp] -> Exp
appEMulti = foldl AppE

-- | Helper function to apply the (.) operator on expressions
compose :: Exp -> Exp -> Exp
compose f g = VarE '(.) `AppE` f `AppE` g

-- | @patQQ str pat@ builds a quasi-quoter named @str@ that parses
-- | patterns with @pat@
patQQ :: String -> (String -> Q Pat) -> QuasiQuoter
patQQ n pat = QuasiQuoter (err "Exp") pat (err "Type") (err "Decs")
  where err s = error $ "QQ `" ++ n ++ "' is for patterns, not " ++ s ++ "."


-- | A @WrapKit@ specifies a transformation to be applied to variables
-- | in a Template Haskell patterns, as follows:
--
-- * @_varView@ gives an expression for a function to be applied, as a
--   view pattern, to variables before matching them, including to
--   variables bound by @\@@ patterns;
--
-- * @_asXform@ gives a function to transform the bodies of \@
--   patterns, i.e., this function is applied to @p@ in pattern @x\@p@;
--
-- * @_topXform@ gives a function to transform the whole pattern after
--    @_varView@ and/or @_asXform@ have been applied to sub-patterns;
--    as the first argument, @_topXform@ also takes a flag indicating
--    whether any transformations have been applied to sub-patterns.
--
data WrapKit =
  WrapKit {_varView :: Exp, _asXform :: Pat -> Pat, _topXform :: Bool -> Pat -> Pat}

-- | Combine two WrapKits, composing the individual components
combineWrapKits :: WrapKit -> WrapKit -> WrapKit
combineWrapKits (WrapKit {_varView = varViewO, _asXform = asXformO, _topXform = topXformO})
           (WrapKit {_varView = varViewI, _asXform = asXformI, _topXform = topXformI}) =
  WrapKit {_varView = varViewO `compose` varViewI,
           _asXform = asXformO . asXformI,
           _topXform = \b -> topXformO b . topXformI b}

-- | Apply a 'WrapKit' to a pattern
wrapVars :: MonadFail m => WrapKit -> Pat -> m Pat
wrapVars (WrapKit {_varView = varView, _asXform = asXform, _topXform = topXform}) pat = do
  (pat', Any usedVarView) <- runWriterT m
  return $ topXform usedVarView pat'
  where
    m = IU.everywhereButM (SYB.mkQ False isExp) (SYB.mkM w) pat
      where isExp :: Exp -> Bool
            -- don't recur into the expression part of view patterns
            isExp _ = True

    -- this should be called if the 'varView' function is ever used
    hit x = tell (Any True) >> return x

    -- wraps up bound names
    w p@VarP{} = hit $ ViewP varView p
    -- wraps for the bound name, then immediately unwraps
    -- for the rest of the pattern
    w (AsP v p) = hit $ ViewP varView $ AsP v $ asXform p
    -- requires the expression to be closed
    w (ViewP (VarE n) p) = return $ ViewP (VarE 'unClosed `AppE` VarE n) p
    w (ViewP e _) = fail $ "view function must be a single name: `" ++ show (TH.ppr e) ++ "'"
    w p = return p

-- | Parse a pattern from a string, using 'parsePattern'
parseHere :: String -> Q Pat
parseHere s = do
  fn <- loc_filename `fmap` location
  case parsePattern fn s of
    Left e -> error $ "Parse error: `" ++ e ++
      "'\n\n\t when parsing pattern: `" ++ s ++ "'."
    Right p -> return p


-- | A helper function used to ensure two multi-bindings have the same contexts
same_ctx :: Mb ctx a -> Mb ctx b -> Mb ctx b
same_ctx _ x = x

-- | Builds a 'WrapKit' for parsing patterns that match over 'Mb'.
-- | Takes two fresh names as arguments.
nuKit :: TH.Name -> TH.Name -> WrapKit
nuKit topVar namesVar = WrapKit {_varView = varView, _asXform = asXform, _topXform = topXform} where
  varView = (VarE 'same_ctx `AppE` VarE topVar) `compose`
        (appEMulti (ConE 'MkMbPair) [VarE 'nuMatchingProof, VarE namesVar])
  asXform p = ViewP (VarE 'ensureFreshPair) (TupP [WildP, p])
  topXform b p = if b then AsP topVar $ ViewP (VarE 'ensureFreshPair) (TupP [VarP namesVar, p]) else asXform p

-- | Quasi-quoter for patterns that match over 'Mb'
nuP = patQQ "nuP" $ \s -> do
  topVar <- newName "topMb"
  namesVar <- newName "topNames"
  parseHere s >>= wrapVars (nuKit topVar namesVar)

-- | Builds a 'WrapKit' for parsing patterns that match over 'Closed'
clKit = WrapKit {_varView = ConE 'Closed, _asXform = asXform, _topXform = const asXform}
  where asXform p = ConP 'Closed [p]

-- | Quasi-quoter for patterns that match over 'Closed', built using 'clKit'
clP = patQQ "clP" $ (>>= wrapVars clKit) . parseHere

-- | Quasi-quoter for patterns that match over @'Closed' ('Mb' ctx a)@
clNuP = patQQ "clNuP" $ \s -> do
  topVar <- newName "topMb"
  namesVar <- newName "topNames"
  parseHere s >>= wrapVars (clKit `combineWrapKits` nuKit topVar namesVar)
