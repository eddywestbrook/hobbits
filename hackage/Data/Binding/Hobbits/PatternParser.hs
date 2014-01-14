-- |
-- Module      : Data.Binding.Hobbits.PatternParser
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--
-- Using the haskell-src-meta package to parse Haskell patterns.

module Data.Binding.Hobbits.PatternParser (parsePattern) where

import Language.Haskell.TH

import qualified Language.Haskell.Exts.Parser as Meta

import qualified Language.Haskell.Meta.Parse as Meta

import qualified Language.Haskell.Meta.Parse as Sloppy
import qualified Language.Haskell.Meta.Syntax.Translate as Translate

#if MIN_VERSION_haskell_src_exts(1,14,0)
import Language.Haskell.Exts.Extension (KnownExtension(ViewPatterns),
                                        Extension(EnableExtension))
parsePatternExtensions =
  map EnableExtension $ ViewPatterns : Sloppy.myDefaultExtensions
#else
import Language.Haskell.Exts.Extension (KnownExtension(ViewPatterns))
parsePatternExtensions = ViewPatterns : Sloppy.myDefaultExtensions
#endif






parsePattern :: String -> String -> Either String Pat
parsePattern fn =
  fmap Translate.toPat . Meta.parseResultToEither .
  Meta.parsePatWithMode (Sloppy.myDefaultParseMode
                    {Meta.parseFilename = fn,
                     Meta.extensions = parsePatternExtensions })
