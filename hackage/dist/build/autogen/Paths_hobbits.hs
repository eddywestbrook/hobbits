module Paths_hobbits (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [2,0], versionTags = []}
bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/eddy/.cabal/bin"
libdir     = "/Users/eddy/.cabal/lib/hobbits-2.0/ghc-7.6.3"
datadir    = "/Users/eddy/.cabal/share/hobbits-2.0"
libexecdir = "/Users/eddy/.cabal/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catchIO (getEnv "hobbits_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "hobbits_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "hobbits_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "hobbits_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
