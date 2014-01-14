module Paths_hobbits (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [1,1,1], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/eddy/Library/Haskell/ghc-7.6.3/lib/hobbits-1.1.1/bin"
libdir     = "/Users/eddy/Library/Haskell/ghc-7.6.3/lib/hobbits-1.1.1/lib"
datadir    = "/Users/eddy/Library/Haskell/ghc-7.6.3/lib/hobbits-1.1.1/share"
libexecdir = "/Users/eddy/Library/Haskell/ghc-7.6.3/lib/hobbits-1.1.1/libexec"
sysconfdir = "/Users/eddy/Library/Haskell/ghc-7.6.3/lib/hobbits-1.1.1/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "hobbits_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "hobbits_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "hobbits_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "hobbits_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "hobbits_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
