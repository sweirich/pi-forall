module Paths_pi_forall (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,1], versionTags = []}
bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/sweirich/Library/Haskell/ghc-7.6.3/lib/pi-forall-0.1/bin"
libdir     = "/Users/sweirich/Library/Haskell/ghc-7.6.3/lib/pi-forall-0.1/lib"
datadir    = "/Users/sweirich/Library/Haskell/ghc-7.6.3/lib/pi-forall-0.1/share"
libexecdir = "/Users/sweirich/Library/Haskell/ghc-7.6.3/lib/pi-forall-0.1/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catchIO (getEnv "pi_forall_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "pi_forall_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "pi_forall_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "pi_forall_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
