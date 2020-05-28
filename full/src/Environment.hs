{- OPLSS -}

{-# LANGUAGE GADTs, NamedFieldPuns, FlexibleContexts, ViewPatterns, RankNTypes, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Utilities for managing a typechecking context.
module Environment
  (
    TcMonad, runTcMonad,
    Env,Hint(..),
    emptyEnv,
    lookupTy, lookupTyMaybe, lookupDef, lookupRecDef, lookupHint,     lookupTCon, lookupDCon, lookupDConAll, extendCtxTele, 
    getTys, getCtx, getLocalCtx, extendCtx,
    extendCtxs, extendCtxsGlobal,
    extendCtxMods,
    extendHints,
    extendSourceLocation, getSourceLocation,
    err, warn, extendErr, D(..),Err(..),
  ) where

import Syntax
import PrettyPrint

import Unbound.Generics.LocallyNameless

import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos(SourcePos)
import Control.Monad.Reader
import Control.Monad.Except


#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(7,10,3,0)
-- ghc >= 7.10.3
#else
-- older ghc versions, but MIN_VERSION_GLASGOW_HASKELL defined
#endif
#else
-- MIN_VERSION_GLASGOW_HASKELL not even defined yet (ghc <= 7.8.x)
import Data.Monoid
#endif


-- import Data.Semigroup if it is not already in base
#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup
#endif

import Data.List
import Data.Maybe (listToMaybe, catMaybes)


-- | The type checking Monad includes a reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), error (for error reporting), and IO
-- (for e.g.  warning messages).
type TcMonad = FreshMT (ReaderT Env (ExceptT Err IO))

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = runExceptT $
                     runReaderT (runFreshMT m) env


-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. Disp a => SourcePos -> a -> SourceLocation

-- | Type declarations
data Hint = Hint TName Term

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env { ctx :: [Decl],
               -- ^ elaborated term and datatype declarations.
                 globals :: Int,
               -- ^ how long the tail of "global" variables in the context is
               --    (used to supress printing those in error messages)
                 hints :: [Hint],
               -- ^ Type declarations (signatures): it's not safe to
               -- put these in the context until a corresponding term
               -- has been checked.
                 sourceLocation ::  [SourceLocation]
               -- ^ what part of the file we are in (for errors/warnings)
               }
  --deriving Show



-- | The initial environment.
emptyEnv :: Env
emptyEnv = Env { ctx = [] , globals = 0, hints = [], sourceLocation = [] }

instance Disp Env where
  disp e = vcat [disp decl | decl <- ctx e]

-- | Return a list of all type bindings, and their names.
getTys :: (MonadReader Env m) => m [(TName,Term)]
getTys = do
  ctx <- asks ctx
  return $ catMaybes (map unwrap ctx)
    where unwrap (Sig v ty) = Just (v,ty)
          unwrap _ = Nothing

-- | Find a name's user supplied type signature.
lookupHint   :: (MonadReader Env m) => TName -> m (Maybe Term)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [ ty | Hint v' ty <- hints, v == v']

-- | Find a name's type in the context.
lookupTyMaybe :: (MonadReader Env m)
         => TName -> m (Maybe Term)
lookupTyMaybe v = do
  ctx <- asks ctx
  return $ listToMaybe [ty | Sig  v' ty <- ctx, v == v']

-- | Find the type of a name specified in the context
-- throwing an error if the name doesn't exist
lookupTy :: (MonadReader Env m, MonadError Err m)
         => TName -> m Term
lookupTy v =
  do x <- lookupTyMaybe v
     gamma <- getLocalCtx
     case x of
       Just res -> return res
       Nothing -> err [DS ("The variable " ++ show v++ " was not found."),
                       DS "in context", DD gamma]

-- | Find a name's def in the context.
lookupDef :: (MonadReader Env m)
          => TName -> m (Maybe Term)
lookupDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | Def v' a <- ctx, v == v']

lookupRecDef :: (MonadReader Env m)
          => TName -> m (Maybe Term)
lookupRecDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | RecDef v' a <- ctx, v == v']

-- | Find a type constructor in the context
lookupTCon :: (MonadReader Env m, MonadError Err m)
          => TCName -> m (Telescope,Maybe [ConstructorDef])
lookupTCon v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = do currentEnv <- asks ctx
                      err [DS "The type constructor", DD v, DS "was not found.",
                           DS "The current environment is", DD currentEnv]
    scanGamma ((Data v' delta cs):g) =
      if v == v'
        then return $ (delta,Just cs)
        else  scanGamma g
    scanGamma ((DataSig v' delta):g) =
      if v == v'
         then return $ (delta,Nothing)
         else scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll :: (MonadReader Env m)
          => DCName -> m [(TCName,(Telescope,ConstructorDef))]
lookupDConAll v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((Data v' delta cs):g) =
        case find (\(ConstructorDef _ v'' tele) -> v''==v ) cs of
          Nothing -> scanGamma g
          Just c -> do more <- scanGamma g
                       return $ [ (v', (delta, c)) ] ++ more
    scanGamma ((DataSig v' delta):g) = scanGamma g
    scanGamma (_:g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon :: (MonadReader Env m, MonadError Err m)
              => DCName -> TCName -> m (Telescope,Telescope)
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just (delta, ConstructorDef _ _ deltai) ->
      return (delta, deltai)
    Nothing  ->
      err ([DS "Cannot find data constructor", DS c,
           DS "for type", DD tname,
           DS "Potential matches were:"] ++
           (map (DD . fst) matches) ++
           (map (DD . snd . snd) matches))



-- | Extend the context with a new binding.
extendCtx :: (MonadReader Env m) => Decl -> m a -> m a
extendCtx d =
  local (\ m@(Env {ctx = cs}) -> m { ctx = d:cs })

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [Decl] -> m a -> m a
extendCtxs ds =
  local (\ m@(Env {ctx = cs}) -> m { ctx = ds ++ cs })

-- | Extend the context with a list of bindings, marking them as "global"
extendCtxsGlobal :: (MonadReader Env m) => [Decl] -> m a -> m a
extendCtxsGlobal ds =
  local (\ m@(Env {ctx = cs}) -> m { ctx     = ds ++ cs,
                                     globals = length (ds ++ cs)})

-- | Extend the context with a telescope
extendCtxTele :: (MonadReader Env m, MonadIO m) => Telescope -> m a -> m a
extendCtxTele Empty m = m
extendCtxTele (Constraint (Var x) t2 tele) m =
  extendCtx (Def x t2) $ extendCtxTele tele m
extendCtxTele (Constraint t1 t2 tele) m = do
  warn [DS "extendCtxTele found:", DD t1, DS "=", DD t2]
  extendCtxTele tele m
extendCtxTele (Cons ep x ty tele) m =
  extendCtx (Sig x ty) $ extendCtxTele tele m


-- | Extend the context with a module
-- Note we must reverse the order.
extendCtxMod :: (MonadReader Env m) => Module -> m a -> m a
extendCtxMod m k = extendCtxs (reverse $ moduleEntries m) k

-- | Extend the context with a list of modules
extendCtxMods :: (MonadReader Env m) => [Module] -> m a -> m a
extendCtxMods mods k = foldr extendCtxMod k mods

-- | Get the complete current context
getCtx :: MonadReader Env m => m [Decl]
getCtx = asks ctx

-- | Get the prefix of the context that corresponds to local variables.
getLocalCtx :: MonadReader Env m => m [Decl]
getLocalCtx = do
  g <- asks ctx
  glen <- asks globals
  return $ take (length g - glen) g

-- | Push a new source position on the location stack.
extendSourceLocation :: (MonadReader Env m, Disp t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t =
  local (\ e@(Env {sourceLocation = locs}) -> e {sourceLocation = (SourceLocation p t):locs})

-- | access current source location
getSourceLocation :: MonadReader Env m => m [SourceLocation]
getSourceLocation = asks sourceLocation

-- | Add a type hint
extendHints :: (MonadReader Env m) => Hint -> m a -> m a
extendHints h = local (\m@(Env {hints = hs}) -> m { hints = h:hs })


-- | An error that should be reported to the user
data Err = Err [SourceLocation] Doc

-- | Augment the error message with addition information
extendErr :: MonadError Err m => m a -> Doc -> m a
extendErr ma msg'  =
  ma `catchError` \(Err ps msg) ->
  throwError $ Err ps (msg $$ msg')

#if MIN_VERSION_base(4,11,0)
instance Semigroup Err where
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)
#endif

instance Monoid Err where
  mempty = Err [] mempty
#if !MIN_VERSION_base(4,11,0)
  mappend (Err src1 d1) (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)
#endif

-- instance Error Err where
--  strMsg msg = Err [] (text msg)

instance Disp Err where
  disp (Err [] msg) = msg
  disp (Err ((SourceLocation p term):_) msg)  =
    disp p $$
    nest 2 msg $$
    nest 2 (text "In the expression" $$ nest 2 (disp term))

-- | Throw an error
err :: (Disp a, MonadError Err m, MonadReader Env m) => a -> m b
err d = do
  loc <- getSourceLocation
  throwError $ Err loc (disp d)

-- | Print a warning
warn :: (Disp a, MonadReader Env m, MonadIO m) => a -> m ()
warn e = do
  loc <- getSourceLocation
  liftIO $ putStrLn $ "warning: " ++ render (disp (Err loc (disp e)))
