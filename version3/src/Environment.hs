{- pi-forall language -}

-- | Utilities for managing a typechecking context.
module Environment
  ( TcMonad,
    runTcMonad,
    Env,
    emptyEnv,
    lookupTy,
    lookupTyMaybe,
    lookupDef,
    lookupRecDef,
    lookupHint ,
    getCtx,
    getLocalCtx,
    extendCtx,
    extendCtxs,
    extendCtxsGlobal,
    extendCtxMods,
    extendHints,
    extendSourceLocation,
    getSourceLocation,
    err,
    warn,
    extendErr,
    D (..),
    Err (..){- SOLN EP -},
    getStage,
    withStage,
    checkStage {- STUBWITH -}
  )
where

import Control.Monad.Except
    ( unless, MonadError(..), MonadIO(..), ExceptT, runExceptT )
import Control.Monad.Reader
    ( MonadReader(local), asks, ReaderT(runReaderT) )

import Data.Maybe ( listToMaybe )
import PrettyPrint ( SourcePos, render, D(..), Disp(..), Doc )
import Syntax
import Text.PrettyPrint.HughesPJ ( ($$), nest, sep, text, vcat )
import qualified Unbound.Generics.LocallyNameless as Unbound

-- | The type checking Monad includes a reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), error (for error reporting), and IO
-- (for e.g.  warning messages).
type TcMonad = Unbound.FreshMT (ReaderT Env (ExceptT Err IO))

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m =
  runExceptT $
    runReaderT (Unbound.runFreshMT m) env

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. Disp a => SourcePos -> a -> SourceLocation

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env
  { -- | elaborated term and datatype declarations.
    ctx :: [Decl],
    -- | how long the tail of "global" variables in the context is
    --    (used to supress printing those in error messages)
    globals :: Int,
    -- | Type declarations (signatures): it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [Sig],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation] {- SOLN EP -},
    epsilon :: Epsilon {- STUBWITH -}
  }

--deriving Show

-- | The initial environment.
emptyEnv :: Env
emptyEnv = Env {ctx = []
               , globals = 0
               , hints = []
              , sourceLocation = []
  {- SOLN EP-}, epsilon = Rel {- STUBWITH -}}

instance Disp Env where
  disp e = vcat [disp decl | decl <- ctx e]

-- | Find a name's user supplied type signature.
lookupHint :: (MonadReader Env m) => TName -> m (Maybe Sig)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [ sig | sig <- hints, v == sigName sig]

-- | Find a name's type in the context.
lookupTyMaybe ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Sig)
lookupTyMaybe v = do
  ctx <- asks ctx
  return $ go ctx where
    go [] = Nothing
    go (TypeSig sig : ctx)
      | v == sigName sig = Just sig
      | otherwise = go ctx 
    go (Demote ep : ctx) = demoteSig ep <$> go ctx

    go (_ : ctx) = go ctx

demoteSig :: Epsilon -> Sig -> Sig
demoteSig ep s = s { sigEp = min ep (sigEp s) }


-- | Find the type of a name specified in the context
-- throwing an error if the name doesn't exist
lookupTy ::
  (MonadReader Env m, MonadError Err m) =>
  TName -> m Sig
lookupTy v =
  do
    x <- lookupTyMaybe v
    gamma <- getLocalCtx
    case x of
      Just res -> return res
      Nothing ->
        err
          [ DS ("The variable " ++ show v ++ " was not found."),
            DS "in context",
            DD gamma
          ]

-- | Find a name's def in the context.
lookupDef ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Term)
lookupDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | Def v' a <- ctx, v == v']

lookupRecDef ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Term)
lookupRecDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | RecDef v' a <- ctx, v == v']



-- | Extend the context with a new binding
extendCtx :: (MonadReader Env m) => Decl -> m a -> m a
extendCtx d =
  local (\m@Env{ctx = cs} -> m {ctx = d : cs})

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [Decl] -> m a -> m a
extendCtxs ds =
  local (\m@Env {ctx = cs} -> m {ctx = ds ++ cs})

-- | Extend the context with a list of bindings, marking them as "global"
extendCtxsGlobal :: (MonadReader Env m) => [Decl] -> m a -> m a
extendCtxsGlobal ds =
  local
    ( \m@Env {ctx = cs} ->
        m
          { ctx = ds ++ cs,
            globals = length (ds ++ cs)
          }
    )



-- | Extend the context with a module
-- Note we must reverse the order.
extendCtxMod :: (MonadReader Env m) => Module -> m a -> m a
extendCtxMod m = extendCtxs (reverse $ moduleEntries m)

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
  local (\e@Env {sourceLocation = locs} -> e {sourceLocation = SourceLocation p t : locs})

-- | access current source location
getSourceLocation :: MonadReader Env m => m [SourceLocation]
getSourceLocation = asks sourceLocation

-- | Add a type hint
extendHints :: (MonadReader Env m) => Sig -> m a -> m a
extendHints h = local (\m@Env {hints = hs} -> m {hints = h : hs})

-- | An error that should be reported to the user
data Err = Err [SourceLocation] Doc

-- | Augment the error message with addition information
extendErr :: MonadError Err m => m a -> Doc -> m a
extendErr ma msg' =
  ma `catchError` \(Err ps msg) ->
    throwError $ Err ps (msg $$ msg')

instance Semigroup Err where
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Monoid Err where
  mempty = Err [] mempty
  mappend (Err src1 d1) (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Disp Err where
  disp (Err [] msg) = msg
  disp (Err ((SourceLocation p term) : _) msg) =
    disp p
      $$ nest 2 msg
      $$ nest 2 (text "In the expression" $$ nest 2 (disp term))

-- | Throw an error
err :: (Disp a, MonadError Err m, MonadReader Env m) => [a] -> m b
err d = do
  loc <- getSourceLocation
  throwError $ Err loc (sep $ map disp d)

-- | Print a warning
warn :: (Disp a, MonadReader Env m, MonadIO m) => a -> m ()
warn e = do
  loc <- getSourceLocation
  liftIO $ putStrLn $ "warning: " ++ render (disp (Err loc (disp e)))

checkStage ::
  (MonadReader Env m, MonadError Err m) =>
  Epsilon ->
  m ()
checkStage ep1 = do
  ep2 <- asks epsilon
  unless (ep1 <= ep2) $ do
    err
      [ DS "Cannot access ",
        DD ep1,
        DS " variables in this context"
      ]

withStage :: (MonadReader Env m) => Epsilon -> m a -> m a
withStage Irr = extendCtx (Demote Rel)
withStage ep = id
--  local (\e -> e {epsilon = max (epsilon e) ep})

getStage :: (MonadReader Env m) => m Epsilon
getStage = asks epsilon
