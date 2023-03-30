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
    lookupTCon,
    lookupDCon,
    lookupDConAll,
    extendCtxTele  ,
    getCtx,
    getLocalCtx,
    extendCtx,
    extendCtxs,
    extendCtxsGlobal,
    extendCtxMods,
    extendHints,
    extendSourceLocation,
    extendLevelConstraint,
    dumpConstraints,
    getSourceLocation,
    err,
    warn,
    extendErr,
    Locality(..),
    D (..),
    Err (..),
    SourceLocation(..),
    withStage,
    checkStage 
  )
where

import Control.Monad.Except
    ( unless, MonadError(..), MonadIO(..), ExceptT, runExceptT )
import Control.Monad.Reader
    ( MonadReader(local), asks, ReaderT(runReaderT) )
import Control.Monad.State
import Data.List 
import Data.Maybe ( listToMaybe )
import PrettyPrint ( SourcePos, render, D(..), Disp(..), Doc )
import Syntax
import Text.PrettyPrint.HughesPJ ( ($$), nest, sep, text, vcat )
import qualified Unbound.Generics.LocallyNameless as Unbound

-- | The type checking Monad includes a reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), error (for error reporting), and IO
-- (for e.g.  warning messages).
type TcMonad = StateT TcState (Unbound.FreshMT (ReaderT Env (ExceptT Err IO)))

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: Env -> TcMonad a -> IO (Either Err (a, TcState))
runTcMonad env m =
  runExceptT $
    runReaderT (Unbound.runFreshMT (runStateT m initState)) env

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. Disp a => SourcePos -> a -> SourceLocation

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env
  { -- | elaborated term and datatype declarations.
    ctx :: [Decl],
    -- | How many local variables are stored in the context
    locals :: Int,
    -- | how long the tail of "global" variables in the context is
    --    (used to supress printing those in error messages)
    globals :: Int,
    -- | Type declarations (signatures): it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [Sig],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation]
  }

data TcState = TcState {
    -- | constraints about levels
    constraints :: [(SourceLocation, LevelConstraint)] 
  }

--deriving Show

-- | The initial environment.
emptyEnv :: Env
emptyEnv = Env {ctx = preludeDataDecls 
               , globals = length preludeDataDecls 
               , locals = 0
               , hints = []
               , sourceLocation = []
              }

initState :: TcState
initState = TcState { constraints = [] }

instance Disp Env where
  disp e = vcat [disp decl | decl <- ctx e]

instance Disp TcState where
  disp s = vcat [disp l <> disp c | (SourceLocation p l,c) <- constraints s ]

-- | Find a name's user supplied type signature.
lookupHint :: (MonadReader Env m) => TName -> m (Maybe Sig)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [ sig | sig <- hints, v == sigName sig]

data Locality = Local | Global | Any

-- | Find either the local or the global or both
localizedDecls :: MonadReader Env m => Locality -> m [Decl]
localizedDecls l = do
  ctx <- asks ctx
  locals <- asks locals
  globals <- asks globals
  let (start, stop) = case l of 
                Local -> (ctx, locals)
                Global -> (drop locals ctx, globals)
                Any -> (ctx, locals + globals)
  return (take stop start)

-- | Find a name's type in the context.
lookupTyMaybe ::
  (MonadReader Env m) =>
  Locality ->
  TName ->
  m (Maybe Sig)
lookupTyMaybe l v = do
  ctx <- localizedDecls l
  let go [] = Nothing
      go (TypeSig sig : ctx')
        | v == sigName sig = Just sig
        | otherwise = go ctx' 
      go (Demote ep : ctx') = demoteSig ep <$> go ctx'
      go (_ : ctx') = go ctx'
  return $ go ctx 
    
      

demoteSig :: Rho -> Sig -> Sig
demoteSig r s = s { sigRho = min r (sigRho s) } 


-- | Find the type of a name specified in the context
-- throwing an error if the name doesn't exist
lookupTy ::
  TName -> TcMonad Sig
lookupTy v =
  do
    x <- lookupTyMaybe Any v
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
  Locality ->
  TName ->
  m (Maybe Term)
lookupDef l v = do
  ctx <- localizedDecls l
  return $ listToMaybe [a | Def v' a <- ctx, v == v']

lookupRecDef ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Term)
lookupRecDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | RecDef v' a <- ctx, v == v']

-- | Find a type constructor in the context
lookupTCon ::
  (MonadReader Env m, MonadError Err m) =>
  TCName ->
  m (Telescope, Maybe [ConstructorDef], Level)
lookupTCon v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = do
      currentEnv <- asks ctx
      err
        [ DS "The type constructor",
          DD v,
          DS "was not found.",
          DS "The current environment is",
          DD currentEnv
        ]
    scanGamma ((Data v' delta cs k) : g) =
      if v == v'
        then return (delta, Just cs, k)
        else scanGamma g
    scanGamma ((DataSig v' delta k) : g) =
      if v == v'
        then return (delta, Nothing, k)
        else scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll ::
  (MonadReader Env m) =>
  DCName ->
  m [(TCName, (Telescope, ConstructorDef, Level))]
lookupDConAll v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((Data v' delta cs k) : g) =
      case find (\(ConstructorDef _ v'' tele) -> v'' == v) cs of
        Nothing -> scanGamma g
        Just c -> do
          more <- scanGamma g
          return $ (v', (delta, c, k)) :  more
    scanGamma ((DataSig v' delta _) : g) = scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon ::
  (MonadReader Env m, MonadError Err m) =>
  DCName ->
  TCName ->
  m (Telescope, Telescope, Level)
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just (delta, ConstructorDef _ _ deltai, k) ->
      return (delta, deltai, k)
    Nothing ->
      err
        ( [ DS "Cannot find data constructor",
            DS c,
            DS "for type",
            DD tname,
            DS "Potential matches were:"
          ]
            ++ map (DD . fst) matches
            -- ++ map (DD . snd) matches
        )



-- | Extend the context with a new binding
extendCtx :: (MonadReader Env m) => Decl -> m a -> m a
extendCtx d =
  local (\m@Env{ctx = cs, locals=l} -> m {ctx = d : cs, locals = l+1})

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [Decl] -> m a -> m a
extendCtxs ds =
  local (\m@Env {ctx = cs, locals=l} -> m {ctx = ds ++ cs, locals = l + length ds})

-- | Extend the context with a list of bindings, marking them as "global"
extendCtxsGlobal :: (MonadError Err m, MonadReader Env m) => [Decl] -> m a -> m a
extendCtxsGlobal ds ma = do
  nl <- asks locals
  unless (nl == 0) $ err [DS "Global extension of nonempty local context"]
  local
    ( \m@Env {ctx = cs, globals = l} ->
        m
          { ctx = ds ++ cs,
            globals = length ds + l
          }
    ) ma

-- | Extend the context with a telescope
extendCtxTele :: 
  (MonadReader Env m, MonadIO m, MonadError Err m) => [Decl] -> m a -> m a
extendCtxTele [] m = m
extendCtxTele (Def x t2 : tele) m =
  extendCtx (Def x t2) $ extendCtxTele tele m
extendCtxTele (TypeSig sig : tele) m =
  extendCtx (TypeSig sig) $ extendCtxTele tele m
extendCtxTele ( _ : tele) m = 
  err [DS "Invalid telescope ", DD tele]



-- | Extend the context with a module
-- Note we must reverse the order.
extendCtxMod :: (MonadError Err m, MonadReader Env m) => Module -> m a -> m a
extendCtxMod m = extendCtxsGlobal (reverse $ moduleEntries m)

-- | Extend the context with a list of modules
extendCtxMods :: (MonadError Err m, MonadReader Env m) => [Module] -> m a -> m a
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
  Rho ->
  m ()
checkStage ep1 = do
  unless (ep1 <= Rel) $ do
    err
      [ DS "Cannot access",
        DD ep1,
        DS "variables in this context"
      ]

withStage :: (MonadReader Env m) => Rho -> m a -> m a
withStage Irr = extendCtx (Demote Rel)
withStage ep = id



extendLevelConstraint :: (MonadReader Env m, MonadError Err m, MonadState TcState m) => LevelConstraint -> m ()
extendLevelConstraint c@(Lt (LConst i) (LConst j)) = 
    if i < j then return () else err [DS "Cannot solve constraint", DD c]
extendLevelConstraint (Eq l1 l2) | l1 == l2 = return ()
extendLevelConstraint (Le l1 l2) | l1 == l2 = return ()
extendLevelConstraint c@(Lt l1 l2) | l1 == l2 = 
  err [DS "Cannot solve constraint", DD c]
extendLevelConstraint c = do
  locs <- asks sourceLocation
  st <- get
  let cs = constraints st
  -- if c `elem` cs then return () else 
  put $ TcState { constraints = (head locs,c) : cs }

dumpConstraints :: (MonadState TcState m) => m [(SourceLocation,LevelConstraint)]
dumpConstraints = do
  st <- get
  put (TcState [])
  return (constraints st)