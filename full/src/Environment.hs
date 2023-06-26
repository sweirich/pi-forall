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
    getSourceLocation,
    err,
    warn,
    extendErr,
    D (..),
    Err (..),
    withStage,
    checkStage 
  )
where

import Control.Monad.Except
    ( unless, MonadError(..), MonadIO(..), ExceptT, runExceptT )
import Control.Monad.Reader
    ( MonadReader(local), asks, ReaderT(runReaderT) )
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
  { -- | elaborated term and datatype declarations
    ctx :: [Entry],
    -- | how long the tail of "global" variables in the context is
    --    (used to supress printing those in error messages)
    globals :: Int,
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [Decl],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation] 
  }



-- | The initial environment.
emptyEnv :: Env
emptyEnv = Env {ctx = preludeDataDecls 
               , globals = length preludeDataDecls 
               , hints = []
               , sourceLocation = []
              }

instance Disp Env where
  disp :: Env -> Doc
  disp e = vcat [disp decl | decl <- ctx e]
  debugDisp :: Env -> Doc
  debugDisp e = vcat [debugDisp decl | decl <- ctx e]

-- | Find a name's user supplied type signature.
lookupHint :: (MonadReader Env m) => TName -> m (Maybe Decl)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [ sig | sig <- hints, v == declName sig]

-- | Find a name's type in the context.
lookupTyMaybe ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Decl)
lookupTyMaybe v = do
  ctx <- asks ctx
  return $ go ctx where
    go [] = Nothing
    go (TypeDecl sig : ctx)
      | v == declName sig = Just sig
      | otherwise = go ctx 
    go (Demote ep : ctx) = demoteDecl ep <$> go ctx

    go (_ : ctx) = go ctx

demoteDecl :: Epsilon -> Decl -> Decl
demoteDecl ep s = s { declEp = min ep (declEp s) }


-- | Find the type of a name specified in the context
-- throwing an error if the name doesn't exist
lookupTy ::
  TName -> TcMonad Decl
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

-- | Find a type constructor in the context
lookupTCon ::
  (MonadReader Env m, MonadError Err m) =>
  TyConName ->
  m (Telescope, Maybe [ConstructorDef])
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
    scanGamma ((Data v' delta cs) : g) =
      if v == v'
        then return (delta, Just cs)
        else scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll ::
  (MonadReader Env m) =>
  DataConName ->
  m [(TyConName, (Telescope, ConstructorDef))]
lookupDConAll v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((Data v' delta cs) : g) =
      case find (\(ConstructorDef _ v'' tele) -> v'' == v) cs of
        Nothing -> scanGamma g
        Just c -> do
          more <- scanGamma g
          return $ (v', (delta, c)) :  more
    scanGamma (_ : g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon ::
  (MonadReader Env m, MonadError Err m) =>
  DataConName ->
  TyConName ->
  m (Telescope, Telescope)
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just (delta, ConstructorDef _ _ deltai) ->
      return (delta, deltai)
    Nothing ->
      err
        ( [ DS "Cannot find data constructor",
            DS c,
            DS "for type",
            DD tname,
            DS "Potential matches were:"
          ]
            ++ map (DD . fst) matches
            ++ map (DD . snd . snd) matches
        )



-- | Extend the context with a new binding
extendCtx :: (MonadReader Env m) => Entry -> m a -> m a
extendCtx d =
  local (\m@Env{ctx = cs} -> m {ctx = d : cs})

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [Entry] -> m a -> m a
extendCtxs ds =
  local (\m@Env {ctx = cs} -> m {ctx = ds ++ cs})

-- | Extend the context with a list of bindings, marking them as "global"
extendCtxsGlobal :: (MonadReader Env m) => [Entry] -> m a -> m a
extendCtxsGlobal ds =
  local
    ( \m@Env {ctx = cs} ->
        m
          { ctx = ds ++ cs,
            globals = length (ds ++ cs)
          }
    )

-- | Extend the context with a telescope
extendCtxTele :: (MonadReader Env m, MonadIO m, MonadError Err m) => [Entry] -> m a -> m a
extendCtxTele [] m = m
extendCtxTele (Def x t2 : tele) m =
  extendCtx (Def x t2) $ extendCtxTele tele m
extendCtxTele (TypeDecl sig : tele) m =
  extendCtx (TypeDecl sig) $ extendCtxTele tele m
extendCtxTele ( _ : tele) m = 
  err [DS "Invalid telescope ", DD tele]



-- | Extend the context with a module
-- Note we must reverse the order.
extendCtxMod :: (MonadReader Env m) => Module -> m a -> m a
extendCtxMod m = extendCtxs (reverse $ moduleEntries m)

-- | Extend the context with a list of modules
extendCtxMods :: (MonadReader Env m) => [Module] -> m a -> m a
extendCtxMods mods k = foldr extendCtxMod k mods

-- | Get the complete current context
getCtx :: MonadReader Env m => m [Entry]
getCtx = asks ctx

-- | Get the prefix of the context that corresponds to local variables.
getLocalCtx :: MonadReader Env m => m [Entry]
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
extendHints :: (MonadReader Env m) => Decl -> m a -> m a
extendHints h = local (\m@Env {hints = hs} -> m {hints = h : hs})

-- | An error that should be reported to the user
data Err = Err [SourceLocation] Doc

-- | Augment the error message with addition information
extendErr :: MonadError Err m => m a -> Doc -> m a
extendErr ma msg' =
  ma `catchError` \(Err ps msg) ->
    throwError $ Err ps (msg $$ msg')

instance Semigroup Err where
  (<>) :: Err -> Err -> Err
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Monoid Err where
  mempty :: Err
  mempty = Err [] mempty

dispErr :: (forall a. Disp a => a -> Doc) -> Err -> Doc
dispErr disp (Err [] msg) = msg
dispErr disp (Err ((SourceLocation p term) : _) msg) =
    disp p
      $$ nest 2 msg
      $$ nest 2 (text "In the expression" $$ nest 2 (disp term))

instance Disp Err where
  disp :: Err -> Doc
  disp = dispErr disp
  debugDisp = dispErr debugDisp

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
  unless (ep1 <= Rel) $ do
    err
      [ DS "Cannot access",
        DD ep1,
        DS "variables in this context"
      ]

withStage :: (MonadReader Env m) => Epsilon -> m a -> m a
withStage Irr = extendCtx (Demote Rel)
withStage ep = id

