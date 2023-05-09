{- pi-forall language -}

-- | A Pretty Printer.
module PrettyPrint (Disp (..), D (..), SourcePos, PP.Doc, PP.render, pp) where

import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Set qualified as S

import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Text.PrettyPrint (Doc, ($$), (<+>))
import qualified Text.PrettyPrint as PP
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Data.Typeable (Typeable)

import Syntax

-------------------------------------------------------------------------

-- * Classes and Types for Pretty Printing

pp :: Display d => d -> String
pp p = PP.render (display p initDI)

-------------------------------------------------------------------------

-- | The 'Disp' class governs all types which can be turned into 'Doc's
-- The `disp` function is the entry point for the pretty printer
class Disp d where
  disp :: d -> Doc
  default disp :: (Display d) => d -> Doc
  disp d = display d initDI

-- | The 'Display' class is like the 'Disp' class. It qualifies
--   types that can be turned into 'Doc'.  The difference is that the
--   this uses the 'DispInfo' parameter and the Unbound library
--   to generate fresh names.
class (Unbound.Alpha t) => Display t where
  -- | Convert a value to a 'Doc'.
  display :: t -> DispInfo -> Doc

-- | The data structure for information about the display
data DispInfo = DI
  { -- | should we show the annotations?
    showAnnots :: Bool,
    -- | names that have been used
    dispAvoid :: S.Set Unbound.AnyName,
    -- | current precedence level
    prec :: Int,
    -- 
    showLevels :: Bool,
    showLongNames :: Bool
  }

initDI :: DispInfo
initDI = DI {showAnnots = False, 
                          dispAvoid = S.empty, 
                          prec = 0, 
                          showLevels = True, 
                          showLongNames = True}

-- | Error message quoting
data D
  = -- | String literal
    DS String
  | -- | Displayable value
    forall a. Disp a => DD a

-------------------------------------------------------------------------

-- * Disp Instances for quoting, errors, source positions, 

-------------------------------------------------------------------------

instance Disp D where
  disp (DS s) = PP.text s
  disp (DD d) = PP.nest 2 $ disp d

instance Disp [D] where
  disp dl = PP.sep $ map disp dl

instance Disp ParseError where
  disp = PP.text . show

instance Disp SourcePos where
  disp p =
    PP.text (sourceName p) PP.<> PP.colon PP.<> PP.int (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.int (sourceColumn p)
      PP.<> PP.colon

-------------------------------------------------------------------------

-- * Disp Instances for Term syntax (defaults to Display, see below)

-------------------------------------------------------------------------


instance Disp Term

instance Disp Arg

instance Disp Pattern

instance Disp Match

instance Disp Level

instance Typeable a => Disp (Unbound.Name a)

instance Disp Decl

instance Disp [Decl]

instance Disp Module

instance Disp Sig

instance Disp ConstructorDef

instance Disp LevelConstraint

------------------------------------------------------------------------

-- * Disp/Display Instances for Modules

-------------------------------------------------------------------------

instance Display [Decl] where
  display ds = do 
    dd <- mapM display ds
    pure $ PP.vcat dd

instance Disp Rho where
  disp Irr = PP.text "irrelevant"
  disp Rel = PP.text "relevant"

instance Display Epsilon where
  display (Mode rho (Just lvl)) = do
    sl <- asks showLevels
    dl <- display lvl
    if sl then  
      pure $ disp rho <+> dl
    else 
      pure $ disp rho
  display (Mode rho Nothing) = pure $ disp rho

instance Display Level where
  display (LVar x) = display x
  display (LConst i) = return $ PP.int i
  display (LAdd l1 l2) = do
    d1 <- display l1
    d2 <- display l2
    return $ d1 <+> PP.text "+" <+> d2

instance Display LevelConstraint where
  display (Lt l1 l2) = do
    d1 <- display l1
    d2 <- display l2
    pure $ d1 <+> PP.text "<" <+> d2
  display (Le l1 l2) = do
    d1 <- display l1
    d2 <- display l2
    pure $ d1 <+> PP.text "<=" <+> d2
  display (Eq l1 l2) = do
    d1 <- display l1
    d2 <- display l2
    pure $ d1 <+> PP.text "=" <+> d2

instance Display Module where
  display m = do
    dn <- display (moduleName m)
    di <- mapM display (moduleImports m)
    de <- mapM display (moduleEntries m)
    pure $ PP.text "module" <+> dn <+> PP.text "where"
      $$ PP.vcat di
      $$ PP.vcat de 

instance Display ModuleImport where
  display (ModuleImport i) = pure $ PP.text "import" <+> disp i

instance Display Sig where
  display (Sig n r (Just l) ty) = do
    dn <- display n
    b <- asks showLevels
    dt <- display ty
    dl <- display l
    if b then
      pure $ dn <+> PP.text ":" <+> dt <+> PP.text "@" <+> dl
    else
      pure $ dn <+> PP.text ":" <+> dt
  display (Sig n r Nothing ty) = do
    dn <- display n
    dt <- display ty
    pure $ dn <+> PP.text ":" <+> dt

instance Display Decl where
  display (Def n term) = do
    dn <- display n
    dt <- display term
    pure $ dn <+> PP.text "=" <+> dt
  display (RecDef n f) = display (Def n f)
  display (TypeSig sig) = display sig
  display (Demote ep) = return mempty
  display (Data n params constructors i) = do
    dn <- display n
    dp <- display params
    dc <- mapM display constructors
    di <- display i
    pure $ PP.hang
      ( PP.text "data" <+> dn <+> dp
          <+> PP.colon
          <+> PP.text "Type"
          <+> di
          <+> PP.text "where"
      )
      2
      (PP.vcat dc)
  display (DataSig t delta i) = do
    dt <- display t
    dd <- display delta
    di <- display i
    pure $ PP.text "data" <+> dt <+> dd <+> PP.colon
      <+> PP.text "Type" <+> di

instance Display ConstructorDef where
  display (ConstructorDef _ c (Telescope []) k) = do
    dk <- display k
    sk <- asks showLevels 
    pure $ PP.text c <+> (if sk then PP.text "@" <+> dk else mempty)
  display (ConstructorDef _ c tele k) = do
    dc <- display c
    dt <- display tele
    dk <- display k
    sk <- asks showLevels
    pure $ dc <+> PP.text "of" <+> dt <+> (if sk then PP.text "@" <+> dk else mempty)



-------------------------------------------------------------------------

-- * Disp Instances for Prelude types

-------------------------------------------------------------------------

instance Disp String where
  disp = PP.text

instance Disp Int where
  disp = PP.text . show

instance Disp Integer where
  disp = PP.text . show

instance Disp Double where
  disp = PP.text . show

instance Disp Float where
  disp = PP.text . show

instance Disp Char where
  disp = PP.text . show

instance Disp Bool where
  disp = PP.text . show

instance Disp a => Disp (Maybe a) where
  disp (Just a) = PP.text "Just" <+> disp a
  disp Nothing = PP.text "Nothing"

instance (Disp a, Disp b) => Disp (Either a b) where
  disp (Left a) = PP.text "Left" <+> disp a
  disp (Right a) = PP.text "Right" <+> disp a

-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display String where
  display = return . PP.text

instance Display Int where
  display = return . PP.text . show

instance Display Integer where
  display = return . PP.text . show

instance Display Double where
  display = return . PP.text . show

instance Display Float where
  display = return . PP.text . show

instance Display Char where
  display = return . PP.text . show

instance Display Bool where
  display = return . PP.text . show

-------------------------------------------------------------------------

-- * Display class instances for Terms

-------------------------------------------------------------------------


levelApp :: Int
levelApp     = 10
levelIf :: Int
levelIf      = 0
levelLet :: Int
levelLet     = 0
levelCase :: Int
levelCase    = 0
levelLam :: Int
levelLam     = 0
levelPi :: Int
levelPi      = 0
levelSigma :: Int
levelSigma   = 0
levelProd :: Int
levelProd    = 0
levelArrow :: Int
levelArrow   = 5

withPrec :: MonadReader DispInfo m => Int -> m a -> m a
withPrec p = local (\d -> d { prec = p })

parens :: Bool -> Doc -> Doc
parens b = if b then PP.parens else id

brackets :: Bool -> Doc -> Doc
brackets b = if b then PP.brackets else id


instance (Typeable a) => Display (Unbound.Name a) where
  display n = do
    b <- asks showLongNames
    if b then
        pure $ PP.text (show n)
      else
        pure $ PP.text (Unbound.name2String n)

--instance (Typeable a) => Display (Unbound.Name a) where
--  display = return . disp

instance Display Term where
  display Type = return $ PP.text "Type"
  display (Var n) = display n
  display a@(Lam _ b) = do
    n <- ask prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ PP.hang (PP.text "\\" PP.<> PP.sep binds PP.<> PP.text ".") 2 body
  display (App f x) = do
    n <- ask prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp+1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (Pi (Mode ep mk) a bnd) = do
    Unbound.lunbind bnd $ \(n, b) -> do
      p <- ask prec
      lhs <- case mk of 
              Just k -> do
                dn <- display n
                da <- withPrec 0 (display a)
                dk <- display k
                return $ mandatoryBindParens ep  (dn <+> PP.colon <+> da <+> dk)
              Nothing ->
                case ep of
                  Rel -> withPrec (levelArrow+1) (display a)
                  Irr -> PP.brackets <$> withPrec 0 (display a)
      db <- withPrec levelPi (display b)
      return $ parens (levelArrow < p) $ lhs <+> PP.text "->" <+> db
  display (Ann a b) = do
    sa <- ask showAnnots
    if sa then do
      da <- withPrec 0 (display a)
      db <- withPrec 0 (display b)
      return $ PP.parens (da <+> PP.text ":" <+> db)
      else display a
  display (Pos _ e) = display e
  display TrustMe = do
    return $ PP.text "TRUSTME"
  display PrintMe = do
    return $ PP.text "PRINTME"
  display TyUnit = return $ PP.text "Unit"
  display LitUnit = return $ PP.text "()"
  display TyBool = return $ PP.text "Bool"
  display (LitBool b) = return $ if b then PP.text "True" else PP.text "False"
  display (If a b c) = do
    p <- ask prec
    da <- withPrec 0 $ display a
    db <- withPrec 0 $ display b
    dc <- withPrec 0 $ display c
    return $ parens (levelIf < p) $
      PP.text "if" <+> da <+> PP.text "then" <+> db
        <+> PP.text "else"
        <+> dc
  display (Sigma tyA lvl bnd) =
    Unbound.lunbind bnd $ \(x, tyB) -> do
      if x `elem` toListOf Unbound.fv tyB then do
        dx <- display x
        dA <- withPrec 0 $ display tyA
        dB <- withPrec 0 $ display tyB
        dl <- display lvl
        return $
          PP.text "{" <+> dx <+> PP.text ":" <+> dA <+> dl
            <+> PP.text "|"
            <+> dB
            <+> PP.text "}"
        else do
          p <- ask prec
          dA <- withPrec levelSigma $ display tyA
          dB <- withPrec levelSigma $ display tyB
          return $ parens (levelSigma < p) (dA PP.<+> PP.text "*" PP.<+> dB)
  display (Prod a b) = do
    p <- ask prec
    da <- withPrec levelProd $ display a
    db <- withPrec levelProd $ display b
    return $ parens (levelProd < p) (da PP.<> PP.text "," PP.<> db)
  display (LetPair a bnd) = do
    da <- display a
    Unbound.lunbind bnd $ \((x, y), body) -> do
      p <- ask prec
      dx <- withPrec 0 $ display x
      dy <- withPrec 0 $ display y
      dbody <- withPrec 0 $ display body
      return $
        parens (levelLet < p) $
        (PP.text "let"
          <+> (PP.text "("
          PP.<> dx
          PP.<> PP.text ","
          PP.<> dy
          PP.<> PP.text ")")
          <+> PP.text "="
          <+> da
          <+> PP.text "in")
        $$ dbody
  display (Let a bnd) = do
    Unbound.lunbind bnd $ \(x, b) -> do
      p <- ask prec
      da <- display a
      dx <- display x
      db <- display b
      return $
        parens (levelLet < p) $
        PP.sep
          [ PP.text "let" <+> dx
              <+> PP.text "="
              <+> da
              <+> PP.text "in",
            db
          ]

  display (Subst a b) = do
    p <- asks prec
    da <- withPrec 0 $ display a
    db <- withPrec 0 $ display b
    return $
      parens (levelPi < p) $
      PP.fsep
        [ PP.text "subst" <+> da,
          PP.text "by" <+> db
        ]
  display (TyEq a b) = do
    p <- ask prec
    da <- withPrec (levelApp+1) $ display a
    db <- withPrec (levelApp+1) $ display b
    return $ PP.parens $ (da <+> PP.text "=" <+> db)
  display Refl = do
    return $ PP.text "Refl"
  display (Contra ty) = do
    p <- ask prec
    dty <- display ty
    return $ parens (levelPi < p) $ PP.text "contra" <+> dty


  display (isNumeral -> Just i) = display i
  display (TCon n j args) = do
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && length args > 0) (dn <+> PP.hsep dargs)
  display (DCon n j args) = do
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && length args > 0) (dn <+> PP.hsep dargs)
  display (Case scrut alts) = do
    p <- asks prec
    dscrut <- withPrec 0 $ display scrut
    dalts <- withPrec 0 $ mapM display alts
    let top = PP.text "case" <+> dscrut <+> PP.text "of"
    return $
      parens (levelCase < p) $
        if null dalts then top <+> PP.text "{ }" else top $$ PP.nest 2 (PP.vcat dalts)
  display (Displace t (LConst 0)) = do
    display t
  display (Displace t j) = do
    dt <- display t
    dj <- display j
    return $ dt <> PP.text "^" <> dj


instance Display Arg where
  display arg =
    case argEp arg of
      Irr -> PP.brackets <$> withPrec 0 (display (unArg arg))
      Rel -> display (unArg arg)


instance Display Match where
  display (Match bd) =
    Unbound.lunbind bd $ \(pat, ubd) -> do
      dpat <- display pat
      dubd <- display ubd
      return $ PP.hang (dpat <+> PP.text "->") 2 dubd

instance Display Pattern where
  display (PatCon c [])   = display c
  display (PatCon c args) = do
    dc <- display c
    dargs <- mapM wrap args
    return $ dc <+> PP.hsep dargs
      where
        wrap (a@(PatVar _),ep)    = bindParens ep <$> display a
        wrap (a@(PatCon _ []),ep) = bindParens ep <$> display a
        wrap (a@(PatCon _ _),ep)  = mandatoryBindParens ep <$> display a

  display (PatVar x) = display x


instance Display Telescope where
  display (Telescope t) = do
    dt <- mapM display t
    pure $ PP.sep (map PP.parens dt)

instance Display a => Display (a, Epsilon) where
  display (t, Mode ep _) = bindParens ep <$> display t




-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term -> DispInfo -> ([Doc], Doc)
gatherBinders (Lam ep b) =
  Unbound.lunbind b $ \(n, body) -> do
    dn <- display n
    let db = bindParens ep  dn
    (rest, body') <- gatherBinders body
    return (db : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)

precBindParens :: Rho -> Bool -> Doc -> Doc
precBindParens Rel b d = parens b d
precBindParens Irr b d = PP.brackets d

-- | Add [] for irrelevant arguments, leave other arguments alone
bindParens :: Rho -> Doc -> Doc
bindParens Rel d = d
bindParens Irr d = PP.brackets d

-- | Always add () or [], shape determined by epsilon
mandatoryBindParens :: Rho -> Doc -> Doc
mandatoryBindParens Rel d = PP.parens d
mandatoryBindParens Irr d = PP.brackets d



-------------------------------------------------------------------------

-- * LFresh instance for DisplayInfo reader monad

-------------------------------------------------------------------------

instance Unbound.LFresh ((->) DispInfo) where
  lfresh nm = do
    let s = Unbound.name2String nm
    di <- ask
    return $
      head
        ( filter
            (\x -> Unbound.AnyName x `S.notMember` dispAvoid di)
            (map (Unbound.makeName s) [0 ..])
        )
  getAvoids = asks dispAvoid
  avoid names = local upd
    where
      upd di =
        di
          { dispAvoid =
              S.fromList names `S.union` dispAvoid di
          }