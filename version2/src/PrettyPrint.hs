{- pi-forall language -}

-- | A Pretty Printer.
module PrettyPrint (Disp (..), D (..), SourcePos, PP.Doc, PP.render) where

import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Set qualified as S

import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Text.PrettyPrint (Doc, ($$), (<+>))
import qualified Text.PrettyPrint as PP
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

import Syntax

-------------------------------------------------------------------------

-- * Classes and Types for Pretty Printing

-------------------------------------------------------------------------

-- | The 'Disp' class governs all types which can be turned into 'Doc's
-- The `disp` function is the entry point for the pretty printer
class Disp d where
  disp :: d -> Doc
  default disp :: (Display d) => d -> Doc
  disp d = display d (DI {showAnnots = False, dispAvoid = S.empty, prec = 0})

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
    prec :: Int
  }

-- | Error message quoting
data D
  = -- | String literal
    DS String
  | -- | Displayable value
    forall a. Disp a => DD a

-------------------------------------------------------------------------

-- * Disp Instances for quoting, errors, source positions, names

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

instance Disp (Unbound.Name Term) where
  disp = PP.text . Unbound.name2String

-------------------------------------------------------------------------

-- * Disp Instances for Term syntax (defaults to Display, see below)

-------------------------------------------------------------------------

instance Disp Term





------------------------------------------------------------------------

-- * Disp Instances for Modules

-------------------------------------------------------------------------

instance Disp [Decl] where
  disp = PP.vcat . map disp



instance Disp Module where
  disp m =
    PP.text "module" <+> disp (moduleName m) <+> PP.text "where"
      $$ PP.vcat (map disp (moduleImports m))
      $$ PP.vcat (map disp (moduleEntries m))

instance Disp ModuleImport where
  disp (ModuleImport i) = PP.text "import" <+> disp i

instance Disp Sig where
  disp (Sig n  ty) = disp n <+> PP.text ":" <+> disp ty

instance Disp Decl where
  disp (Def n term)  = disp n <+> PP.text "=" <+> disp term
  disp (RecDef n r)  = disp (Def n r)
  disp (TypeSig sig) = disp sig



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
withPrec p t =
  local (\d -> d { prec = p }) t

parens :: Bool -> Doc -> Doc
parens b = if b then PP.parens else id

brackets :: Bool -> Doc -> Doc
brackets b = if b then PP.brackets else id

instance Display (Unbound.Name Term) where
  display = return . disp

instance Display Term where
  display TyType = return $ PP.text "Type"
  display (Var n) = display n
  display a@(Lam b) = do
    n <- ask prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ PP.hang (PP.text "\\" PP.<> PP.sep binds PP.<> PP.text ".") 2 body
  display (App f x) = do
    n <- ask prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp+1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (TyPi a bnd) = do
    Unbound.lunbind bnd $ \(n, b) -> do
      p <- ask prec
      lhs <-
            if n `elem` toListOf Unbound.fv b
              then do
                dn <- display n
                da <- withPrec 0 (display a)
                return $ PP.parens (dn <+> PP.colon <+> da)
              else withPrec (levelArrow+1) (display a)
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
  display (TySigma tyA bnd) =
    Unbound.lunbind bnd $ \(x, tyB) -> do
      if x `elem` toListOf Unbound.fv tyB then do
        dx <- display x
        dA <- withPrec 0 $ display tyA
        dB <- withPrec 0 $ display tyB
        return $
          PP.text "{" <+> dx <+> PP.text ":" <+> dA
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
  







-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term -> DispInfo -> ([Doc], Doc)
gatherBinders (Lam b) =
  Unbound.lunbind b $ \(n, body) -> do
    dn <- display n
    let db =  dn
    (rest, body') <- gatherBinders body
    return (db : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)



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