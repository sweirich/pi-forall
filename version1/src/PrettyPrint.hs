{- pi-forall language -}

-- | A Pretty Printer.
module PrettyPrint (Disp (..), D (..), SourcePos, PP.Doc, PP.render) where

import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Set qualified as S
import Syntax
import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Text.PrettyPrint as PP
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

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
  disp (DS s) = text s
  disp (DD d) = nest 2 $ disp d

instance Disp [D] where
  disp dl = sep $ map disp dl

instance Disp ParseError where
  disp = text . show

instance Disp SourcePos where
  disp p =
    text (sourceName p) PP.<> colon PP.<> int (sourceLine p)
      PP.<> colon
      PP.<> int (sourceColumn p)
      PP.<> colon

instance Disp (Unbound.Name Term) where
  disp = text . Unbound.name2String

-------------------------------------------------------------------------

-- * Disp Instances for Term syntax (defaults to Display, see below)

-------------------------------------------------------------------------

instance Disp Term

instance Disp Arg



------------------------------------------------------------------------

-- * Disp Instances for Modules

-------------------------------------------------------------------------

instance Disp [Decl] where
  disp = vcat . map disp



instance Disp Module where
  disp m =
    text "module" <+> disp (moduleName m) <+> text "where"
      $$ vcat (map disp (moduleImports m))
      $$ vcat (map disp (moduleEntries m))

instance Disp ModuleImport where
  disp (ModuleImport i) = text "import" <+> disp i

instance Disp Sig where
  disp (Sig n  ty) = disp n <+> text ":" <+> disp ty

instance Disp Decl where
  disp (Def n term)  = disp n <+> text "=" <+> disp term
  disp (RecDef n r)  = disp (Def n r)
  disp (TypeSig sig) = disp sig



-------------------------------------------------------------------------

-- * Disp Instances for Prelude types

-------------------------------------------------------------------------

instance Disp String where
  disp = text

instance Disp Int where
  disp = text . show

instance Disp Integer where
  disp = text . show

instance Disp Double where
  disp = text . show

instance Disp Float where
  disp = text . show

instance Disp Char where
  disp = text . show

instance Disp Bool where
  disp = text . show

instance Disp a => Disp (Maybe a) where
  disp (Just a) = text "Just" <+> disp a
  disp Nothing = text "Nothing"

instance (Disp a, Disp b) => Disp (Either a b) where
  disp (Left a) = text "Left" <+> disp a
  disp (Right a) = text "Right" <+> disp a

-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display String where
  display = return . text

instance Display Int where
  display = return . text . show

instance Display Integer where
  display = return . text . show

instance Display Double where
  display = return . text . show

instance Display Float where
  display = return . text . show

instance Display Char where
  display = return . text . show

instance Display Bool where
  display = return . text . show

-------------------------------------------------------------------------

-- * Display class instances for Terms

-------------------------------------------------------------------------

instance Display (Unbound.Name Term) where
  display = return . disp

instance Display Term where
  display Type = return $ text "Type"
  display (Var n) = display n
  display a@(Lam b) = do
    (binds, body) <- gatherBinders a
    return $ hang (text "\\" PP.<> sep binds PP.<> text ".") 2 body
  display (App f x) = do
    df <- display f
    dx <- display x
    return $ wrapf f df <+> dx
  display (Pi a bnd) = do
    Unbound.lunbind bnd $ \((n ), b) -> do
      st <- ask
      da <- display a
      dn <- display n
      db <- display b
      let lhs =
            if n `elem` toListOf Unbound.fv b
              then parens (dn <+> colon <+> da)
              else  da
      return $ lhs <+> text "->" <+> db
  display (Ann a b) = do
    st <- ask
    da <- display a
    db <- display b
    if showAnnots st then
      return $ parens (da <+> text ":" <+> db)
      else return da 
  display (Pos _ e) = display e
  display TrustMe = do
    return $ text "TRUSTME"
  display PrintMe = do
    return $ text "PRINTME"
  display TyUnit = return $ text "Unit"
  display LitUnit = return $ text "()"
  display TyBool = return $ text "Bool"
  display (LitBool b) = return $ if b then text "True" else text "False"
  display (If a b c) = do
    da <- display a
    db <- display b
    dc <- display c
    return $
      text "if" <+> da <+> text "then" <+> db
        <+> text "else"
        <+> dc
  display (Sigma tyA bnd) =
    Unbound.lunbind bnd $ \(x, tyB) -> do
      dx <- display x
      dA <- display tyA
      dB <- display tyB
      if x `elem` toListOf Unbound.fv tyB then
        return $
          text "{" <+> dx <+> text ":" <+> dA
            <+> text "|"
            <+> dB
            <+> text "}"
        else return $ parens (dA PP.<+> text "*" PP.<+> dB)
  display (Prod a b) = do
    da <- display a
    db <- display b
    return $ parens (da PP.<> text "," PP.<> db)
  display (LetPair a bnd) = do
    da <- display a
    Unbound.lunbind bnd $ \((x, y), body) -> do
      dx <- display x
      dy <- display y
      dbody <- display body
      return $
        (text "let" 
          <+> (text "("
          PP.<> dx
          PP.<> text ","
          PP.<> dy
          PP.<> text ")")
          <+> text "="
          <+> da 
          <+> text "in")
        $$ dbody
  display (Let a bnd) = do
    Unbound.lunbind bnd $ \(x, b) -> do
      da <- display a
      dx <- display x
      db <- display b
      return $
        sep
          [ text "let" <+> dx
              <+> text "="
              <+> da
              <+> text "in",
            db
          ]





instance Display Arg where
  display arg = do
    st <- ask
    wraparg st arg <$> display (unArg arg)



-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term -> DispInfo -> ([Doc], Doc)
gatherBinders (Lam b) =
  Unbound.lunbind b $ \((n ), body) -> do
    dn <- display n
    let db =  dn
    (rest, body') <- gatherBinders body
    return (db : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)



-- | decide whether to add parens to the function of an application
wrapf :: Term -> Doc -> Doc
wrapf f = case f of
  Var _ -> id
  App _ _ -> id
  Ann a _ -> wrapf a
  Pos _ a -> wrapf a
  TrustMe -> id
  PrintMe -> id
  _ -> parens

-- | decide whether to add parens to an argument in an application
wraparg :: DispInfo -> Arg -> Doc -> Doc
wraparg st a = case unArg a of
  Var _ -> std
  Type -> std
  TyUnit -> std
  LitUnit -> std
  TyBool -> std
  LitBool b -> std
  Sigma _ _ -> std
  Prod _ _ -> force
  Ann b _ -> wraparg st a {unArg = b}
  Pos _ b -> wraparg st a {unArg = b}
  TrustMe -> std
  PrintMe -> std


  _ -> force
  where
    std = id
    force = parens
    

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