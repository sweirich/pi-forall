{- PiForall language, OPLSS -}

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

{- SOLN DATA -}

instance Disp Pattern

instance Disp Match

{- STUBWITH -}

------------------------------------------------------------------------

-- * Disp Instances for Modules

-------------------------------------------------------------------------

instance Disp [Decl] where
  disp = vcat . map disp

{- SOLN EP -}
instance Disp Epsilon where
  disp Irr = text "-"
  disp Rel = text "+"

{- STUBWITH -}

instance Disp Module where
  disp m =
    text "module" <+> disp (moduleName m) <+> text "where"
      $$ vcat (map disp (moduleImports m))
      $$ vcat (map disp (moduleEntries m))

instance Disp ModuleImport where
  disp (ModuleImport i) = text "import" <+> disp i

instance Disp Sig where
  disp (Sig n {- SOLN EP -} ep {- STUBWITH -} ty) = disp n <+> text ":" <+> disp ty

instance Disp Decl where
  disp (Def n term)  = disp n <+> text "=" <+> disp term
  disp (RecDef n r)  = disp (Def n r)
  disp (TypeSig sig) = disp sig
{- SOLN EP -}
  disp (Demote ep)   = mempty
{- STUBWITH -}
{- SOLN DATA -}
  disp (Data n params constructors) =
    hang
      ( text "data" <+> disp n <+> disp params
          <+> colon
          <+> text "Type"
          <+> text "where"
      )
      2
      (vcat $ map disp constructors)
  disp (DataSig t delta) =
    text "data" <+> disp t <+> disp delta <+> colon
      <+> text "Type"

instance Disp ConstructorDef where
  disp (ConstructorDef _ c (Telescope [])) = text c
  disp (ConstructorDef _ c tele) = text c <+> text "of" <+> disp tele

{- STUBWITH -}

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
  display (Pi bnd) = do
    Unbound.lunbind bnd $ \((n {- SOLN EP -}, ep {- STUBWITH -}, Unbound.unembed -> a), b) -> do
      st <- ask
      da <- display a
      dn <- display n
      db <- display b
      let lhs =
            if n `elem` toListOf Unbound.fv b
              then {- SOLN EP -} mandatoryBindParens ep {- STUBWITH parens -} (dn <+> colon <+> da)
              else {- SOLN EP -} wraparg st (Arg ep a) {- STUBWITH -} da
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
  display (Sigma bnd) =
    Unbound.lunbind bnd $ \((x, Unbound.unembed -> tyA), tyB) -> do
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
  display (Let bnd) = do
    Unbound.lunbind bnd $ \((x, a), b) -> do
      da <- display (Unbound.unembed a)
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

{- SOLN EQUAL -}
  display (Subst a b) = do
    da <- display a
    db <- display b
    return $
      fsep
        [ text "subst" <+> da,
          text "by" <+> db
        ]
  display (TyEq a b) = do
    da <- display a
    db <- display b
    return $ da <+> text "=" <+> db
  display Refl = do
    return $ text "Refl"
  display (Contra ty) = do
    dty <- display ty
    return $ text "contra" <+> dty
  {- STUBWITH -}

{- SOLN DATA -}
  display (isNumeral -> Just i) = display i
  display (TCon n args) = do
    st <- ask
    dn <- display n
    dargs <- mapM display args
    let wargs = zipWith (wraparg st) args dargs
    return $ dn <+> hsep wargs
  display (DCon n args) = do
    dn <- display n
    dargs <- mapM display args
    return $ dn <+> hsep dargs
  display (Case scrut alts) = do
    dscrut <- display scrut
    dalts <- mapM display alts
    return $
      text "case" <+> dscrut <+> text "of"
        $$ nest 2 (vcat dalts)

{- STUBWITH -}

instance Display Arg where
  display arg = do
    st <- ask
    wraparg st arg <$> display (unArg arg)

{- SOLN DATA -}
instance Display Match where
  display (Match bd) =
    Unbound.lunbind bd $ \(pat, ubd) -> do
      dpat <- display pat
      dubd <- display ubd
      return $ hang (dpat <+> text "->") 2 dubd

instance Display Pattern where
  display (PatCon c [])   = display c
  display (PatCon c args) = do
    dc <- display c 
    dargs <- mapM wrap args
    return $ dc <+> hsep dargs
      where 
        wrap (a@(PatVar _),ep)    = bindParens ep <$> display a
        wrap (a@(PatCon _ []),ep) = bindParens ep <$> display a 
        wrap (a@(PatCon _ _),ep)  = mandatoryBindParens ep <$> display a
      
  display (PatVar x) = display x

instance Disp Telescope where
  disp (Telescope t) = sep $ map disp t

instance Display a => Display (a, Epsilon) where
  display (t, ep) = bindParens ep <$> display t

{- STUBWITH -}

-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term -> DispInfo -> ([Doc], Doc)
gatherBinders (Lam b) =
  Unbound.lunbind b $ \((n {- SOLN EP -}, ep {- STUBWITH -}), body) -> do
    dn <- display n
    let db = {- SOLN EP -} bindParens ep {- STUBWITH -} dn
    (rest, body') <- gatherBinders body
    return (db : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)

{- SOLN EP -}

-- | Add [] for irrelevant arguments
bindParens :: Epsilon -> Doc -> Doc
bindParens Rel d = d
bindParens Irr d = brackets d

-- | Always add () or [], shape determined by epsilon
mandatoryBindParens :: Epsilon -> Doc -> Doc
mandatoryBindParens Rel d = parens d
mandatoryBindParens Irr d = brackets d

{- STUBWITH -}

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
  Sigma _ -> std
  Prod _ _ -> force
  Ann b _ -> wraparg st a {unArg = b}
  Pos _ b -> wraparg st a {unArg = b}
  TrustMe -> std
  PrintMe -> std
{- SOLN DATA -}
  TCon _ [] -> std
  (isNumeral -> Just x) -> std
  DCon _ [] -> std
  {- STUBWITH -}
{- SOLN EQUAL -}
  Refl -> std
  {- STUBWITH -}
  _ -> force
  where
    std = {- SOLN EP -} bindParens (argEp a)
    {- STUBWITH id -}
    force = {- SOLN EP -} mandatoryBindParens (argEp a)
    {- STUBWITH parens -}
    

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