{- PiForall language, OPLSS -}

{-# LANGUAGE PatternGuards, FlexibleInstances, FlexibleContexts, TupleSections, ExplicitForAll #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

-- | A parsec-based parser for the concrete syntax.
module Parser
  (
   parseModuleFile, 
   parseModuleImports,
   parseExpr
  )
  where


import Syntax hiding (moduleImports)

import Unbound.LocallyNameless hiding (Data,Refl,Infix,join,name)

import Text.Parsec hiding (State,Empty)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified LayoutToken as Token

import Control.Monad.State.Lazy hiding (join)
import Control.Applicative ( (<$>), (<*>))
import Control.Monad.Error hiding (join)

import Data.List
import qualified Data.Set as S

{- 

Concrete syntax for the language: 
Optional components in this BNF are marked with < >

  terms:
    a,b,A,B ::=
      Type                     Universes
    | x                        Variables   (start with lowercase)
    | \ x . a                  Function definition
    | a b                      Application
    | (x : A) -> B             Pi type

    | (a : A)                  Annotations
    | (a)                      Parens
    | TRUSTME                  An axiom 'TRUSTME', inhabits all types 

    | let x = a in b           Let expression

    | One                      Unit type
    | tt                       Unit value

    | Bool                     Boolean type
    | True | False             Boolean values
    | if a then b else c       If 

    | { x : A | B }            Dependent pair type
    | (a, b)                   Prod introduction
    | pcase a of (x,y) -> b    Prod elimination
    | a = b                    Equality type
    | refl                     Equality proof
    | subst a by b             Type conversion
    | contra a                 Contra

    | C a ...                  Type / Term constructors
    | case a [y] of            Pattern matching
        C1 [x] y z -> b1
        C2 x [y]   -> b2

    | \ [x <:A> ] . a          Erased lambda
    | a [b]                    Erased application
    | [x : A] -> B             Erased pi    


  declarations:

      foo : A
      foo = a

      data T D : Type where
         C1 of D1
         ...
         Cn of Dn

  telescopes:
    D ::=
                               Empty
     | (x : A) D               runtime cons
     | (A) D                   runtime cons
     | [x : A] D               erased cons
     | [A = B] D               equality constraint


  Syntax sugar:

   - You can collapse lambdas, like:

         \ x [y] z . a

     This gets parsed as \ x . \ [y] . \ z . a

-}

liftError :: (MonadError e m) => Either e a -> m a
liftError (Left e) = throwError e
liftError (Right a) = return a

-- | Parse a module declaration from the given filepath.
parseModuleFile :: (MonadError ParseError m, MonadIO m) => ConstructorNames -> String -> m Module
parseModuleFile cnames name = do
  liftIO $ putStrLn $ "Parsing File " ++ show name
  contents <- liftIO $ readFile name
  liftError $ runFreshM $ 
    flip evalStateT cnames $
     (runParserT (do { whiteSpace; v <- moduleDef;eof; return v}) [] name contents)


-- | Parse only the imports part of a module from the given filepath.
parseModuleImports :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleImports name = do
  contents <- liftIO $ readFile name
  liftError $ runFreshM $ 
    flip evalStateT emptyConstructorNames $

     (runParserT (do { whiteSpace; moduleImports }) [] name contents)

-- | Test an 'LParser' on a String.
testParser :: (LParser t) -> String -> Either ParseError t
testParser parser str = runFreshM $ 
   flip evalStateT emptyConstructorNames $

     runParserT (do { whiteSpace; v <- parser; eof; return v}) [] "<interactive>" str

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser expr

-- * Lexer definitions
type LParser a = ParsecT
                    String                      -- The input is a sequence of Char
                    [Column] (                  -- The internal state for Layout tabs
    StateT ConstructorNames 
                       FreshM)                  -- The internal state for generating fresh names, 
                    a                           -- the type of the object being parsed

instance Fresh (ParsecT s u (StateT ConstructorNames FreshM))  where
  fresh = lift . lift . fresh



-- Based on Parsec's haskellStyle (which we can not use directly since
-- Parsec gives it a too specific type).
trellysStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
trellysStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart	       = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  ["refl"
                  ,"ind"
                  ,"Type"
                  ,"data"
                  ,"where"
                  ,"case"
                  ,"of"
                  ,"with"
                  ,"contra"
                  ,"subst", "by", "at"
                  ,"let", "in"
                  ,"axiom"
                  ,"erased"
                  ,"TRUSTME"
                  ,"ord" 
                  , "pcase"
                  , "Bool", "True", "False" 
                  ,"if","then","else"
                  , "One", "tt"                               
                  ]
               , Token.reservedOpNames =
                 ["!","?","\\",":",".",",","<", "=", "+", "-", "^", "()", "_","|","{", "}"]
                }
tokenizer :: Token.GenTokenParser String [Column] (StateT ConstructorNames FreshM)

layout :: forall a t. LParser a -> LParser t -> LParser [a]
(tokenizer, layout) = 
  let (t, Token.LayFun l) = Token.makeTokenParser trellysStyle "{" ";" "}"
      in (t, l)

identifier :: LParser String
identifier = Token.identifier tokenizer

whiteSpace :: LParser ()
whiteSpace = Token.whiteSpace tokenizer

variable :: LParser TName
variable =
  do i <- identifier 
     cnames <- get
     if (i `S.member` (tconNames cnames) || 
         i `S.member` (dconNames cnames))
       then fail "Expected a variable, but a constructor was found"
       else return $ string2Name i
     
     
wildcard :: LParser TName
wildcard = reservedOp "_" >> return wildcardName

varOrWildcard :: LParser TName
varOrWildcard = try wildcard <|> variable

dconstructor :: LParser DCName
dconstructor =
  do i <- identifier 
     cnames <- get
     if (i `S.member` dconNames cnames)
       then return i
       else if (i `S.member` tconNames cnames)
             then fail "Expected a data constructor, but a type constructor was found."
             else fail "Expected a constructor, but a variable was found"
                  
tconstructor :: LParser TCName
tconstructor =
  do i <- identifier
     cnames <- get
     if (i `S.member` tconNames cnames)
       then return i
       else if (i `S.member` dconNames cnames)
             then fail "Expected a type constructor, but a data constructor was found."
             else fail "Expected a constructor, but a variable was found"                  


-- variables or zero-argument constructors
varOrCon :: LParser Term
varOrCon = do i <- identifier
              cnames <- get
              if  (i `S.member` (dconNames cnames))
                then return (DCon i [] (Annot Nothing))
                else if  (i `S.member` tconNames cnames)
                       then return (TCon i [])
                       else return (Var (string2Name i))


colon, dot, comma :: LParser ()
colon = Token.colon tokenizer >> return ()
dot = Token.dot tokenizer >> return ()
comma = Token.comma tokenizer >> return ()
  
reserved,reservedOp :: String -> LParser ()
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer

parens,brackets :: LParser a -> LParser a
parens = Token.parens tokenizer
brackets = Token.brackets tokenizer
-- braces = Token.braces tokenizer

natural :: LParser Int
natural = fromInteger <$> Token.natural tokenizer

natenc :: LParser Term
natenc =
  do n <- natural
     return $ encode n 
   where encode 0 = DCon "Zero" [] natty
         encode n = DCon "Succ" [Arg Runtime (encode (n-1))] natty
         natty    = Annot $ Just (TCon "Nat" [])


moduleImports :: LParser Module
moduleImports = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  return $ Module modName imports []     emptyConstructorNames

moduleDef :: LParser Module
moduleDef = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  decls <- layout decl (return ())
  cnames <- get
  return $ Module modName imports decls     cnames

importDef :: LParser ModuleImport
importDef = do reserved "import" >>  (ModuleImport <$> importName)
  where importName = identifier

telescope :: LParser Telescope
telescope = do 
  bindings <- telebindings
  return $ foldr g Empty bindings where
    g (n, t, ep) rst = Cons ep n t rst
  
telebindings :: LParser [(TName, Term, Epsilon)]
telebindings = many teleBinding
  where
    annot = do
      (x,ty) <-    try ((,) <$> varOrWildcard        <*> (colon >> expr))
                <|>    ((,) <$> (fresh wildcardName) <*> expr)
      return (x,ty,Runtime)

    imp = (,,) <$> varOrWildcard <*> (colon >> expr) <*> return Erased
    
    equal = (,,) <$> variable <*> (reservedOp "=" >> expr) <*> return Constraint
    
    teleBinding :: LParser (TName, Term, Epsilon)
    teleBinding =
      (    parens annot
       <|> try (brackets imp)
       <|> brackets equal) <?> "binding"

    
---
--- Top level declarations
---

decl,sigDef,valDef :: LParser Decl
decl = (try dataDef) <|>  sigDef <|> valDef 

-- datatype declarations.
dataDef :: LParser Decl
dataDef = do
  reserved "data"
  name <- identifier
  params <- telescope
  colon
  Type <- typen
  modify (\cnames -> 
           cnames{ tconNames = S.insert name 
                               (tconNames cnames) })
  reserved "where"
  cs <- layout constructorDef (return ())
  forM_ cs
    (\(ConstructorDef _ cname _) ->
       modify (\cnames -> cnames{ dconNames = S.insert cname (dconNames cnames)}))
  return $ Data name params cs

constructorDef :: LParser ConstructorDef
constructorDef = do
  pos <- getPosition
  cname <- identifier
  args <- option Empty (reserved "of" >> telescope)
  return $ ConstructorDef pos cname args
  <?> "Constructor"

  
sigDef = do
  n <- try (variable >>= \v -> colon >> return v)
  ty <- expr
  return $ Sig n ty 

valDef = do
  n <- try (do {n <- variable; reservedOp "="; return n})
  val <- expr
  return $ Def n val


------------------------
------------------------
-- Terms
------------------------
------------------------

trustme :: LParser Term
trustme = do reserved "TRUSTME" 
             return (TrustMe (Annot Nothing))

refl :: LParser Term
refl =
  do reserved "refl"
     return $ Refl (Annot Nothing)

     
-- Expressions

expr,term,factor :: LParser Term
 
-- expr is the toplevel expression grammar
expr = do
    p <- getPosition
    Pos p <$> (buildExpressionParser table term)
  where table = [
                 [ifix  AssocLeft "=" TyEq],
                 [ifixM AssocRight "->" mkArrow]
                ]   
        ifix  assoc op f = Infix (reservedOp op >> return f) assoc 
        ifixM assoc op f = Infix (reservedOp op >> f) assoc
        mkArrow  = 
          do n <- fresh wildcardName
             return $ \tyA tyB -> 
               Pi (bind (n,embed tyA) tyB)
               
-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = try dconapp <|>  try tconapp <|>  funapp

arg :: LParser Arg
arg = (Arg Erased) <$> brackets expr <|> (Arg Runtime) <$> factor

dconapp :: LParser Term
dconapp = do 
  c <- dconstructor
  args <- many arg
  return $ DCon c args (Annot Nothing)
  
tconapp :: LParser Term  
tconapp = do
  c <- tconstructor
  ts <- many factor
  return $ TCon c ts

  
funapp :: LParser Term
funapp = do 
  f <- factor
  foldl' app f <$> many bfactor
  where
        bfactor = ((,Erased)  <$> brackets expr) 
                             <|> ((,Runtime) <$> factor)
        app e1 (e2,Runtime)  =  App e1 e2
        app e1 (e2,Erased)   =  ErasedApp e1 e2
        app e1 (e2,Constraint) = error "internal error"


factor = choice [ varOrCon   <?> "a variable or nullary data constructor"
                                  
                , typen      <?> "Type"
                , lambda     <?> "a lambda"
                , letExpr    <?> "a let"
                                  , natenc     <?> "a literal"                  
                , caseExpr   <?> "a case" 
                                  , substExpr  <?> "a subst"
                , refl       <?> "refl"
                , contra     <?> "a contra" 
                , trustme    <?> "TRUSTME"
                                  , impProd    <?> "an implicit function type"
                  
                , bconst     <?> "a constant"  
                , ifExpr     <?> "an if expression" 
                , sigmaTy    <?> "a sigma type"  
                , pcaseExpr  <?> "a pcase"
                , expProdOrAnnotOrParens
                    <?> "an explicit function type or annotated expression"
                ]

impOrExpVar :: LParser (TName, Epsilon)
impOrExpVar = try ((,Erased) <$> (brackets variable)) 
              <|> (,Runtime) <$> variable


typen :: LParser Term
typen =
  do reserved "Type"
     return Type



  -- Lambda abstractions have the syntax '\x . e' 
lambda :: LParser Term
lambda = do reservedOp "\\"
            binds <- many1                      impOrExpVar
            dot
            body <- expr
            return $ foldr lam body binds 
  where
    lam (x, Runtime) m = Lam (bind (x, embed $ Annot Nothing) m)           

    lam (x, Erased) m  = ErasedLam (bind (x, embed $ Annot Nothing) m)         
    
    lam (x, _) m = error "internal error"

                            


bconst  :: LParser Term
bconst = choice [reserved "Bool"  >> return TyBool,
                 reserved "False" >> return (LitBool False),
                 reserved "True"  >> return (LitBool True),
                 reserved "One"   >> return TyUnit,
                 reserved "tt"    >> return LitUnit]

ifExpr :: LParser Term
ifExpr = 
  do reserved "if"
     a <- expr
     reserved "then"
     b <- expr
     reserved "else"
     c <- expr
     return (If a b c (Annot Nothing))
     {-
     let tm = Match (bind (PatCon "True"  []) b)
     let fm = Match (bind (PatCon "False" []) c)
     return $ (Case a [tm, fm] (Annot Nothing))
     -}

-- 
letExpr :: LParser Term
letExpr =
  do reserved "let"
     x <- variable
     reservedOp "="
     boundExp <- expr
     reserved "in"
     body <- expr
     return $ (Let (bind (x,embed boundExp) body))

-- impProd - implicit dependent products
-- These have the syntax [x:a] -> b or [a] -> b .
impProd :: LParser Term
impProd =
  do (x,tyA) <- brackets 
       (try ((,) <$> variable <*> (colon >> expr))
        <|> ((,) <$> fresh wildcardName <*> expr))
     reservedOp "->" 
     tyB <- expr
     return $ ErasedPi (bind (x,embed tyA) tyB)


-- Function types have the syntax '(x:A) -> B'.  This production deals
-- with the ambiguity caused because these types, annotations and
-- regular old parens all start with parens.

data InParens = Colon Term Term | Comma Term Term | Nope Term

expProdOrAnnotOrParens :: LParser Term
expProdOrAnnotOrParens =
  let
    -- afterBinder picks up the return type of a pi
    afterBinder :: LParser Term
    afterBinder = do reservedOp "->"
                     rest <- expr
                     return rest

    -- before binder parses an expression in parens
    -- If it doesn't involve a colon, you get (Right tm)
    -- If it does, you get (Left tm1 tm2).  tm1 might be a variable,
    --    in which case you might be looking at an explicit pi type.
    beforeBinder :: LParser InParens
    beforeBinder = parens $
      choice [do e1 <- try (term >>= (\e1 -> colon >> return e1))
                 e2 <- expr
                 return $ Colon e1 e2
             , do e1 <- try (term >>= (\e1 -> comma >> return e1))
                  e2 <- expr
                  return $ Comma e1 e2
             , Nope <$> expr]
  in
    do bd <- beforeBinder
       case bd of
         Colon (Var x) a ->
           option (Ann (Var x) a)
                  (do b <- afterBinder
                      return $ Pi (bind (x,embed a) b))
         Colon a b -> return $ Ann a b
         Comma a b -> return $ Prod a b (Annot Nothing)
         Nope a    -> return $ Paren a

pattern :: LParser Pattern 
-- Note that 'dconstructor' and 'variable' overlaps, annoyingly.
pattern =  try (PatCon <$> dconstructor <*> many arg_pattern)
       <|> atomic_pattern
  where
    arg_pattern    =  ((,Erased) <$> brackets pattern) 
                  <|> ((,Runtime) <$> atomic_pattern)
    atomic_pattern =    (parens pattern)
                  <|> (PatVar <$> wildcard)
                  <|> do t <- varOrCon
                         case t of
                           (Var x) -> return $ PatVar x
                           (DCon c [] _) -> return $ PatCon c []
                           (TCon c []) -> fail "expected a data constructor but a type constructor was found"
                           _ -> error "internal error in atomic_pattern"

match :: LParser Match
match = 
  do pat <- pattern 
     reservedOp "->"
     body <- term
     return $ Match (bind pat body)

caseExpr :: LParser Term
caseExpr = do
    reserved "case"
    scrut <- factor
    reserved "of"
    alts <- layout match (return ())
    return $ Case scrut alts (Annot Nothing)
    
    
pcaseExpr :: LParser Term
pcaseExpr = do
    reserved "pcase"
    scrut <- expr
    reserved "of"
    reservedOp "("
    x <- variable
    reservedOp ","
    y <- variable
    reservedOp ")"
    reservedOp "->"
    a <- expr
    return $ Pcase scrut (bind (x,y) a) (Annot Nothing)

-- subst e0 by e1 
substExpr :: LParser Term
substExpr = do
  reserved "subst"
  a <- expr
  reserved "by"
  b <- expr
  return $ Subst a b (Annot Nothing)

contra :: LParser Term
contra = do
  reserved "contra"
  witness <- expr
  return $ Contra witness (Annot Nothing)


sigmaTy :: LParser Term 
sigmaTy = do
  reservedOp "{"
  x <- variable
  colon
  a <- expr
  reservedOp "|"
  b <- expr
  reservedOp "}"
  return (Sigma (bind (x, embed a) b))
  
  