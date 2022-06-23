{- pi-forall language -}

-- | A parsec-based parser for the concrete syntax
module Parser
  (
   parseModuleFile, 
   parseModuleImports,
   parseExpr,
   expr,
   decl,
   testParser
  )
  where


import Syntax hiding (moduleImports)

import qualified Unbound.Generics.LocallyNameless as Unbound

import Text.Parsec hiding (State,Empty)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified LayoutToken as Token 

import Control.Monad.State.Lazy hiding (join)
import Control.Monad.Except ( MonadError(throwError) )
import Data.List ( foldl' )
{- SOLN DATA -}
import qualified Data.Set as S
{- STUBWITH -}

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
    | PRINTME                  Show the current goal and context

    | let x = a in b           Let expression

    | Unit                     Unit type
    | ()                       Unit value

    | Bool                     Boolean type
    | True | False             Boolean values
    | if a then b else c       If 

    | { x : A | B }            Dependent pair type
    | A * B                    Nondependent pair syntactic sugar
    | (a, b)                   Prod introduction
    | let (x,y) = a in b       Prod elimination

{- SOLN EQUAL -}
    | a = b                    Equality type
    | Refl                     Equality proof
    | subst a by b             Type conversion
    | contra a                 Contra
{- STUBWITH -}
{- SOLN DATA -}
    | C a ...                  Type / Term constructors
    | case a [y] of            Pattern matching
        C1 [x] y z -> b1
        C2 x [y]   -> b2
{- STUBWITH -}
{- SOLN EP -}
    | \ [x <:A> ] . a          Irr lambda
    | a [b]                    Irr application
    | [x : A] -> B             Irr pi    
{- STUBWITH -}

  declarations:

      foo : A
      foo = a

{- SOLN DATA -}
      data T D : Type where
         C1 of D1
         ...
         Cn of Dn

  telescopes:
    D ::=
                               Empty
     | (x : A) D               runtime cons
     | (A) D                   runtime cons
     | [x : A] D               irrelevant cons
     | [A = B] D               equality constraint
{- STUBWITH -}

  Syntax sugar:

   - You can collapse lambdas, like:

         \ x [y] z . a

     This gets parsed as \ x . \ [y] . \ z . a

-}

liftError :: (MonadError e m) => Either e a -> m a
liftError (Left e) = throwError e
liftError (Right a) = return a

{- SOLN DATA -}
-- | Parse a module declaration from the given filepath.
parseModuleFile :: (MonadError ParseError m, MonadIO m) => ConstructorNames -> String -> m Module
parseModuleFile cnames name = do
  liftIO $ putStrLn $ "Parsing File " ++ show name
  contents <- liftIO $ readFile name
  liftError $ Unbound.runFreshM $ 
    flip evalStateT cnames 
     (runParserT (do { whiteSpace; v <- moduleDef;eof; return v}) [] name contents)
{- STUBWITH      
-- | Parse a module declaration from the given filepath.
parseModuleFile :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleFile name = do
  liftIO $ putStrLn $ "Parsing File " ++ show name
  contents <- liftIO $ readFile name
  liftError $ Unbound.runFreshM 
     (runParserT (do { whiteSpace; v <- moduleDef;eof; return v}) [] name contents)
-}

-- | Parse only the imports part of a module from the given filepath
parseModuleImports :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleImports name = do
  contents <- liftIO $ readFile name
  liftError $ Unbound.runFreshM $ 
{- SOLN DATA -}
    flip evalStateT emptyConstructorNames $
{- STUBWITH -}
     (runParserT (do { whiteSpace; moduleImports }) [] name contents)

-- | Test an 'LParser' on a String.
testParser :: {- SOLN DATA -} ConstructorNames -> {- STUBWITH -} LParser t -> String -> Either ParseError t
testParser {- SOLN DATA -} cn{- STUBWITH -} parser str = Unbound.runFreshM $ 
{- SOLN DATA -}
   flip evalStateT cn $
{- STUBWITH -}
     runParserT (do { whiteSpace; v <- parser; eof; return v}) [] "<interactive>" str

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser {- SOLN DATA -} emptyConstructorNames{- STUBWITH -} expr

-- * Lexer definitions
type LParser a = ParsecT
                    String                      -- The input is a sequence of Char
                    [Column] (                  -- The internal state for Layout tabs
{- SOLN DATA -}     StateT ConstructorNames {- STUBWITH -}
                    Unbound.FreshM)             -- The internal state for generating fresh names, 
                    a                           -- the type of the object being parsed

{- SOLN DATA -}
instance Unbound.Fresh (ParsecT s u (StateT ConstructorNames Unbound.FreshM))  where
  fresh = lift . lift . Unbound.fresh
{- STUBWITH 
instance Unbound.Fresh (ParsecT s u Unbound.FreshM)  where
  fresh = lift . Unbound.fresh -}


-- Based on Parsec's haskellStyle (which we can not use directly since
-- Parsec gives it a too specific type).
piforallStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
piforallStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart        = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  ["Refl"
                  ,"ind"
                  ,"Type"
                  ,"data"
                  ,"where"
                  ,"case"
                  ,"of"
                  ,"with"
                  ,"contra"
                  ,"subst", "by"
                  ,"let", "in"
                  ,"axiom"
                  ,"TRUSTME"
                  ,"PRINTME"
                  ,"ord" 
                  ,"Bool", "True", "False" 
                  ,"if","then","else"
                  ,"Unit", "()"                               
                  ]
               , Token.reservedOpNames =
                 ["!","?","\\",":",".",",","<", "=", "+", "-", "*", "^", "()", "_","|","{", "}"]
                }
{- SOLN DATA -}
tokenizer :: Token.GenTokenParser String [Column] (StateT ConstructorNames Unbound.FreshM)
{- STUBWITH tokenizer :: Token.GenTokenParser String [Column] (Unbound.FreshM) -}
layout :: forall a t. LParser a -> LParser t -> LParser [a]
(tokenizer, Token.LayFun layout) = Token.makeTokenParser piforallStyle  "{" ";" "}"

identifier :: LParser String
identifier = Token.identifier tokenizer

whiteSpace :: LParser ()
whiteSpace = Token.whiteSpace tokenizer

variable :: LParser TName
variable =
  do i <- identifier 
{- SOLN DATA -}
     cnames <- get
     if (i `S.member` (tconNames cnames) || 
         i `S.member` (dconNames cnames))
       then fail "Expected a variable, but a constructor was found"
       else return $ Unbound.string2Name i
     {- STUBWITH      return $ Unbound.string2Name i -}
     
{- SOLN DATA -}
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
{- STUBWITH -}

{- SOLN DATA -}
-- variables or zero-argument constructors
varOrCon :: LParser Term
varOrCon = do i <- identifier
              cnames <- get
              if  (i `S.member` (dconNames cnames))
                then return (DCon i [] )
                else if  (i `S.member` tconNames cnames)
                       then return (TCon i [])
                       else return (Var (Unbound.string2Name i))
{- STUBWITH -}

colon, dot, comma :: LParser ()
colon = Token.colon tokenizer >> return ()
dot = Token.dot tokenizer >> return ()
comma = Token.comma tokenizer >> return ()
  
reserved,reservedOp :: String -> LParser ()
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer

parens, brackets, braces :: LParser a -> LParser a
parens = Token.parens tokenizer
brackets = Token.brackets tokenizer
braces = Token.braces tokenizer

{- SOLN DATA -}
natural :: LParser Int
natural = fromInteger <$> Token.natural tokenizer

natenc :: LParser Term
natenc = encode <$> natural 
   where encode 0 = DCon "Zero" []
         encode n = DCon "Succ" [Arg Rel (encode (n-1))]
{- STUBWITH -}

moduleImports :: LParser Module
moduleImports = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  return $ Module modName imports [] {- SOLN DATA -}
    emptyConstructorNames{- STUBWITH -}

moduleDef :: LParser Module
moduleDef = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  decls <- layout decl (return ())
{- SOLN DATA -}
  cnames <- get{- STUBWITH -}
  return $ Module modName imports decls {- SOLN DATA -}
    cnames{- STUBWITH -}

importDef :: LParser ModuleImport
importDef = do reserved "import" >>  (ModuleImport <$> importName)
  where importName = identifier

{- SOLN DATA -}
telescope :: LParser Telescope
telescope = do 
  bindings <- telebindings
  return $ Telescope (foldr id [] bindings) where
  
telebindings :: LParser [[Decl] -> [Decl]]
telebindings = many teleBinding
  where
    annot = do
      (x,ty) <-    try ((,) <$> varOrWildcard        <*> (colon >> expr))
                <|>    ((,) <$> (Unbound.fresh wildcardName) <*> expr)
      return (TypeSig (Sig x Rel ty):)

    imp = do
        v <- varOrWildcard
        colon
        t <- expr
        return (TypeSig (Sig v Irr t):)
    
    equal = do
        v <- variable
        reservedOp "="
        t <- expr
        return (Def v t :)
    
    teleBinding :: LParser ([Decl] -> [Decl])
    teleBinding =
      (    parens annot
       <|> try (brackets imp)
       <|> brackets equal) <?> "binding"
{- STUBWITH -}
    
---
--- Top level declarations
---

decl,sigDef,valDef :: LParser Decl
decl = {- SOLN DATA -} (try dataDef) <|> {- STUBWITH -} sigDef <|> valDef 

{- SOLN DATA -}
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
  args <- option (Telescope []) (reserved "of" >> telescope)
  return $ ConstructorDef pos cname args
  <?> "Constructor"
{- STUBWITH -}
  
sigDef = do
  n <- try (variable >>= \v -> colon >> return v)
  ty <- expr
  return (mkSig n ty)

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
trustme = reserved "TRUSTME" *> return (TrustMe )

printme :: LParser Term
printme = reserved "PRINTME" *> return (PrintMe )

{- SOLN EQUAL -}
refl :: LParser Term
refl =
  do reserved "Refl"
     return $ Refl 
{- STUBWITH -}

-- Expressions

expr,term,factor :: LParser Term
 
-- expr is the toplevel expression grammar
expr = do
    p <- getPosition
    Pos p <$> buildExpressionParser table term
  where table = [
{- SOLN EQUAL -}
                 [ifix  AssocLeft "=" TyEq],{- STUBWITH -}
                 [ifixM AssocRight "->" mkArrowType],
                 [ifixM AssocRight "*" mkTupleType]
                ]   
{- SOLN EQUAL -} 
        ifix  assoc op f = Infix (reservedOp op >> return f) assoc {- STUBWITH -}
        ifixM assoc op f = Infix (reservedOp op >> f) assoc
        mkArrowType  = 
          do n <- Unbound.fresh wildcardName
             return $ \tyA tyB -> 
               Pi {- SOLN EP -} Rel {- STUBWITH -}tyA (Unbound.bind n tyB)
        mkTupleType = 
          do n <- Unbound.fresh wildcardName
             return $ \tyA tyB -> 
{- SOLN DATA -}
               TCon sigmaName [Arg Rel tyA, Arg Rel $ Lam Rel (Unbound.bind n tyB)]
{- STUBWITH               Sigma tyA (Unbound.bind n tyB) -}
               
-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = {- SOLN DATA -} try dconapp <|> try tconapp <|> {- STUBWITH -} funapp

{- SOLN DATA -}
arg :: LParser Arg
arg = try (Arg Irr <$> brackets expr)
   <|> Arg Rel <$> factor

dconapp :: LParser Term
dconapp = do 
  c <- dconstructor
  args <- many arg
  return $ DCon c args 
  
tconapp :: LParser Term  
tconapp = do
  c <- tconstructor
  ts <- many arg
  return $ TCon c ts
{- STUBWITH -}
  
funapp :: LParser Term
funapp = do 
  f <- factor
  foldl' app f <$> many bfactor
  where
{- SOLN EP -}
        bfactor = ((,Irr)  <$> brackets expr) 
                             <|> ((,Rel) <$> factor)
        app e1 (e2,ep)  =  App e1 (Arg ep e2)

{- STUBWITH      
        bfactor = factor 
        app e1 e2 = App e1 e2 -}

factor = choice [ {- SOLN DATA -} varOrCon   <?> "a variable or nullary data constructor"
                  {- STUBWITH Var <$> variable <?> "a variable" -}                
                , typen      <?> "Type"
                , lambda     <?> "a lambda"
                , try letPairExp  <?> "a let pair"
                , letExpr <?> "a let"
                  {- SOLN DATA -}
                , natenc     <?> "a literal"                  
                , caseExpr   <?> "a case" {- STUBWITH -}
                  {- SOLN EQUAL -}
                , substExpr  <?> "a subst"
                , refl       <?> "Refl"
                , contra     <?> "a contra" {- STUBWITH -}
                , trustme    <?> "TRUSTME"
                , printme    <?> "PRINTME"
                  {- SOLN EP -}
                , impProd    <?> "an implicit function type"
                  {- STUBWITH -}
                , bconst     <?> "a constant"  
                , ifExpr     <?> "an if expression" 
                , sigmaTy    <?> "a sigma type"  
                
                , expProdOrAnnotOrParens
                    <?> "an explicit function type or annotated expression"
                ]

{- SOLN EP -}
impOrExpVar :: LParser (TName, Epsilon)
impOrExpVar = try ((,Irr) <$> (brackets variable)) 
              <|> (,Rel) <$> variable
{- STUBWITH -}

typen :: LParser Term
typen =
  do reserved "Type"
     return Type



  -- Lambda abstractions have the syntax '\x . e' 
lambda :: LParser Term
lambda = do reservedOp "\\"
            binds <- many1 {- SOLN EP -}
                     impOrExpVar{- STUBWITH variable -}
            dot
            body <- expr
            return $ foldr lam body binds 
  where
{- SOLN EP -}
    lam (x, ep) m = Lam ep (Unbound.bind x m)           
{- STUBWITH         lam x m = Lam (Unbound.bind x m) -}  

                            


bconst  :: LParser Term
{- SOLN DATA -}
bconst = choice [reserved "Bool"  >> return (TCon boolName []),
                 reserved "False" >> return (DCon falseName []),
                 reserved "True"  >> return (DCon trueName []),
                 reserved "Unit"  >> return (TCon tyUnitName []),
                 reserved "()"    >> return (DCon litUnitName [])]
{- STUBWITH 
bconst = choice [reserved "Bool"  >> return TyBool,
                 reserved "False" >> return (LitBool False),
                 reserved "True"  >> return (LitBool True),
                 reserved "Unit"   >> return TyUnit,
                 reserved "()"    >> return LitUnit] -}


ifExpr :: LParser Term
ifExpr = 
  do reserved "if"
     a <- expr
     reserved "then"
     b <- expr
     reserved "else"
     c <- expr
{- SOLN DATA -}
     return (Case a [Match $ Unbound.bind (PatCon trueName []) b, 
                     Match $ Unbound.bind (PatCon falseName []) c])
{- STUBWITH
     return (If a b c ) -}
    

-- 
letExpr :: LParser Term
letExpr =
  do reserved "let"
     x <- variable
     reservedOp "="
     rhs <- expr
     reserved "in"
     body <- expr
     return $ Let rhs (Unbound.bind x body)

letPairExp :: LParser Term
letPairExp = do
    reserved "let"
    reservedOp "("
    x <- variable
    reservedOp ","
    y <- variable
    reservedOp ")"
    reservedOp "="
    scrut <- expr
    reserved "in"
    a <- expr
{- SOLN DATA -}
    let pat = PatCon prodName [(PatVar x, Rel), (PatVar y, Rel)]
    return $ Case scrut [Match (Unbound.bind pat a)]
{- STUBWITH     return $ LetPair scrut (Unbound.bind (x,y) a)  -}


{- SOLN EP -}
-- impProd - implicit dependent products
-- These have the syntax [x:a] -> b or [a] -> b .
impProd :: LParser Term
impProd =
  do (x,tyA) <- brackets 
       (try ((,) <$> variable <*> (colon >> expr))
        <|> ((,) <$> Unbound.fresh wildcardName <*> expr))
     reservedOp "->" 
     tyB <- expr
     return $ Pi Irr tyA (Unbound.bind x tyB)
{- STUBWITH -}

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
                      return $ Pi {- SOLN EP -} Rel {- STUBWITH -}a (Unbound.bind x b))
         Colon a b -> return $ Ann a b
      
         Comma a b -> 
{- SOLN DATA -}   
           return $ DCon prodName [Arg Rel a, Arg Rel b] 
{- STUBWITH            return $ Prod a b -}
         Nope a    -> return a

{- SOLN DATA -}
-- patterns are 
-- p :=  x
--       _
--       K ap*
--       (p)
--       (p, p)
-- ap ::= [p] | p        

-- Note that 'dconstructor' and 'variable' overlaps, annoyingly.
pattern :: LParser Pattern
pattern =  try (PatCon <$> dconstructor <*> many arg_pattern)
       <|> atomic_pattern
  where
    arg_pattern    =  ((,Irr) <$> brackets pattern) 
                  <|> ((,Rel) <$> atomic_pattern)
    paren_pattern  = do 
      pattern >>= \p ->
        ( (reservedOp ")" >> pure p)
       <|> reservedOp "," *> (atomic_pattern >>= \q -> 
                              pure (PatCon prodName [(p, Rel), (q, Rel)]))
        ) 
    atomic_pattern =  reservedOp "(" *> paren_pattern
                  <|> reserved "True" *> pure (PatCon trueName [])
                  <|> reserved "False" *> pure (PatCon falseName [])
                  <|> reserved "()" *> pure (PatCon litUnitName [])
                  <|> PatVar <$> wildcard
                  <|> do t <- varOrCon
                         case t of
                           (Var x) -> return $ PatVar x
                           (DCon c []) -> return $ PatCon c []
                           (TCon c []) -> fail "expected a data constructor but a type constructor was found"
                           _ -> error "internal error in atomic_pattern"


match :: LParser Match
match = 
  do pat <- pattern 
     reservedOp "->"
     pos <- getPosition
     body <- expr
     return $ Match (Unbound.bind pat (Pos pos body))

caseExpr :: LParser Term
caseExpr = do
    reserved "case"
    pos <- getPosition
    scrut <- expr
    reserved "of"
    alts <- layout match (return ())
    return $ Case (Pos pos scrut) alts 
{- STUBWITH -}    
    

{- SOLN EQUAL -}
-- subst e0 by e1 
substExpr :: LParser Term
substExpr = do
  reserved "subst"
  a <- expr
  reserved "by"
  b <- expr
  return $ Subst a b 

contra :: LParser Term
contra = do
  reserved "contra"
  witness <- expr
  return $ Contra witness 
{- STUBWITH -}

sigmaTy :: LParser Term 
sigmaTy = do
  reservedOp "{"
  x <- variable
  colon
  a <- expr
  reservedOp "|"
  b <- expr
  reservedOp "}"
{- SOLN DATA -}
  return $ TCon sigmaName [Arg Rel a, Arg Rel (Lam Rel (Unbound.bind x b))]
{- STUBWITH   return (Sigma a (Unbound.bind x b)) -}
  
  
