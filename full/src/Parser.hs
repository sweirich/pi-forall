{- pi-forall language -}

-- | A parsec-based parser for the concrete syntax
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant bracket" #-}
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
    | (x : A @ k) -> B         Pi type

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

    | a = b                    Equality type
    | Refl                     Equality proof
    | subst a by b             Type conversion
    | contra a                 Contra

    | C a ...                  Type / Term constructors
    | case a [y] of            Pattern matching
        C1 [x] y z -> b1
        C2 x [y]   -> b2

    | \ [x <:A> ] . a          Irr lambda
    | a [b]                    Irr application
    | [x : A] -> B             Irr pi    

    | x ^ i                    Displacement

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
     | [x : A] D               irrelevant cons
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
  liftError $ Unbound.runFreshM $
    flip evalStateT cnames
     (runParserT (do { whiteSpace; v <- moduleDef;eof; return v}) [] name contents)


-- | Parse only the imports part of a module from the given filepath
parseModuleImports :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleImports name = do
  contents <- liftIO $ readFile name
  liftError $ Unbound.runFreshM $
    flip evalStateT emptyConstructorNames $

     (runParserT (do { whiteSpace; moduleImports }) [] name contents)

-- | Test an 'LParser' on a String.
testParser :: ConstructorNames ->  LParser t -> String -> Either ParseError t
testParser cn parser str = Unbound.runFreshM $
   flip evalStateT cn $

     runParserT (do { whiteSpace; v <- parser; eof; return v}) [] "<interactive>" str

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser emptyConstructorNames expr

-- * Lexer definitions
type LParser a = ParsecT
                    String                      -- The input is a sequence of Char
                    [Column] (                  -- The internal state for Layout tabs
    StateT ConstructorNames
                    Unbound.FreshM)             -- The internal state for generating fresh names, 
                    a                           -- the type of the object being parsed

instance Unbound.Fresh (ParsecT s u (StateT ConstructorNames Unbound.FreshM))  where
  fresh = lift . lift . Unbound.fresh



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
                 ["!","?","\\",":",".",",","<", "=", "+", "-", "*", "^", "()", "_","|","{", "}", "@", "^"]
                }
tokenizer :: Token.GenTokenParser String [Column] (StateT ConstructorNames Unbound.FreshM)

layout :: forall a t. LParser a -> LParser t -> LParser [a]
(tokenizer, Token.LayFun layout) = Token.makeTokenParser piforallStyle  "{" ";" "}"

at :: LParser ()
at = Token.reservedOp tokenizer "@"

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
       else return $ Unbound.string2Name i


wildcard :: LParser TName
wildcard = reservedOp "_" >> return wildcardName

varOrWildcard :: LParser TName
varOrWildcard = try wildcard <|> variable

dconstructor :: LParser DCName
dconstructor =
  do i <- identifier
     cnames <- get
     if i `S.member` dconNames cnames
       then return i
       else if i `S.member` tconNames cnames
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
                then do
                  j <- Unbound.fresh (Unbound.string2Name "j")
                  return (DCon i (LVar j) [] )
                else if  (i `S.member` tconNames cnames)
                       then do
                          j <- Unbound.fresh (Unbound.string2Name "j")
                          return (TCon i (LVar j) [])
                       else return (Var (Unbound.string2Name i))


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

natural :: LParser Int
natural = fromInteger <$> Token.natural tokenizer

natenc :: LParser Term
natenc = do
     j <- Unbound.fresh (Unbound.string2Name "j")
     encode j <$> natural
   where encode j 0 = DCon "Zero" (LVar j) []
         encode j n = DCon "Succ" (LVar j) [Arg Rel (encode j (n-1))]


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

telescope :: LevelContext -> LParser Telescope
telescope ctx = do
  bindings <- telebindings ctx
  return $ Telescope (foldr id [] bindings) where

-- Omitted levels are unification variables
levelP :: LParser Level
levelP =
  try (LConst <$> (at *> natural)) <|> do
    x <- Unbound.fresh (Unbound.string2Name "l")
    return (LVar x)

optLevel :: LevelContext -> LParser (Maybe Level)
optLevel Fixed = Just <$> levelP
optLevel Float = 
      try (Just . LConst <$> (at *> natural)) 
  <|> try (at *> do x <- Unbound.fresh (Unbound.string2Name "l")
                    return (Just (LVar x)))
  <|> return Nothing


telebindings :: LevelContext -> LParser [[Decl] -> [Decl]]
telebindings ctx = many teleBinding
  where
    --  `_ : A`   or `x : A @ l`  or `A`
    -- if there is a colon and no level defined, we use the context to determine whether to 
    -- generate a level variable. If there is no colon, we don't generate a level variable
    annot rho = do
      (x,ty,lvl) <-    try ((,,) <$> wildcard <*> (colon >> expr) <*> optLevel ctx)
                <|>    try ((,,) <$> variable <*> (colon >> expr) <*> optLevel ctx)
                <|>        ((,,) <$> Unbound.fresh wildcardName <*> expr <*> optLevel Float)
      return (TypeSig (Sig x rho lvl ty):)

    equal = do
        v <- variable
        reservedOp "="
        t <- expr
        -- l <- try (at *> natural) <|> pure 0
        return (Def v t :)

    teleBinding :: LParser ([Decl] -> [Decl])
    teleBinding =
      (    parens (annot Rel)
       <|> try (brackets equal)
       <|> brackets (annot Irr)) <?> "binding"


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
  params <- telescope Float
  colon
  Type <- typen
  lvl  <- levelP
  modify (\cnames ->
           cnames{ tconNames = S.insert name
                               (tconNames cnames) })
  reserved "where"
  cs <- layout constructorDef (return ())
  forM_ cs
    (\(ConstructorDef _ cname _ _) ->
       modify (\cnames -> cnames{ dconNames = S.insert cname (dconNames cnames)}))
  return $ Data name params cs lvl

constructorDef :: LParser ConstructorDef
constructorDef = do
  pos <- getPosition
  cname <- identifier
  args <- option (Telescope []) (reserved "of" >> telescope Fixed)
  lvl  <- levelP
  return $ ConstructorDef pos cname args lvl
  <?> "Constructor"


sigDef = do
  n <- try (variable >>= \v -> colon >> return v)
  ty <- expr
  l  <- levelP
  return (mkSig n ty l)

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

refl :: LParser Term
refl =
  do reserved "Refl"
     return $ Refl


-- Expressions

expr,term,factor :: LParser Term

-- expr is the toplevel expression grammar
expr = do
    p <- getPosition
    Pos p <$> buildExpressionParser table term
  where table = [
                 [ifix  AssocLeft "=" TyEq],
                 [ifixM AssocRight "->" mkArrowType],
                 [ifixM AssocRight "*" mkTupleType]
                ]
        ifix  assoc op f = Infix (reservedOp op >> return f) assoc
        ifixM assoc op f = Infix (reservedOp op >> f) assoc
        mkArrowType  =
          do n <- Unbound.fresh wildcardName
             return $ \tyA tyB ->
               Pi (Mode Rel Nothing) tyA (Unbound.bind n tyB)
        mkTupleType =
          do n <- Unbound.fresh wildcardName
             j <- Unbound.fresh (Unbound.string2Name "j")
             return $ \tyA tyB ->
               TCon sigmaName (LVar j) [Arg Rel tyA, Arg Rel $ Lam Rel (Unbound.bind n tyB)]


-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = try dconapp <|> try tconapp <|>  funapp

arg :: LParser Arg
arg = try (Arg Irr <$> brackets expr)
   <|> Arg Rel <$> factor

dconapp :: LParser Term
dconapp = do
  c <- dconstructor
  j <- Unbound.fresh (Unbound.string2Name "j")
  args <- many arg
  return $ DCon c (LVar j) args

tconapp :: LParser Term
tconapp = do
  c <- tconstructor
  j <- Unbound.fresh (Unbound.string2Name "j")
  ts <- many arg
  return $ TCon c (LVar j) ts


funapp :: LParser Term
funapp = do
  f <- factor
  foldl' app f <$> many bfactor
  where
        bfactor = ((,Irr)  <$> brackets expr)
                             <|> ((,Rel) <$> factor)
        app e1 (e2,ep)  =  App e1 (Arg ep e2)



factor = choice [ try displaceTm <?> "displaced term"
                , varOrCon   <?> "a variable or nullary data constructor"

                , typen      <?> "Type"
                , lambda     <?> "a lambda"
                , try letPairExp  <?> "a let pair"
                , letExpr <?> "a let"
                , natenc     <?> "a literal"
                , caseExpr   <?> "a case"
                , substExpr  <?> "a subst"
                , refl       <?> "Refl"
                , contra     <?> "a contra"
                , trustme    <?> "TRUSTME"
                , printme    <?> "PRINTME"
                , impProd    <?> "an implicit function type"
                , bconst     <?> "a constant"
                , ifExpr     <?> "an if expression"
                , sigmaTy    <?> "a sigma type"

                , expProdOrAnnotOrParens
                    <?> "an explicit function type or annotated expression"
                ]

impOrExpVar :: LParser (TName, Rho)
impOrExpVar = try ((,Irr) <$> (brackets variable))
              <|> (,Rel) <$> variable


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
    lam (x, ep) m = Lam ep (Unbound.bind x m)


lj :: LParser Level
lj = do
  l <- Unbound.fresh (Unbound.string2Name "j")
  return (LVar l)


bconst  :: LParser Term
bconst = choice [reserved "Bool"  >> lj >>= \j -> return (TCon boolName j []),
                 reserved "False" >> lj >>= \j -> return (DCon falseName j []),
                 reserved "True"  >> lj >>= \j -> return (DCon trueName j []),
                 reserved "Unit"  >> lj >>= \j -> return (TCon tyUnitName j []),
                 reserved "()"    >> lj >>= \j -> return (DCon litUnitName j [])]



ifExpr :: LParser Term
ifExpr =
  do reserved "if"
     a <- expr
     reserved "then"
     b <- expr
     reserved "else"
     c <- expr
     return (Case a [Match $ Unbound.bind (PatCon trueName []) b,
                     Match $ Unbound.bind (PatCon falseName []) c])



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
    let pat = PatCon prodName [(PatVar x, Rel), (PatVar y, Rel)]
    return $ Case scrut [Match (Unbound.bind pat a)]



-- impProd - implicit dependent products
-- These have the syntax [x:a @ l] -> b or [a] -> b .
impProd :: LParser Term
impProd =
  do (x,tyA,lvl) <- brackets
       (try ((,,) <$> variable <*> (colon >> expr) <*> (Just <$> levelP))
        <|> ((,,) <$> Unbound.fresh wildcardName <*> expr <*> pure Nothing))
     reservedOp "->"
     Pi (Mode Irr lvl) tyA . Unbound.bind x <$> expr


-- Function types have the syntax '(x:A) -> B'.  This production deals
-- with the ambiguity caused because these types, annotations and
-- regular old parens all start with parens.

data InParens = Colon Term Term Level | Comma Term Term | Nope Term

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
                 Colon e1 e2 <$> levelP
             , do e1 <- try (term >>= (\e1 -> comma >> return e1))
                  Comma e1 <$> expr
             , Nope <$> expr]
  in
    do bd <- beforeBinder
       case bd of
         Colon (Var x) a l ->
           option (Ann (Var x) a)
                  (do b <- afterBinder
                      return $ Pi (Mode Rel (Just l)) a (Unbound.bind x b))
         Colon a b _ -> return $ Ann a b

         Comma a b -> do
           j <- lj
           return $ DCon prodName j [Arg Rel a, Arg Rel b]

         Nope a    -> return a

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
        (reservedOp ")" >> pure p)
       <|> reservedOp "," *> (atomic_pattern >>= \q ->
                              pure (PatCon prodName [(p, Rel), (q, Rel)]))
    atomic_pattern =  reservedOp "(" *> paren_pattern
                  <|> reserved "True" *> pure (PatCon trueName [])
                  <|> reserved "False" *> pure (PatCon falseName [])
                  <|> reserved "()" *> pure (PatCon litUnitName [])
                  <|> PatVar <$> wildcard
                  <|> do t <- varOrCon
                         case t of
                           (Var x) -> return $ PatVar x
                           (DCon c _ []) -> return $ PatCon c []
                           (TCon c _ []) -> fail "expected a data constructor but a type constructor was found"
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


sigmaTy :: LParser Term
sigmaTy = do
  reservedOp "{"
  x <- variable
  colon
  a <- expr
  reservedOp "|"
  b <- expr
  reservedOp "}"
  j <- lj
  return $ TCon sigmaName j [Arg Rel a, Arg Rel (Lam Rel (Unbound.bind x b))]

displaceTm :: LParser Term
displaceTm = do
  x <- variable
  reservedOp "^"
  l <- try (LConst <$> natural) <|> do
    lv <- Unbound.fresh (Unbound.string2Name "l")
    return (LVar lv)
  return $ Displace (Var x) l
