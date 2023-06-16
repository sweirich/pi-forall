----------------------------------------------------------------------------
-- THIS is a MODIFIED VERSION of Text.Parsec.Token
-- Modified to support layout combinators by Tim Sheard 7/27/09
-- Further updated to Parsec 3.1 by Vilhelm Sjoberg 2011-01-13
-- Find modified and added lines by searching for "--MOD"
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-do-bind -fno-warn-unused-matches #-}

-- |
-- Module      :  Text.Parsec.Token
-- Copyright   :  (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- License     :  BSD-style (see the LICENSE file)
--
-- Maintainer  :  derek.a.elkins@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (uses local universal quantification: PolymorphicComponents)
--
-- A helper module to parse lexical elements (tokens). See 'makeTokenParser'
-- for a description of how to use it.
module LayoutToken
  ( LanguageDef,
    GenLanguageDef (..),
    TokenParser,
    GenTokenParser (..),
    makeTokenParser,
    LayoutFun (..),
  )
where

import Control.Monad.Identity
import Data.Char (digitToInt, isAlpha, isSpace, toLower, toUpper)
import Data.Kind (Type)
import Data.List (nub, sort)
import Text.Parsec (Column, setSourceColumn, sourceColumn)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim

-----------------------------------------------------------
-- Language Definition
-----------------------------------------------------------

type LanguageDef st = GenLanguageDef String st Identity

-- | The @GenLanguageDef@ type is a record that contains all parameterizable
-- features of the 'Text.Parsec.Token' module. The module 'Text.Parsec.Language'
-- contains some default definitions.
data GenLanguageDef s u m = LanguageDef
  { -- | Describes the start of a block comment. Use the empty string if the
    -- language doesn't support block comments. For example \"\/*\".
    commentStart :: String,
    -- | Describes the end of a block comment. Use the empty string if the
    -- language doesn't support block comments. For example \"*\/\".
    commentEnd :: String,
    -- | Describes the start of a line comment. Use the empty string if the
    -- language doesn't support line comments. For example \"\/\/\".
    commentLine :: String,
    -- | Set to 'True' if the language supports nested block comments.
    nestedComments :: Bool,
    -- | This parser should accept any start characters of identifiers. For
    -- example @letter \<|> char \"_\"@.
    identStart :: ParsecT String [Column] m Char,
    -- | This parser should accept any legal tail characters of identifiers.
    -- For example @alphaNum \<|> char \"_\"@.
    identLetter :: ParsecT String [Column] m Char,
    -- | This parser should accept any start characters of operators. For
    -- example @oneOf \":!#$%&*+.\/\<=>?\@\\\\^|-~\"@
    opStart :: ParsecT String [Column] m Char,
    -- | This parser should accept any legal tail characters of operators.
    -- Note that this parser should even be defined if the language doesn't
    -- support user-defined operators, or otherwise the 'reservedOp'
    -- parser won't work correctly.
    opLetter :: ParsecT String [Column] m Char,
    -- | The list of reserved identifiers.
    reservedNames :: [String],
    -- | The list of reserved operators.
    reservedOpNames :: [String],
    -- | Set to 'True' if the language is case sensitive.
    caseSensitive :: Bool
  }

-----------------------------------------------------------
-- A first class module: TokenParser
-----------------------------------------------------------

type TokenParser st = GenTokenParser String st Identity

-- | The type of the record that holds lexical parsers that work on
-- @s@ streams with state @u@ over a monad @m@.
data GenTokenParser s u m = TokenParser
  { -- | This lexeme parser parses a legal identifier. Returns the identifier
    -- string. This parser will fail on identifiers that are reserved
    -- words. Legal identifier (start) characters and reserved words are
    -- defined in the 'LanguageDef' that is passed to
    -- 'makeTokenParser'. An @identifier@ is treated as
    -- a single token using 'try'.
    identifier :: ParsecT String [Column] m String,
    -- | The lexeme parser @reserved name@ parses @symbol
    -- name@, but it also checks that the @name@ is not a prefix of a
    -- valid identifier. A @reserved@ word is treated as a single token
    -- using 'try'.
    reserved :: String -> ParsecT String [Column] m (),
    -- | This lexeme parser parses a legal operator. Returns the name of the
    -- operator. This parser will fail on any operators that are reserved
    -- operators. Legal operator (start) characters and reserved operators
    -- are defined in the 'LanguageDef' that is passed to
    -- 'makeTokenParser'. An @operator@ is treated as a
    -- single token using 'try'.
    operator :: ParsecT String [Column] m String,
    -- | The lexeme parser @reservedOp name@ parses @symbol
    --  name@, but it also checks that the @name@ is not a prefix of a
    --  valid operator. A @reservedOp@ is treated as a single token using
    --  'try'.
    reservedOp :: String -> ParsecT String [Column] m (),
    -- | This lexeme parser parses a single literal character. Returns the
    -- literal character value. This parsers deals correctly with escape
    -- sequences. The literal character is parsed according to the grammar
    -- rules defined in the Haskell report (which matches most programming
    -- languages quite closely).
    charLiteral :: ParsecT String [Column] m Char,
    -- | This lexeme parser parses a literal string. Returns the literal
    -- string value. This parsers deals correctly with escape sequences and
    -- gaps. The literal string is parsed according to the grammar rules
    -- defined in the Haskell report (which matches most programming
    -- languages quite closely).
    stringLiteral :: ParsecT String [Column] m String,
    -- | This lexeme parser parses a natural number (a positive whole
    -- number). Returns the value of the number. The number can be
    -- specified in 'decimal', 'hexadecimal' or
    -- 'octal'. The number is parsed according to the grammar
    -- rules in the Haskell report.
    natural :: ParsecT String [Column] m Integer,
    -- | This lexeme parser parses an integer (a whole number). This parser
    -- is like 'natural' except that it can be prefixed with
    -- sign (i.e. \'-\' or \'+\'). Returns the value of the number. The
    -- number can be specified in 'decimal', 'hexadecimal'
    -- or 'octal'. The number is parsed according
    -- to the grammar rules in the Haskell report.
    integer :: ParsecT String [Column] m Integer,
    -- | This lexeme parser parses a floating point value. Returns the value
    -- of the number. The number is parsed according to the grammar rules
    -- defined in the Haskell report.
    float :: ParsecT String [Column] m Double,
    -- | This lexeme parser parses either 'natural' or a 'float'.
    -- Returns the value of the number. This parsers deals with
    -- any overlap in the grammar rules for naturals and floats. The number
    -- is parsed according to the grammar rules defined in the Haskell report.
    naturalOrFloat :: ParsecT String [Column] m (Either Integer Double),
    -- | Parses a positive whole number in the decimal system. Returns the
    -- value of the number.
    decimal :: ParsecT String [Column] m Integer,
    -- | Parses a positive whole number in the hexadecimal system. The number
    -- should be prefixed with \"0x\" or \"0X\". Returns the value of the
    -- number.
    hexadecimal :: ParsecT String [Column] m Integer,
    -- | Parses a positive whole number in the octal system. The number
    -- should be prefixed with \"0o\" or \"0O\". Returns the value of the
    -- number.
    octal :: ParsecT String [Column] m Integer,
    -- | Lexeme parser @symbol s@ parses 'string' @s@ and skips
    -- trailing white space.
    symbol :: String -> ParsecT String [Column] m String,
    -- | @lexeme p@ first applies parser @p@ and than the 'whiteSpace'
    -- parser, returning the value of @p@. Every lexical
    -- token (lexeme) is defined using @lexeme@, this way every parse
    -- starts at a point without white space. Parsers that use @lexeme@ are
    -- called /lexeme/ parsers in this document.
    --
    -- The only point where the 'whiteSpace' parser should be
    -- called explicitly is the start of the main parser in order to skip
    -- any leading white space.
    --
    -- >    mainParser  = do{ whiteSpace
    -- >                     ; ds <- many (lexeme digit)
    -- >                     ; eof
    -- >                     ; return (sum ds)
    -- >                     }
    lexeme :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m a,
    -- | Parses any white space. White space consists of /zero/ or more
    -- occurrences of a 'space', a line comment or a block (multi
    -- line) comment. Block comments may be nested. How comments are
    -- started and ended is defined in the 'LanguageDef'
    -- that is passed to 'makeTokenParser'.
    whiteSpace :: ParsecT String [Column] m (),
    -- | Lexeme parser @parens p@ parses @p@ enclosed in parenthesis,
    -- returning the value of @p@.
    parens :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m a,
    -- | Lexeme parser @braces p@ parses @p@ enclosed in braces (\'{\' and
    -- \'}\'), returning the value of @p@.
    braces :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m a,
    -- | Lexeme parser @angles p@ parses @p@ enclosed in angle brackets (\'\<\'
    -- and \'>\'), returning the value of @p@.
    angles :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m a,
    -- | Lexeme parser @brackets p@ parses @p@ enclosed in brackets (\'[\'
    -- and \']\'), returning the value of @p@.
    brackets :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m a,
    -- | DEPRECATED: Use 'brackets'.
    squares :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m a,
    -- | Lexeme parser |semi| parses the character \';\' and skips any
    -- trailing white space. Returns the string \";\".
    semi :: ParsecT String [Column] m String,
    -- | Lexeme parser @comma@ parses the character \',\' and skips any
    -- trailing white space. Returns the string \",\".
    comma :: ParsecT String [Column] m String,
    -- | Lexeme parser @colon@ parses the character \':\' and skips any
    -- trailing white space. Returns the string \":\".
    colon :: ParsecT String [Column] m String,
    -- | Lexeme parser @dot@ parses the character \'.\' and skips any
    -- trailing white space. Returns the string \".\".
    dot :: ParsecT String [Column] m String,
    -- | Lexeme parser @semiSep p@ parses /zero/ or more occurrences of @p@
    -- separated by 'semi'. Returns a list of values returned by
    -- @p@.
    semiSep :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m [a],
    -- | Lexeme parser @semiSep1 p@ parses /one/ or more occurrences of @p@
    -- separated by 'semi'. Returns a list of values returned by @p@.
    semiSep1 :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m [a],
    -- | Lexeme parser @commaSep p@ parses /zero/ or more occurrences of
    -- @p@ separated by 'comma'. Returns a list of values returned
    -- by @p@.
    commaSep :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m [a],
    -- | Lexeme parser @commaSep1 p@ parses /one/ or more occurrences of
    -- @p@ separated by 'comma'. Returns a list of values returned
    -- by @p@.
    commaSep1 :: forall a. ParsecT String [Column] m a -> ParsecT String [Column] m [a]
  }

-----------------------------------------------------------
-- Given a LanguageDef, create a token parser.
-----------------------------------------------------------

-- | The expression @makeTokenParser language@ creates a 'GenTokenParser'
-- record that contains lexical parsers that are
-- defined using the definitions in the @language@ record.
--
-- The use of this function is quite stylized - one imports the
-- appropiate language definition and selects the lexical parsers that
-- are needed from the resulting 'GenTokenParser'.
--
-- >  module Main where
-- >
-- >  import Text.Parsec
-- >  import qualified Text.Parsec.Token as P
-- >  import Text.Parsec.Language (haskellDef)
-- >
-- >  -- The parser
-- >  ...
-- >
-- >  expr  =   parens expr
-- >        <|> identifier
-- >        <|> ...
-- >
-- >
-- >  -- The lexer
-- >  lexer       = P.makeTokenParser haskellDef
-- >
-- >  parens      = P.parens lexer
-- >  braces      = P.braces lexer
-- >  identifier  = P.identifier lexer
-- >  reserved    = P.reserved lexer
-- >  ...
makeTokenParser ::
  Monad m =>
  GenLanguageDef String [Column] m ->
  String ->
  String ->
  String ->
  (GenTokenParser String [Column] m, LayoutFun String m)
{-# INLINEABLE makeTokenParser #-}
-- MOD: add parameters open,sep,close.
-- MOD: specialize to
makeTokenParser languageDef open sep close =
  ( TokenParser
      { identifier = identifier,
        reserved = reserved,
        operator = operator,
        reservedOp = reservedOp,
        charLiteral = charLiteral,
        stringLiteral = stringLiteral,
        natural = natural,
        integer = integer,
        float = float,
        naturalOrFloat = naturalOrFloat,
        decimal = decimal,
        hexadecimal = hexadecimal,
        octal = octal,
        symbol = symbol,
        lexeme = lexeme,
        whiteSpace = whiteSpace,
        parens = parens,
        braces = braces,
        angles = angles,
        brackets = brackets,
        squares = brackets,
        semi = semi,
        comma = comma,
        colon = colon,
        dot = dot,
        semiSep = semiSep,
        semiSep1 = semiSep1,
        commaSep = commaSep,
        commaSep1 = commaSep1
      }, --MOD also return the layout combinator!
    LayFun layout
  )
  where
    -----------------------------------------------------------
    -- Bracketing
    -----------------------------------------------------------
    parens,
      braces,
      angles,
      brackets ::
        Monad m =>
        ParsecT String [Column] m a ->
        ParsecT String [Column] m a
    parens p = between (symbol "(") (symbol ")") p
    braces p = between (symbol "{") (symbol "}") p
    angles p = between (symbol "<") (symbol ">") p
    brackets p = between (symbol "[") (symbol "]") p

    comma, semi :: (Monad m) => ParsecT String [Column] m String
    semi = symbol ";"
    comma = symbol ","
    dot = symbol "."
    colon = symbol ":"

    commaSep, semiSep :: Monad m => ParsecT String [Column] m a -> ParsecT String [Column] m [a]
    commaSep p = sepBy p comma
    semiSep p = sepBy p semi

    commaSep1 p = sepBy1 p comma
    semiSep1 p = sepBy1 p semi

    -----------------------------------------------------------
    -- Chars & Strings
    -----------------------------------------------------------
    charLiteral =
      lexeme
        ( between
            (char '\'')
            (char '\'' <?> "end of character")
            characterChar
        )
        <?> "character"

    characterChar =
      charLetter <|> charEscape
        <?> "literal character"

    charEscape = do _ <- char '\\'; escapeCode
    charLetter = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))

    stringLiteral =
      lexeme
        ( do
            str <-
              between
                (char '"')
                (char '"' <?> "end of string")
                (many stringChar)
            return (foldr (maybe id (:)) "" str)
            <?> "literal string"
        )

    stringChar =
      do c <- stringLetter; return (Just c)
        <|> stringEscape
        <?> "string character"

    stringLetter = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

    stringEscape = do
      _ <- char '\\'
      do _ <- escapeGap; return Nothing
        <|> do _ <- escapeEmpty; return Nothing
        <|> do esc <- escapeCode; return (Just esc)

    escapeEmpty = char '&'
    escapeGap = do
      _ <- many1 space
      char '\\' <?> "end of string gap"

    -- escape codes
    escapeCode =
      charEsc <|> charNum <|> charAscii <|> charControl
        <?> "escape code"

    charControl = do
      _ <- char '^'
      code <- upper
      return (toEnum (fromEnum code - fromEnum 'A'))

    charNum = do
      code <-
        decimal
          <|> do _ <- char 'o'; number 8 octDigit
          <|> do _ <- char 'x'; number 16 hexDigit
      if code > 0x10FFFF
        then fail "invalid escape sequence"
        else return (toEnum (fromInteger code))

    charEsc = choice (map parseEsc escMap)
      where
        parseEsc (c, code) = do _ <- char c; return code

    charAscii = choice (map parseAscii asciiMap)
      where
        parseAscii (asc, code) = try (do _ <- string asc; return code)

    -- escape code tables
    escMap = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
    asciiMap = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

    ascii2codes =
      [ "BS",
        "HT",
        "LF",
        "VT",
        "FF",
        "CR",
        "SO",
        "SI",
        "EM",
        "FS",
        "GS",
        "RS",
        "US",
        "SP"
      ]
    ascii3codes =
      [ "NUL",
        "SOH",
        "STX",
        "ETX",
        "EOT",
        "ENQ",
        "ACK",
        "BEL",
        "DLE",
        "DC1",
        "DC2",
        "DC3",
        "DC4",
        "NAK",
        "SYN",
        "ETB",
        "CAN",
        "SUB",
        "ESC",
        "DEL"
      ]

    ascii2 =
      [ '\BS',
        '\HT',
        '\LF',
        '\VT',
        '\FF',
        '\CR',
        '\SO',
        '\SI',
        '\EM',
        '\FS',
        '\GS',
        '\RS',
        '\US',
        '\SP'
      ]
    ascii3 =
      [ '\NUL',
        '\SOH',
        '\STX',
        '\ETX',
        '\EOT',
        '\ENQ',
        '\ACK',
        '\BEL',
        '\DLE',
        '\DC1',
        '\DC2',
        '\DC3',
        '\DC4',
        '\NAK',
        '\SYN',
        '\ETB',
        '\CAN',
        '\SUB',
        '\ESC',
        '\DEL'
      ]

    -----------------------------------------------------------
    -- Numbers
    -----------------------------------------------------------
    naturalOrFloat = lexeme (natFloat) <?> "number"

    float = lexeme floating <?> "float"
    integer = lexeme int <?> "integer"
    natural = lexeme nat <?> "natural"

    -- floats
    floating = do
      n <- decimal
      fractExponent n

    natFloat =
      do
        _ <- char '0'
        zeroNumFloat
        <|> decimalFloat

    zeroNumFloat =
      do
        n <- hexadecimal <|> octal
        return (Left n)
        <|> decimalFloat
        <|> fractFloat (0 :: Integer)
        <|> return (Left 0)

    decimalFloat = do
      n <- decimal
      option
        (Left n)
        (fractFloat n)

    fractFloat n = do
      f <- fractExponent n
      return (Right f)

    fractExponent n =
      do
        fract <- fraction
        expo <- option "" exponent'
        readDouble (show n ++ fract ++ expo)
        <|> do
          expo <- exponent'
          readDouble (show n ++ expo)
      where
        readDouble s =
          case reads s of
            [(x, "")] -> return x
            _ -> parserZero

    fraction =
      do
        _ <- char '.'
        digits <- many1 digit <?> "fraction"
        return ('.' : digits)
        <?> "fraction"

    exponent' =
      do
        _ <- oneOf "eE"
        sign' <- fmap (: []) (oneOf "+-") <|> return ""
        e <- decimal <?> "exponent"
        return ('e' : sign' ++ show e)
        <?> "exponent"

    -- integers and naturals
    int = do
      f <- lexeme sign
      n <- nat
      return (f n)

    sign =
      (char '-' >> return negate)
        <|> (char '+' >> return id)
        <|> return id

    nat = zeroNumber <|> decimal

    zeroNumber =
      do
        _ <- char '0'
        hexadecimal <|> octal <|> decimal <|> return 0
        <?> ""

    decimal = number 10 digit
    hexadecimal = do _ <- oneOf "xX"; number 16 hexDigit
    octal = do _ <- oneOf "oO"; number 8 octDigit

    number base baseDigit =
      do
        digits <- many1 baseDigit
        let n = foldl (\x d -> base * x + toInteger (digitToInt d)) 0 digits
        seq n (return n)

    -----------------------------------------------------------
    -- Operators & reserved ops
    -----------------------------------------------------------
    reservedOp name =
      lexeme $
        try $
          do
            _ <- string name
            notFollowedBy (opLetter languageDef) <?> ("end of " ++ show name)

    operator =
      lexeme $
        try $
          do
            name <- oper
            if (isReservedOp name)
              then unexpected ("reserved operator " ++ show name)
              else return name

    oper =
      do
        c <- (opStart languageDef)
        cs <- many (opLetter languageDef)
        return (c : cs)
        <?> "operator"

    isReservedOp name =
      isReserved (sort (reservedOpNames languageDef)) name

    -----------------------------------------------------------
    -- Identifiers & Reserved words
    -----------------------------------------------------------
    reserved name =
      lexeme $
        try $
          do
            _ <- caseString name
            notFollowedBy (identLetter languageDef) <?> ("end of " ++ show name)

    caseString name
      | caseSensitive languageDef = string name
      | otherwise = do walk name; return name
      where
        walk [] = return ()
        walk (c : cs) = do _ <- caseChar c <?> msg; walk cs

        caseChar c
          | isAlpha c = char (toLower c) <|> char (toUpper c)
          | otherwise = char c

        msg = show name

    identifier =
      lexeme $
        try $
          do
            name <- ident
            if (isReservedName name)
              then unexpected ("reserved word " ++ show name)
              else return name

    ident =
      do
        c <- identStart languageDef
        cs <- many (identLetter languageDef)
        return (c : cs)
        <?> "identifier"

    isReservedName name =
      isReserved theReservedNames caseName
      where
        caseName
          | caseSensitive languageDef = name
          | otherwise = map toLower name

    isReserved names name =
      scan names
      where
        scan [] = False
        scan (r : rs) = case (compare r name) of
          LT -> scan rs
          EQ -> True
          GT -> False

    theReservedNames
      | caseSensitive languageDef = sort reserved
      | otherwise = sort . map (map toLower) $ reserved
      where
        reserved = reservedNames languageDef

    -----------------------------------------------------------
    -- White space & symbols
    -----------------------------------------------------------
    symbol :: (Monad m) => String -> ParsecT String [Column] m String
    symbol name =
      lexeme (string name)

    lexeme p =
      do x <- p; whiteSpace; return x

    --whiteSpace
    -- MOD: this function renamed from whiteSpace to ws, and changed to return the matched string.
    ws :: forall (m :: Type -> Type). (Monad m) => ParsecT String [Column] m [String]
    ws
      | noLine && noMulti = many (simpleSpace <?> "")
      | noLine = many (simpleSpace <|> multiLineComment <?> "")
      | noMulti = many (simpleSpace <|> oneLineComment <?> "")
      | otherwise = many (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
      where
        noLine = null (commentLine languageDef)
        noMulti = null (commentStart languageDef)

    --simpleSpace = skipMany1 (eoln ws <|> satisfy isSpace)
    --MOD  simpleSpace WAS MODIFIED FOR LAYOUT TOKEN PARSERS by Tim Sheard 7/27/09
    simpleSpace :: (Monad m) => ParsecT String [Column] m String
    simpleSpace =
      many1 (satisfy isSpace)

    -- MOD return matched string
    oneLineComment :: (Monad m) => ParsecT String [Column] m String
    oneLineComment =
      do
        xs <- try (string (commentLine languageDef))
        ys <- many (satisfy (/= '\n'))
        return (xs ++ ys)

    -- MOD: return matched string
    multiLineComment :: (Monad m) => ParsecT String [Column] m String
    multiLineComment =
      do
        xs <- try (string (commentStart languageDef))
        ys <- inComment
        return (xs ++ ys)

    inComment :: (Monad m) => ParsecT String [Column] m String
    inComment
      | nestedComments languageDef = inCommentMulti
      | otherwise = inCommentSingle

    -- MOD: return matched string
    inCommentMulti :: (Monad m) => ParsecT String [Column] m String
    inCommentMulti =
      do xs <- try (string (commentEnd languageDef)); return xs
        <|> do xs <- multiLineComment; ys <- inCommentMulti; return (xs ++ ys)
        <|> do xs <- many1 (noneOf startEnd); ys <- inCommentMulti; return (xs ++ ys)
        <|> do y <- oneOf startEnd; ys <- inCommentMulti; return (y : ys)
        <?> "end of comment"
      where
        startEnd = nub (commentEnd languageDef ++ commentStart languageDef)

    inCommentSingle :: (Monad m) => ParsecT String [Column] m String
    inCommentSingle =
      do xs <- try (string (commentEnd languageDef)); return xs
        <|> do xs <- many1 (noneOf startEnd); ys <- inCommentSingle; return (xs ++ ys)
        <|> do y <- oneOf startEnd; ys <- inCommentSingle; return (y : ys)
        <?> "end of comment"
      where
        startEnd = nub (commentEnd languageDef ++ commentStart languageDef)

    --MOD --------------------------------------------------------------------
    -- THE FOLLOWING WAS ADDED FOR LAYOUT TOKEN PARSERS by Tim Sheard 7/27/09

    layoutSep, layoutEnd, layoutBegin :: (Monad m) => ParsecT String [Column] m String
    layoutSep = (symbol sep) <?> ("inserted layout separator (" ++ sep ++ ")")
    layoutEnd = (symbol close) <?> ("inserted layout closing symbol(" ++ close ++ ")")
    layoutBegin = (symbol open) <?> ("layout opening symbol (" ++ open ++ ")")

    layout ::
      forall m a t.
      (Monad m) =>
      ParsecT String [Column] m a ->
      ParsecT String [Column] m t ->
      ParsecT String [Column] m [a]
    layout p stop =
      ( do
          try layoutBegin
          xs <- sepBy p (symbol ";")
          layoutEnd <?> "explicit layout closing brace"
          stop
          return (xs)
      )
        <|> (do indent; xs <- align p stop; return xs)

    align p stop = ormore <|> zero
      where
        zero = do stop; option "" layoutSep; undent; return []
        ormore = do
          x <- p
          whiteSpace
          (do try layoutSep; xs <- align p stop; return (x : xs))
            <|> (do try layoutEnd; stop; return ([x]))
            <|>
            -- removing indentation happens automatically
            -- in function whiteSpace
            (do stop; undent; return ([x]))

    whiteSpace :: forall m. (Monad m) => ParsecT String [Column] m ()
    whiteSpace =
      do
        (col1, _, _) <- getInfo
        wsChars <- ws
        (col2, tabs, more) <- getInfo
        case (wsChars, tabs, more, compare col2 col1) of
          ([], _, _, _) -> return ()
          (_, [], _, _) -> return ()
          (_, _, [], _) ->
            -- No more input, close all the pending layout with '}'
            setInfo (col2, [], concat (map (const close) tabs))
          (cs, p : ps, _, EQ) -> setInfo (col2 -1, tabs, sep ++ more)
          (cs, p : ps, _, LT) ->
            let adjust (col, [], add) = setInfo (col, [], rev add more)
                adjust (col, p : ps, add)
                  | col2 < p = adjust (col -1, ps, close : add)
                  | col2 == p = setInfo (col -1, p : ps, rev (sep : add) more)
                  | col2 > p = setInfo (col, p : ps, rev add more)
                  | True = error "impossible"
                rev [] xs = xs
                rev (s : ss) xs = rev ss (s ++ xs)
             in adjust (col2, p : ps, [])
          (cs, p : ps, _, GT) -> return ()

getInfo ::
  forall (m :: Type -> Type) t t1.
  Monad m =>
  ParsecT t1 t m (Column, t, t1)
getInfo =
  do
    pos <- getPosition
    tabs <- getState
    tokens <- getInput
    return (sourceColumn pos, tabs, tokens)

setInfo ::
  forall (m :: Type -> Type).
  Monad m =>
  (Column, [Column], String) ->
  ParsecT String [Column] m ()
setInfo (col, tabs, tokens) =
  do
    p <- getPosition
    setPosition (setSourceColumn p col)
    setState tabs
    setInput tokens

indent ::
  forall (m :: Type -> Type).
  Monad m =>
  ParsecT String [Column] m ()
indent =
  do
    pos <- getPosition
    tabs <- getState
    setState (sourceColumn pos : tabs)

undent :: forall (m :: Type -> Type) t. Monad m => ParsecT String [t] m ()
undent =
  do
    (p : ps) <- getState
    setState ps

_eoln ::
  forall (m :: Type -> Type) a.
  Monad m =>
  ParsecT [Char] [Column] m a ->
  ParsecT [Char] [Column] m Char
_eoln whiteSpace =
  do
    c <- satisfy (== '\n') -- c == '\n' to succeed
    (col, tabs@(p : ps), input) <- getInfo
    whiteSpace -- this may screw up the tabs,
    -- but use the old tabs, but the
    -- new column (col2) and input (cs)
    (col2, _, cs) <- getInfo
    case cs of
      [] ->
        -- No more input, close all the pending layout with '}'
        setInfo (col2, [], map (const '}') tabs)
      _ -> case compare col2 p of
        EQ -> setInfo (col2 -1, tabs, ';' : cs)
        GT -> setInfo (col2, tabs, cs)
        LT ->
          let adjust prefix cs column [] = setInfo (column, [], rev prefix cs)
              adjust prefix cs column (tabs@(p : ps))
                | col2 == p = setInfo (column -1, tabs, rev (';' : prefix) cs)
                | col2 < p = adjust ('}' : prefix) cs (column - 1) ps
                | col2 > p = setInfo (column, tabs, rev prefix cs)
                | True = error "impossible"
              rev [] ys = ys
              rev (x : xs) ys = rev xs (x : ys)
           in adjust [] cs col2 tabs
    return '\n'

data LayoutFun s m
  = LayFun
      ( forall a t.
        (Monad m) =>
        ParsecT String [Column] m a ->
        ParsecT String [Column] m t ->
        ParsecT String [Column] m [a]
      )

-- End of added code
--MOD --------------------------------------------------------------------
