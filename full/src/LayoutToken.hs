----------------------------------------------------------------------------
-- THIS is a MODIFIED VERSION of Text.Parsec.Token
-- Modified to support layout combinators by Tim Sheard 7/27/09
-- Further updated to Parsec 3.1 by Vilhelm Sjoberg 2011-01-13
-- Find modified and added lines by searching for "--MOD"

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
-- 
-----------------------------------------------------------------------------

{-# LANGUAGE PolymorphicComponents, NoMonomorphismRestriction, KindSignatures  #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-do-bind -fno-warn-unused-matches #-}

module LayoutToken
    ( LanguageDef
    , GenLanguageDef (..)
    , TokenParser
    , GenTokenParser (..)
    , makeTokenParser
    , LayoutFun (..)
    ) where

import Data.Char ( isAlpha, toLower, toUpper, isSpace, digitToInt )
import Data.List ( nub, sort )
import Control.Monad.Identity
import Text.Parsec (Column,sourceColumn, setSourceColumn)
import Text.Parsec.Prim
import Text.Parsec.Char
import Text.Parsec.Combinator

-----------------------------------------------------------
-- Language Definition
-----------------------------------------------------------

type LanguageDef st = GenLanguageDef String st Identity

-- | The @GenLanguageDef@ type is a record that contains all parameterizable
-- features of the 'Text.Parsec.Token' module. The module 'Text.Parsec.Language'
-- contains some default definitions.

data GenLanguageDef s u m
    = LanguageDef { 
    
    -- | Describes the start of a block comment. Use the empty string if the
    -- language doesn't support block comments. For example \"\/*\". 

    commentStart   :: String,

    -- | Describes the end of a block comment. Use the empty string if the
    -- language doesn't support block comments. For example \"*\/\". 

    commentEnd     :: String,

    -- | Describes the start of a line comment. Use the empty string if the
    -- language doesn't support line comments. For example \"\/\/\". 

    commentLine    :: String,

    -- | Set to 'True' if the language supports nested block comments. 

    nestedComments :: Bool,

    -- | This parser should accept any start characters of identifiers. For
    -- example @letter \<|> char \"_\"@. 

    identStart     :: ParsecT s u m Char,

    -- | This parser should accept any legal tail characters of identifiers.
    -- For example @alphaNum \<|> char \"_\"@. 

    identLetter    :: ParsecT s u m Char,

    -- | This parser should accept any start characters of operators. For
    -- example @oneOf \":!#$%&*+.\/\<=>?\@\\\\^|-~\"@ 

    opStart        :: ParsecT s u m Char,

    -- | This parser should accept any legal tail characters of operators.
    -- Note that this parser should even be defined if the language doesn't
    -- support user-defined operators, or otherwise the 'reservedOp'
    -- parser won't work correctly. 

    opLetter       :: ParsecT s u m Char,

    -- | The list of reserved identifiers. 

    reservedNames  :: [String],

    -- | The list of reserved operators. 

    reservedOpNames:: [String],

    -- | Set to 'True' if the language is case sensitive. 

    caseSensitive  :: Bool

    }

-----------------------------------------------------------
-- A first class module: TokenParser
-----------------------------------------------------------

type TokenParser st = GenTokenParser String st Identity

-- | The type of the record that holds lexical parsers that work on
-- @s@ streams with state @u@ over a monad @m@.

data GenTokenParser s u m
    = TokenParser {

        -- | This lexeme parser parses a legal identifier. Returns the identifier
        -- string. This parser will fail on identifiers that are reserved
        -- words. Legal identifier (start) characters and reserved words are
        -- defined in the 'LanguageDef' that is passed to
        -- 'makeTokenParser'. An @identifier@ is treated as
        -- a single token using 'try'.

        identifier       :: ParsecT s u m String,
        
        -- | The lexeme parser @reserved name@ parses @symbol 
        -- name@, but it also checks that the @name@ is not a prefix of a
        -- valid identifier. A @reserved@ word is treated as a single token
        -- using 'try'. 

        reserved         :: String -> ParsecT s u m (),

        -- | This lexeme parser parses a legal operator. Returns the name of the
        -- operator. This parser will fail on any operators that are reserved
        -- operators. Legal operator (start) characters and reserved operators
        -- are defined in the 'LanguageDef' that is passed to
        -- 'makeTokenParser'. An @operator@ is treated as a
        -- single token using 'try'. 

        operator         :: ParsecT s u m String,

        -- |The lexeme parser @reservedOp name@ parses @symbol
        -- name@, but it also checks that the @name@ is not a prefix of a
        -- valid operator. A @reservedOp@ is treated as a single token using
        -- 'try'. 

        reservedOp       :: String -> ParsecT s u m (),


        -- | This lexeme parser parses a single literal character. Returns the
        -- literal character value. This parsers deals correctly with escape
        -- sequences. The literal character is parsed according to the grammar
        -- rules defined in the Haskell report (which matches most programming
        -- languages quite closely). 

        charLiteral      :: ParsecT s u m Char,

        -- | This lexeme parser parses a literal string. Returns the literal
        -- string value. This parsers deals correctly with escape sequences and
        -- gaps. The literal string is parsed according to the grammar rules
        -- defined in the Haskell report (which matches most programming
        -- languages quite closely). 

        stringLiteral    :: ParsecT s u m String,

        -- | This lexeme parser parses a natural number (a positive whole
        -- number). Returns the value of the number. The number can be
        -- specified in 'decimal', 'hexadecimal' or
        -- 'octal'. The number is parsed according to the grammar
        -- rules in the Haskell report. 

        natural          :: ParsecT s u m Integer,

        -- | This lexeme parser parses an integer (a whole number). This parser
        -- is like 'natural' except that it can be prefixed with
        -- sign (i.e. \'-\' or \'+\'). Returns the value of the number. The
        -- number can be specified in 'decimal', 'hexadecimal'
        -- or 'octal'. The number is parsed according
        -- to the grammar rules in the Haskell report. 
        
        integer          :: ParsecT s u m Integer,

        -- | This lexeme parser parses a floating point value. Returns the value
        -- of the number. The number is parsed according to the grammar rules
        -- defined in the Haskell report. 

        float            :: ParsecT s u m Double,

        -- | This lexeme parser parses either 'natural' or a 'float'.
        -- Returns the value of the number. This parsers deals with
        -- any overlap in the grammar rules for naturals and floats. The number
        -- is parsed according to the grammar rules defined in the Haskell report. 

        naturalOrFloat   :: ParsecT s u m (Either Integer Double),

        -- | Parses a positive whole number in the decimal system. Returns the
        -- value of the number. 

        decimal          :: ParsecT s u m Integer,

        -- | Parses a positive whole number in the hexadecimal system. The number
        -- should be prefixed with \"0x\" or \"0X\". Returns the value of the
        -- number. 

        hexadecimal      :: ParsecT s u m Integer,

        -- | Parses a positive whole number in the octal system. The number
        -- should be prefixed with \"0o\" or \"0O\". Returns the value of the
        -- number. 

        octal            :: ParsecT s u m Integer,

        -- | Lexeme parser @symbol s@ parses 'string' @s@ and skips
        -- trailing white space. 

        symbol           :: String -> ParsecT s u m String,

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

        lexeme           :: forall a. ParsecT s u m a -> ParsecT s u m a,

        -- | Parses any white space. White space consists of /zero/ or more
        -- occurrences of a 'space', a line comment or a block (multi
        -- line) comment. Block comments may be nested. How comments are
        -- started and ended is defined in the 'LanguageDef'
        -- that is passed to 'makeTokenParser'. 

        whiteSpace       :: ParsecT s u m (),

        -- | Lexeme parser @parens p@ parses @p@ enclosed in parenthesis,
        -- returning the value of @p@.

        parens           :: forall a. ParsecT s u m a -> ParsecT s u m a,

        -- | Lexeme parser @braces p@ parses @p@ enclosed in braces (\'{\' and
        -- \'}\'), returning the value of @p@. 

        braces           :: forall a. ParsecT s u m a -> ParsecT s u m a,

        -- | Lexeme parser @angles p@ parses @p@ enclosed in angle brackets (\'\<\'
        -- and \'>\'), returning the value of @p@. 

        angles           :: forall a. ParsecT s u m a -> ParsecT s u m a,

        -- | Lexeme parser @brackets p@ parses @p@ enclosed in brackets (\'[\'
        -- and \']\'), returning the value of @p@. 

        brackets         :: forall a. ParsecT s u m a -> ParsecT s u m a,

        -- | DEPRECATED: Use 'brackets'.

        squares          :: forall a. ParsecT s u m a -> ParsecT s u m a,

        -- | Lexeme parser |semi| parses the character \';\' and skips any
        -- trailing white space. Returns the string \";\". 

        semi             :: ParsecT s u m String,

        -- | Lexeme parser @comma@ parses the character \',\' and skips any
        -- trailing white space. Returns the string \",\". 

        comma            :: ParsecT s u m String,

        -- | Lexeme parser @colon@ parses the character \':\' and skips any
        -- trailing white space. Returns the string \":\". 

        colon            :: ParsecT s u m String,

        -- | Lexeme parser @dot@ parses the character \'.\' and skips any
        -- trailing white space. Returns the string \".\". 

        dot              :: ParsecT s u m String,

        -- | Lexeme parser @semiSep p@ parses /zero/ or more occurrences of @p@
        -- separated by 'semi'. Returns a list of values returned by
        -- @p@.

        semiSep          :: forall a . ParsecT s u m a -> ParsecT s u m [a],

        -- | Lexeme parser @semiSep1 p@ parses /one/ or more occurrences of @p@
        -- separated by 'semi'. Returns a list of values returned by @p@. 

        semiSep1         :: forall a . ParsecT s u m a -> ParsecT s u m [a],

        -- | Lexeme parser @commaSep p@ parses /zero/ or more occurrences of
        -- @p@ separated by 'comma'. Returns a list of values returned
        -- by @p@. 

        commaSep         :: forall a . ParsecT s u m a -> ParsecT s u m [a],

        -- | Lexeme parser @commaSep1 p@ parses /one/ or more occurrences of
        -- @p@ separated by 'comma'. Returns a list of values returned
        -- by @p@. 

        commaSep1        :: forall a . ParsecT s u m a -> ParsecT s u m [a]
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

makeTokenParser :: (Monad m) => GenLanguageDef String [Column] m -> String -> String -> String 
                   -> (GenTokenParser String [Column] m, LayoutFun String m)
-- MOD: add parameters open,sep,close.
makeTokenParser languageDef open sep close
    =(TokenParser{ identifier = identifier
                 , reserved = reserved
                 , operator = operator
                 , reservedOp = reservedOp

                 , charLiteral = charLiteral
                 , stringLiteral = stringLiteral
                 , natural = natural
                 , integer = integer
                 , float = float
                 , naturalOrFloat = naturalOrFloat
                 , decimal = decimal
                 , hexadecimal = hexadecimal
                 , octal = octal

                 , symbol = symbol
                 , lexeme = lexeme
                 , whiteSpace = whiteSpace

                 , parens = parens
                 , braces = braces
                 , angles = angles
                 , brackets = brackets
                 , squares = brackets
                 , semi = semi
                 , comma = comma
                 , colon = colon
                 , dot = dot
                 , semiSep = semiSep
                 , semiSep1 = semiSep1
                 , commaSep = commaSep
                 , commaSep1 = commaSep1
                 }--MOD also return the layout combinator!
     ,LayFun layout)
    where

    -----------------------------------------------------------
    -- Bracketing
    -----------------------------------------------------------
    parens p        = between (symbol "(") (symbol ")") p
    braces p        = between (symbol "{") (symbol "}") p
    angles p        = between (symbol "<") (symbol ">") p
    brackets p      = between (symbol "[") (symbol "]") p

    semi            = symbol ";"
    comma           = symbol ","
    dot             = symbol "."
    colon           = symbol ":"

    commaSep p      = sepBy p comma
    semiSep p       = sepBy p semi

    commaSep1 p     = sepBy1 p comma
    semiSep1 p      = sepBy1 p semi


    -----------------------------------------------------------
    -- Chars & Strings
    -----------------------------------------------------------
    charLiteral     = lexeme (between (char '\'')
                                      (char '\'' <?> "end of character")
                                      characterChar )
                    <?> "character"

    characterChar   = charLetter <|> charEscape
                    <?> "literal character"

    charEscape      = do{ char '\\'; escapeCode }
    charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



    stringLiteral   = lexeme (
                      do{ str <- between (char '"')
                                         (char '"' <?> "end of string")
                                         (many stringChar)
                        ; return (foldr (maybe id (:)) "" str)
                        }
                      <?> "literal string")

    stringChar      =   do{ c <- stringLetter; return (Just c) }
                    <|> stringEscape
                    <?> "string character"

    stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

    stringEscape    = do{ char '\\'
                        ;     do{ escapeGap  ; return Nothing }
                          <|> do{ escapeEmpty; return Nothing }
                          <|> do{ esc <- escapeCode; return (Just esc) }
                        }

    escapeEmpty     = char '&'
    escapeGap       = do{ many1 space
                        ; char '\\' <?> "end of string gap"
                        }



    -- escape codes
    escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                    <?> "escape code"

    charControl     = do{ char '^'
                        ; code <- upper
                        ; return (toEnum (fromEnum code - fromEnum 'A'))
                        }

    charNum         = do{ code <- decimal
                                  <|> do{ char 'o'; number 8 octDigit }
                                  <|> do{ char 'x'; number 16 hexDigit }
                        ; return (toEnum (fromInteger code))
                        }

    charEsc         = choice (map parseEsc escMap)
                    where
                      parseEsc (c,code)     = do{ char c; return code }

    charAscii       = choice (map parseAscii asciiMap)
                    where
                      parseAscii (asc,code) = try (do{ string asc; return code })


    -- escape code tables
    escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
    asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

    ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                       "FS","GS","RS","US","SP"]
    ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                       "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                       "CAN","SUB","ESC","DEL"]

    ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                       '\EM','\FS','\GS','\RS','\US','\SP']
    ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                       '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                       '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']


    -----------------------------------------------------------
    -- Numbers
    -----------------------------------------------------------
    naturalOrFloat  = lexeme (natFloat) <?> "number"

    float           = lexeme floating   <?> "float"
    integer         = lexeme int        <?> "integer"
    natural         = lexeme nat        <?> "natural"


    -- floats
    floating        = do{ n <- decimal
                        ; fractExponent n
                        }


    natFloat        = do{ char '0'
                        ; zeroNumFloat
                        }
                      <|> decimalFloat

    zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                         ; return (Left n)
                         }
                    <|> decimalFloat
                    <|> fractFloat 0
                    <|> return (Left 0)

    decimalFloat    = do{ n <- decimal
                        ; option (Left n)
                                 (fractFloat n)
                        }

    fractFloat n    = do{ f <- fractExponent n
                        ; return (Right f)
                        }

    fractExponent n = do{ fract <- fraction
                        ; expo  <- option 1.0 exponent'
                        ; return ((fromInteger n + fract)*expo)
                        }
                    <|>
                      do{ expo <- exponent'
                        ; return ((fromInteger n)*expo)
                        }

    fraction        = do{ char '.'
                        ; digits <- many1 digit <?> "fraction"
                        ; return (foldr op 0.0 digits)
                        }
                      <?> "fraction"
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10.0

    exponent'       = do{ oneOf "eE"
                        ; f <- sign
                        ; e <- decimal <?> "exponent"
                        ; return (power (f e))
                        }
                      <?> "exponent"
                    where
                       power e  | e < 0      = 1.0/power(-e)
                                | otherwise  = fromInteger (10^e)


    -- integers and naturals
    int             = do{ f <- lexeme sign
                        ; n <- nat
                        ; return (f n)
                        }

    sign            =   (char '-' >> return negate)
                    <|> (char '+' >> return id)
                    <|> return id

    nat             = zeroNumber <|> decimal

    zeroNumber      = do{ char '0'
                        ; hexadecimal <|> octal <|> decimal <|> return 0
                        }
                      <?> ""

    decimal         = number 10 digit
    hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
    octal           = do{ oneOf "oO"; number 8 octDigit  }

    number base baseDigit
        = do{ digits <- many1 baseDigit
            ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
            ; seq n (return n)
            }

    -----------------------------------------------------------
    -- Operators & reserved ops
    -----------------------------------------------------------
    reservedOp name =
        lexeme $ try $
        do{ string name
          ; notFollowedBy (opLetter languageDef) <?> ("end of " ++ show name)
          }

    operator =
        lexeme $ try $
        do{ name <- oper
          ; if (isReservedOp name)
             then unexpected ("reserved operator " ++ show name)
             else return name
          }

    oper =
        do{ c <- (opStart languageDef)
          ; cs <- many (opLetter languageDef)
          ; return (c:cs)
          }
        <?> "operator"

    isReservedOp name =
        isReserved (sort (reservedOpNames languageDef)) name


    -----------------------------------------------------------
    -- Identifiers & Reserved words
    -----------------------------------------------------------
    reserved name =
        lexeme $ try $
        do{ caseString name
          ; notFollowedBy (identLetter languageDef) <?> ("end of " ++ show name)
          }

    caseString name
        | caseSensitive languageDef  = string name
        | otherwise               = do{ walk name; return name }
        where
          walk []     = return ()
          walk (c:cs) = do{ caseChar c <?> msg; walk cs }

          caseChar c  | isAlpha c  = char (toLower c) <|> char (toUpper c)
                      | otherwise  = char c

          msg         = show name


    identifier =
        lexeme $ try $
        do{ name <- ident
          ; if (isReservedName name)
             then unexpected ("reserved word " ++ show name)
             else return name
          }


    ident
        = do{ c <- identStart languageDef
            ; cs <- many (identLetter languageDef)
            ; return (c:cs)
            }
        <?> "identifier"

    isReservedName name
        = isReserved theReservedNames caseName
        where
          caseName      | caseSensitive languageDef  = name
                        | otherwise               = map toLower name


    isReserved names name
        = scan names
        where
          scan []       = False
          scan (r:rs)   = case (compare r name) of
                            LT  -> scan rs
                            EQ  -> True
                            GT  -> False

    theReservedNames
        | caseSensitive languageDef  = sortedNames
        | otherwise               = map (map toLower) sortedNames
        where
          sortedNames   = sort (reservedNames languageDef)



    -----------------------------------------------------------
    -- White space & symbols
    -----------------------------------------------------------
    symbol name
        = lexeme (string name)

    lexeme p
        = do{ x <- p; whiteSpace; return x  }


    --whiteSpace
    -- MOD: this function renamed from whiteSpace to ws, and changed to return the matched string.
    ws
        | noLine && noMulti  = many (simpleSpace <?> "")
        | noLine             = many (simpleSpace <|> multiLineComment <?> "")
        | noMulti            = many (simpleSpace <|> oneLineComment <?> "")
        | otherwise          = many (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
        where
          noLine  = null (commentLine languageDef)
          noMulti = null (commentStart languageDef)

    --simpleSpace = skipMany1 (eoln ws <|> satisfy isSpace)        
    --MOD  simpleSpace WAS MODIFIED FOR LAYOUT TOKEN PARSERS by Tim Sheard 7/27/09
    simpleSpace =
        many1 (satisfy isSpace)

    -- MOD return matched string
    oneLineComment =
        do{ xs <- try (string (commentLine languageDef))
          ; ys <- many (satisfy (/= '\n'))
          ; return (xs++ys)
          }

    -- MOD: return matched string
    multiLineComment =
        do { xs <- try (string (commentStart languageDef))
           ; ys <- inComment
           ; return (xs++ys)
           }

    inComment
        | nestedComments languageDef  = inCommentMulti
        | otherwise                = inCommentSingle

    -- MOD: return matched string
    inCommentMulti
        =   do{ xs <- try (string (commentEnd languageDef)) ; return xs }
        <|> do{ xs <- multiLineComment              ; ys <- inCommentMulti; return (xs++ys) }
        <|> do{ xs <- many1 (noneOf startEnd)       ; ys <- inCommentMulti; return (xs++ys) }
        <|> do{ y  <- oneOf startEnd                ; ys <- inCommentMulti; return (y:ys)  }
        <?> "end of comment"
        where
          startEnd   = nub (commentEnd languageDef ++ commentStart languageDef)

    inCommentSingle
        =   do{ xs <- try (string (commentEnd languageDef)); return xs }
        <|> do{ xs <- many1 (noneOf startEnd)     ; ys <- inCommentSingle; return (xs++ys) }
        <|> do{ y  <- oneOf startEnd              ; ys <- inCommentSingle; return (y:ys) }
        <?> "end of comment"
        where
          startEnd   = nub (commentEnd languageDef ++ commentStart languageDef)

--MOD --------------------------------------------------------------------
-- THE FOLLOWING WAS ADDED FOR LAYOUT TOKEN PARSERS by Tim Sheard 7/27/09

    layoutSep   = (symbol sep)   <?> ("inserted layout separator ("++sep++")")
    layoutEnd   = (symbol close) <?> ("inserted layout closing symbol("++close++")")
    layoutBegin = (symbol open)  <?> ("layout opening symbol ("++open++")")
   
    layout p stop =
	   (do { try layoutBegin; xs <- sepBy p (symbol ";") 
	       ; layoutEnd <?> "explicit layout closing brace"
	       ; stop; return (xs)}) <|>
           (do { indent; xs <- align p stop; return xs})
           
    align p stop = ormore <|> zero
      where zero = do { stop; option "" layoutSep; undent; return []}
	    ormore = do { x <- p
	                ; whiteSpace
	                ; (do { try layoutSep; xs <- align p stop; return (x:xs)}) <|>
	                  (do { try layoutEnd; stop; return([x])}) <|>
	                     -- removing indentation happens automatically
	                     -- in function whiteSpace
	                  (do { stop; undent; return ([x])})}
  
    whiteSpace =
       do { (col1,_,_) <- getInfo
          ; wsChars <- ws
          ; (col2,tabs,more) <- getInfo
          ; case (wsChars,tabs,more,compare col2 col1) of
              ([],_,_,_) -> return ()
              (_,[],_,_) -> return ()
              (_,_,[],_) -> -- No more input, close all the pending layout with '}'
                            setInfo (col2,[],concat(map (const close) tabs))
              (cs,p:ps,_,EQ) -> setInfo (col2-1,tabs,sep++more)
              (cs,p:ps,_,LT) -> let adjust (col,[],add) = setInfo(col,[],rev add more)
                                    adjust (col,p:ps,add)
                                       | col2 < p = adjust(col-1,ps,close:add)
                                       | col2== p = setInfo(col-1,p:ps,rev (sep:add) more)
                                       | col2 > p = setInfo(col,p:ps,rev add more)
                                       | True = error "impossible"
                                    rev [] xs = xs
                                    rev (s:ss) xs = rev ss (s++xs)
                                in adjust (col2,p:ps,[])
              (cs,p:ps,_,GT) -> return ()
          }    	             
getInfo :: forall (m :: * -> *) t t1.
                 Monad m =>
                 ParsecT t1 t m (Column, t, t1)
getInfo = 
   do { pos <- getPosition
      ; tabs <- getState
      ; tokens <- getInput
      ; return(sourceColumn pos,tabs,tokens) }

setInfo :: forall s u (m :: * -> *).
                 Monad m =>
                 (Column, u, s) -> ParsecT s u m ()
setInfo (col,tabs,tokens) =
  do { p <- getPosition
     ; setPosition (setSourceColumn p col)
     ; setState tabs
     ; setInput tokens }

indent :: forall s (m :: * -> *).
                Monad m =>
                ParsecT s [Column] m ()
indent =
  do { pos <- getPosition
     ; tabs <- getState
     ; setState (sourceColumn pos : tabs)
     }
undent :: forall s (m :: * -> *) t. Monad m => ParsecT s [t] m ()
undent =
  do { (p:ps) <- getState
     ; setState ps
     }
     
_eoln :: forall (m :: * -> *) a.
               Monad m =>
               ParsecT [Char] [Column] m a -> ParsecT [Char] [Column] m Char  
_eoln whiteSpace =
  do { c <- satisfy (=='\n')  -- c == '\n' to succeed
     ; (col,tabs@(p:ps),input) <- getInfo
     ; whiteSpace -- this may screw up the tabs, 
                  -- but use the old tabs, but the 
                  -- new column (col2) and input (cs)
     ; (col2,_,cs) <- getInfo
     ; case cs of
         [] -> -- No more input, close all the pending layout with '}'
               setInfo (col2,[],map (const '}') tabs)
         _  ->  case compare col2 p of
                  EQ -> setInfo (col2-1,tabs,';':cs)
                  GT -> setInfo (col2,tabs,cs)
                  LT -> let adjust prefix cs column [] = setInfo (column,[],rev prefix cs)
                            adjust prefix cs column (tabs @ (p:ps))
                              | col2==p = setInfo (column-1,tabs,rev (';':prefix) cs)
                              | col2<p  = adjust ('}':prefix) cs (column - 1) ps
                              | col2>p  = setInfo (column,tabs,rev prefix cs)
                              | True    = error "impossible"
                            rev [] ys = ys
                            rev (x:xs) ys = rev xs (x:ys)
                        in  adjust [] cs col2 tabs
      ; return '\n' }    
      
data LayoutFun s m = 
   LayFun (forall a t. ParsecT s [Column] m a
             -> ParsecT s [Column] m t
             -> ParsecT s [Column] m [a])          
          
-- End of added code          
--MOD --------------------------------------------------------------------
          
