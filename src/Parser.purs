module Parser where

import Prelude
import Global              (readInt)
import Data.Int (floor)
import qualified Data.String as String
import Data.List
import qualified Data.Array as Arr
-- import Data.Identity       (Identity())
import Data.Maybe
import Data.Either
import Data.Foldable
import Control.Alt         ((<|>))
import Control.Apply       ((<*), (*>))

import Text.Parsing.StringParser
import Text.Parsing.StringParser.Combinators as PC
import Text.Parsing.StringParser.Expr
import Text.Parsing.StringParser.String

import AST

---------------------------------------------------------
-- Parsers for Atoms
---------------------------------------------------------

-- | Parser for Int. (0 to 2^31-1)
int :: Parser Atom
int = do
  ds <- PC.many1 anyDigit
  let value = floor $ readInt 10 $ String.fromCharArray $ fromList ds
  return $ AInt value

-- | Parser for characters at the start of variables
lowerCaseLetter :: Parser Char
lowerCaseLetter = oneOf $ toList $ String.toCharArray "_abcdefghijklmnopqrstuvwxyz"

-- | Parser for characters at the start of constructors and types
upperCaseLetter :: Parser Char
upperCaseLetter = oneOf $ toList $ String.toCharArray "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

-- | Parser for all characters after the first in names
anyLetter :: Parser Char
anyLetter = lowerCaseLetter <|> upperCaseLetter <|> char '\''

-- | List of reserved key words
reservedWords :: List String
reservedWords = toList ["if", "then", "else"]

-- | Parser for variables
variable :: Parser Atom
variable = do
  c <- lowerCaseLetter
  cs <- PC.many anyLetter
  let var = String.fromCharArray $ fromList $ Cons c cs
  case elemIndex var reservedWords of
    Nothing -> return $ Name var
    Just _  -> fail $ var ++ " is a reserved word!"

---------------------------------------------------------
-- Parsers for Expressions
---------------------------------------------------------

-- | Table of operators (math, boolean, ...)
operatorTable :: OperatorTable Expr
operatorTable =
  [
    [ Infix (spaced (string "*") *> return (Binary Mul)) AssocLeft
    , Infix (spaced (string "`div`") *> return (Binary Div)) AssocLeft
    ]
  , [ Infix (spaced (string "+") *> return (Binary Add)) AssocLeft
    , Infix (spaced (string "-") *> return (Binary Sub)) AssocLeft
    ]
  ]

-- | Parse an expression between brackets
brackets :: forall a. Parser a -> Parser a
brackets p = PC.between (char '(' *> skipSpaces) (skipSpaces *> char ')') p

-- | Parse an expression between spaces (backtracks)
spaced :: forall a. Parser a -> Parser a
spaced p = try $ PC.between skipSpaces skipSpaces p

-- | Parse a base expression (atoms) or an arbitrary expression inside brackets
base :: Parser Expr -> Parser Expr
base expr = (Atom <$> (int <|> variable)) <|> brackets expr

-- | Parse syntax constructs like if_then_else, lambdas or function application
syntax :: Parser Expr -> Parser Expr
syntax expr = 
      try (ifThenElse expr)
  <|> application (base expr)

-- | Parse an if_then_else construct
ifThenElse :: Parser Expr -> Parser Expr
ifThenElse expr = do
  string "if" *> PC.lookAhead (oneOf $ toList [' ', '\t', '\n', '('])
  testExpr <- spaced expr
  string "then"
  thenExpr <- spaced expr
  string "else"
  elseExpr <- spaced expr
  return $ IfExpr testExpr thenExpr elseExpr

-- | Parse a lambda expression
lambda :: Parser Expr -> Parser Expr
lambda expr = do
  char '\\'
  -- TODO
  body <- expr
  return body

-- | Parse function application
application :: Parser Expr -> Parser Expr
application expr = do
  e <- expr
  mArgs <- PC.optionMaybe (try (skipSpaces *> (try expr) `PC.sepEndBy1` whiteSpace))
  case mArgs of
    Nothing   -> return e
    Just args -> return $ App e args

-- | Parse an arbitrary expression
expression :: Parser Expr
expression = PC.fix $ \expr -> buildExprParser operatorTable (syntax expr)
