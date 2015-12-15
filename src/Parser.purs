module Parser where

import Prelude
import Global              (readInt)
import qualified Data.String as String
import Data.Int            (floor)
import Data.List
import Data.Maybe
import Data.Tuple
import Data.Tuple.Nested

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

-- | Fail if the specified parser matches.
notFollowedBy :: forall a. Parser a -> Parser Unit
notFollowedBy p = try $ (try p *> fail "Negated parser succeeded") <|> return unit

-- | Table for operator parsers and their AST representation. Sorted by precedence.
infixOperators :: Array (Array (Tuple3 (Parser String) Op Assoc))
infixOperators =
  [ [ (tuple3 (string ".") Composition AssocRight) ]
  , [ (tuple3 (string "^") Power AssocRight) ]
  , [ (tuple3 (string "*") Mul AssocLeft)
    , (tuple3 (string "`div`") Div AssocLeft)
    , (tuple3 (string "`mod`") Mod AssocLeft)
    ]
  , [ (tuple3 (try $ string "+" <* notFollowedBy (char '+')) Add AssocLeft)
    , (tuple3 (string "-") Sub AssocLeft)
    ]
  , [ (tuple3 (string ":") Colon AssocRight)
    , (tuple3 (string "++") Append AssocRight)
    ]
  , [ (tuple3 (string "==") Equ AssocNone)
    , (tuple3 (string "/=") Neq AssocNone)
    , (tuple3 (try $ string "<" <* notFollowedBy (char '=')) Lt AssocNone)
    , (tuple3 (try $ string ">" <* notFollowedBy (char '=')) Gt AssocNone)
    , (tuple3 (string "<=") Leq AssocNone)
    , (tuple3 (string ">=") Geq AssocNone)
    ]
  , [ (tuple3 (string "&&") And AssocRight) ]
  , [ (tuple3 (string "||") Or AssocRight) ]
  , [ (tuple3 (string "$") Dollar AssocRight) ]
  ]

-- | Table of operators (math, boolean, ...)
operatorTable :: OperatorTable Expr
operatorTable = ((uncurry3 (\p op assoc -> Infix (spaced p *> return (Binary op)) assoc)) <$>) <$> infixOperators

-- | Parser for operators
opParser :: Parser Op
opParser = PC.choice $ ((uncurry3 (\p op _ -> p *> return op)) <$>) $ concat $ (toList <$>) $ toList infixOperators

-- | Parse an expression between brackets
brackets :: forall a. Parser a -> Parser a
brackets p = PC.between (char '(' *> skipSpaces) (skipSpaces *> char ')') p

-- | Parse an expression between spaces (backtracks)
spaced :: forall a. Parser a -> Parser a
spaced p = try $ PC.between skipSpaces skipSpaces p

-- | Parse a base expression (atoms) or an arbitrary expression inside brackets
base :: Parser Expr -> Parser Expr
base expr =
      try (tuples expr)
  <|> section expr
  <|> list expr
  <|> (Atom <$> (int <|> variable))

-- | Parse syntax constructs like if_then_else, lambdas or function application
syntax :: Parser Expr -> Parser Expr
syntax expr = 
      try (ifThenElse expr)
  <|> try (lambda expr)
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

-- | Parse tuples.
tuples :: Parser Expr -> Parser Expr
tuples expr = do
  char '(' *> skipSpaces
  e <- expr
  skipSpaces
  mes <- PC.optionMaybe $ try $ do
    char ',' *> skipSpaces
    expr `PC.sepBy1` (try $ whiteSpace *> char ',' *> whiteSpace)
  skipSpaces
  char ')'
  case mes of
    Nothing -> return e
    Just es -> return $ NTuple (Cons e es)

-- | Parser for operator sections
section :: Parser Expr -> Parser Expr
section expr = do
  char '('
  skipSpaces
  me1 <- PC.optionMaybe (syntax expr)
  skipSpaces
  op <- opParser
  skipSpaces
  me2 <- PC.optionMaybe (syntax expr)
  skipSpaces
  char ')'
  case me1 of
    Nothing ->
      case me2 of
        Nothing -> return $ PrefixOp op
        Just e2 -> return $ SectR op e2
    Just e1 ->
      case me2 of
        Nothing -> return $ SectL e1 op
        Just _ -> fail "Cannot have a section with two expressions!"

-- | Parser for lists
list :: Parser Expr -> Parser Expr
list expr = do
  char '['
  skipSpaces
  exprs <- expr `PC.sepBy` (try $ whiteSpace *> char ',' *> whiteSpace)
  skipSpaces
  char ']'
  return $ List exprs

-- | Parse a lambda expression
lambda :: Parser Expr -> Parser Expr
lambda expr = do
  char '(' *> skipSpaces
  char '\\' *> skipSpaces
  binds <- (binding `PC.sepEndBy1` whiteSpace)
  string "->" *> skipSpaces
  body <- expr
  return $ Lambda binds body

-- | Parse function application
application :: Parser Expr -> Parser Expr
application expr = do
  e <- expr
  mArgs <- PC.optionMaybe (try $ skipSpaces *> (try expr) `PC.sepEndBy1` whiteSpace)
  case mArgs of
    Nothing   -> return e
    Just args -> return $ App e args


-- | Parse an arbitrary expression
expression :: Parser Expr
expression = PC.fix $ \expr -> buildExprParser operatorTable (syntax expr)

---------------------------------------------------------
-- Parsers for Bindings
---------------------------------------------------------

lit :: Parser Binding
lit = Lit <$> (int <|> variable)

binding :: Parser Binding
binding = lit