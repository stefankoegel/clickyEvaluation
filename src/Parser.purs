module Parser where

import Prelude (Unit, bind, return, ($), (<$>), (<<<), unit, (++), void, id, flip, negate, liftM1)
import Data.String as String
import Data.List (List(Cons), many, toList, concat, elemIndex, fromList)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested (Tuple3, uncurry3, tuple3)
import Data.Array (modifyAt, snoc)

import Control.Alt ((<|>))
import Control.Apply ((<*), (*>))
import Control.Lazy (fix)
import Data.Identity (Identity)
import Data.Either (Either)

import Text.Parsing.Parser (ParseError, Parser, runParser, fail)
import Text.Parsing.Parser.Combinators as PC
import Text.Parsing.Parser.Expr (OperatorTable, Assoc(AssocRight, AssocNone, AssocLeft), Operator(Infix, Prefix), buildExprParser)
import Text.Parsing.Parser.String (whiteSpace, char, string, oneOf, noneOf)
import Text.Parsing.Parser.Token
import Text.Parsing.Parser.Language (haskellDef)

import AST (Atom(..), Binding(..), Definition(Def), Expr(..), Op(..))


tokenParser :: TokenParser
tokenParser = makeTokenParser haskellDef

---------------------------------------------------------
-- Parsers for Atoms
---------------------------------------------------------

-- | Skip spaces and tabs
eatSpaces :: Parser String Unit
eatSpaces = void $ many $ oneOf [' ','\t']

anyDigit :: Parser String Char
anyDigit = digit

-- | Parser for Int. (0 to 2^31-1)
int :: Parser String Atom
int = AInt <$> tokenParser.decimal

-- | Parser for Boolean
bool :: Parser String Atom
bool = string "True"  *> return (Bool true) 
   <|> string "False" *> return (Bool false)

-- | Parser for characters at the start of variables
lowerCaseLetter :: Parser String Char
lowerCaseLetter = oneOf $ String.toCharArray "_abcdefghijklmnopqrstuvwxyz"

-- | Parser for characters at the start of constructors and types
upperCaseLetter :: Parser String Char
upperCaseLetter = upper

-- | Parser for all characters after the first in names
anyLetter :: Parser String Char
anyLetter = lowerCaseLetter <|> upperCaseLetter <|> char '\'' <|> anyDigit

-- | List of reserved key words
reservedWords :: List String
reservedWords = toList $ (unGenLanguageDef haskellDef).reservedNames

character' :: Parser String Char
character' =
      (char '\\' *>
        (    (char 'n' *> return '\n')
         <|> (char 'r' *> return '\r')
         <|> char '\\'
         <|> char '"'
         <|> char '\''))
  <|> (noneOf ['\\', '\'', '"'])

character :: Parser String Atom
character = liftM1 (Char <<< String.fromChar) tokenParser.charLiteral

-- | Parser for variables names
name :: Parser String String
name = do
  c <- lowerCaseLetter
  cs <- many anyLetter
  let nm = String.fromCharArray $ fromList $ Cons c cs
  case elemIndex nm reservedWords of
    Nothing -> return nm 
    Just _  -> fail $ nm ++ " is a reserved word!"

-- | Parser for variable atoms
variable :: Parser String Atom
variable = Name <$> name

-- | Parser for atoms
atom :: Parser String Atom
atom = int <|> variable <|> bool <|> character

---------------------------------------------------------
-- Parsers for Expressions
---------------------------------------------------------

-- | Fail if the specified parser matches.
notFollowedBy :: forall a. Parser String a -> Parser String Unit
notFollowedBy p = PC.try $ (PC.try p *> fail "Negated parser succeeded") <|> return unit

-- | Table for operator parsers and their AST representation. Sorted by precedence.
infixOperators :: Array (Array (Tuple3 (Parser String String) Op Assoc))
infixOperators =
  [ [ (tuple3 (PC.try $ string "." <* notFollowedBy (char '.')) Composition AssocRight) ]
  , [ (tuple3 (string "^") Power AssocRight) ]
  , [ (tuple3 (string "*") Mul AssocLeft) ]
  , [ (tuple3 (PC.try $ string "+" <* notFollowedBy (char '+')) Add AssocLeft)
    , (tuple3 (string "-") Sub AssocLeft)
    ]
  , [ (tuple3 (string ":") Colon AssocRight)
    , (tuple3 (string "++") Append AssocRight)
    ]
  , [ (tuple3 (string "==") Equ AssocNone)
    , (tuple3 (string "/=") Neq AssocNone)
    , (tuple3 (PC.try $ string "<" <* notFollowedBy (char '=')) Lt AssocNone)
    , (tuple3 (PC.try $ string ">" <* notFollowedBy (char '=')) Gt AssocNone)
    , (tuple3 (string "<=") Leq AssocNone)
    , (tuple3 (string ">=") Geq AssocNone)
    ]
  , [ (tuple3 (string "&&") And AssocRight) ]
  , [ (tuple3 (string "||") Or AssocRight) ]
  , [ (tuple3 (string "$") Dollar AssocRight) ]
  ]

-- | Table of operators (math, boolean, ...)
operatorTable :: OperatorTable Identity String Expr
operatorTable = infixTable2 
  where
    infixTable2 = maybe [] id (modifyAt 2 (flip snoc infixOperator) infixTable1)
    infixTable1 = maybe [] id (modifyAt 3 (flip snoc unaryMinus) infixTable) 

    infixTable :: OperatorTable Identity String Expr
    infixTable = (\x -> (uncurry3 (\p op assoc -> Infix (spaced p *> return (Binary op)) assoc)) <$> x) <$> infixOperators

    unaryMinus :: Operator Identity String Expr
    unaryMinus = Prefix $ spaced minusParse
      where 
        minusParse = do
          string "-"
          return $ \e -> case e of
            Atom (AInt ai) -> (Atom (AInt (-ai)))
            _              -> Unary Sub e

    infixOperator :: Operator Identity String Expr
    infixOperator = Infix (spaced infixParse) AssocLeft
      where 
        infixParse = do
          char '`'
          n <- name
          char '`'
          return $ \e1 e2 -> Binary (InfixFunc n) e1 e2

opParser :: Parser String Op
opParser = (PC.choice $ (\x -> (uncurry3 (\p op _ -> p *> return op)) <$> x) $ concat $ (\x -> toList <$> x) $ toList infixOperators) <|> infixFunc
  where 
    infixFunc = do 
      char '`'
      n <- name
      char '`'
      return $ InfixFunc n

-- | Parse an expression between brackets
brackets :: forall a. Parser String a -> Parser String a
brackets = tokenParser.parens

-- | Parse an expression between spaces (backtracks)
spaced :: forall a. Parser String a -> Parser String a
spaced p = PC.try $ PC.between eatSpaces eatSpaces p

-- | Parse a base expression (atoms) or an arbitrary expression inside brackets
base :: Parser String Expr -> Parser String Expr
base expr =
      PC.try (tuplesOrBrackets expr)
  <|> PC.try (lambda expr)
  <|> section expr
  <|> PC.try (arithmeticSequence expr)
  <|> list expr
  <|> charList
  <|> (Atom <$> atom)

-- | Parse syntax constructs like if_then_else, lambdas or function application
syntax :: Parser String Expr -> Parser String Expr
syntax expr = 
      PC.try (ifThenElse expr)
  <|> PC.try (letExpr expr) 
  <|> applicationOrSingleExpression expr

-- | Parser for function application or single expressions
applicationOrSingleExpression :: Parser String Expr -> Parser String Expr
applicationOrSingleExpression expr = do
  e <- (base expr)
  mArgs <- PC.optionMaybe (PC.try $ eatSpaces *> ((PC.try (base expr)) `PC.sepEndBy1` eatSpaces))
  case mArgs of
    Nothing   -> return e
    Just args -> return $ App e args

-- | Parse an if_then_else construct
ifThenElse :: Parser String Expr -> Parser String Expr
ifThenElse expr = do
  string "if" *> PC.lookAhead (oneOf [' ', '\t', '\n', '('])
  testExpr <- spaced expr
  string "then"
  thenExpr <- spaced expr
  string "else"
  elseExpr <- spaced expr
  return $ IfExpr testExpr thenExpr elseExpr

-- | Parser for tuples or bracketed expressions.
tuplesOrBrackets :: Parser String Expr -> Parser String Expr
tuplesOrBrackets expr = do
  char '(' *> eatSpaces
  e <- expr
  eatSpaces
  mes <- PC.optionMaybe $ PC.try $ do
    char ',' *> eatSpaces
    expr `PC.sepBy1` (PC.try $ eatSpaces *> char ',' *> eatSpaces)
  eatSpaces
  char ')'
  case mes of
    Nothing -> return e
    Just es -> return $ NTuple (Cons e es)

-- | Parser for operator sections
section :: Parser String Expr -> Parser String Expr
section expr = do
  char '('
  eatSpaces
  me1 <- PC.optionMaybe (syntax expr)
  eatSpaces
  op <- opParser
  eatSpaces
  me2 <- PC.optionMaybe (syntax expr)
  eatSpaces
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
list :: Parser String Expr -> Parser String Expr
list expr = do
  char '['
  eatSpaces
  exprs <- expr `PC.sepBy` (PC.try $ eatSpaces *> char ',' *> eatSpaces)
  eatSpaces
  char ']'
  return $ List exprs

-- | Parser for Arithmetic Sequences
arithmeticSequence :: Parser String Expr -> Parser String Expr
arithmeticSequence expr = do
  char '['
  eatSpaces
  start <- expr
  eatSpaces
  step <- PC.optionMaybe $ (char ',') *> eatSpaces *> expr
  eatSpaces
  string ".."
  end <- PC.optionMaybe $ spaced expr
  eatSpaces   
  char ']'    
  return $ ArithmSeq start step end

-- | Parser for strings ("example")
charList :: Parser String Expr
charList = do
  char '"'
  strs <- many character'
  char '"'
  return (List ((Atom <<< Char <<< String.fromChar) <$> strs))

-- | Parse a lambda expression
lambda :: Parser String Expr -> Parser String Expr
lambda expr = do
  char '\\' *> eatSpaces
  binds <- (binding `PC.sepEndBy1` eatSpaces)
  string "->" *> eatSpaces
  body <- expr
  return $ Lambda binds body

-- | Parser for let expression
letExpr :: Parser String Expr -> Parser String Expr
letExpr expr = do
  string "let" *> eatSpaces
  bnd <- binding
  eatSpaces *> char '=' *> eatSpaces
  lexp <- expr
  eatSpaces *> string "in" *> eatSpaces
  body <- expr
  return $ LetExpr bnd lexp body

-- | Parse an arbitrary expression
expression :: Parser String Expr
expression = do
  whiteSpace
  fix $ \expr -> buildExprParser operatorTable (syntax expr)

parseExpr :: String -> Either ParseError Expr
parseExpr input = runParser input expression

---------------------------------------------------------
-- Parsers for Bindings
---------------------------------------------------------

lit :: Parser String Binding
lit = Lit <$> atom

consLit :: Parser String Binding -> Parser String Binding
consLit bnd = do
  char '(' *> eatSpaces
  b <- consLit'
  eatSpaces *> char ')'
  return b
  where
    consLit' :: Parser String Binding
    consLit' = do
      b <- bnd
      eatSpaces *> char ':' *> eatSpaces
      bs <- PC.try consLit' <|> bnd
      return $ ConsLit b bs

listLit :: Parser String Binding -> Parser String Binding
listLit bnd = do
  char '[' *> eatSpaces
  bs <- bnd `PC.sepBy` (PC.try $ eatSpaces *> char ',' *> eatSpaces)
  eatSpaces *> char ']'
  return $ ListLit bs

tupleLit :: Parser String Binding -> Parser String Binding
tupleLit bnd = do
  char '(' *> eatSpaces
  b <- bnd
  eatSpaces *> char ',' *> eatSpaces
  bs <- bnd `PC.sepBy1` (PC.try $ eatSpaces *> char ',' *> eatSpaces)
  eatSpaces *> char ')'
  return $ NTupleLit (Cons b bs)

binding :: Parser String Binding
binding = fix $ \bnd ->
      (PC.try $ consLit bnd)
  <|> (tupleLit bnd)
  <|> (listLit bnd)
  <|> lit

---------------------------------------------------------
-- Parsers for Definitions
---------------------------------------------------------

definition :: Parser String Definition
definition = do
  defName <- name
  eatSpaces
  binds <- binding `PC.sepEndBy` eatSpaces
  char '='
  eatSpaces
  body <- expression
  return $ Def defName binds body

definitions :: Parser String (List Definition)
definitions = do
  whiteSpace
  definition `PC.sepEndBy` whiteSpace

parseDefs :: String -> Either ParseError (List Definition)
parseDefs input = runParser input definitions

