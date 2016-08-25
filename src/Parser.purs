module Parser where

import Prelude (Unit, void, class Monad, bind, return, ($), (<$>), (<<<), (>>=), (+), (*), (++), id, flip, negate)
import Data.String as String
import Data.Foldable (foldl)
import Data.List (List(..), many, toList, concat, elemIndex, fromList)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested (Tuple3, uncurry3, tuple3)
import Data.Array (modifyAt, snoc)
import Data.Either (Either)

import Control.Alt ((<|>))
import Control.Apply ((<*), (*>), lift2)
import Control.Lazy (fix)
import Control.Monad.State (runState) 

import Text.Parsing.Parser (ParseError, ParserT, PState(..), runParserT, fail)
import Text.Parsing.Parser.Combinators as PC
import Text.Parsing.Parser.Expr (OperatorTable, Assoc(AssocRight, AssocNone, AssocLeft), Operator(Infix, Prefix), buildExprParser)
import Text.Parsing.Parser.String (whiteSpace, char, string, oneOf, noneOf)
import Text.Parsing.Parser.Token (unGenLanguageDef, upper, digit)
import Text.Parsing.Parser.Language (haskellDef)
import Text.Parsing.Parser.Pos (initialPos)

import AST (Atom(..), Binding(..), Definition(Def), Expr(..), Qual(..), ExprQual, Op(..))
import IndentParser

---------------------------------------------------------
-- Helpful combinators
---------------------------------------------------------

-- | @ many1 @ should prabably be inside Text.Parsing.Parser.Combinators
many1 :: forall s m a. (Monad m) => ParserT s m a -> ParserT s m (List a)
many1 p = lift2 Cons p (many p)

--skips whitespaces
skipSpaces :: forall m. (Monad m) => ParserT String m Unit
skipSpaces = void $ many $ oneOf [' ', '\t']

--skips whitespaces and linebreaks
skipWhite :: forall m. (Monad m) => ParserT String m Unit 
skipWhite = void $ many $ oneOf ['\n', '\r', '\f', ' ', '\t']

--lexeme parser (skips trailing whitespaces and linebreaks)
ilexe :: forall a m. (Monad m) => ParserT String m a -> ParserT String m a
ilexe p = do
  a <- p
  skipWhite
  return a

indent :: forall a. IndentParser String a -> IndentParser String a
indent p = sameOrIndented *> (ilexe p)

indent' :: forall a. IndentParser String a -> IndentParser String a
indent' p = ilexe $ sameOrIndented *> p

---------------------------------------------------------
-- Parsers for Primitives
---------------------------------------------------------

integer :: forall m. (Monad m) => ParserT String m Int
integer = convert <$> many1 digit
  where 
    convert :: List Char -> Int
    convert = foldl (\acc x -> acc * 10 + table x) 0 

    table '0' = 0
    table '1' = 1
    table '2' = 2
    table '3' = 3
    table '4' = 4
    table '5' = 5
    table '6' = 6
    table '7' = 7
    table '8' = 8
    table '9' = 9
    table _   = 47

boolean :: forall m. (Monad m) => ParserT String m Boolean
boolean = string "True"  *> return true
      <|> string "False" *> return false

charLiteral :: forall m. (Monad m) => ParserT String m Char
charLiteral = do 
  char '\''
  c <- character'
  char '\''
  return c

-- | Parser for characters at the start of variables
lower :: forall m. (Monad m) => ParserT String m Char
lower = oneOf $ String.toCharArray "abcdefghijklmnopqrstuvwxyz"

-- | Parser for all characters after the first in names
anyLetter :: forall m. (Monad m) => ParserT String m Char
anyLetter = char '_' <|> lower <|> upper <|> char '\'' <|> digit

character' :: forall m. (Monad m) => ParserT String m Char
character' =
      (char '\\' *>
        (    (char 'n' *> return '\n')
         <|> (char 'r' *> return '\r')
         <|> char '\\'
         <|> char '"'
         <|> char '\''))
  <|> (noneOf ['\\', '\'', '"'])

-- | Parser for variables names
name :: forall m. (Monad m) => ParserT String m String
name = do
  c  <- char '_' <|> lower
  cs <- many anyLetter
  let nm = String.fromCharArray $ fromList $ Cons c cs
  case elemIndex nm reservedWords of
    Nothing -> return nm 
    Just _  -> fail $ nm ++ " is a reserved word!"
  where
    -- | List of reserved key words
    reservedWords :: List String
    reservedWords = toList $ (unGenLanguageDef haskellDef).reservedNames

---------------------------------------------------------
-- Parsers for Atoms
---------------------------------------------------------

-- | Parser for Int. (0 to 2^31-1)
int :: forall m. (Monad m) => ParserT String m Atom
int = AInt <$> integer

-- | Parser for Boolean
bool :: forall m. (Monad m) => ParserT String m Atom
bool = Bool <$> boolean

-- | Parser for Char
character :: forall m. (Monad m) => ParserT String m Atom
character = (Char <<< String.fromChar) <$> charLiteral

-- | Parser for variable atoms
variable :: forall m. (Monad m) => ParserT String m Atom
variable = Name <$> name

-- | Parser for atoms
atom :: forall m. (Monad m) => ParserT String m Atom
atom = int <|> variable <|> bool <|> character

---------------------------------------------------------
-- Parsers for Expressions
---------------------------------------------------------

-- | Table for operator parsers and their AST representation. Sorted by precedence.
infixOperators :: forall m. (Monad m) => Array (Array (Tuple3 (ParserT String m String) Op Assoc))
infixOperators =
  [ [ (tuple3 (PC.try $ string "." <* PC.notFollowedBy (char '.')) Composition AssocRight) ]
  , [ (tuple3 (string "^") Power AssocRight) ]
  , [ (tuple3 (string "*") Mul AssocLeft) ]
  , [ (tuple3 (PC.try $ string "+" <* PC.notFollowedBy (char '+')) Add AssocLeft)
    , (tuple3 (string "-") Sub AssocLeft)
    ]
  , [ (tuple3 (string ":") Colon AssocRight)
    , (tuple3 (string "++") Append AssocRight)
    ]
  , [ (tuple3 (string "==") Equ AssocNone)
    , (tuple3 (string "/=") Neq AssocNone)
    , (tuple3 (PC.try $ string "<" <* PC.notFollowedBy (char '=')) Lt AssocNone)
    , (tuple3 (PC.try $ string ">" <* PC.notFollowedBy (char '=')) Gt AssocNone)
    , (tuple3 (string "<=") Leq AssocNone)
    , (tuple3 (string ">=") Geq AssocNone)
    ]
  , [ (tuple3 (string "&&") And AssocRight) ]
  , [ (tuple3 (string "||") Or AssocRight) ]
  , [ (tuple3 (string "$") Dollar AssocRight) ]
  ]

-- | Table of operators (math, boolean, ...)
operatorTable :: forall m. (Monad m) => OperatorTable m String Expr
operatorTable = infixTable2 
  where
    infixTable2 = maybe [] id (modifyAt 2 (flip snoc infixOperator) infixTable1)
    infixTable1 = maybe [] id (modifyAt 3 (flip snoc unaryMinus) infixTable) 

    infixTable :: OperatorTable m String Expr
    infixTable = (\x -> (uncurry3 (\p op assoc -> Infix (spaced p *> return (Binary op)) assoc)) <$> x) <$> infixOperators

    unaryMinus :: Operator m String Expr
    unaryMinus = Prefix $ spaced minusParse
      where 
        minusParse = do
          string "-"
          return $ \e -> case e of
            Atom (AInt ai) -> (Atom (AInt (-ai)))
            _              -> Unary Sub e

    infixOperator :: Operator m String Expr
    infixOperator = Infix (spaced infixParse) AssocLeft
      where 
        infixParse = do
          char '`'
          n <- name
          char '`'
          return $ \e1 e2 -> Binary (InfixFunc n) e1 e2

opParser :: forall m. (Monad m) => ParserT String m Op
opParser = (PC.choice $ (\x -> (uncurry3 (\p op _ -> p *> return op)) <$> x) $ concat $ (\x -> toList <$> x) $ toList infixOperators) <|> infixFunc
  where 
    infixFunc = do 
      char '`'
      n <- name
      char '`'
      return $ InfixFunc n

-- | Parse an expression between spaces (backtracks)
spaced :: forall a m. (Monad m) => ParserT String m a -> ParserT String m a
spaced p = PC.try $ PC.between skipSpaces skipSpaces p

-- | Parse a base expression (atoms) or an arbitrary expression inside brackets
base :: IndentParser String Expr -> IndentParser String Expr
base expr =
      PC.try (tuplesOrBrackets expr)
  <|> PC.try (lambda expr)
  <|> section expr
  <|> PC.try (listComp expr)
  <|> PC.try (arithmeticSequence expr)
  <|> list expr
  <|> charList
  <|> (Atom <$> atom)

-- | Parse syntax constructs like if_then_else, lambdas or function application
syntax :: IndentParser String Expr -> IndentParser String Expr
syntax expr = 
      PC.try (ifThenElse expr)
  <|> PC.try (letExpr expr) 
  <|> applicationOrSingleExpression expr

-- | Parser for function application or single expressions
applicationOrSingleExpression :: IndentParser String Expr -> IndentParser String Expr
applicationOrSingleExpression expr = do
  e <- (base expr)
  mArgs <- PC.optionMaybe (PC.try $ skipSpaces *> ((PC.try (base expr)) `PC.sepEndBy1` skipSpaces))
  case mArgs of
    Nothing   -> return e
    Just args -> return $ App e args

-- | Parse an if_then_else construct - layout sensitive
ifThenElse :: IndentParser String Expr -> IndentParser String Expr
ifThenElse expr = do
  ilexe $ string "if" *> PC.lookAhead (oneOf [' ', '\t', '\n', '('])
  testExpr <- indent expr
  indent $ string "then"
  thenExpr <- indent expr
  indent $ string "else"
  elseExpr <- indent expr
  return $ IfExpr testExpr thenExpr elseExpr

-- | Parser for tuples or bracketed expressions.
tuplesOrBrackets :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m Expr
tuplesOrBrackets expr = do
  char '(' *> skipSpaces
  e <- expr
  skipSpaces
  mes <- PC.optionMaybe $ PC.try $ do
    char ',' *> skipSpaces
    expr `PC.sepBy1` (PC.try $ skipSpaces *> char ',' *> skipSpaces)
  skipSpaces
  char ')'
  case mes of
    Nothing -> return e
    Just es -> return $ NTuple (Cons e es)

-- | Parser for operator sections
section :: IndentParser String Expr -> IndentParser String Expr
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
list :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m Expr
list expr = do
  char '['
  skipSpaces
  exprs <- expr `PC.sepBy` (PC.try $ skipSpaces *> char ',' *> skipSpaces)
  skipSpaces
  char ']'
  return $ List exprs

-- | Parser for Arithmetic Sequences
arithmeticSequence :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m Expr
arithmeticSequence expr = do
  char '['
  skipSpaces
  start <- expr
  skipSpaces
  step <- PC.optionMaybe $ (char ',') *> skipSpaces *> expr
  skipSpaces
  string ".."
  end <- PC.optionMaybe $ spaced expr
  skipSpaces   
  char ']'    
  return $ ArithmSeq start step end

-- | Parser for List Comprehensions
listComp :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m Expr
listComp expr = do
  char '['
  skipSpaces
  start <- expr
  skipSpaces
  PC.try $ char '|' <* PC.notFollowedBy (char '|')
  skipSpaces
  quals <- (qual expr) `PC.sepBy1` (PC.try $ skipSpaces *> char ',' *> skipSpaces)
  skipSpaces
  char ']'
  return $ ListComp start quals

qual :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m ExprQual
qual expr = (PC.try parseLet) <|> (PC.try parseGen) <|> parseGuard
  where
    parseLet = do 
      string "let" *> skipSpaces 
      b <- binding
      skipSpaces *> char '=' *> skipSpaces
      e <- expr
      return $ Let b e        
    parseGen = do
      b <- binding
      skipSpaces *> string "<-" *> skipSpaces
      e <- expr
      return $ Gen b e
    parseGuard = do
      e <- expr
      return $ Guard e

-- | Parser for strings ("example")
charList :: forall m. (Monad m) => ParserT String m Expr
charList = do
  char '"'
  strs <- many character'
  char '"'
  return (List ((Atom <<< Char <<< String.fromChar) <$> strs))

-- | Parse a lambda expression
lambda :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m Expr
lambda expr = do
  char '\\' *> skipSpaces
  binds <- (binding `PC.sepEndBy1` skipSpaces)
  string "->" *> skipSpaces
  body <- expr
  return $ Lambda binds body

-- Parser for let expressions - layout sensitive
letExpr :: IndentParser String Expr -> IndentParser String Expr
letExpr expr = do
  ilexe $ string "let"
  --sameLine <|> indented'

  binds <- bindingBlock expr
  skipWhite
  --sameLine <|> indented'
  ilexe $ string "in"

  --sameLine <|> indented'
  body  <- ilexe expr
  return $ LetExpr binds body
  where
    bindingItem :: forall m. (Monad m) => ParserT String m Expr -> ParserT String m (Tuple Binding Expr)
    bindingItem expr = do
      b <- ilexe binding
      ilexe $ char '='
      e <- ilexe expr
      return $ Tuple b e

    bindingBlock :: IndentParser String Expr -> IndentParser String (List (Tuple Binding Expr))
    bindingBlock expr = curly <|> (PC.try layout) <|> (PC.try iblock)
      where 
        curly  = PC.between (ilexe $ char '{') (ilexe $ char '}') iblock 
        iblock = (bindingItem expr) `PC.sepBy1` (ilexe $ char ';')  
        layout = block (PC.try $ bindingItem expr >>= \x -> PC.notFollowedBy (ilexe $ char ';') *> return x)

----------------------------------------------------------------------------------

-- | Parse an arbitrary expression
expression :: IndentParser String Expr
expression = do
  whiteSpace
  fix $ \expr -> buildExprParser operatorTable (syntax expr)

runParserIndent :: forall a. IndentParser String a -> String -> Either ParseError a
runParserIndent p src = fst $ flip runState initialPos $ runParserT (PState {input: src,position: initialPos}) p

parseExpr :: String -> Either ParseError Expr
parseExpr = runParserIndent expression

---------------------------------------------------------
-- Parsers for Bindings
---------------------------------------------------------

lit :: forall m. (Monad m) => ParserT String m Binding
lit = Lit <$> atom

consLit :: forall m. (Monad m) => ParserT String m Binding -> ParserT String m Binding
consLit bnd = do
  char '(' *> skipSpaces
  b <- consLit'
  skipSpaces *> char ')'
  return b
  where
    consLit' :: ParserT String m Binding
    consLit' = do
      b <- bnd
      skipSpaces *> char ':' *> skipSpaces
      bs <- PC.try consLit' <|> bnd
      return $ ConsLit b bs

listLit :: forall m. (Monad m) => ParserT String m Binding -> ParserT String m Binding
listLit bnd = do
  char '[' *> skipSpaces
  bs <- bnd `PC.sepBy` (PC.try $ skipSpaces *> char ',' *> skipSpaces)
  skipSpaces *> char ']'
  return $ ListLit bs

tupleLit :: forall m. (Monad m) => ParserT String m Binding -> ParserT String m Binding
tupleLit bnd = do
  char '(' *> skipSpaces
  b <- bnd
  skipSpaces *> char ',' *> skipSpaces
  bs <- bnd `PC.sepBy1` (PC.try $ skipSpaces *> char ',' *> skipSpaces)
  skipSpaces *> char ')'
  return $ NTupleLit (Cons b bs)

binding :: forall m. (Monad m) => ParserT String m Binding
binding = fix $ \bnd ->
      (PC.try $ consLit bnd)
  <|> (tupleLit bnd)
  <|> (listLit bnd)
  <|> lit

---------------------------------------------------------
-- Parsers for Definitions
---------------------------------------------------------

definition :: IndentParser String Definition
definition = do
  defName <- name
  skipSpaces
  binds <- binding `PC.sepEndBy` skipSpaces
  char '='
  skipSpaces
  body <- expression
  return $ Def defName binds body

definitions :: IndentParser String (List Definition)
definitions = do
  whiteSpace
  definition `PC.sepEndBy` whiteSpace

parseDefs :: String -> Either ParseError (List Definition)
parseDefs = runParserIndent definitions