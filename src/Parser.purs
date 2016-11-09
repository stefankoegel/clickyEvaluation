module Parser where

import Prelude (Unit, void, class Monad, bind, ($), (<$>), (<<<), (>>=), (+), (*), (<>), id, flip, negate)
import Data.String as String
import Data.Foldable (foldl)
import Data.List (List(..), many, concat, elemIndex)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested (Tuple3, uncurry3, tuple3)
import Data.Array (modifyAt, snoc)
import Data.Array (fromFoldable, toUnfoldable) as Array
import Data.Either (Either)

import Control.Applicative (pure)
import Control.Alt ((<|>))
import Control.Apply ((<*), (*>), lift2)
import Control.Lazy (fix)
import Control.Monad.State (runState) 

import Text.Parsing.Parser (ParseError, ParserT, ParseState(..), runParserT, fail)
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
ilexe p = p >>= \a -> skipWhite *> pure a

-- parses <p> if it is on the same line or indented, does NOT change indentation state
indent :: forall a. IndentParser String a -> IndentParser String a
indent p = ((sameLine <|> indented') PC.<?> "Missing indentation! Did you type a tab-character?") *> ilexe p

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
boolean = string "True"  *> pure true
      <|> string "False" *> pure false

charLiteral :: forall m. (Monad m) => ParserT String m Char
charLiteral = do 
  char '\''
  c <- character'
  char '\''
  pure c

-- | Parser for characters at the start of variables
lower :: forall m. (Monad m) => ParserT String m Char
lower = oneOf $ String.toCharArray "abcdefghijklmnopqrstuvwxyz"

-- | Parser for all characters after the first in names
anyLetter :: forall m. (Monad m) => ParserT String m Char
anyLetter = char '_' <|> lower <|> upper <|> char '\'' <|> digit

character' :: forall m. (Monad m) => ParserT String m Char
character' =
      (char '\\' *>
        (    (char 'n' *> pure '\n')
         <|> (char 'r' *> pure '\r')
         <|> char '\\'
         <|> char '"'
         <|> char '\''))
  <|> (noneOf ['\\', '\'', '"'])

-- | Parser for variables names
name :: forall m. (Monad m) => ParserT String m String
name = do
  c  <- char '_' <|> lower
  cs <- many anyLetter
  let nm = String.fromCharArray $ Array.fromFoldable $ Cons c cs
  case elemIndex nm reservedWords of
    Nothing -> pure nm
    Just _  -> fail $ nm <> " is a reserved word!"
  where
    -- | List of reserved key words
    reservedWords :: List String
    reservedWords = Array.toUnfoldable $ (unGenLanguageDef haskellDef).reservedNames

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
character = (Char <<< String.singleton) <$> charLiteral

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
    infixTable = (\x -> (uncurry3 (\p op assoc -> Infix (spaced p *> pure (Binary op)) assoc)) <$> x) <$> infixOperators

    unaryMinus :: Operator m String Expr
    unaryMinus = Prefix $ spaced minusParse
      where 
        minusParse = do
          string "-"
          pure $ \e -> case e of
            Atom (AInt ai) -> (Atom (AInt (-ai)))
            _              -> Unary Sub e

    infixOperator :: Operator m String Expr
    infixOperator = Infix (spaced infixParse) AssocLeft
      where 
        infixParse = do
          char '`'
          n <- name
          char '`'
          pure $ \e1 e2 -> Binary (InfixFunc n) e1 e2

    -- | Parse an expression between spaces (backtracks)
    spaced :: forall a. ParserT String m a -> ParserT String m a
    spaced p = PC.try $ PC.between skipSpaces skipSpaces p

opParser :: forall m. (Monad m) => ParserT String m Op
opParser = (PC.choice $ (\x -> (uncurry3 (\p op _ -> p *> pure op)) <$> x) $ concat $ (\x -> Array.toUnfoldable <$> x) $ Array.toUnfoldable infixOperators) <|> infixFunc
  where 
    infixFunc = do
      char '`'
      n <- name
      char '`'
      pure $ InfixFunc n

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
  e     <- ilexe $ base expr
  mArgs <- PC.optionMaybe (PC.try $ ((PC.try (indent (base expr))) `PC.sepEndBy1` skipWhite))
  case mArgs of
    Nothing   -> pure e
    Just args -> pure $ App e args

-- | Parse an if_then_else construct - layout sensitive
ifThenElse :: IndentParser String Expr -> IndentParser String Expr
ifThenElse expr = do
  ilexe $ string "if" *> PC.lookAhead (oneOf [' ', '\t', '\n', '('])
  testExpr <- indent expr
  indent $ string "then"
  thenExpr <- indent expr
  indent $ string "else"
  elseExpr <- indent expr
  pure $ IfExpr testExpr thenExpr elseExpr

-- | Parser for tuples or bracketed expressions - layout sensitive
tuplesOrBrackets :: IndentParser String Expr -> IndentParser String Expr
tuplesOrBrackets expr = do
  ilexe $ char '('
  e <- indent expr
  mes <- PC.optionMaybe $ PC.try $ do
    indent $ char ','
    (indent expr) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ')'
  case mes of
    Nothing -> pure e
    Just es -> pure $ NTuple (Cons e es)

-- | Parser for operator sections - layout sensitive
section :: IndentParser String Expr -> IndentParser String Expr
section expr = do
  ilexe $ char '('
  me1 <- PC.optionMaybe (indent $ syntax expr)
  op <- opParser
  skipWhite
  me2 <- PC.optionMaybe (indent $ syntax expr)
  indent $ char ')'
  case me1 of
    Nothing ->
      case me2 of
        Nothing -> pure $ PrefixOp op
        Just e2 -> pure $ SectR op e2
    Just e1 ->
      case me2 of
        Nothing -> pure $ SectL e1 op
        Just _ -> fail "Cannot have a section with two expressions!"

-- | Parser for lists - layout sensitive
list :: IndentParser String Expr -> IndentParser String Expr
list expr = do
  ilexe $ char '['
  exprs <- (indent expr) `PC.sepBy` (PC.try $ indent $ char ',')
  indent $ char ']'
  pure $ List exprs

-- | Parser for Arithmetic Sequences - layout sensitive
arithmeticSequence :: IndentParser String Expr -> IndentParser String Expr
arithmeticSequence expr = do
  ilexe $ char '['
  start <- indent expr
  step  <- PC.optionMaybe $ (indent $ char ',') *> (indent expr)
  indent $ string ".."
  end   <- PC.optionMaybe $ indent expr
  indent $ char ']'
  pure $ ArithmSeq start step end

-- | Parser for list comprehensions - layout sensitive
listComp :: IndentParser String Expr -> IndentParser String Expr
listComp expr = do
  ilexe $ char '['
  start <- indent expr
  PC.try $ (char '|') *> PC.notFollowedBy (char '|')
  skipWhite
  quals <- (indent $ qual expr) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ']'
  pure $ ListComp start quals
  where
    -- | Parser for list comprehension qualifiers
    qual :: IndentParser String Expr -> IndentParser String ExprQual
    qual expr = (PC.try parseLet) <|> (PC.try parseGen) <|> parseGuard
      where
        parseLet = do
          ilexe $ string "let"
          b <- indent binding
          indent $ char '='
          e <- indent expr
          pure $ Let b e
        parseGen = do
          b <- ilexe binding
          indent $ string "<-"
          e <- indent expr
          pure $ Gen b e
        parseGuard = ilexe expr >>= (pure <<< Guard)

-- | Parser for strings ("example")
charList :: forall m. (Monad m) => ParserT String m Expr
charList = do
  char '"'
  strs <- many character'
  char '"'
  skipWhite
  pure (List ((Atom <<< Char <<< String.singleton) <$> strs))

-- | Parse a lambda expression - layout sensitive
lambda :: IndentParser String Expr -> IndentParser String Expr
lambda expr = do
  ilexe $ char '\\'
  binds <- many1 $ indent binding
  indent $ string "->"
  body <- indent expr
  pure $ Lambda binds body

-- Parser for let expressions - layout sensitive
letExpr :: IndentParser String Expr -> IndentParser String Expr
letExpr expr = do
  ilexe $ string "let"
  binds <- indent $ bindingBlock expr
  indent $ string "in"
  body  <- indent $ withPos expr
  pure $ LetExpr binds body
  where
    bindingItem :: IndentParser String Expr -> IndentParser String (Tuple Binding Expr)
    bindingItem expr = do
      b <- ilexe binding
      indent $ char '='
      e <- indent $ withPos expr
      pure $ Tuple b e

    bindingBlock :: IndentParser String Expr -> IndentParser String (List (Tuple Binding Expr))
    bindingBlock expr = curly <|> (PC.try layout) <|> (PC.try iblock)
      where 
        curly  = PC.between (ilexe $ char '{') (ilexe $ char '}') iblock 
        iblock = (bindingItem expr) `PC.sepBy1` (ilexe $ char ';')  
        layout = block1 (PC.try $ bindingItem expr >>= \x -> PC.notFollowedBy (ilexe $ char ';') *> pure x)

-- | Parse an arbitrary expression
expression :: IndentParser String Expr
expression = do
  whiteSpace
  fix $ \expr -> buildExprParser operatorTable (syntax expr)

runParserIndent :: forall a. IndentParser String a -> String -> Either ParseError a
runParserIndent p src = fst $ flip runState initialPos $ runParserT src p

parseExpr :: String -> Either ParseError Expr
parseExpr = runParserIndent expression

---------------------------------------------------------
-- Parsers for Bindings
---------------------------------------------------------

lit :: forall m. (Monad m) => ParserT String m Binding
lit = Lit <$> atom

consLit :: IndentParser String Binding -> IndentParser String Binding
consLit bnd = do
  ilexe $ char '('
  b <- indent consLit'
  indent $ char ')'
  pure b
  where
    consLit' :: IndentParser String Binding
    consLit' = do
      b <- ilexe $ bnd
      indent $ char ':'
      bs <- (PC.try $ indent consLit') <|> (indent bnd)
      pure $ ConsLit b bs

listLit :: IndentParser String Binding -> IndentParser String Binding
listLit bnd = do
  ilexe $ char '['
  bs <- (indent bnd) `PC.sepBy` (PC.try $ indent $ char ',')
  indent $ char ']'
  pure $ ListLit bs

tupleLit :: IndentParser String Binding -> IndentParser String Binding
tupleLit bnd = do
  ilexe $ char '('
  b <- indent bnd
  indent $ char ','
  bs <- (indent bnd) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ')'
  pure $ NTupleLit (Cons b bs)

binding :: IndentParser String Binding
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
  defName <- ilexe name
  binds   <- many $ indent binding
  indent $ char '='
  body    <- indent expression
  pure $ Def defName binds body

definitions :: IndentParser String (List Definition)
definitions = skipWhite *> block definition

parseDefs :: String -> Either ParseError (List Definition)
parseDefs = runParserIndent $ definitions
