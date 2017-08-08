module Parser where

import Prelude
import Data.String as String
import Data.Foldable (foldl)
import Data.List (List(..), many, concat, elemIndex, length)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested (Tuple3, uncurry3, tuple3)
import Data.Array (modifyAt, snoc)
import Data.Array (fromFoldable, toUnfoldable) as Array
import Data.Either (Either)

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Lazy (fix)
import Control.Monad.State (runState) 

import Text.Parsing.Parser (ParseError, ParserT, runParserT, fail)
import Text.Parsing.Parser.Combinators as PC
import Text.Parsing.Parser.Expr (OperatorTable, Assoc(AssocRight, AssocNone, AssocLeft), Operator(Infix, Prefix), buildExprParser)
import Text.Parsing.Parser.String (whiteSpace, char, string, oneOf, noneOf)
import Text.Parsing.Parser.Token (unGenLanguageDef, upper, digit)
import Text.Parsing.Parser.Language (haskellDef)
import Text.Parsing.Parser.Pos (initialPos)

import AST
  ( MType
  , Tree(..)
  , Atom(..)
  , Binding(..)
  , Definition(Def)
  , Op(..)
  , QualTree(..)
  , TypeQual
  , TypeTree
  , toOpTuple
  , ADTDef(..)
  , Associativity(..)
  , DataCons(..)
  , Type(..))
import IndentParser (IndentParser, block, withPos, block1, indented', sameLine)

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

symbol :: forall m. (Monad m) => ParserT String m Char
symbol = oneOf
  [':','!','#','$','%','&','*'
  ,'+','.','/','<','>','=','?'
  ,'@','\\','^','|','-','~','_'
  ,'°']

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

-- | Parser for type names
typeName :: forall m. (Monad m) => ParserT String m String
typeName = do
  c  <- upper
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
operatorTable :: forall m. (Monad m) => OperatorTable m String TypeTree
operatorTable = infixTable2 
  where
    infixTable2 = maybe [] id (modifyAt 2 (flip snoc infixOperator) infixTable1)
    infixTable1 = maybe [] id (modifyAt 3 (flip snoc unaryMinus) infixTable) 

    infixTable :: OperatorTable m String TypeTree
    infixTable = (\x -> (uncurry3 (\p op assoc -> Infix (spaced p *> pure (Binary Nothing (toOpTuple op))) assoc)) <$> x) <$> infixOperators

    unaryMinus :: Operator m String TypeTree
    unaryMinus = Prefix $ spaced minusParse
      where 
        minusParse = do
          string "-"
          pure $ \e -> case e of
            Atom _ (AInt ai) -> (Atom Nothing (AInt (-ai)))
            _                -> Unary Nothing (toOpTuple Sub) e

    infixOperator :: Operator m String TypeTree
    infixOperator = Infix (spaced infixParse) AssocLeft
      where 
        infixParse = do
          char '`'
          n <- name
          char '`'
          pure $ \e1 e2 -> Binary Nothing (toOpTuple $ InfixFunc n) e1 e2

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
base :: IndentParser String TypeTree -> IndentParser String TypeTree
base expr =
      PC.try (tuplesOrBrackets expr)
  <|> PC.try (lambda expr)
  <|> section expr
  <|> PC.try (listComp expr)
  <|> PC.try (arithmeticSequence expr)
  <|> list expr
  <|> charList
  <|> (Atom Nothing <$> atom)

-- | Parse syntax constructs like if_then_else, lambdas or function application
syntax :: IndentParser String TypeTree -> IndentParser String TypeTree
syntax expr =
      PC.try (ifThenElse expr)
  <|> PC.try (letExpr expr)
  <|> applicationOrSingleExpression expr

-- | Parser for function application or single expressions
applicationOrSingleExpression :: IndentParser String TypeTree -> IndentParser String TypeTree
applicationOrSingleExpression expr = do
  e     <- ilexe $ base expr
  mArgs <- PC.optionMaybe (PC.try $ ((PC.try (indent (base expr))) `PC.sepEndBy1` skipWhite))
  case mArgs of
    Nothing   -> pure e
    Just args -> pure $ App Nothing e args

-- | Parse an if_then_else construct - layout sensitive
ifThenElse :: IndentParser String TypeTree -> IndentParser String TypeTree
ifThenElse expr = do
  ilexe $ string "if" *> PC.lookAhead (oneOf [' ', '\t', '\n', '('])
  testExpr <- indent expr
  indent $ string "then"
  thenExpr <- indent expr
  indent $ string "else"
  elseExpr <- indent expr
  pure $ IfExpr Nothing testExpr thenExpr elseExpr

-- | Parser for tuples or bracketed expressions - layout sensitive
tuplesOrBrackets :: IndentParser String TypeTree -> IndentParser String TypeTree
tuplesOrBrackets expr = do
  ilexe $ char '('
  e <- indent expr
  mes <- PC.optionMaybe $ PC.try $ do
    indent $ char ','
    (indent expr) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ')'
  case mes of
    Nothing -> pure e
    Just es -> pure $ NTuple Nothing (Cons e es)

-- | Parser for operator sections - layout sensitive
section :: IndentParser String TypeTree -> IndentParser String TypeTree
section expr = do
  ilexe $ char '('
  me1 <- PC.optionMaybe (indent $ syntax expr)
  op <- toOpTuple <$> opParser
  skipWhite
  me2 <- PC.optionMaybe (indent $ syntax expr)
  indent $ char ')'
  case me1 of
    Nothing ->
      case me2 of
        Nothing -> pure $ PrefixOp Nothing op
        Just e2 -> pure $ SectR Nothing op e2
    Just e1 ->
      case me2 of
        Nothing -> pure $ SectL Nothing e1 op
        Just _ -> fail "Cannot have a section with two expressions!"

-- | Parser for lists - layout sensitive
list :: IndentParser String TypeTree -> IndentParser String TypeTree
list expr = do
  ilexe $ char '['
  exprs <- (indent expr) `PC.sepBy` (PC.try $ indent $ char ',')
  indent $ char ']'
  pure $ List Nothing exprs

-- | Parser for Arithmetic Sequences - layout sensitive
arithmeticSequence :: IndentParser String TypeTree -> IndentParser String TypeTree
arithmeticSequence expr = do
  ilexe $ char '['
  start <- indent expr
  step  <- PC.optionMaybe $ (indent $ char ',') *> (indent expr)
  indent $ string ".."
  end   <- PC.optionMaybe $ indent expr
  indent $ char ']'
  pure $ ArithmSeq Nothing start step end

-- | Parser for list comprehensions - layout sensitive
listComp :: IndentParser String TypeTree -> IndentParser String TypeTree
listComp expr = do
  ilexe $ char '['
  start <- indent expr
  PC.try $ (char '|') *> PC.notFollowedBy (char '|')
  skipWhite
  quals <- (indent $ qual expr) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ']'
  pure $ ListComp Nothing start quals
  where
    -- | Parser for list comprehension qualifiers
    qual :: IndentParser String TypeTree -> IndentParser String TypeQual
    qual expr = (PC.try parseLet) <|> (PC.try parseGen) <|> parseGuard
      where
        parseLet = do
          ilexe $ string "let"
          b <- indent binding
          indent $ char '='
          e <- indent expr
          pure $ Let Nothing b e
        parseGen = do
          b <- ilexe binding
          indent $ string "<-"
          e <- indent expr
          pure $ Gen Nothing b e
        parseGuard = ilexe expr >>= (pure <<< Guard Nothing)

-- | Parser for strings ("example")
charList :: forall m. (Monad m) => ParserT String m TypeTree
charList = do
  char '"'
  strs <- many character'
  char '"'
  pure (List Nothing ((Atom Nothing <<< Char <<< String.singleton) <$> strs))

-- | Parse a lambda expression - layout sensitive
lambda :: IndentParser String TypeTree -> IndentParser String TypeTree
lambda expr = do
  ilexe $ char '\\'
  binds <- many1 $ indent binding
  indent $ string "->"
  body <- indent expr
  pure $ Lambda Nothing binds body

-- Parser for let expressions - layout sensitive
letExpr :: IndentParser String TypeTree -> IndentParser String TypeTree
letExpr expr = do
  ilexe $ string "let"
  binds <- indent $ bindingBlock expr
  indent $ string "in"
  body  <- indent $ withPos expr
  pure $ LetExpr Nothing binds body
  where
    bindingItem :: IndentParser String TypeTree -> IndentParser String (Tuple (Binding MType) TypeTree)
    bindingItem expr = do
      b <- ilexe binding
      indent $ char '='
      e <- indent $ withPos expr
      pure $ Tuple b e

    bindingBlock :: IndentParser String TypeTree -> IndentParser String (List (Tuple (Binding MType) TypeTree))
    bindingBlock expr = curly <|> (PC.try layout) <|> (PC.try iblock)
      where 
        curly  = PC.between (ilexe $ char '{') (ilexe $ char '}') iblock 
        iblock = (bindingItem expr) `PC.sepBy1` (ilexe $ char ';')  
        layout = block1 (PC.try $ bindingItem expr >>= \x -> PC.notFollowedBy (ilexe $ char ';') *> pure x)

-- | Parse an arbitrary expression
expression :: IndentParser String TypeTree
expression = do
  whiteSpace
  fix $ \expr -> buildExprParser operatorTable (syntax expr)

runParserIndent :: forall a. IndentParser String a -> String -> Either ParseError a
runParserIndent p src = fst $ flip runState initialPos $ runParserT src p

parseExpr :: String -> Either ParseError TypeTree
parseExpr = runParserIndent expression

---------------------------------------------------------
-- Parsers for Bindings
---------------------------------------------------------

lit :: forall m. (Monad m) => ParserT String m (Binding MType)
lit = Lit Nothing <$> atom

consLit :: IndentParser String (Binding MType) -> IndentParser String (Binding MType)
consLit bnd = do
  ilexe $ char '('
  b <- indent consLit'
  indent $ char ')'
  pure b
  where
    consLit' :: IndentParser String (Binding MType)
    consLit' = do
      b <- ilexe $ bnd
      indent $ char ':'
      bs <- (PC.try $ indent consLit') <|> (indent bnd)
      pure $ ConsLit Nothing b bs

listLit :: IndentParser String (Binding MType) -> IndentParser String (Binding MType)
listLit bnd = do
  ilexe $ char '['
  bs <- (indent bnd) `PC.sepBy` (PC.try $ indent $ char ',')
  indent $ char ']'
  pure $ ListLit Nothing bs

tupleLit :: IndentParser String (Binding MType) -> IndentParser String (Binding MType)
tupleLit bnd = do
  ilexe $ char '('
  b <- indent bnd
  indent $ char ','
  bs <- (indent bnd) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ')'
  pure $ NTupleLit Nothing (Cons b bs)

binding :: IndentParser String (Binding MType)
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

---------------------------------------------------------
-- Parsers for Types
---------------------------------------------------------

types :: IndentParser String Type
types = (TypVar <$> ilexe name)

---------------------------------------------------------
-- Parsers for Type Definitions
---------------------------------------------------------

typeDefinition :: IndentParser String ADTDef
typeDefinition = do
  ilexe $ string "data"
  n <- ilexe typeName
  tvs <- many $ ilexe name
  conss <- (do PC.try (indent $ char '=')
               indent dataConstructorDefinition `PC.sepBy` (PC.try $ indent $ ilexe $ char '|'))
           <|> pure Nil
  pure $ ADTDef n tvs conss

dataConstructorDefinition :: IndentParser String (DataCons Type)
dataConstructorDefinition
  = PC.try prefixDataConstructorDefinition
  <|> infixDataConstructorDefinition

prefixDataConstructorDefinition :: IndentParser String (DataCons Type)
prefixDataConstructorDefinition = do
  n <- ilexe typeName
  ps <- many types
  pure $ PrefixCons n (length ps) ps

infixDataConstructorDefinition :: IndentParser String (DataCons Type)
infixDataConstructorDefinition = do
  l <- types
  o <- indent $ ilexe infixConstructor
  r <- types
  pure $ InfixCons ASSOC o l r


infixConstructor :: forall m. (Monad m) => ParserT String m String
infixConstructor = do
  char ':'
  syms <- many symbol
  pure $ String.fromCharArray $ Array.fromFoldable $ Cons ':' syms
