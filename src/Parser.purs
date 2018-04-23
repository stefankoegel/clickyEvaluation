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
-- import Control.Applicative ((<*), (*>))
import Control.Lazy (fix)
import Control.Monad.State (State, StateT, runState, runStateT, get, put, modify, lift)

import Text.Parsing.Parser (ParseError, ParserT, runParserT, fail)
import Text.Parsing.Parser.Combinators as PC
import Text.Parsing.Parser.Expr (OperatorTable, Assoc(AssocRight, AssocNone, AssocLeft), Operator(Infix, Prefix), buildExprParser)
import Text.Parsing.Parser.String (whiteSpace, char, string, oneOf, noneOf, anyChar)
import Text.Parsing.Parser.Token (unGenLanguageDef, upper, digit)
import Text.Parsing.Parser.Language (haskellDef)
import Text.Parsing.Parser.Pos (initialPos, Position)

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
  , compileADTDef
  , Associativity(..)
  , DataConstr(..)
  , Type(..)
  , Meta(..))
import AST as AST
import IndentParser (block, withPos, block1, indented', sameLine)

---------------------------------------------------------
-- Utils
---------------------------------------------------------

type FixedIndentParser s a = IndentParser s a -> IndentParser s a

type IndexingT m a = StateT Int m a

type IndexingParserT s m a = IndexingT (ParserT s m) a

runIndexingT :: forall m a. (Monad m) => IndexingT m a -> m (Tuple a Int)
runIndexingT action = runStateT action 0

type IndentParser s a = IndexingT (ParserT s (State Position)) a

fresh :: forall m. (Monad m) => IndexingT m Int
fresh = do
  i <- get
  modify (\i -> i + 1)
  pure i

freshMeta :: forall m. (Monad m) => ParserT s () Meta
freshMeta = AST.idxMeta <$> fresh

---------------------------------------------------------
-- Helpful combinators
---------------------------------------------------------

-- | @ many1 @ should prabably be inside Text.Parsing.Parser.Combinators
many1' :: forall s m a. (Monad m) => IndexingParserT s m a -> IndexingParserT s m (List a)
many1' p = lift2 Cons p (many p)

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
ilexe p = p <* skipWhite

ilexe' :: forall a m. (Monad m) => IndexingParserT String m a -> IndexingParserT String m a
ilexe' p = p <* lift skipWhite

-- parses <p> if it is on the same line or indented, does NOT change indentation state
indent :: forall a. IndentParser String a -> IndentParser String a
indent p = lift ((sameLine <|> indented') PC.<?> "Missing indentation! Did you type a tab-character?") *> ilexe' p

-- returns the next non whitespace character
lookAhead :: forall m. (Monad m) => ParserT String m Char
lookAhead = PC.lookAhead $ whiteSpace *> anyChar

---------------------------------------------------------
-- Parsers for Primitives
---------------------------------------------------------

symbol :: forall m. (Monad m) => ParserT String m Char
symbol = oneOf
  [':','!','#','$','%','&','*'
  ,'+','.','/','<','>','=','?'
  ,'@','\\','^','|','-','~'
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
upperCaseName :: forall m. (Monad m) => ParserT String m String
upperCaseName = do
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

-- | Parser for data constructors
constructor :: forall m. (Monad m) => ParserT String m Atom
constructor = Constr <$> upperCaseName

-- | Parser for atoms
atom :: forall m. (Monad m) => ParserT String m Atom
atom = int <|> variable <|> bool <|> constructor <|> character

---------------------------------------------------------
-- Parsers for Expressions
---------------------------------------------------------

-- | Table for operator parsers and their AST representation. Sorted by precedence.
infixOperators :: forall m. (Monad m) => Array (Array (Tuple3 (ParserT String m String) (String -> Op) Assoc))
infixOperators =
  [ [ (tuple3 (PC.try infixConstructor) InfixConstr AssocLeft)
    , (tuple3 (PC.try infixFunc) InfixFunc AssocLeft)
    , (tuple3 (PC.try $ string "." <* PC.notFollowedBy (char '.')) (const Composition) AssocRight) ]
  , [ (tuple3 (string "^") (const Power) AssocRight) ]
  , [ (tuple3 (string "*") (const Mul) AssocLeft) ]
  , [ (tuple3 (PC.try $ string "+" <* PC.notFollowedBy (char '+')) (const Add) AssocLeft)
    , (tuple3 (string "-") (const Sub) AssocLeft)
    ]
  , [ (tuple3 (string ":") (const Colon) AssocRight)
    , (tuple3 (string "++") (const Append) AssocRight)
    ]
  , [ (tuple3 (string "==") (const Equ) AssocNone)
    , (tuple3 (string "/=") (const Neq) AssocNone)
    , (tuple3 (PC.try $ string "<" <* PC.notFollowedBy (char '=')) (const Lt) AssocNone)
    , (tuple3 (PC.try $ string ">" <* PC.notFollowedBy (char '=')) (const Gt) AssocNone)
    , (tuple3 (string "<=") (const Leq) AssocNone)
    , (tuple3 (string ">=") (const Geq) AssocNone)
    ]
  , [ (tuple3 (string "&&") (const And) AssocRight) ]
  , [ (tuple3 (string "||") (const Or) AssocRight) ]
  , [ (tuple3 (string "$") (const Dollar) AssocRight) ]
  ]

infixFunc :: forall m. (Monad m) => ParserT String m String
infixFunc = char '`' *> name <* char '`'

-- | Table of operators (math, boolean, ...)
operatorTable :: forall m. (Monad m) => OperatorTable m String TypeTree
operatorTable = maybe [] id (modifyAt 3 (flip snoc unaryMinus) infixTable)
  where
    infixTable :: OperatorTable m String TypeTree
    infixTable =
      (\x ->
        (uncurry3
          (\p op assoc ->
            Infix (do
                  meta <- freshMeta
                  Binary freshMeta <<< toOpTuple <<< op <$> spaced p) assoc))
        <$> x)
      <$> infixOperators

    unaryMinus :: Operator m String TypeTree
    unaryMinus = Prefix $ spaced minusParse
      where 
        minusParse = do
          string "-"
          meta <- freshMeta
          pure $ \e -> case e of
            Atom _ (AInt ai) -> Atom meta (AInt (-ai))
            _                -> Unary meta (toOpTuple Sub) e

    -- | Parse an expression between spaces (backtracks)
    spaced :: forall a. ParserT String m a -> ParserT String m a
    spaced p = PC.try $ PC.between skipSpaces skipSpaces p

opParser :: forall m. (Monad m) => ParserT String m Op
opParser = PC.choice $ (\x -> (uncurry3 (\p op _ -> op <$> p)) <$> x) $ concat $ (\x -> Array.toUnfoldable <$> x) $ Array.toUnfoldable infixOperators

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
  <|> (do
      meta <- freshMeta
      Atom meta <$> atom)

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
    Just args -> do
      meta <- freshMeta
      pure $ App meta e args

-- | Parse an if_then_else construct - layout sensitive
ifThenElse :: IndentParser String TypeTree -> IndentParser String TypeTree
ifThenElse expr = do
  ilexe $ string "if" *> PC.lookAhead (oneOf [' ', '\t', '\n', '('])
  testExpr <- indent expr
  indent $ string "then"
  thenExpr <- indent expr
  indent $ string "else"
  elseExpr <- indent expr
  meta <- freshMeta
  pure $ IfExpr meta testExpr thenExpr elseExpr

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
    Just es -> do
      meta <- freshMeta
      pure $ NTuple meta (Cons e es)

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
    Nothing -> do
      meta <- freshMeta
      case me2 of
        Nothing -> pure $ PrefixOp meta op
        Just e2 -> pure $ SectR meta op e2
    Just e1 ->
      case me2 of
        Nothing -> do
          meta <- freshMeta
          pure $ SectL meta e1 op
        Just _ -> fail "Cannot have a section with two expressions!"

-- | Parser for lists - layout sensitive
list :: IndentParser String TypeTree -> IndentParser String TypeTree
list expr = do
  ilexe $ char '['
  exprs <- (indent expr) `PC.sepBy` (PC.try $ indent $ char ',')
  indent $ char ']'
  meta <- freshMeta
  pure $ List meta exprs

-- | Parser for Arithmetic Sequences - layout sensitive
arithmeticSequence :: IndentParser String TypeTree -> IndentParser String TypeTree
arithmeticSequence expr = do
  ilexe $ char '['
  start <- indent expr
  step  <- PC.optionMaybe $ (indent $ char ',') *> (indent expr)
  indent $ string ".."
  end   <- PC.optionMaybe $ indent expr
  indent $ char ']'
  meta <- freshMeta
  pure $ ArithmSeq meta start step end

-- | Parser for list comprehensions - layout sensitive
listComp :: IndentParser String TypeTree -> IndentParser String TypeTree
listComp expr = do
  ilexe $ char '['
  start <- indent expr
  PC.try $ (char '|') *> PC.notFollowedBy (char '|')
  skipWhite
  quals <- (indent $ qual expr) `PC.sepBy1` (PC.try $ indent $ char ',')
  indent $ char ']'
  meta <- freshMeta
  pure $ ListComp meta start quals
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
          meta <- freshMeta
          pure $ Let meta b e
        parseGen = do
          b <- ilexe binding
          indent $ string "<-"
          e <- indent expr
          meta <- freshMeta
          pure $ Gen meta b e
        parseGuard = do
          meta <- freshMeta
          expr' <- ilexe expr
          pure $ Guard meta expr'

-- | Parser for strings ("example")
charList :: forall m. (Monad m) => ParserT String m TypeTree
charList = do
  char '"'
  strs <- many character'
  char '"'
  meta1 <- freshMeta
  meta2 <- freshMeta
  pure (List meta1 ((Atom meta2 <<< Char <<< String.singleton) <$> strs))

-- | Parse a lambda expression - layout sensitive
lambda :: IndentParser String TypeTree -> IndentParser String TypeTree
lambda expr = do
  ilexe $ char '\\'
  binds <- many1 $ indent binding
  indent $ string "->"
  body <- indent expr
  meta <- freshMeta
  pure $ Lambda meta binds body

-- Parser for let expressions - layout sensitive
letExpr :: IndentParser String TypeTree -> IndentParser String TypeTree
letExpr expr = do
  ilexe $ string "let"
  binds <- indent $ bindingBlock expr
  indent $ string "in"
  body  <- indent $ withPos expr
  meta <- freshMeta
  pure $ LetExpr meta binds body
  where
    bindingItem :: IndentParser String TypeTree -> IndentParser String (Tuple (Binding Meta) TypeTree)
    bindingItem expr = do
      b <- ilexe binding
      indent $ char '='
      e <- indent $ withPos expr
      pure $ Tuple b e

    bindingBlock :: IndentParser String TypeTree -> IndentParser String (List (Tuple (Binding Meta) TypeTree))
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

runParserIndent :: forall a. IndentParser String a -> String -> Either ParseError (Tuple a Int)
runParserIndent p src = fst $ flip runState initialPos $ runParserT src $ runIndexingT p

parseExpr :: String -> Either ParseError TypeTree
parseExpr = runParserIndent expression

---------------------------------------------------------
-- Parsers for Bindings
---------------------------------------------------------
-- Grammar
----------
{-
<BINDING>
  ::= <SIMPLE>
    | `[` <LIST> `]`
    | `(` <LIST> `)`

<SIMPLE>
  ::= <LIT>

<LIST>
  ::= <CONSES> { `,` <CONSES> }

<CONSES>
  ::= <INFIXES> { `:` <INFIXES> }

<INFIXES>
  ::= { <COMPLEX> <INF_CONSTR> } <COMPLEX>

<COMPLEX>
  ::= <CONSTR> { <BINDING> }
    | <BINDING>
-}


binding :: IndentParser String (Binding Meta)
binding = do
  whiteSpace
  fix $ \bnd -> do
    la <- lookAhead
    case la of
         '(' -> do
            cs <- ilexe (char '(') *> indent (bndList bnd) <* indent (char ')')
            case cs of
                 Nil        -> NTupleLit <$> freshMeta <*> pure Nil
                 Cons c Nil -> pure c
                 cs'        -> NTupleLit <$> freshMeta <*> pure cs'
         '[' -> do
            cs <- ilexe (char '[') *> indent (bndList bnd) <* indent (char ']')
            case cs of
                 Nil        -> ListLit <$> freshMeta <*> pure Nil
                 cs'        -> ListLit <$> freshMeta <*> pure cs'
         _   -> PC.try $ ilexe bndSimple


bndSimple :: IndentParser String (Binding Meta)
bndSimple = PC.try bndLit

bndLit :: forall m. (Monad m) => ParserT String m (Binding Meta)
bndLit = Lit <$> freshMeta <*> atom

bndList :: IndentParser String (Binding Meta) -> IndentParser String (List (Binding Meta))
bndList bnd = PC.sepBy
  (PC.try <<< indent <<< bndConses $ bnd)
  (PC.try <<< indent <<< char $ ',')

bndConses :: FixedIndentParser String (Binding Meta)
bndConses bnd = PC.chainr1
  (PC.try <<< ilexe <<< bndInfixes $ bnd)
  (do PC.try <<< indent <<< char $ ':'
      ConsLit <$> freshMeta)

bndInfixes :: FixedIndentParser String (Binding Meta)
bndInfixes bnd = PC.chainl1
  (PC.try (ilexe ((bndComplex bnd))))
  (do o <- PC.try (indent infixConstructor)
      meta <- freshMeta
      pure (\l r -> ConstrLit meta (InfixDataConstr o LEFTASSOC 9 l r)))

bndComplex :: FixedIndentParser String (Binding Meta)
bndComplex bnd =
  PC.try
    (do n  <- ilexe upperCaseName
        as <- many1 bnd
        meta <- freshMeta
        pure $ ConstrLit meta (PrefixDataConstr n (length as) as))
  <|> indent bnd

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

typeDefinition' :: IndentParser String (List Definition)
typeDefinition' = compileADTDef <$> typeDefinition

-- TODO: Infix function definition

definitions :: IndentParser String (List Definition)
definitions = do
  skipWhite
  defs <- many $ (PC.try typeDefinition') <|> (pure <$> definition)
  pure $ concat defs

  

parseDefs :: String -> Either ParseError (List Definition)
parseDefs = runParserIndent $ definitions

---------------------------------------------------------
-- Parsers for Types
---------------------------------------------------------
-- Grammar
----------
{-
<TYPE>
  ::= <TYPE1> [ `->` <TYPE> ]

<TYPE1>
  ::= <SIMPLE>
    | `[` <TYPE> `]`
    | `(` <TYPE> { `,` <TYPE> } `)`
    | <CONS> { <TYPE> }

<SIMPLE>
  ::= `Int` | `Bool` | `Char` | <TYPEVAR>
-}


type1 :: FixedIndentParser String Type
type1 t = do
  la <- lookAhead
  case la of
       '(' -> do
          ts <- PC.between
            (PC.try <<< ilexe <<< char $ '(')
            (PC.try <<< indent <<< char $ ')')
            (indent t `PC.sepBy1` (PC.try <<< indent <<< char) ',')
          case ts of
               Nil         -> fail "Empty Tuple"
               Cons t' Nil -> pure t'
               ts'         -> (pure <<< TTuple) ts'
       '[' -> PC.between
          (PC.try <<< ilexe <<< char $ '[')
          (PC.try <<< indent <<< char $ ']')
          (TList <$> indent t)
       _ -> (PC.try <<< indent) simpleType <|> (indent <<< typeCons) t

simpleType :: IndentParser String Type
simpleType = do
  la <- lookAhead
  case la of
       'B' -> TypCon <$> string "Bool"
       'I' -> TypCon <$> string "Int"
       'C' -> TypCon <$> string "Char"
       _   -> TypVar <$> name

typeCons :: IndentParser String Type -> IndentParser String Type
typeCons t = do
  n <- ilexe upperCaseName
  ps <- many <<< indent $ types1 t <|> simpleType
  pure $ TTypeCons n ps

typeExpr :: IndentParser String Type -> IndentParser String Type
typeExpr t = PC.between
  (indent <<< lift <<< PC.try <<< char $ '(')
  (indent <<< lift <<< PC.try <<< char $ ')')
  (indent t)

types :: IndentParser String Type
types = do
  whiteSpace
  fix $ \t -> (indent <<< type1) t `PC.chainr1` ((indent <<< string) "->" *> pure TypArr)

typeTuple :: IndentParser String Type -> IndentParser String Type
typeTuple t = PC.between
  (ilexe <<< char $ '(')
  (PC.try <<< indent <<< char $ ')')
  (do ts <- indent t `PC.sepBy1` (PC.try <<< indent <<< char) ','
      case ts of
           Nil        -> fail "Empty Tuple"
           Cons x Nil -> pure x
           xs         -> (pure <<< TTuple) xs)

types1 :: IndentParser String Type -> IndentParser String Type
types1 t = do
  la <- lookAhead
  case la of
       '[' -> TList <$> ((ilexe <<< char) '[' *> indent t <* (indent <<< char) ']')
       '(' -> PC.try (typeExpr t) <|> typeTuple t
       _   -> PC.try simpleType <|> typeCons t


---------------------------------------------------------
-- Parsers for Type Definitions
---------------------------------------------------------
-- Grammar
----------
{-
<TYPEDEFINITION>
  ::= 'data' <UCASENAME> { <NAME> } [ '=' <CONSTR> { '|' <CONSTR> } ]

<CONSTR>
  ::= <PREFIXCONSTR>
    | <INFIXCONSTR>

<PREFIXCONSTR>
  ::= <UCASENAME> { <TYPE> }
    | <TYPE> <CONSTROP> <TYPE>

<CONSTROP>
  ::= ':' <SYMBOL> { <SYMBOL> }       (* at least one symbol after ':' is needed,
                                       * to no confuse it with a list-(:).
                                       *)
-}


typeDefinition :: IndentParser String ADTDef
typeDefinition = do
  ilexe $ string "data"
  n <- indent upperCaseName
  tvs <- many $ indent name
  conss <- (do PC.try (indent $ char '=')
               indent dataConstructorDefinition `PC.sepBy` (PC.try $ indent $ char '|'))
           <|> pure Nil
  pure $ ADTDef n tvs conss

dataConstructorDefinition :: IndentParser String (DataConstr Type)
dataConstructorDefinition
  = PC.try prefixDataConstrtructorDefinition
  <|> infixDataConstrtructorDefinition

prefixDataConstrtructorDefinition :: IndentParser String (DataConstr Type)
prefixDataConstrtructorDefinition = do
  n <- ilexe upperCaseName
  ps <- many types
  pure $ PrefixDataConstr n (length ps) ps

infixDataConstrtructorDefinition :: IndentParser String (DataConstr Type)
infixDataConstrtructorDefinition = do
  l <- ilexe types
  o <- indent $ ilexe infixConstructor
  r <- indent $ ilexe types
  pure $ InfixDataConstr o LEFTASSOC 9 l r


infixConstructor :: forall m. (Monad m) => ParserT String m String
infixConstructor = do
  char ':'
  syms <- many1 symbol
  pure $ String.fromCharArray $ Array.fromFoldable $ Cons ':' syms
