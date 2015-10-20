module Parser where

import Prelude
import Global              (readInt)
import Data.Int (floor)
import qualified Data.String as Str
import Data.List (fromList, List(Cons, Nil), concat)
import qualified Data.Array as Arr
-- import Data.Identity       (Identity())
import Data.Either
import Data.Foldable
import Control.Alt         ((<|>))
import Control.Apply       ((*>))

import Text.Parsing.StringParser
import Text.Parsing.StringParser.Combinators
import Text.Parsing.StringParser.String

import AST

---------------------------------------
-- Parsers for the 'Atom' type
---------------------------------------

-- | Transforms a list of characters to a string.
listToString :: List Char -> String
listToString = Str.fromCharArray <<< fromList

-- | Parses a decimal `Int`. (Leading zeroes are allowed)
aint :: Parser Atom
aint = (AInt <<< floor <<< readInt 10 <<< listToString) <$> many1 anyDigit

-- | Parses `True` or `False`.
bool :: Parser Atom
bool = do
  f <|> t
  where
  f = string "False" *> return (Bool false)
  t = string "True"  *> return (Bool true)

-- | Parses one character and handles some escape sequences.
escapedChar :: Parser String
escapedChar = choice 
                 [ string "\\\\" *> return "\\"
                 , string "\\n"  *> return "\n"
                 , string "\\r"  *> return "\r"
                 , string "\\t"  *> return "\t"
                 , string "\\\"" *> return "\""
                 , string "\\\"" *> return "\'"
                 , Str.singleton <$> anyChar
                 ]

-- | Parses one character between apostrophes.
character :: Parser Atom
character = Char <$> between (string "'") (string "'") escapedChar

-- | List of lower case letters that are allowed as first characters in a variable names.
lowerCaseLetters :: Array Char
lowerCaseLetters =
  [ '_'
  , 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's'
  , 't', 'u', 'v', 'w', 'x', 'y', 'z'
  ]

-- | List of upper case letters that are allowed as first characters in type and constructor names.
upperCaseLetters :: Array Char
upperCaseLetters =
  [ 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S'
  , 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'
  ]

-- | List of all letters that can be used in names.
allLetters :: Array Char
allLetters = Arr.concat [lowerCaseLetters, upperCaseLetters, ['\'']]

-- | Parses the name of a variable and contains a `String`.
varName :: Parser String
varName = do
  first <- oneOf lowerCaseLetters
  rest  <- many1 $ oneOf allLetters
  return $ listToString $ Cons first rest

-- | Parses an `Atom`.
atom :: Parser Atom
atom = do
  aint <|> try bool <|> character <|> (Name <$> varName) <?> "Atom (Int, Boolean, Char, Variable name)"

---------------------------------------
-- Parsers for the 'Expr' type
---------------------------------------

-- | Parses a list of elements between square brackets and separated by commas.
list :: forall a. Parser a -> Parser (List a)
list p = do
  string "["
  skipSpaces
  ls <- p `sepBy` (try (skipSpaces *> string "," *> skipSpaces))
  skipSpaces
  string "]"
  return ls

-- | 
app :: Parser Expr -> Parser Expr
app expr = do
  func <- expr
  exprs <- many1 (try $ skipSpaces *> expr)
  return $ App func exprs

bracket :: forall a. Parser a -> Parser a
bracket p = do
  string "("
  skipSpaces
  e <- p
  skipSpaces
  string ")"
  return e

section :: Parser Expr -> Parser Expr
section expr = bracket (try sectR <|> sectL)
  where
  sectR = do
    op <- choice opList
    skipSpaces
    e <- expr
    return $ SectR op e
  sectL = do
    e <- expr
    skipSpaces
    op <- choice opList
    return $ SectL e op

opList :: Array (Parser Op)
opList =
  [ opP (string ".")     Composition
  , opP (string "^")     Power
  , opP (string "*")     Mul
  , opP (try $ string "`div`") Div
  , opP (string "`mod`") Mod
  , opP (string "++")    Append
  , opP (string "+")     Add
  , opP (string "-")     Sub
  , opP (string ":")     Colon
  , opP (string "==")    Equ
  , opP (string "/=")    Neq
  , opP (string "<=")    Leq
  , opP (string "<")     Lt
  , opP (string ">=")    Geq
  , opP (string ">")     Gt
  , opP (string "&&")    And
  , opP (string "||")    Or
  , opP (string "$")     Dollar
  ]

prefixOp :: Parser Expr
prefixOp = bracket $ Prefix <$> choice opList

tuple :: forall a. Parser a -> Parser (List a)
tuple expr = bracket $ expr `sepBy` (try (skipSpaces *> string "," *> skipSpaces)) -- TODO sepby2

-- | Parses a string between quotation marks
quotedString :: Parser (List Expr)
quotedString = do
  string "\""
  str <- escapedChar `manyTill` (string "\"")
  return $ (Atom <<< Char) <$> str

base :: Parser Expr -> Parser Expr
base expr =  (List <$> list expr)
         <|> List <$> quotedString
         <|> bracket expr
         <|> (Atom <$> atom)

lambda :: Parser Expr -> Parser Expr
lambda expr = bracket $ do
  string "\\"
  skipSpaces
  binds <- binding `sepEndBy` skipSpaces
  string "->"
  skipSpaces
  body <- expr
  return $ Lambda binds body

ifthenelse :: Parser Expr -> Parser Expr
ifthenelse expr = do
  string "if" *> skipSpaces
  condition <- expr
  skipSpaces *> string "then" *> skipSpaces
  thenPart <- expr
  skipSpaces *> string "else" *> skipSpaces
  elsePart <- expr
  return $ IfExpr condition thenPart elsePart

termNTuple :: Parser Expr -> Parser Expr
termNTuple expr = try (NTuple <$> tuple expr) <|> base expr

termLambda :: Parser Expr -> Parser Expr
termLambda expr = try (lambda expr) <|> termNTuple expr

termPrefixOp :: Parser Expr -> Parser Expr
termPrefixOp expr = try prefixOp <|> termLambda expr

termSect :: Parser Expr -> Parser Expr
termSect expr = try (section (termPrefixOp expr)) <|> termPrefixOp expr

termIf :: Parser Expr -> Parser Expr
termIf expr = try (ifthenelse expr) <|> termSect expr

termApp :: Parser Expr -> Parser Expr
termApp expr = try (app (termIf expr)) <|> termIf expr

opP :: forall a. Parser a -> Op -> Parser Op
opP strP opConstructor = try $
  (skipSpaces *> strP *> skipSpaces *> return opConstructor)

term9r :: Parser Expr -> Parser Expr
term9r expr = chainr1 (termApp expr) (Binary <$> opP (string ".") Composition)

term8r :: Parser Expr -> Parser Expr
term8r expr = chainr1 (term9r expr) (Binary <$> opP (string "^") Power)

term7l :: Parser Expr -> Parser Expr
term7l expr = chainl1 (term8r expr) (mulP <|> try divP <|> modP)
  where
  mulP = Binary <$> opP (string "*") Mul
  divP = Binary <$> opP (string "`div`") Div
  modP = Binary <$> opP (string "`mod`") Mod

term6neg :: Parser Expr -> Parser Expr
term6neg expr = try negation <|> (term7l expr)
  where
  negation = do
    string "-"
    skipSpaces
    e <- (term7l expr)
    return $ Unary Sub e

term6l :: Parser Expr -> Parser Expr
term6l expr = chainl1 (term6neg expr) (addP <|> subP)
  where
  addP = Binary <$> opP (string "+") Add
  subP = Binary <$> opP (string "-") Sub

term5r :: Parser Expr -> Parser Expr
term5r expr = chainr1 (term6l expr) (consP <|> appendP)
  where
  consP = Binary <$> opP (string ":") Colon
  appendP = Binary <$> opP (string "++") Append

term4 :: Parser Expr -> Parser Expr
term4 expr = try comparison <|> term5r expr
  where
  comparison = do
    e1 <- term5r expr
    op <- choice [eq, neq, leq, lt, geq, gt]
    e2 <- term5r expr
    return $ Binary op e1 e2
  eq  = opP (string "==") Equ
  neq = opP (string "/=") Neq
  leq = opP (string "<=") Leq
  lt  = opP (string "<")  Lt
  geq = opP (string ">=") Geq
  gt  = opP (string ">")  Gt

term3r :: Parser Expr -> Parser Expr
term3r expr = chainr1 (term4 expr) (Binary <$> opP (string "&&") And)

term2r :: Parser Expr -> Parser Expr
term2r expr = chainr1 (term3r expr) (Binary <$> opP (string "||") Or)

term0r :: Parser Expr -> Parser Expr
term0r expr = chainr1 (term2r expr) (Binary <$> opP (string "$") Dollar)

expression :: Parser Expr
expression = fix $ \expr -> term0r expr

lit :: Parser Binding
lit = Lit <$> atom

listLit :: Parser Binding -> Parser Binding
listLit binds = ListLit <$> list binds 

consLit :: Parser Binding -> Parser Binding
consLit binds = do
  string "("
  skipSpaces
  b <-binds 
  skipSpaces
  string ":"
  skipSpaces
  bs <-binds 
  skipSpaces
  string ")"
  return $ ConsLit b bs
-- TODO: handle (x:y:zs)

tupleLit :: Parser Binding -> Parser Binding
tupleLit binds = NTupleLit <$> tuple binds 

binding :: Parser Binding
binding = fix $ \binds -> lit <|> try (consLit binds) <|> tupleLit binds <|> listLit binds 

---------------------------------------
-- Parsers for the 'Definition' type
---------------------------------------

def :: Parser Definition
def = do
  defName <- varName
  skipSpaces
  binds <- binding `sepEndBy` skipSpaces
  string "="
  skipSpaces
  body <- expression
  return $ Def defName binds body

defs :: Parser (List Definition)
defs = def `sepEndBy` skipSpaces
