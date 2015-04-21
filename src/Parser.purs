module Parser where

import Global              (readInt)
import Data.String         (joinWith, split)
import Data.Identity       (Identity())
import Data.Either
import Control.Alt         ((<|>))
import Control.Apply       ((*>))
import Control.Alternative (some, many)
import Control.Lazy        (fix1)

import Text.Parsing.Parser
import Text.Parsing.Parser.Combinators
import Text.Parsing.Parser.String

import AST

eatSpaces :: Parser String Unit
eatSpaces = void $ many $ string " " <|> string "\t"

parse :: forall a. Parser String a -> String -> Either String a
parse p s = case runParser s p of
  Left err -> Left $ show err
  Right a  -> Right a

---------------------------------------
-- Parsers for the 'Atom' type
---------------------------------------

num :: Parser String Atom
num = do
  str <- string "0" <|> nat
  return $ Num $ readInt 10 str
  where
  nat = do
    d <- oneOf $ split "" "123456789"
    ds <- many $ oneOf $ split "" "0123456789"
    return $ joinWith "" $ d:ds

bool :: Parser String Atom
bool = do
  f <|> t
  where
  f = string "False" *> return (Bool false)
  t = string "True" *> return (Bool true)

char_ :: Parser String Atom
char_ = Char <$> choice [ string "\\\\" *> return "\\"
--                        , string "\\n"  *> return "\n"
--                        , string "\\r"  *> return "\r"
--                        , string "\\t"  *> return "\t"
                        , string "\\\""  *> return "\""
                        , char
                        ]


character :: Parser String Atom
character = between (string "'") (string "'") char_

name :: Parser String String
name = do
  str <- joinWith "" <$> (some $ oneOf $ split "" "_abcdefghijklmnopqrstuvwxyz'")
  if str == "if" || str == "then" || str == "else"
    then fail $ "Trying to match reserved keyword: " ++ str
    else return str

atom :: Parser String Atom
atom = do
  num <|> try bool <|> character <|> (Name <$> name) <?> "Atom (Number, Boolean, Name)"

---------------------------------------
-- Parsers for the 'Expr' type
---------------------------------------

parseExpr :: String -> Either String Expr
parseExpr = parse (eatSpaces *> expr)

list :: forall a. Parser String a -> Parser String [a]
list p = do
  string "["
  eatSpaces
  ls <- p `sepBy` (try (eatSpaces *> string "," *> eatSpaces))
  eatSpaces
  string "]"
  return ls

stringList :: Parser String [Atom]
stringList = do
  string "\""
  char_ `manyTill` (string "\"")

app :: Parser String Expr -> Parser String Expr
app expr = do
  func <- expr
  exprs <- some (try $ eatSpaces *> expr)
  return $ App func exprs

bracket :: forall a. Parser String a -> Parser String a
bracket p = do
  string "("
  eatSpaces
  e <- p
  eatSpaces
  string ")"
  return e

section :: Parser String Expr -> Parser String Expr
section expr = bracket (try sectR <|> sectL)
  where
  sectR = do
    op <- choice opList
    eatSpaces
    e <- expr
    return $ SectR op e
  sectL = do
    e <- expr
    eatSpaces
    op <- choice opList
    return $ SectL e op

opList :: [Parser String Op]
opList =
  [ opP (string ".")     Composition
  , opP (string "^")     Power
  , opP (string "*")     Mul
  , opP (try $ string "`div`") Div
  , opP (string "`mod`") Mod
  , opP (string "+" *> notFollowedBy (string "+")) Add
  , opP (string "-" *> notFollowedBy (eatSpaces *> num)) Sub
  , opP (string ":")     Cons
  , opP (string "++")    Append
  , opP (string "==")    Eq
  , opP (string "/=")    Neq
  , opP (string "<=")    Leq
  , opP (string "<")     Lt
  , opP (string ">=")    Geq
  , opP (string ">")     Gt
  , opP (string "&&")    And
  , opP (string "||")    Or
  , opP (string "$")     Dollar
  ]

prefixOp :: Parser String Expr
prefixOp = bracket $ Prefix <$> choice opList

sepBy2 :: forall m s a sep. (Monad m) => ParserT s m a -> ParserT s m sep -> ParserT s m [a]
sepBy2 p sep = do
  a <- p
  as <- some $ do
    sep
    p
  return (a:as)

tuple :: forall a. Parser String a -> Parser String [a]
tuple expr = bracket $ expr `sepBy2` (try (eatSpaces *> string "," *> eatSpaces))

base :: Parser String Expr -> Parser String Expr
base expr =  (List <$> list expr)
         <|> ((List <<< (Atom <$>)) <$> stringList)
         <|> bracket expr
         <|> (Atom <$> atom)

lambda :: Parser String Expr -> Parser String Expr
lambda expr = bracket $ do
  string "\\"
  eatSpaces
  binds <- binding `sepEndBy` eatSpaces
  string "->"
  eatSpaces
  body <- expr
  return $ Lambda binds body

ifthenelse :: Parser String Expr -> Parser String Expr
ifthenelse expr = do
  string "if" *> eatSpaces
  condition <- expr
  eatSpaces *> string "then" *> eatSpaces
  thenPart <- expr
  eatSpaces *> string "else" *> eatSpaces
  elsePart <- expr
  return $ IfExpr condition thenPart elsePart

termNTuple :: Parser String Expr -> Parser String Expr
termNTuple expr = try (NTuple <$> tuple expr) <|> base expr

termLambda :: Parser String Expr -> Parser String Expr
termLambda expr = try (lambda expr) <|> termNTuple expr

termPrefixOp :: Parser String Expr -> Parser String Expr
termPrefixOp expr = try prefixOp <|> termLambda expr

termSect :: Parser String Expr -> Parser String Expr
termSect expr = try (section (termPrefixOp expr)) <|> termPrefixOp expr

termIf :: Parser String Expr -> Parser String Expr
termIf expr = try (ifthenelse expr) <|> termSect expr

termApp :: Parser String Expr -> Parser String Expr
termApp expr = try (app (termIf expr)) <|> termIf expr

opP :: forall a. Parser String a -> Op -> Parser String Op
opP strP opConstructor = try $
  (eatSpaces *> strP *> eatSpaces *> return opConstructor)

term9r :: Parser String Expr -> Parser String Expr
term9r expr = chainr1 (termApp expr) (Binary <$> opP (string ".") Composition)

term8r :: Parser String Expr -> Parser String Expr
term8r expr = chainr1 (term9r expr) (Binary <$> opP (string "^") Power)

term7l :: Parser String Expr -> Parser String Expr
term7l expr = chainl1 (term8r expr) (mulP <|> try divP <|> modP)
  where
  mulP = Binary <$> opP (string "*") Mul
  divP = Binary <$> opP (string "`div`") Div
  modP = Binary <$> opP (string "`mod`") Mod

term6neg :: Parser String Expr -> Parser String Expr
term6neg expr = try negation <|> (term7l expr)
  where
  negation = do
    string "-"
    eatSpaces
    e <- (term7l expr)
    return $ Unary Sub e

term6l :: Parser String Expr -> Parser String Expr
term6l expr = chainl1 (term6neg expr) (addP <|> subP)
  where
  addP = Binary <$> opP (string "+" *> notFollowedBy (string "+")) Add
  subP = Binary <$> opP (string "-") Sub

term5r :: Parser String Expr -> Parser String Expr
term5r expr = chainr1 (term6l expr) (consP <|> appendP)
  where
  consP = Binary <$> opP (string ":") Cons
  appendP = Binary <$> opP (string "++") Append

term4 :: Parser String Expr -> Parser String Expr
term4 expr = try comparison <|> term5r expr
  where
  comparison = do
    e1 <- term5r expr
    op <- choice [eq, neq, leq, lt, geq, gt]
    e2 <- term5r expr
    return $ Binary op e1 e2
  eq  = opP (string "==") Eq
  neq = opP (string "/=") Neq
  leq = opP (string "<=") Leq
  lt  = opP (string "<")  Lt
  geq = opP (string ">=") Geq
  gt  = opP (string ">")  Gt

term3r :: Parser String Expr -> Parser String Expr
term3r expr = chainr1 (term4 expr) (Binary <$> opP (string "&&") And)

term2r :: Parser String Expr -> Parser String Expr
term2r expr = chainr1 (term3r expr) (Binary <$> opP (string "||") Or)

term0r :: Parser String Expr -> Parser String Expr
term0r expr = chainr1 (term2r expr) (Binary <$> opP (string "$") Dollar)

expr :: Parser String Expr
expr = fix1 $ \expr -> term0r expr

---------------------------------------
-- Parsers for the 'Binding' type
---------------------------------------

lit :: Parser String Binding
lit = Lit <$> atom

listLit :: Parser String Binding -> Parser String Binding
listLit binding = ListLit <$> list binding

consLit :: Parser String Binding -> Parser String Binding
consLit binding = bracket recurse
  where
  recurse = fix1 $ \recurse -> try (cons recurse) <|> binding
  cons recurse = do
    b <- binding
    eatSpaces
    string ":"
    eatSpaces
    bs <- recurse
    return $ ConsLit b bs

tupleLit :: Parser String Binding -> Parser String Binding
tupleLit binding = NTupleLit <$> tuple binding

binding :: Parser String Binding
binding = fix1 $ \binding -> lit <|> try (consLit binding) <|> tupleLit binding <|> listLit binding

---------------------------------------
-- Parsers for the 'Definition' type
---------------------------------------

parseDefs :: String -> Either String [Definition]
parseDefs = parse (skipSpaces *> defs)

def :: Parser String Definition
def = do
  defName <- name
  eatSpaces
  binds <- binding `sepEndBy` eatSpaces
  string "="
  eatSpaces
  body <- expr
  return $ Def defName binds body

defs :: Parser String [Definition]
defs = def `sepEndBy` skipSpaces
