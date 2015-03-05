module Parser where

import Global              (readInt)
import Data.String         (joinWith, split)
import Data.Identity       (Identity())
import Data.Maybe
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
  f = string "false" *> return (Bool false)
  t = string "true" *> return (Bool true)

name :: Parser String String
name = do
  str <- some $ oneOf $ split "" "_abcdefghijklmnopqrstuvwxyz'"
  return $ joinWith "" str

atom :: Parser String Atom
atom = do
  num <|> try bool <|> (Name <$> name) <?> "Atom (Number, Boolean, Name)"

---------------------------------------
-- Parsers for the 'Expr' type
---------------------------------------

list :: forall a. Parser String a -> Parser String [a]
list p = do
  string "["
  eatSpaces
  ls <- p `sepBy` (try (eatSpaces *> string ","))
  eatSpaces
  string "]"
  return ls

app :: Parser String Expr -> Parser String Expr
app expr = do
  str <- name
  exprs <- some (try $ eatSpaces *> expr)
  return $ App str exprs

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
  [ opP (string "+" *> notFollowedBy (string "+")) Add
  , opP (string "-" *> notFollowedBy (eatSpaces *> num)) Sub
  , opP (string "*")     Mul
  , opP (string "`div`") Div
  , opP (string ":")     Cons
  , opP (string "++")    Append
  , opP (string "&&")    And
  , opP (string "||")    Or
  ]

base :: Parser String Expr -> Parser String Expr
base expr =  (List <$> list expr)
         <|> bracket expr
         <|> (Atom <$> atom)

termSect :: Parser String Expr -> Parser String Expr
termSect expr = try (section (base expr)) <|> base expr

termApp :: Parser String Expr -> Parser String Expr
termApp expr = try (app (termSect expr)) <|> termSect expr

opP :: forall a. Parser String a -> Op -> Parser String Op
opP strP opConstructor = try $
  (eatSpaces *> strP *> eatSpaces *> return opConstructor)

term7l :: Parser String Expr -> Parser String Expr
term7l expr = chainl1 (termApp expr) (mulP <|> divP)
  where
  mulP = Binary <$> opP (string "*") Mul
  divP = Binary <$> opP (string "`div`") Div

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

term3r :: Parser String Expr -> Parser String Expr
term3r expr = chainr1 (term5r expr) (Binary <$> opP (string "&&") And)

term2r :: Parser String Expr -> Parser String Expr
term2r expr = chainr1 (term3r expr) (Binary <$> opP (string "||") Or)

expr :: Parser String Expr
expr = fix1 $ \expr -> term2r expr

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

binding :: Parser String Binding
binding = fix1 $ \binding -> lit <|> consLit binding <|> listLit binding

---------------------------------------
-- Parsers for the 'Definition' type
---------------------------------------

def :: Parser String Definition
def = do
  defName <- name
  eatSpaces
  binds <- binding `sepEndBy` eatSpaces
  string "="
  eatSpaces
  body <- expr
  return $ Def defName binds body
