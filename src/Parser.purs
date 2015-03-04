module Parser where

import Global              (readInt)
import Data.String         (joinWith, split)
import Data.Identity       (Identity())
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

num :: Parser String Atom
num = do
  sign <- option "" (string "-")
  eatSpaces
  str <- string "0" <|> nat
  return $ Num $ readInt 10 $ sign ++ str
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
  eatSpaces
  num <|> try bool <|> (Name <$> name) <?> "Atom (Number, Boolean, Name)"

list :: Parser String Expr -> Parser String Expr
list expr = do
  string "["
  eatSpaces
  ls <- expr `sepBy` (try (eatSpaces *> string ","))
  eatSpaces
  string "]"
  return $ List ls

app :: Parser String Expr -> Parser String Expr
app expr = do
  str <- name
  exprs <- some (try $ eatSpaces *> expr)
  return $ App str exprs

bracket :: Parser String Expr -> Parser String Expr
bracket expr = do
  string "("
  eatSpaces
  e <- expr
  eatSpaces
  string ")"
  return e

base :: Parser String Expr -> Parser String Expr
base expr = list expr <|> bracket expr <|> (Atom <$> atom)

termApp :: Parser String Expr -> Parser String Expr
termApp expr = try (app (base expr)) <|> base expr

op :: forall a. Parser String a -> Op -> Parser String (Expr -> Expr -> Expr)
op opParser opType = try $
  (eatSpaces *> opParser *> eatSpaces) *> return (Binary opType)

term7l :: Parser String Expr -> Parser String Expr
term7l expr = chainl1 (termApp expr) (mulP <|> divP)
  where
  mulP = op (string "*") Mul
  divP = op (string "`div`") Div

term6l :: Parser String Expr -> Parser String Expr
term6l expr = chainl1 (term7l expr) (addP <|> subP)
  where
  addP = op (string "+" *> notFollowedBy (string "+")) Add
  subP = op (string "-") Sub

term5r :: Parser String Expr -> Parser String Expr
term5r expr = chainr1 (term6l expr) (consP <|> appendP)
  where
  consP = op (string ":") Cons
  appendP = op (string "++") Append

term3r :: Parser String Expr -> Parser String Expr
term3r expr = chainr1 (term5r expr) (op (string "&&") And)

term2r :: Parser String Expr -> Parser String Expr
term2r expr = chainr1 (term3r expr) (op (string "||") Or)

expr :: Parser String Expr
expr = fix1 $ \expr -> term2r expr
