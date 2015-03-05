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
section expr = do
  mop1 <- optionMaybe $ choice ops
  eatSpaces
  e <- optionMaybe $ base expr
  eatSpaces
  mop2 <- optionMaybe $ choice ops
  match mop1 e mop2
  where
  match (Just op) (Just e)  (Nothing) = return $ SectR op e
  match (Nothing) (Just e)  (Just op) = return $ SectL e op
  match (Nothing) (Just e)  (Nothing) = return e
  match (Just op) (Nothing) (Nothing) = return $ (App (show op) [])
  match _         _         _         = fail "Neither section nor expression!"
  ops =
    [ op (string "+" *> notFollowedBy (string "+")) Add
    , op (string "-" *> notFollowedBy num) Sub
    , op (string "*")     Mul
    , op (string "`div`") Div
    , op (string ":")     Cons
    , op (string "++")    Append
    , op (string "&&")    And
    , op (string "||")    Or
    ]

base :: Parser String Expr -> Parser String Expr
base expr =  (List <$> list expr)
         <|> (bracket $ section expr)
         <|> (Atom <$> atom)

termApp :: Parser String Expr -> Parser String Expr
termApp expr = try (app (base expr)) <|> base expr

op :: forall a. Parser String a -> Op -> Parser String Op
op opParser opConstructor = try $
  (eatSpaces *> opParser *> eatSpaces *> return opConstructor)

term7l :: Parser String Expr -> Parser String Expr
term7l expr = chainl1 (termApp expr) (mulP <|> divP)
  where
  mulP = Binary <$> op (string "*") Mul
  divP = Binary <$> op (string "`div`") Div

term6l :: Parser String Expr -> Parser String Expr
term6l expr = chainl1 (term7l expr) (addP <|> subP)
  where
  addP = Binary <$> op (string "+" *> notFollowedBy (string "+")) Add
  subP = Binary <$> op (string "-") Sub

term5r :: Parser String Expr -> Parser String Expr
term5r expr = chainr1 (term6l expr) (consP <|> appendP)
  where
  consP = Binary <$> op (string ":") Cons
  appendP = Binary <$> op (string "++") Append

term3r :: Parser String Expr -> Parser String Expr
term3r expr = chainr1 (term5r expr) (Binary <$> op (string "&&") And)

term2r :: Parser String Expr -> Parser String Expr
term2r expr = chainr1 (term3r expr) (Binary <$> op (string "||") Or)

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
