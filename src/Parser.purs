module Parser where

import Global              (readInt)
import Data.String         (joinWith, split)
import Data.Identity       (Identity())
import Control.Alt         ((<|>))
import Control.Apply       ((*>))
import Control.Alternative (some, many)

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
