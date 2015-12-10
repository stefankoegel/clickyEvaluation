module Test.Main where

import Prelude

import Data.Either

import Control.Monad.Eff
import Control.Monad.Eff.Console

import Text.Parsing.StringParser

import AST
import Parser

parseTest :: forall a eff. (Show a) => String -> Parser a -> String -> Eff (console :: CONSOLE | eff) Unit
parseTest _ p input = case runParser p input of
  Left (ParseError err) -> print err
  Right result -> print result

main :: forall eff. Eff (console :: CONSOLE | eff) Unit
main = do
  parseTest "composition" expression "f . g"
  parseTest "power" expression "2 ^ 10"
  parseTest "mul" expression "2 * 2"
  parseTest "div" expression "13 `div` 3"
  parseTest "mod" expression "13 `mod` 3"
  parseTest "add1" expression "1 + 1"
  parseTest "add2" expression "2+2"
  parseTest "sub" expression "5 - 3"
  parseTest "colon" expression "x:xs"
  parseTest "append1" expression "xs ++ ys"
  parseTest "append2" expression "xs++ys"
  parseTest "equ" expression "5 == 5"
  parseTest "neq" expression "1 /= 2"
  parseTest "lt1" expression "1 < 234"
  parseTest "lt2" expression "x<y"
  parseTest "leq" expression "1 <= 234"
  parseTest "gt1" expression "567 > 1"
  parseTest "gt2" expression "x>y"
  parseTest "geq" expression "567 >= 1"
  parseTest "and" expression "hot && cold"
  parseTest "or" expression "be || notBe"
  parseTest "dollar" expression "f $ 1 + 2"
