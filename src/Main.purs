module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff
import DOM

import Data.Either

import Web
import Parser
import Evaluator
import AST

import Debug.Trace


main = J.ready $ do
  print "Hello world!"
  let expr = case parseExpr "1 : (1 + 2) : [3 * 4, 9 `div` 3]" of Right e -> e
  let env = defsToEnv $ case parseDefs "double x = x + x" of Right d -> d
  showExpr expr
  return unit

showExpr :: forall eff. Expr -> Eff (dom :: DOM | eff) Unit
showExpr expr = do
  test <- J.select "#test"
  J.clear test
  jexpr <- exprToJQuery expr showExpr
  J.append jexpr test
  return unit
