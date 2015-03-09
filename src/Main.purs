module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff
import DOM

import Data.Either
import Data.Maybe

import Web
import Parser
import Evaluator
import AST

import Debug.Trace


main = J.ready $ do
  print "Hello world!"
  let expr = case parseExpr "id (double (double (1 + 1)))" of Right e -> e
  let env = defsToEnv $ case parseDefs "double x = x + x\nid x = x" of Right d -> d
  showExpr env expr End
  return unit

showExpr :: forall eff. Env -> Expr -> Path -> Eff (dom :: DOM | eff) Unit
showExpr env expr path =
  case evalPath1 env path expr of
    Nothing    -> return unit
    Just expr' -> do
      test <- J.select "#test"
      J.clear test
      jexpr <- exprToJQuery expr' (showExpr env)
      J.append jexpr test
      return unit
