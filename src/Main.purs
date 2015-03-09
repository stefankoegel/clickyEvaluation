module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff
import DOM
import Data.Foreign (readString)

import Data.Either
import Data.Maybe

import Web
import Parser
import Evaluator
import AST

import Debug.Trace


main = J.ready $ do
  input       <- J.select "#input"       >>= getValue
  definitions <- J.select "#definitions" >>= getValue
  output      <- J.select "#output"
  info        <- J.select "#info"

  let expr = case parseExpr input of Right e -> e
  let env = defsToEnv $ case parseDefs definitions of Right d -> d
  showExpr env expr End
  return unit

showExpr :: forall eff. Env -> Expr -> Path -> Eff (dom :: DOM | eff) Unit
showExpr env expr path =
  case evalPath1 env path expr of
    Nothing    -> return unit
    Just expr' -> do
      test <- J.select "#output"
      J.clear test
      jexpr <- exprToJQuery expr' (showExpr env)
      J.append jexpr test
      return unit

getValue :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) String
getValue j = do
  value <- J.getValue j
  case readString value of
    Right str -> return str
