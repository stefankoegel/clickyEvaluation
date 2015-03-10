module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff
import DOM
import Data.Foreign (readString)

import Data.Either
import Data.Maybe
import Control.Apply ((*>))

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
  showExpr env expr
  return unit

showExpr :: forall eff. Env -> Expr -> Eff (dom :: DOM | eff) Unit
showExpr env expr = do
  output <- J.select "#output"
  J.clear output
  jexpr <- exprToJQuery env expr (evalExpr env)
  J.append jexpr output

  J.select "#output .clickable"
    >>= J.on "mouseover" (\je j -> do
      J.stopImmediatePropagation je
      J.select "#output .mouseOver"
        >>= J.removeClass "mouseOver"
      J.addClass "mouseOver" j)
  J.body
    >>= J.on "mouseover" (\_ _ -> J.select "#output .mouseOver" >>= J.removeClass "mouseOver")
  return unit

evalExpr :: forall eff. Env -> Expr -> Path -> Eff (dom :: DOM | eff) Unit
evalExpr env expr path =
  case evalPath1 env path expr of
    Nothing    -> return unit
    Just expr' -> do
      showExpr env expr'

getValue :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) String
getValue j = do
  value <- J.getValue j
  case readString value of
    Right str -> return str
