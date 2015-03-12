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
  J.select "#input"
    >>= J.on "change" (\_ _ -> startEvaluation)
  startEvaluation

startEvaluation :: forall eff. Eff (dom :: DOM | eff) Unit
startEvaluation = do
  definitions <- J.select "#definitions" >>= getValue
  let env = defsToEnv $ case parseDefs definitions of Right d -> d

  input       <- J.select "#input"       >>= getValue
  let expr = case parseExpr input of Right e -> e

  showExpr env expr

showExpr :: Env -> Expr -> forall eff. Eff (dom :: DOM | eff) Unit
showExpr env expr = do
  output <- J.select "#output"
  J.clear output
  jexpr <- exprToJQuery env expr evalExpr
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

evalExpr :: forall eff. Env -> Path -> Expr -> Eff (dom :: DOM | eff) Unit
evalExpr env path expr =
  case evalPath1 env path expr of
    Nothing    -> return unit
    Just expr' -> do
      showExpr env expr'

getValue :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) String
getValue j = do
  value <- J.getValue j
  case readString value of
    Right str -> return str
