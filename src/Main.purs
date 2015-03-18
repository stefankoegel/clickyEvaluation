module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff
import DOM
import Data.Foreign (readString)

import Data.Either
import Data.Maybe
import Control.Apply ((*>))

import Web (exprToJQuery, getPath)
import Parser
import Evaluator
import AST

import Debug.Trace


main = J.ready $ do
  J.select "#input"
    >>= J.on "change" (\_ _ -> startEvaluation)
  startEvaluation

type DOMEff a = forall eff. Eff (dom :: DOM, trace :: Trace | eff) a

startEvaluation :: DOMEff Unit
startEvaluation = do
  definitions <- J.select "#definitions" >>= getValue
  let env = defsToEnv $ case parseDefs definitions of Right d -> d

  input       <- J.select "#input"       >>= getValue
  let expr = case parseExpr input of Right e -> e

  showExpr env expr

foreign import map
  """
  function map(callback) {
    return function(ob) {
      return function () {
        return ob.map( function(i, e) { return callback(jQuery(e))(); } );
      };
    };
  }
  """ :: forall eff. (J.JQuery -> Eff (dom :: DOM | eff) Unit) -> J.JQuery -> Eff (dom :: DOM | eff) Unit

showExpr :: forall eff. Env -> Expr -> DOMEff Unit
showExpr env expr = do
  outputContainer <- J.select "#output-container"
  J.clear outputContainer

  output <- J.create "<div></div>" >>= J.addClass "output"
  J.append output outputContainer

  jexpr <- exprToJQuery expr
  J.append jexpr output

  J.find ".binary, .app, .func" output >>= map (makeClickable env expr)

  J.find ".clickable" output
    >>= J.on "mouseover" (\je j -> do
      J.stopImmediatePropagation je
      J.find ".mouseOver" output >>= J.removeClass "mouseOver"
      J.addClass "mouseOver" j)

  J.body
    >>= J.on "mouseover" (\_ _ -> J.find ".mouseOver" output >>= J.removeClass "mouseOver")
  return unit

makeClickable :: forall eff. Env -> Expr -> J.JQuery -> DOMEff Unit
makeClickable env expr jq = do
  path <- getPath jq
  case evalPath1 env path expr of
    Nothing -> return unit
    Just _  -> void $ J.addClass "clickable" jq

evalExpr :: forall eff. Env -> Path -> Expr -> DOMEff Unit
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
