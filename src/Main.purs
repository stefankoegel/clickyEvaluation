module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff
import DOM
import Data.Foreign (unsafeFromForeign)

import Data.Either
import Data.Maybe
import Data.Foldable (for_)
import Control.Apply ((*>))
import Control.Monad.State.Trans
import Control.Monad.State.Class
import Control.Monad.Eff.Class

import Web (exprToJQuery, getPath)
import Parser
import Evaluator
import AST

import Debug.Trace


main = J.ready $ do
  J.select "#input"
    >>= J.on "change" (\_ _ -> startEvaluation)
  startEvaluation

type DOMEff = Eff (dom :: DOM, trace :: Trace)

type EvalState = { env :: Env, expr :: Expr, history :: [Expr] }

type EvalM a = StateT EvalState DOMEff a

startEvaluation :: DOMEff Unit
startEvaluation = do
  definitions <- J.select "#definitions" >>= getValue
  let env = defsToEnv $ case parseDefs definitions of Right d -> d

  input       <- J.select "#input"       >>= getValue
  let expr = case parseExpr input of Right e -> e

  void $ runStateT showEvaluationState { env: env, expr: expr, history: [] }

foreign import map
  """
  function map(callback) {
    return function(ob) {
      return function () {
        return ob.map( function(i, e) { return callback(jQuery(e))(); } );
      };
    };
  }
  """ :: (J.JQuery -> DOMEff Unit) -> J.JQuery -> DOMEff Unit

showEvaluationState :: EvalM Unit
showEvaluationState = do
  output <- liftEff $ prepareContainer "output"
  history <- liftEff $ prepareContainer "history"

  { env = env, expr = expr, history = hists } <- get :: EvalM EvalState

  liftEff $ exprToJQuery expr >>= flip J.append output
  liftEff $ showHistory hists history

  liftEff (J.find ".binary, .app, .func" output)
    >>= makeClickable
  liftEff (J.find ".clickable" output)
    >>= addMouseOverListener
    >>= addClickListener
  liftEff (J.body >>= J.on "mouseover" (\_ _ -> removeMouseOver))

  liftEff $ return unit :: DOMEff Unit

showHistory :: [Expr] -> J.JQuery -> DOMEff Unit
showHistory exprs jq = for_ exprs $ \expr -> do
  exprToJQuery expr >>= flip J.append jq
  J.create "<br></br>" >>= flip J.append jq
  return unit


prepareContainer :: String -> DOMEff J.JQuery
prepareContainer name = do
  container <- J.select ("#" ++ name ++ "-container") >>= J.clear
  content <- J.create "<div></div>" >>= J.addClass name
  J.append content container
  return content

makeClickable :: J.JQuery -> EvalM Unit
makeClickable jq = do
  { env = env, expr = expr } <- get
  liftEff $ map (testEval env expr) jq
  where
  testEval :: Env -> Expr -> J.JQuery -> DOMEff Unit
  testEval env expr jq = do
    path <- getPath jq
    case evalPath1 env path expr of
      Nothing -> return unit
      Just _  -> void $ J.addClass "clickable" jq

addMouseOverListener :: J.JQuery -> EvalM J.JQuery
addMouseOverListener jq = liftEff $ J.on "mouseover" handler jq
  where
  handler :: J.JQueryEvent -> J.JQuery -> DOMEff Unit
  handler jEvent jq = do
    J.stopImmediatePropagation jEvent
    removeMouseOver
    J.addClass "mouseOver" jq
    return unit

addClickListener :: J.JQuery -> EvalM J.JQuery
addClickListener jq = do
  evaluationState <- get
  liftEff $ J.on "click" (handler evaluationState) jq
  where
  handler :: EvalState -> J.JQueryEvent -> J.JQuery -> DOMEff Unit
  handler evaluationState jEvent jq = do
    J.stopImmediatePropagation jEvent
    path <- getPath jq
    void $ runStateT (evalExpr path) evaluationState

removeMouseOver :: DOMEff Unit
removeMouseOver = void $ J.select ".mouseOver" >>= J.removeClass "mouseOve"

evalExpr :: Path -> EvalM Unit
evalExpr path = do
  { env = env, expr = expr } <- get
  case evalPath1 env path expr of
    Nothing    -> return unit
    Just expr' -> do
      modify (\es -> es { expr = expr' })
      modify (\es -> es { history = expr : es.history })
      showEvaluationState

getValue :: J.JQuery -> DOMEff String
getValue jq = unsafeFromForeign <$> J.getValue jq
