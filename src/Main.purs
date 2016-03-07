module Main where

import Prelude (class Applicative, Unit, (<$>), bind, show, ($), (>>=), void, unit, return, (++), id, (+), flip, (<<<), (-))
import Data.Foreign (unsafeFromForeign)
import Data.Foldable (any)
import Data.Either (Either(Right, Left), either)
import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.List (List(Nil), (:), singleton, (!!), drop, deleteAt, length, (..), zipWithA)

import Control.Monad.Eff.JQuery as J
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, print)
import Control.Monad.State.Trans (StateT, modify, get, runStateT)
import Control.Monad.Eff.Class (liftEff)

import Text.Parsing.Parser (ParseError(ParseError))
import Text.Parsing.Parser.Pos (Position(Position))
import DOM (DOM)
import Ace.Types (ACE())
import Ace.Editor as Editor
import Ace.EditSession as Session
import Ace.Range as  Range

import Web (exprToJQuery, getPath, idExpr, makeDiv)
import Evaluator (evalPath1, evalPathAll, Env(), defsToEnv, envToDefs, EvalError(..), MatchingError(..))
import AST (Path, Expr, TypeTree, Output, TypeError)
import TypeChecker (TypeEnv, txToABC, buildEmptyTypeTree, typeTreeProgramnEnv, checkForError, prettyPrintTypeError, buildTypeEnv)
import Parser (parseDefs, parseExpr)
import JSHelpers (ctrlKeyPressed, prepend, jqMap, warnOnRefresh, isEnterKey, showTypes)

main :: DOMEff J.JQuery
main = J.ready $ do
  J.select "#input"
    >>= J.on "change" (\_ _ -> startEvaluation)
    >>= J.on "keyup"  (\e _ -> if isEnterKey e then startEvaluation else return unit)
  startEvaluation

type DOMEff = Eff (dom :: DOM, console :: CONSOLE, ace :: ACE)

type EvalState = { env :: Env, out :: Output, history :: List Output, typEnv :: TypeEnv }

type EvalM a = StateT EvalState DOMEff a

startEvaluation :: DOMEff Unit
startEvaluation = do
  clearInfo
  editor <- Ace.edit "definitions" Ace.ace
  definitions <- Editor.getValue editor
  input       <- J.select "#input"       >>= getValue

  case parseExpr input of
    Left err   -> showInfo "Expression" (show err)
    Right expr -> do
      case defsToEnv <$> parseDefs definitions of
        Left err@(ParseError { position: (Position { line: line, column: column }) })  -> do
          showInfo "Definitions" (show err)
          markText (line - 1) column
        Right env -> case buildTypeEnv (envToDefs env) of --  type Env
          Left err -> showInfo "Definitions" (prettyPrintTypeError err)
          Right typEnv -> do
            let showEvalState typ' = let typ = txToABC typ' in
              let idTree = idExpr expr in
              void $ runStateT showEvaluationState { env: env, out: {expr:expr, typ:typ, idTree:idTree}, history: Nil, typEnv:typEnv }
            case typeTreeProgramnEnv typEnv expr of
              Left err -> do
                showTypes
                let typ' = buildEmptyTypeTree typEnv expr
                showEvalState typ'
              Right typ' -> showEvalState typ'




outIfErr::forall b. String -> Either TypeError b -> DOMEff Unit
outIfErr origin either = case either of
  Left err -> showInfo origin (prettyPrintTypeError err)
  Right _ -> return unit

markText :: Int -> Int -> DOMEff Unit
markText line column = do
  editor <- Ace.edit "definitions" Ace.ace
  session <- Editor.getSession editor
  rang <- Range.create line column 100000 100000
  void $ Session.addMarker rang "syntaxError" "" false session

showEvaluationState :: EvalM Unit
showEvaluationState = do
  liftEff $ warnOnRefresh
  output <- liftEff $ prepareContainer "output"
  history <- liftEff $ prepareContainer "history"
  typContainer <- liftEff $ prepareContainer "typ"
  svgContainer <- liftEff $ prepareContainer "svg"

  { env = env, out = out, history = histExprs } <- get :: EvalM EvalState
  liftEff $ print out.expr
  liftEff $ print out.typ

  liftEff $ exprToJQuery out >>= wrapInDiv "output" >>= flip J.append output
  showHistoryList histExprs >>= liftEff <<< flip J.append history

  liftEff (J.find ".binary, .app, .func, .list, .if, .name" output)
     >>= makeClickable
  liftEff (J.find ".output div" output)
    >>= addMouseOverListener
    >>= addClickListener (out.typ)
  liftEff (J.body >>= J.on "mouseover" (\_ _ -> removeMouseOver))

  liftEff $ return unit :: DOMEff Unit

forIndex :: forall m a b. (Applicative m) => (List a) -> (a -> Int -> m b) -> m (List b)
forIndex as f = zipWithA f as (0 .. (length as - 1))

showHistoryList :: (List Output) -> EvalM J.JQuery
showHistoryList exprs = do
  box <- liftEff $ J.create "<table></table>" >>= J.addClass "historyBox" >>= J.addClass "vertical" >>= J.addClass "frame"
  forIndex exprs $ \expr i -> do
    showHistoryRow expr i >>= liftEff <<< flip J.append box
  scroll <- liftEff $ J.create "<div></div>" >>= J.addClass "scroll"
  liftEff $ J.append box scroll
  return scroll


showHistoryRow :: Output -> Int -> EvalM J.JQuery
showHistoryRow out i = do
  row <- liftEff $ J.create "<tr></tr>" >>= J.addClass "history"
  tdExpr <- liftEff $ J.create "<td></td>"
  liftEff $ exprToJQuery out >>= flip J.append tdExpr
  liftEff $ J.append tdExpr row
  es <- get :: EvalM EvalState
  let deleteHandler = \_ _ -> do
                        let es' = es { history = maybe es.history id (deleteAt i es.history) }
                        void $ runStateT showEvaluationState es'
  delete <- liftEff $ J.create "<button></button>"
    >>= J.setText "Delete"
    >>= J.addClass "delete"
    >>= J.on "click" deleteHandler
  tdDelete <- liftEff $ J.create "<td></td>"
  liftEff $ J.append delete tdDelete
  liftEff $ J.append tdDelete row
  let restoreHandler = \_ _ -> do
                         let es' = es { history = drop (i + 1) es.history, out = maybe es.out id (es.history !! i) }
                         void $ runStateT showEvaluationState es'
  restore <- liftEff $ J.create "<button></button>"
    >>= J.setText "Restore"
    >>= J.addClass "restore"
    >>= J.on "click" restoreHandler
  tdRestore <- liftEff $ J.create "<td></td>"
  liftEff $ J.append restore tdRestore
  liftEff $ J.append tdRestore row
  return row

showInfo :: String -> String -> DOMEff Unit
showInfo origin msg = do
  info <- J.create "<p></p>"
    >>= J.addClass "info"
    >>= J.setText ("Error in " ++ origin ++ " => " ++ msg)
  clearInfo
  J.select "#info"
    >>= J.append info
  return unit

clearInfo :: DOMEff Unit
clearInfo = void $ J.select "#info" >>= J.clear

prepareContainer :: String -> DOMEff J.JQuery
prepareContainer name = do
  J.select ("#" ++ name ++ "-container") >>= J.clear

wrapInDiv :: String -> J.JQuery -> DOMEff J.JQuery
wrapInDiv name jq = do
  J.create "<div></div>" >>= J.addClass name >>= J.append jq

makeClickable :: J.JQuery -> EvalM Unit
makeClickable jq = do
  { env = env, out = out } <- get
  let expr = out.expr
  let typeTree = out.typ
  liftEff $ jqMap (testEval env expr typeTree) jq
  where
  testEval :: Env -> Expr -> TypeTree -> J.JQuery -> DOMEff Unit
  testEval env expr typeTree jq = do
    mpath <- getPath jq
    case mpath of
      Nothing   -> return unit
      Just path ->
        case evalPath1 env path expr of
          Left err -> displayEvalError err jq
          Right _  -> if checkForError path typeTree
            then return unit
            else void $ J.addClass "clickable" jq

displayEvalError :: EvalError -> J.JQuery -> DOMEff Unit
displayEvalError err jq = case err of
  DivByZero -> void $ makeDiv "Division by zero!" (singleton "evalError") >>= flip prepend jq
  NoMatchingFunction _ errs -> if (any missesArguments errs)
    then return unit
    else void $ makeDiv "No matching function!" (singleton "evalError") >>= flip prepend jq
  _         -> return unit
  where
    missesArguments (TooFewArguments _ _) = true
    missesArguments (StrictnessError _ _) = true
    missesArguments _                     = false

addMouseOverListener :: J.JQuery -> EvalM J.JQuery
addMouseOverListener jq = liftEff $ J.on "mouseover" handler jq
  where
  handler :: J.JQueryEvent -> J.JQuery -> DOMEff Unit
  handler jEvent jq = do
    J.stopPropagation jEvent
    removeMouseOver
    J.addClass "mouseOver" jq
    return unit

addClickListener :: TypeTree ->  J.JQuery -> EvalM J.JQuery
addClickListener typeTree jq = do
  evaluationState <- get
  liftEff $ J.on "click" (handler evaluationState) jq
  where
  handler :: EvalState -> J.JQueryEvent -> J.JQuery -> DOMEff Unit
  handler evaluationState jEvent jq = do
    J.stopImmediatePropagation jEvent
    mpath <- getPath jq
    case mpath of
      Nothing   -> return unit
      Just path -> do
        return unit
        if checkForError path typeTree
          then return unit
          else case ctrlKeyPressed jEvent of
                false -> void $ runStateT (evalExpr evalPath1 path) evaluationState
                true  -> void $ runStateT (evalExpr evalPathAll path) evaluationState

removeMouseOver :: DOMEff Unit
removeMouseOver = void $ J.select ".mouseOver" >>= J.removeClass "mouseOver"

evalExpr :: (Env -> Path -> Expr -> Either EvalError Expr) -> Path -> EvalM Unit
evalExpr eval path = do
  { env = env, out = out, typEnv = typEnv} <- get
  let expr = out.expr
  liftEff $ print path
  case eval env path expr of
    Left msg    -> return unit
    Right expr' -> do
        let eitherTyp = typeTreeProgramnEnv typEnv expr'
        let typ'' = either (\_ -> buildEmptyTypeTree typEnv expr') id eitherTyp
        let typ' = txToABC typ''
        modify (\es -> es { out = {expr:expr', typ:typ', idTree:idExpr expr'} })
        modify (\es -> es { history = out : es.history })
        showEvaluationState

getValue :: J.JQuery -> DOMEff String
getValue jq = unsafeFromForeign <$> J.getValue jq
