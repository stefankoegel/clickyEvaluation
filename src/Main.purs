module Main where

import AST as AST
import Parser as Parser
import Evaluator as Eval
import Web as Web
import TypeChecker as TypeChecker
import JSHelpers (ctrlKeyPressed, getType)

import Prelude
import DOM (DOM)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.StrMap (empty)
import Data.Array (cons)
import Data.Traversable (for)

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Eff.JQuery as J

main :: forall eff. Eff (console :: CONSOLE | eff) Unit
main = log "hello"

makeCE :: forall eff. String -> String -> Eff (dom :: DOM | eff) Unit
makeCE input selector = do
  clearInfo
  container <- J.select selector
  doWithJust (parseExpr input) \expr -> do
    let env = preludeEnv
    showExprIn expr env [] container Nothing
    pure unit

makeCEwithDefs :: forall eff. String -> String -> String -> Eff (dom :: DOM | eff) Unit
makeCEwithDefs input defs selector = do
  clearInfo
  container <- J.select selector
  doWithJust (parseExpr input) \expr -> do
    let env = stringToEnv defs
    showExprIn expr env [] container Nothing

makeCEwithHistory :: forall eff. String -> String -> String -> Eff (dom :: DOM | eff) Unit
makeCEwithHistory input selector histSelector = do
  clearInfo
  container <- J.select selector
  histContainer <- J.select histSelector
  doWithJust (parseExpr input) \expr -> do
    let env = preludeEnv
    showExprIn expr env [] container (Just histContainer)

makeCEwithDefsAndHistory :: forall eff. String -> String -> String -> String -> Eff (dom :: DOM | eff) Unit
makeCEwithDefsAndHistory  input defs selector histSelector = do
  clearInfo
  container <- J.select selector
  histContainer <- J.select histSelector
  doWithJust (parseExpr input) \expr -> do
    let env = stringToEnv defs
    showExprIn expr env [] container (Just histContainer)

-- | Try to parse the given expression and report parser errors.
parseExpr :: forall eff. String -> Eff (dom :: DOM | eff) (Maybe AST.TypeTree)
parseExpr input = case Parser.parseExpr input of
  Left error -> do
    showError "Parser" (show error)
    pure Nothing
  Right expr -> pure $ Just expr

eval1 :: Eval.Env -> AST.TypeTree -> AST.TypeTree
eval1 env expr = case Eval.runEvalM (Eval.eval1 env expr) of
  Left _      -> expr
  Right expr' -> expr'

makeCallback :: Eval.Env -> Array AST.TypeTree -> J.JQuery -> Maybe J.JQuery-> Web.Callback
makeCallback env history container histContainer expr hole event jq = do
  J.stopImmediatePropagation event
  let evalFunc = if ctrlKeyPressed event then Eval.eval else eval1
  case getType event of
    "click"     -> if evalFunc env expr /= expr
                   then showExprIn (hole (evalFunc env expr)) env (cons (hole expr) history) container histContainer
                   else pure unit
    "mouseover" -> if evalFunc env expr /= expr
                   then void $ J.addClass "highlight" jq
                   else pure unit
    "mouseout"  -> void $ J.removeClass "highlight" jq
    _           -> pure unit
  pure unit

exprToJQuery :: forall eff. Web.Callback -> AST.TypeTree -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery callback = Web.exprToDiv >>> Web.divToJQuery true callback

-- | Clear the contents of info div.
clearInfo :: forall eff. Eff (dom :: DOM | eff) Unit
clearInfo = void $ J.select "#info" >>= J.clear

-- | Create an info div and display an error inside.
showError :: forall eff. String -> String -> Eff (dom :: DOM | eff) Unit
showError origin msg = do
  info <- do
    paragraph <- J.create "<p></p>"
    J.addClass "info" paragraph
    J.setText ("Error in " <> origin <> " => " <> msg) paragraph
    pure paragraph
  clearInfo
  infoDiv <- J.select "#info"
  J.append info infoDiv

-- | Execute the given function if the given maybe (wrapped inside an effect) is a `Just x` value
-- | using `x` as the argument. If the maybe is `Nothing` don't do anything.
doWithJust :: forall a eff. Eff (dom :: DOM | eff) (Maybe a)
         -> (a -> Eff (dom :: DOM | eff) Unit)
         -> Eff (dom :: DOM | eff) Unit
doWithJust mMaybe f = do
  mValue <- mMaybe
  case mValue of
    Nothing -> pure unit
    Just x  -> f x

-- | Given a type tree and an evaluation environment, try to infere the types inside the given
-- | environment.
buildTypeEnvironment :: forall eff. AST.TypeTree -> Eval.Env
                     -> Eff (dom :: DOM | eff) (Maybe TypeChecker.TypeEnv)
buildTypeEnvironment expr env =
  let defs = Eval.envToDefs env
  in case TypeChecker.tryInferEnvironment defs of
    Left error -> pure Nothing
    Right typedEnv -> pure $ Just typedEnv

-- | Type check an expression using a given typed environment.
-- | Construct a div tree from the given typed expression.
typeCheckExpression :: forall eff. TypeChecker.TypeEnv -> AST.TypeTree
                 -> Eff (dom :: DOM | eff) (Maybe AST.TypeTree)
typeCheckExpression typedEnv expr = do
  case TypeChecker.runInferWith typedEnv false (TypeChecker.inferExpr expr) of
    Left typeError -> do
      showError "Expression" (AST.prettyPrintTypeError typeError)
      pure Nothing
    Right typedExpr -> do
      pure $ Just typedExpr

-- | Construct a div tree from the given typed expression.
buildDivTreeFromExpression :: forall eff. AST.TypeTree -> Eval.Env -> Array AST.TypeTree
                           -> J.JQuery -> Maybe J.JQuery -> Eff (dom :: DOM | eff) Unit
buildDivTreeFromExpression typedExpr env history container histContainer = do
    content <- exprToJQuery (makeCallback env history container histContainer) typedExpr
    J.clear container
    J.append content container
    case histContainer of
      Nothing -> pure unit
      Just histContainer -> do
        J.clear histContainer
        for history $ \typedExpr -> do
          histExpr <- exprToJQuery (\_ _ _ _ -> pure unit) typedExpr
          histDiv <- J.create "<div></div>"
          J.addClass "history-element" histDiv
          J.append histExpr histDiv
          J.append histDiv histContainer
        pure unit
    pure unit

-- | Show the given expression inside a given environment after the types of the environment as
-- | well as the expression have been inferred.
showExprIn :: forall eff. AST.TypeTree -> Eval.Env -> Array AST.TypeTree -> J.JQuery
           -> Maybe J.JQuery -> Eff (dom :: DOM | eff) Unit
showExprIn expr env history container histContainer = do
  -- Try to infer the types of the environment.
  doWithJust (buildTypeEnvironment expr env) \typedEnv -> do
    -- Try to infer the type of the given expression.
    doWithJust (typeCheckExpression typedEnv expr) \typedExpr ->
      buildDivTreeFromExpression typedExpr env history container histContainer

stringToEnv :: String -> Eval.Env
stringToEnv str = case Parser.parseDefs str of
  Left _     -> empty
  Right defs -> Eval.defsToEnv defs

preludeEnv :: Eval.Env
preludeEnv = stringToEnv prelude

prelude :: String
prelude =
  "and (True:xs)  = and xs\n" <>
  "and (False:xs) = False\n" <>
  "and []         = True\n" <>
  "\n" <>
  "or (False:xs) = or xs\n" <>
  "or (True:xs)  = True\n" <>
  "or []         = False\n" <>
  "\n" <>
  "all p = and . map p\n" <>
  "any p = or . map p\n" <>
  "\n" <>
  "head (x:xs) = x\n" <>
  "tail (x:xs) = xs\n" <>
  "\n" <>
  "take 0 xs     = []\n" <>
  "take n (x:xs) = x : take (n - 1) xs\n" <>
  "\n" <>
  "drop 0 xs     = xs\n" <>
  "drop n (x:xs) = drop (n - 1) xs\n" <>
  "\n" <>
  "elem e []     = False\n" <>
  "elem e (x:xs) = if e == x then True else elem e xs\n" <>
  "\n" <>
  "max a b = if a >= b then a else b\n" <>
  "min a b = if b >= a then a else b\n" <>
  "\n" <>
  "maximum (x:xs) = foldr max x xs\n" <>
  "minimum (x:xs) = foldr min x xs\n" <>
  "\n" <>
  "length []     = 0\n" <>
  "length (x:xs) = 1 + length xs\n" <>
  "\n" <>
  "zip (x:xs) (y:ys) = (x, y) : zip xs ys\n" <>
  "zip []      _     = []\n" <>
  "zip _       []    = []\n" <>
  "\n" <>
  "zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys\n" <>
  "zipWith _ []     _      = []\n" <>
  "zipWith _ _      []     = []\n" <>
  "\n" <>
  "unzip []          = ([], [])\n" <>
  "unzip ((a, b):xs) = (\\(as, bs) -> (a:as, b:bs)) $ unzip xs\n" <>
  "\n" <>
  "fst (x,_) = x\n" <>
  "snd (_,x) = x\n" <>
  "\n" <>
  "curry f a b = f (a, b)\n" <>
  "uncurry f (a, b) = f a b\n" <>
  "\n" <>
  "repeat x = x : repeat x\n" <>
  "\n" <>
  "replicate 0 _ = []\n" <>
  "replicate n x = x : replicate (n - 1) x\n" <>
  "\n" <>
  "enumFromTo a b = if a <= b then a : enumFromTo (a + 1) b else []\n" <>
  "\n" <>
  "sum (x:xs) = x + sum xs\n" <>
  "sum [] = 0\n" <>
  "\n" <>
  "product (x:xs) = x * product xs\n" <>
  "product [] = 1\n" <>
  "\n" <>
  "reverse []     = []\n" <>
  "reverse (x:xs) = reverse xs ++ [x]\n" <>
  "\n" <>
  "concat = foldr (++) []\n" <>
  "\n" <>
  "map f []     = []\n" <>
  "map f (x:xs) = f x : map f xs\n" <>
  "\n" <>
  "not True  = False\n" <>
  "not False = True\n" <>
  "\n" <>
  "filter p (x:xs) = if p x then x : filter p xs else filter p xs\n" <>
  "filter p []     = []\n" <>
  "\n" <>
  "foldr f ini []     = ini\n" <>
  "foldr f ini (x:xs) = f x (foldr f ini xs)\n" <>
  "\n" <>
  "foldl f acc []     = acc\n" <>
  "foldl f acc (x:xs) = foldl f (f acc x) xs\n" <>
  "\n" <>
  "scanl f b []     = [b]\n" <>
  "scanl f b (x:xs) = b : scanl f (f b x) xs\n" <>
  "\n" <>
  "iterate f x = x : iterate f (f x)\n" <>
  "\n" <>
  "id x = x\n" <>
  "\n" <>
  "const x _ = x\n" <>
  "\n" <>
  "flip f x y = f y x\n" <>
  "\n" <>
  "even n = (n `mod` 2) == 0\n" <>
  "odd n = (n `mod` 2) == 1\n" <>
  "\n" <>
  "fix f = f (fix f)\n"

-- import Prelude (class Applicative, Unit, (<$>), bind, show, ($), (>>=), void, unit, return, (++), id, (+), flip, (<<<), (-))
-- import Data.Foreign (unsafeFromForeign)
-- import Data.Foldable (any)
-- import Data.Either (Either(Right, Left), either)
-- import Data.Maybe (Maybe(Just, Nothing), maybe)
-- import Data.List (List(Nil), (:), singleton, (!!), drop, deleteAt, length, (..), zipWithA)

-- import Control.Monad.State.Trans (StateT, modify, get, runStateT)
-- import Control.Monad.Eff.Class (liftEff)

-- import Text.Parsing.Parser (ParseError(ParseError))
-- import Text.Parsing.Parser.Pos (Position(Position))
-- import Ace.Types (ACE())
-- import Ace.Editor as Editor
-- import Ace.EditSession as Session
-- import Ace.Range as  Range

-- import Web (exprToJQuery, getPath, idExpr, makeDiv)
-- import Evaluator (evalPath1, evalPathAll, Env(), defsToEnv, envToDefs, EvalError(..), MatchingError(..))
-- import AST (Path, Expr, TypeTree, Output, TypeError)
-- import TypeChecker (TypeEnv, txToABC, buildPartiallyTypedTree, typeTreeProgramnEnv, checkForError, prettyPrintTypeError, buildTypeEnv)
-- import Parser (parseDefs, parseExpr)
-- import JSHelpers (ctrlKeyPressed, prepend, jqMap, warnOnRefresh, isEnterKey, showTypes)

-- main :: DOMEff J.JQuery
-- main = J.ready $ do
--   J.select "#input"
--     >>= J.on "change" (\_ _ -> startEvaluation)
--     >>= J.on "keyup"  (\e _ -> if isEnterKey e then startEvaluation else pure unit)
--   startEvaluation

-- type DOMEff = Eff (dom :: DOM, console :: CONSOLE, ace :: ACE)

-- type EvalState = { env :: Env, out :: Output, history :: List Output, typEnv :: TypeEnv }

-- type EvalM a = StateT EvalState DOMEff a

-- startEvaluation :: DOMEff Unit
-- startEvaluation = do
--   clearInfo
--   editor <- Ace.edit "definitions" Ace.ace
--   definitions <- Editor.getValue editor
--   input       <- J.select "#input"       >>= getValue

--   case parseExpr input of
--     Left err   -> showInfo "Expression" (show err)
--     Right expr -> do
--       case defsToEnv <$> parseDefs definitions of
--         Left err@(ParseError { position: (Position { line: line, column: column }) })  -> do
--           showInfo "Definitions" (show err)
--           markText (line - 1) column
--         Right env -> case buildTypeEnv (envToDefs env) of --  type Env
--           Left err -> showInfo "Definitions" (prettyPrintTypeError err)
--           Right typEnv -> do
--             let showEvalState typ' = let typ = txToABC typ' in
--               let idTree = idExpr expr in
--               void $ runStateT showEvaluationState { env: env, out: {expr:expr, typ:typ, idTree:idTree}, history: Nil, typEnv:typEnv }
--             case typeTreeProgramnEnv typEnv expr of
--               Left err -> do
--                 showTypes
--                 let typ' = buildPartiallyTypedTree typEnv expr
--                 showEvalState typ'
--               Right typ' -> showEvalState typ'




-- outIfErr::forall b. String -> Either TypeError b -> DOMEff Unit
-- outIfErr origin either = case either of
--   Left err -> showInfo origin (prettyPrintTypeError err)
--   Right _ -> pure unit

-- markText :: Int -> Int -> DOMEff Unit
-- markText line column = do
--   editor <- Ace.edit "definitions" Ace.ace
--   session <- Editor.getSession editor
--   rang <- Range.create line column 100000 100000
--   void $ Session.addMarker rang "syntaxError" "" false session

-- showEvaluationState :: EvalM Unit
-- showEvaluationState = do
--   liftEff $ warnOnRefresh
--   output <- liftEff $ prepareContainer "output"
--   history <- liftEff $ prepareContainer "history"
--   typContainer <- liftEff $ prepareContainer "typ"
--   svgContainer <- liftEff $ prepareContainer "svg"

--   { env = env, out = out, history = histExprs } <- get :: EvalM EvalState
--   liftEff $ print out.expr
--   liftEff $ print out.typ

--   liftEff $ exprToJQuery out >>= wrapInDiv "output" >>= flip J.append output
--   showHistoryList histExprs >>= liftEff <<< flip J.append history

--   liftEff (J.find ".binary, .app, .func, .list, .if, .name" output)
--      >>= makeClickable
--   liftEff (J.find ".output div" output)
--     >>= addMouseOverListener
--     >>= addClickListener (out.typ)
--   liftEff (J.body >>= J.on "mouseover" (\_ _ -> removeMouseOver))

--   liftEff $ pure unit :: DOMEff Unit

-- forIndex :: forall m a b. (Applicative m) => (List a) -> (a -> Int -> m b) -> m (List b)
-- forIndex as f = zipWithA f as (0 .. (length as - 1))

-- showHistoryList :: (List Output) -> EvalM J.JQuery
-- showHistoryList exprs = do
--   box <- liftEff $ J.create "<table></table>" >>= J.addClass "historyBox" >>= J.addClass "vertical" >>= J.addClass "frame"
--   forIndex exprs $ \expr i -> do
--     showHistoryRow expr i >>= liftEff <<< flip J.append box
--   scroll <- liftEff $ J.create "<div></div>" >>= J.addClass "scroll"
--   liftEff $ J.append box scroll
--   pure scroll


-- showHistoryRow :: Output -> Int -> EvalM J.JQuery
-- showHistoryRow out i = do
--   row <- liftEff $ J.create "<tr></tr>" >>= J.addClass "history"
--   tdExpr <- liftEff $ J.create "<td></td>"
--   liftEff $ exprToJQuery out >>= flip J.append tdExpr
--   liftEff $ J.append tdExpr row
--   es <- get :: EvalM EvalState
--   let deleteHandler = \_ _ -> do
--                         let es' = es { history = maybe es.history id (deleteAt i es.history) }
--                         void $ runStateT showEvaluationState es'
--   delete <- liftEff $ J.create "<button></button>"
--     >>= J.setText "Delete"
--     >>= J.addClass "delete"
--     >>= J.on "click" deleteHandler
--   tdDelete <- liftEff $ J.create "<td></td>"
--   liftEff $ J.append delete tdDelete
--   liftEff $ J.append tdDelete row
--   let restoreHandler = \_ _ -> do
--                          let es' = es { history = drop (i + 1) es.history, out = maybe es.out id (es.history !! i) }
--                          void $ runStateT showEvaluationState es'
--   restore <- liftEff $ J.create "<button></button>"
--     >>= J.setText "Restore"
--     >>= J.addClass "restore"
--     >>= J.on "click" restoreHandler
--   tdRestore <- liftEff $ J.create "<td></td>"
--   liftEff $ J.append restore tdRestore
--   liftEff $ J.append tdRestore row
--   pure row

-- showInfo :: String -> String -> DOMEff Unit
-- showInfo origin msg = do
--   info <- J.create "<p></p>"
--     >>= J.addClass "info"
--     >>= J.setText ("Error in " <> origin ++ " => " <> msg)
--   clearInfo
--   J.select "#info"
--     >>= J.append info
--   pure unit

-- clearInfo :: DOMEff Unit
-- clearInfo = void $ J.select "#info" >>= J.clear

-- prepareContainer :: String -> DOMEff J.JQuery
-- prepareContainer name = do
--   J.select ("#" <> name <> "-container") >>= J.clear

-- wrapInDiv :: String -> J.JQuery -> DOMEff J.JQuery
-- wrapInDiv name jq = do
--   J.create "<div></div>" >>= J.addClass name >>= J.append jq

-- makeClickable :: J.JQuery -> EvalM Unit
-- makeClickable jq = do
--   { env = env, out = out } <- get
--   let expr = out.expr
--   let typeTree = out.typ
--   liftEff $ jqMap (testEval env expr typeTree) jq
--   where
--   testEval :: Env -> Expr -> TypeTree -> J.JQuery -> DOMEff Unit
--   testEval env expr typeTree jq = do
--     mpath <- getPath jq
--     case mpath of
--       Nothing   -> pure unit
--       Just path ->
--         case evalPath1 env path expr of
--           Left err -> displayEvalError err jq
--           Right _  -> if checkForError path typeTree
--             then pure unit
--             else void $ J.addClass "clickable" jq

-- displayEvalError :: EvalError -> J.JQuery -> DOMEff Unit
-- displayEvalError err jq = case err of
--   DivByZero -> void $ makeDiv "Division by zero!" (singleton "evalError") >>= flip prepend jq
--   NoMatchingFunction _ errs -> if (any missesArguments errs)
--     then pure unit
--     else void $ makeDiv "No matching function!" (singleton "evalError") >>= flip prepend jq
--   _         -> pure unit
--   where
--     missesArguments (TooFewArguments _ _) = true
--     missesArguments (StrictnessError _ _) = true
--     missesArguments _                     = false

-- addMouseOverListener :: J.JQuery -> EvalM J.JQuery
-- addMouseOverListener jq = liftEff $ J.on "mouseover" handler jq
--   where
--   handler :: J.JQueryEvent -> J.JQuery -> DOMEff Unit
--   handler jEvent jq = do
--     J.stopPropagation jEvent
--     removeMouseOver
--     J.addClass "mouseOver" jq
--     pure unit

-- addClickListener :: TypeTree ->  J.JQuery -> EvalM J.JQuery
-- addClickListener typeTree jq = do
--   evaluationState <- get
--   liftEff $ J.on "click" (handler evaluationState) jq
--   where
--   handler :: EvalState -> J.JQueryEvent -> J.JQuery -> DOMEff Unit
--   handler evaluationState jEvent jq = do
--     J.stopImmediatePropagation jEvent
--     mpath <- getPath jq
--     case mpath of
--       Nothing   -> pure unit
--       Just path -> do
--         pure unit
--         if checkForError path typeTree
--           then pure unit
--           else case ctrlKeyPressed jEvent of
--                 false -> void $ runStateT (evalExpr evalPath1 path) evaluationState
--                 true  -> void $ runStateT (evalExpr evalPathAll path) evaluationState

-- removeMouseOver :: DOMEff Unit
-- removeMouseOver = void $ J.select ".mouseOver" >>= J.removeClass "mouseOver"

-- evalExpr :: (Env -> Path -> Expr -> Either EvalError Expr) -> Path -> EvalM Unit
-- evalExpr eval path = do
--   { env = env, out = out, typEnv = typEnv} <- get
--   let expr = out.expr
--   liftEff $ print path
--   case eval env path expr of
--     Left msg    -> pure unit
--     Right expr' -> do
--         let eitherTyp = typeTreeProgramnEnv typEnv expr'
--         let typ'' = either (\_ -> buildPartiallyTypedTree typEnv expr') id eitherTyp
--         let typ' = txToABC typ''
--         modify (\es -> es { out = {expr:expr', typ:typ', idTree:idExpr expr'} })
--         modify (\es -> es { history = out : es.history })
--         showEvaluationState

-- getValue :: J.JQuery -> DOMEff String
-- getValue jq = unsafeFromForeign <$> J.getValue jq
