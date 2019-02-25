module Main where

import AST as AST
import AST (Tree (..), QualTree (..))
import Parser as Parser
import Evaluator as Eval
import Web as Web
import TypeChecker as TypeChecker
import JSHelpers (ctrlKeyPressed, getType)

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Map (empty)
import Data.Array (cons)
import Data.Traversable (for_)
import Data.Tuple (Tuple (..), fst, snd, uncurry)
import Data.Foldable (foldr)
import Data.List ((:), List(..))

import Partial.Unsafe (unsafePartial)

import Effect (Effect)
import Effect.Console (log)
import JQuery as J
import Control.Alternative ((<|>))

main :: Effect Unit
main = log "hello"

makeCE :: String -> String -> Effect Unit
makeCE input selector = do
  clearInfo
  container <- J.select selector
  doWithJust (parseExpr input) \(Tuple expr nextIdx) -> do
    let env = preludeEnv
    showExprIn
      (Tuple (maybeToList $ Tuple "nexteval" <$> lmom env expr) expr)
      nextIdx
      env
      []
      container
      Nothing

makeCEwithDefs :: String -> String -> String -> Effect Unit
makeCEwithDefs input defs selector = do
  clearInfo
  container <- J.select selector
  doWithJust (parseExpr input) \(Tuple expr nextIdx)-> do
    let env = stringToEnv defs
    showExprIn
      (Tuple (maybeToList $ Tuple "nexteval" <$> lmom env expr) expr)
      nextIdx
      env
      []
      container
      Nothing

makeCEwithHistory :: String -> String -> String -> Effect Unit
makeCEwithHistory input selector histSelector = do
  clearInfo
  container <- J.select selector
  histContainer <- J.select histSelector
  doWithJust (parseExpr input) \(Tuple expr nextIdx) -> do
    let env = preludeEnv
    showExprIn
      (Tuple (maybeToList $ Tuple "nexteval" <$> lmom env expr) expr)
      nextIdx
      env
      []
      container
      (Just histContainer)

makeCEwithDefsAndHistory :: String -> String -> String -> String -> Effect Unit
makeCEwithDefsAndHistory  input defs selector histSelector = do
  clearInfo
  container <- J.select selector
  histContainer <- J.select histSelector
  doWithJust (parseExpr input) \(Tuple expr nextIdx) -> do
    let env = stringToEnv defs
    showExprIn
      (Tuple (maybeToList $ Tuple "nexteval" <$> lmom env expr) expr)
      nextIdx
      env
      []
      container
      (Just histContainer)

-- | Try to parse the given expression and report parser errors.
parseExpr :: String -> Effect (Maybe (Tuple AST.TypeTree Int))
parseExpr input = case Parser.parseExpr input of
  Left error -> do
    showError "Parser" (show error)
    pure Nothing
  Right (Tuple expr nextIdx) -> pure $ Just (Tuple expr nextIdx)

eval1 :: Int -> Eval.Env -> AST.TypeTree -> Either String (Tuple AST.TypeTree Int)
eval1 nextIdx env expr = case Eval.runEvalM nextIdx (Eval.eval1 env expr) of
  Left err             -> Left $ show err
  Right exprAndNextIdx -> Right exprAndNextIdx

eval1' :: Int -> Eval.Env -> AST.TypeTree -> Tuple AST.TypeTree Int
eval1' nextIdx env expr = case eval1 nextIdx env expr of
  Left _               -> Tuple expr nextIdx
  Right exprAndNextIdx -> exprAndNextIdx


-- Index of the left-most-outer-most evaluable expression
lmom :: Eval.Env -> AST.TypeTree -> Maybe Int
lmom env expr = case eval1 0 env expr of
  Right _ -> pure (AST.index expr)
  Left  _ -> case expr of
    Atom   _ _  -> Nothing
    List   _ ts -> foldr (<|>) Nothing (map (lmom env) ts)
    NTuple _ ts -> foldr (<|>) Nothing (map (lmom env) ts)
    Binary _ _ l r -> lmom env l <|> lmom env r
    Unary  _ _ t   -> lmom env t
    SectL  _ t _   -> lmom env t
    SectR  _ _ t   -> lmom env t
    PrefixOp _ _   -> Nothing
    IfExpr _ c t e -> lmom env c <|> lmom env t <|> lmom env e
    ArithmSeq _ x ms me -> lmom env x <|> (ms >>= lmom env) <|> (me >>= lmom env)
    LetExpr _ ds e -> foldr (\(Tuple _ e) i -> lmom env e <|> i) Nothing ds <|> lmom env e
    Lambda _ _ e -> lmom env e
    App _ f as -> lmom env f <|> foldr (<|>) Nothing (map (lmom env) as)
    ListComp _ e qs -> lmom env e <|> foldr (<|>) Nothing (map (lmom' env) qs)
 where
  lmom' :: Eval.Env -> AST.TypeQual -> Maybe Int
  lmom' env (Gen _ _ e) = lmom env e
  lmom' env (Let _ _ e) = lmom env e
  lmom' env (Guard _ e) = lmom env e

maybeToList :: forall a. Maybe a -> List a
maybeToList Nothing  = Nil
maybeToList (Just x) = x:Nil

makeCallback :: Int
             -> Eval.Env
             -> Array (Tuple Web.Highlight AST.TypeTree)
             -> J.JQuery
             -> Maybe J.JQuery
             -> Web.Highlight
             -> Web.Callback
makeCallback nextIdx env history container histContainer currHighlight expr hole event jq = do
  J.stopImmediatePropagation event
  let evalFunc  = if ctrlKeyPressed event then Eval.eval nextIdx else eval1' nextIdx
      evaluated = evalFunc env expr -- :: Tuple TypeTree Index
      evalExpr  = fst evaluated
      nextIdx'  = snd evaluated
  case getType event of
    "click"     -> if evalExpr /= expr
                   then showExprIn
                     (Tuple
                      ( Tuple "evaluated" (AST.index evalExpr)
                      : (maybeToList $ Tuple "nexteval" <$> lmom env (hole evalExpr)))
                      (hole evalExpr))
                     nextIdx'
                     env
                     (cons
                      (Tuple
                        (Tuple "clicked" (AST.index expr) : currHighlight)
                        (hole expr))
                      history)
                     container
                     histContainer
                   else pure unit
    "mouseover" -> do
                     log $ show expr
                     log $ show currHighlight
                     case eval1 nextIdx env expr of
                       Right (Tuple expr' _) -> do -- index can be ignored here (I guess...)
                         log $ show expr'
                         J.addClass "highlight" jq
                       Left err   -> log err
    "mouseout"  -> void $ J.removeClass "highlight" jq
    _           -> pure unit
  pure unit

exprToJQuery :: Web.Callback -> Tuple Web.Highlight AST.TypeTree -> Effect J.JQuery
exprToJQuery callback = uncurry Web.exprToDiv >>> Web.divToJQuery true callback

-- | Clear the contents of info div.
clearInfo :: Effect Unit
clearInfo = void $ J.select "#info" >>= J.clear

-- | Create an info div and display an error inside.
showError :: String -> String -> Effect Unit
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
doWithJust :: forall a. Effect (Maybe a) -> (a -> Effect Unit) -> Effect Unit
doWithJust mMaybe f = do
  mValue <- mMaybe
  case mValue of
    Nothing -> pure unit
    Just x  -> f x

-- | Given an evaluation environment, try to infer the types inside of it.
buildTypeEnvironment :: Partial => Eval.Env -> Maybe TypeChecker.TypeEnv
buildTypeEnvironment env =
  let defs = Eval.envToDefs env
  in case TypeChecker.tryInferEnvironment defs of
    Left error -> Nothing
    Right typedEnv -> Just typedEnv

-- | Type check an expression using a given typed environment.
-- | Construct a div tree from the given typed expression.
typeCheckExpression :: Partial => TypeChecker.TypeEnv -> AST.TypeTree -> Effect (Maybe AST.TypeTree)
typeCheckExpression typedEnv expr = do
  case TypeChecker.runInferWith typedEnv false (TypeChecker.inferExpr expr) of
    Left typeError -> do
      showError "Expression" (AST.prettyPrintTypeError typeError)
      pure Nothing
    Right typedExpr -> do
      pure $ Just typedExpr

-- | Construct a div tree from the given typed expression.
buildDivTreeFromExpression :: (Tuple Web.Highlight AST.TypeTree)
                           -> Int
                           -> Eval.Env
                           -> Array (Tuple Web.Highlight AST.TypeTree)
                           -> J.JQuery
                           -> Maybe J.JQuery
                           -> Effect Unit
buildDivTreeFromExpression typedExpr nextIdx env history container histContainer = do
    content <- exprToJQuery
      (makeCallback nextIdx env history container histContainer (fst typedExpr))
      typedExpr
    J.clear container
    J.append content container
    case histContainer of
      Nothing -> pure unit
      Just histContainer -> do
        J.clear histContainer
        for_ history $ \typedExpr -> do
          histExpr <- exprToJQuery (\_ _ _ _ -> pure unit) typedExpr
          histDiv <- J.create "<div></div>"
          J.addClass "history-element" histDiv
          J.append histExpr histDiv
          J.append histDiv histContainer
        pure unit
    pure unit

-- | Show the given expression inside a given environment after the types of the environment as
-- | well as the expression have been inferred.
showExprIn :: (Tuple Web.Highlight AST.TypeTree)
           -> Int
           -> Eval.Env
           -> Array (Tuple Web.Highlight AST.TypeTree)
           -> J.JQuery
           -> Maybe J.JQuery
           -> Effect Unit
showExprIn expr nextIdx env history container histContainer = do
  let tree = snd expr
  let highlight = fst expr
  -- type checking takes too long and types are not displayed in the UI!
  -- typed <- maybe tree id <$> unsafePartial (typeCheckExpression preludeTyped tree)
  let typed = tree
  buildDivTreeFromExpression (Tuple highlight typed) nextIdx env history container histContainer

stringToEnv :: String -> Eval.Env
stringToEnv str = case Parser.parseDefs str of
  Left _     -> empty
  Right (Tuple defs _) -> Eval.defsToEnv defs

preludeTyped :: Partial => TypeChecker.TypeEnv
preludeTyped = case buildTypeEnvironment preludeEnv of
  Just env -> env
  Nothing -> TypeChecker.emptyTypeEnv

preludeEnv :: Eval.Env
preludeEnv = stringToEnv prelude

prelude :: String
prelude =
  "data Maybe a = Nothing | Just a\n" <>
  "data List a = Nil | Cons a (List a)\n" <>
  "data IList a = INil | a :: (IList a)\n" <>
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
