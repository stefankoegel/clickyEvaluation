module Evaluator where

import Prelude (class Show, class Semigroup, Unit, Ordering(..), (++), ($), unit, return, (<*>), (<$>), pure, void, (==), otherwise, (>>=), (<), negate, (>), (>=), (<=), (/=), (-), (+), mod, div, (*), (<<<), compare, id, const, bind, show, map)
import Data.List (List(Nil, Cons), singleton, concatMap, intersect, zipWithA, length, (:), replicate, drop, updateAt, (!!),concat)
import Data.StrMap (StrMap)
import Data.StrMap as Map
import Data.Tuple (Tuple(Tuple))
import Data.Maybe (Maybe(..))
import Data.Foldable (foldl, foldr, foldMap, product)
import Data.Traversable (traverse)
import Data.Identity (Identity, runIdentity)
import Data.Either (Either(..), either)
import Data.Monoid (class Monoid)

import Control.Apply ((*>))
import Control.Alt ((<|>))
import Control.Monad.State.Trans (StateT, modify, execStateT)
import Control.Monad.Except.Trans (ExceptT, throwError, runExceptT)

import AST (Atom(..), Binding(..), Definition(Def), Expr(..), Op(..),Path(..))

data EvalError =
    PathError Path Expr
  | IndexError Int Int
  | DivByZero
  | EvalError Expr
  | BinaryOpError Op Expr Expr
  | UnaryOpError Op Expr
  | NameCaptureError (List String)
  | UnknownFunction String
  | NoMatchingFunction String (List MatchingError)
  | CannotEvaluate Expr
  | NoError
  | MoreErrors EvalError EvalError

instance semigroupEvalError :: Semigroup EvalError where
  append e1 e2 = MoreErrors e1 e2

instance monoidEvalError :: Monoid EvalError where
  mempty = NoError

instance showEvalError :: Show EvalError where
  show (PathError p e)            = "PathError " ++ show p ++ " " ++ show e
  show (IndexError i l)           = "IndexError " ++ show i ++ " " ++ show l
  show DivByZero                  = "DivByZero"
  show (EvalError e)              = "EvalError " ++ show e
  show (BinaryOpError o e1 e2)    = "BinaryOpError " ++ show o ++ " (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (UnaryOpError o e)         = "UnaryOpError " ++ show o ++ " " ++ show e
  show (NameCaptureError ns)      = "NameCaptureError " ++ show ns
  show (UnknownFunction n)        = "UnknownFunction " ++ show n
  show (NoMatchingFunction n mes) = "NoMatchingFunction " ++ show n ++ " " ++ show mes
  show (CannotEvaluate e)         = "CannotEvaluate " ++ show e
  show NoError                    = "NoError"
  show (MoreErrors e1 e2)         = "(MoreErrors " ++ show e1 ++ " " ++ show e2 ++ ")"

data MatchingError =
    MatchingError Binding Expr
  | StrictnessError Binding Expr
  | TooFewArguments (List Binding) (List Expr)

instance showMatchingError :: Show MatchingError where
  show (MatchingError b e)     = "MatchingError " ++ show b ++ " " ++ show e
  show (StrictnessError b e)   = "StrictnessError " ++ show b ++ " " ++ show e
  show (TooFewArguments bs es) = "TooFewArguments " ++ show bs ++ " " ++ show es

type Evaluator = ExceptT EvalError Identity

runEvalM :: forall a. Evaluator a -> Either EvalError a
runEvalM = runIdentity <<< runExceptT

type Matcher = ExceptT MatchingError Identity

runMatcherM :: forall a. Matcher a -> Either MatchingError a
runMatcherM = runIdentity <<< runExceptT


mapWithPath :: Path -> (Expr -> Evaluator Expr) -> Expr -> Evaluator Expr
mapWithPath p f = go p
  where
  go End e     = f e
  go (Fst p) e = case e of
    Binary op e1 e2 -> Binary op <$> go p e1 <*> pure e2
    Unary op e      -> Unary op  <$> go p e
    SectL e op      -> SectL     <$> go p e <*> pure op
    IfExpr ce te ee -> IfExpr <$> go p ce <*> pure te <*> pure ee
    Lambda bs body  -> Lambda bs <$> go p body
    App e es        -> App       <$> go p e <*> pure es
    _               -> throwError $ PathError (Fst p) e
  go (Snd p) e = case e of
    Binary op e1 e2 -> Binary op e1 <$> go p e2
    SectR op e      -> SectR op     <$> go p e
    IfExpr ce te ee -> IfExpr <$> pure ce <*> go p te <*> pure ee
    _               -> throwError $ PathError (Snd p) e
  go (Thrd p) e = case e of
    IfExpr ce te ee -> IfExpr <$> pure ce <*> pure te <*> go p ee
    _               -> throwError $ PathError (Thrd p) e
  go (Nth n p) e = case e of
    List es  -> List  <$> mapIndex n (go p) es
    NTuple es -> NTuple <$> mapIndex n (go p) es
    App e es -> App e <$> mapIndex n (go p) es
    _        -> throwError $ PathError (Nth n p) e

mapIndex :: forall a. Int -> (a -> Evaluator a) -> (List a) -> Evaluator (List a)
mapIndex i f as = do
  case as !! i of
    Nothing -> throwError $ IndexError i (length as)
    Just a  -> do
      a' <- f a
      case updateAt i a' as of
        Nothing  -> throwError $ IndexError i (length as)
        Just as' -> return as'

evalPath1 :: Env -> Path -> Expr -> Either EvalError Expr
evalPath1 env path expr = runEvalM $ mapWithPath path (eval1 env) expr

type Env = StrMap (List (Tuple (List Binding) Expr))

defsToEnv :: (List Definition) -> Env
defsToEnv = foldl insertDef Map.empty

envToDefs :: Env -> (List Definition)
envToDefs env = concat $ map tupleToDef $ Data.StrMap.toList env
  where
    tupleToDef (Tuple name defs) = map
                                    (\(Tuple bin expr) -> Def name bin expr)
                                    defs

insertDef :: Env -> Definition -> Env
insertDef env (Def name bindings body) = case Map.lookup name env of
  Nothing   -> Map.insert name (singleton $ Tuple bindings body) env
  Just defs -> Map.insert name (defs ++ (singleton $ Tuple bindings body)) env

eval1 :: Env -> Expr -> Evaluator Expr
eval1 env expr = case expr of
  (Binary op e1 e2)                  -> binary op e1 e2
  (Unary op e)                       -> unary op e
  (Atom (Name name))                 -> apply env name Nil
  (IfExpr (Atom (Bool true)) te _)   -> return te
  (IfExpr (Atom (Bool false)) _ ee)  -> return ee
--  (List (e:es))                      -> return $ Binary Cons e (List es)
  (App (Binary Composition f g) (Cons e Nil)) -> return $ App f (singleton $ App g (Cons e Nil))
  (App (Lambda binds body) args)     -> tryAll (singleton $ Tuple binds body) args "lambda" Nil
  (App (SectL e1 op) (Cons e2 Nil))           -> binary op e1 e2 <|> (return $ Binary op e1 e2)
  (App (SectR op e2) (Cons e1 Nil))           -> binary op e1 e2 <|> (return $ Binary op e1 e2)
  (App (PrefixOp op) (Cons e1 (Cons e2 Nil)))         -> binary op e1 e2 <|> (return $ Binary op e1 e2)
  (App (Atom (Name name)) args)      -> apply env name args
  (App (App func es) es')            -> return $ App func (es ++ es')
  _                                  -> throwError $ CannotEvaluate expr

eval :: Env -> Expr -> Expr
eval env expr =
  if expr == evald
    then expr
    else eval env evald
  where
  evald :: Expr
  evald = either (const expr') id $ runEvalM $ eval1 env expr'
  expr' :: Expr
  expr' = case expr of
    (Binary op e1 e2)  ->
      Binary op (eval env e1) (eval env e2)
    (Unary op e)       ->
      Unary op (eval env e)
    (IfExpr c t e)     ->
      IfExpr (eval env c) t e
    (App f args)       -> do
      App (eval env f) args
    _                  ->
      expr

wrapLambda :: (List Binding) -> (List Expr) -> Expr -> Evaluator Expr
wrapLambda binds args body =
  case compare (length binds) (length args) of
    EQ -> return body
    GT -> return $ Lambda (drop (length args) binds) body
    LT -> return $ App body (drop (length binds) args)


binary :: Op -> Expr -> Expr -> Evaluator Expr
binary = go
  where
  retA = return <<< Atom
  go Power (Atom (AInt i)) (Atom (AInt j)) = retA $ AInt $ product $ replicate j i

  go Mul (Atom (AInt i)) (Atom (AInt j)) = retA $ AInt $ i * j
  go Div (Atom (AInt i)) (Atom (AInt 0)) = throwError DivByZero
  go Div (Atom (AInt i)) (Atom (AInt j)) = retA $ AInt $ (i `div` j)
  go Mod (Atom (AInt i)) (Atom (AInt 0)) = throwError DivByZero
  go Mod (Atom (AInt i)) (Atom (AInt j)) = retA $ AInt $ i `mod` j

  go Add (Atom (AInt i)) (Atom (AInt j)) = retA $ AInt $ i + j
  go Sub (Atom (AInt i)) (Atom (AInt j)) = retA $ AInt $ i - j

  go Colon  e          (List es)  = return $ List $ e:es
  go Append (List es1) (List es2) = return $ List $ es1 ++ es2

  go Equ  (Atom a1) (Atom a2) = retA $ Bool $ a1 == a2
  go Neq (Atom a1) (Atom a2) = retA $ Bool $ a1 /= a2
  go Leq (Atom (AInt i)) (Atom (AInt j)) = retA $ Bool $ i <= j
  go Lt  (Atom (AInt i)) (Atom (AInt j)) = retA $ Bool $ i < j
  go Geq (Atom (AInt i)) (Atom (AInt j)) = retA $ Bool $ i >= j
  go Gt  (Atom (AInt i)) (Atom (AInt j)) = retA $ Bool $ i > j

  go And (Atom (Bool true))  b = return b
  go And (Atom (Bool false)) _ = retA $ Bool $ false

  go Or  (Atom (Bool true))  _ = retA $ Bool $ true
  go Or  (Atom (Bool false)) b = return b

  go Dollar f e = return $ App f (singleton e)

  go op e1 e2 = throwError $ BinaryOpError op e1 e2

unary :: Op -> Expr -> Evaluator Expr
unary Sub (Atom (AInt i)) = return $ Atom $ AInt (-i)
unary op e = throwError $ UnaryOpError op e

apply :: Env -> String -> (List Expr) -> Evaluator Expr
apply env name args = case Map.lookup name env of
  Nothing    -> throwError $ UnknownFunction name
  Just cases -> tryAll cases args name Nil

tryAll :: (List (Tuple (List Binding) Expr)) -> (List Expr) -> String -> (List MatchingError) -> Evaluator Expr
tryAll Nil                        _    name errs = throwError $ NoMatchingFunction name errs
tryAll (Cons (Tuple binds body) cases) args name errs | (length args) < (length binds) = tryAll cases args name (errs ++ (singleton $ TooFewArguments binds args))
tryAll (Cons (Tuple binds body) cases) args name errs = case runMatcherM $ matchls' binds args of
  Right replMap                 -> replace' replMap body >>= wrapLambda binds args
  Left se@(StrictnessError _ _) -> throwError $ NoMatchingFunction name (errs ++ singleton se)
  Left err                      -> tryAll cases args name (errs ++ singleton err)

whnf :: Expr -> Boolean
whnf (Atom (Name _)) = false
whnf (Atom _)        = true
whnf (List _)        = true
whnf (NTuple _)      = true
whnf _               = false

checkStrictness :: Binding -> Expr -> MatchingError
checkStrictness bs es | whnf es   = MatchingError bs es
                      | otherwise = StrictnessError bs es


matchls' :: (List Binding) -> (List Expr) -> Matcher (StrMap Expr)
matchls' bs es = execStateT (zipWithA match' bs es) Map.empty

match' :: Binding -> Expr -> StateT (StrMap Expr) Matcher Unit
match' (Lit (Name name)) e                   = modify (Map.insert name e)
match' (Lit ba)          (Atom ea)           = case ba == ea of
                                                 true  -> return unit
                                                 false -> throwError $ MatchingError (Lit ba) (Atom ea)
match' (Lit b)           e                   = throwError $ checkStrictness (Lit b) e

match' (ConsLit b bs)    (Binary Colon e es)  = match' b e *> match' bs es
match' (ConsLit b bs)    (List (Cons e es))  = match' (ConsLit b bs) (Binary Colon e (List es))
match' (ConsLit b bs)    (List Nil)           = throwError $ MatchingError (ConsLit b bs) (List Nil)
match' (ConsLit b bs)    e                   = throwError $ checkStrictness (ConsLit b bs) e

match' (ListLit (Cons b bs))  (Binary Colon e es)  = match' b e *> match' (ListLit bs) es
match' (ListLit bs)      (List es)           = case length bs == length es of
                                                 true  -> void $ zipWithA match' bs es
                                                 false -> throwError $ MatchingError (ListLit bs) (List es)
match' (ListLit bs)      e                   = throwError $ checkStrictness (ListLit bs) e

match' (NTupleLit bs)    (NTuple es)         = case length bs == length es of
                                                 true  -> void $ zipWithA match' bs es
                                                 false -> throwError $ MatchingError (NTupleLit bs) (NTuple es)
match' (NTupleLit bs)    e                   = throwError $ checkStrictness (NTupleLit bs) e

replace' :: StrMap Expr -> Expr -> Evaluator Expr
replace' subs = go
  where
  go expr = case expr of
    a@(Atom (Name name)) -> case Map.lookup name subs of
      Just subExpr -> return subExpr
      Nothing      -> return a
    (List exprs)         -> List <$> (traverse go exprs)
    (NTuple exprs)       -> NTuple <$> (traverse go exprs)
    (Binary op e1 e2)    -> Binary <$> pure op <*> go e1 <*> go e2
    (Unary op e)         -> Unary <$> pure op <*> go e
    (SectL e op)         -> SectL <$> go e <*> pure op
    (SectR op e)         -> SectR <$> pure op <*> go e
    (IfExpr ce te ee)    -> IfExpr <$> go ce <*> go te <*> go ee
    (Lambda binds body)  -> (avoidCapture subs binds) *> (Lambda <$> pure binds <*> replace' (foldr Map.delete subs (boundNames' binds)) body)
    (App func exprs)     -> App <$> go func <*> traverse go exprs
    e                    -> return e

avoidCapture :: StrMap Expr -> (List Binding) -> Evaluator Unit
avoidCapture subs binds = case intersect (concatMap freeVariables $ Map.values subs) (boundNames' binds) of
  Nil       -> return unit
  captures -> throwError $ NameCaptureError captures

freeVariables :: Expr -> (List String)
freeVariables _ = Nil
-- freeVariables = nub <<< foldExpr
--   (\a -> case a of
--     Name name -> singleton $ name
--     _         -> Nil)
--   concat
--   concat
--   (\_ f1 f2 -> f1 ++ f2)
--   (\_ f -> f)
--   (\f _ -> f)
--   (\_ f -> f)
--   (\_ -> Nil)
--   (\f1 f2 f3 -> f1 ++ f2 ++ f3)
--   (\bs f -> nub f \\ boundNames' bs)
--   (\f fs -> f ++ concat fs)

boundNames' :: (List Binding) -> (List String)
boundNames' = concatMap boundNames

boundNames :: Binding -> (List String)
boundNames = go
  where
  go (Lit (Name name)) = singleton name
  go (ConsLit b1 b2)   = go b1 ++ go b2
  go (ListLit bs)      = foldMap go bs
  go (NTupleLit bs)    = foldMap go bs
  go _                 = Nil
