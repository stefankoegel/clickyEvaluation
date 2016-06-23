module Evaluator
  ( eval
  , eval1
  , runEvalM
  , defsToEnv
  , EvalError(..)
  , MatchingError(..)
  , Env(..)
  ) where

import Prelude hiding (apply)
import Data.List (List(Nil, Cons), singleton, concatMap, intersect, zipWith, zipWithA, length, (:), replicate, drop, concat)
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

import AST (Expr, Tree(..), Atom(..), Binding(..), Definition(Def), Op(..))

data EvalError =
    IndexError Int Int
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
  (Binary _ op e1 e2)                  -> binary env op e1 e2
  (Unary _ op e)                       -> unary env op e
  (Atom _ (Name name))                 -> apply env name Nil
  (IfExpr _ (Atom _ (Bool true)) te _)   -> return te
  (IfExpr _ (Atom _ (Bool false)) _ ee)  -> return ee
  -- (List _ (Cons e es))                      -> return $ Binary unit Colon e (List unit es)
  (App _ (Binary _ Composition f g) (Cons e Nil)) -> return $ App unit f (singleton $ App unit g (Cons e Nil))
  (App _ (Lambda _ binds body) args)     -> tryAll env (singleton $ Tuple binds body) args "lambda" Nil
  (App _ (SectL _ e1 op) (Cons e2 Nil))           -> binary env op e1 e2 <|> (return $ Binary unit op e1 e2)
  (App _ (SectR _ op e2) (Cons e1 Nil))           -> binary env op e1 e2 <|> (return $ Binary unit op e1 e2)
  (App _ (PrefixOp _ op) (Cons e1 (Cons e2 Nil)))         -> binary env op e1 e2 <|> (return $ Binary unit op e1 e2)
  (App _ (Atom _ (Name name)) args)      -> apply env name args
  (App _ (App _ func es) es')            -> return $ App unit func (es ++ es')
  _                                  -> throwError $ CannotEvaluate expr

eval :: Env -> Expr -> Expr
eval env expr = evalToBinding env expr (Lit (Name "_|_"))

evalToBinding :: Env -> Expr -> Binding -> Expr
evalToBinding env expr bind = case bind of
  (Lit (Name "_|_")) -> recurse env expr bind
  (Lit (Name _))     -> expr
  (Lit _)            -> case expr of
    (Atom _ _) -> expr
    _          -> recurse env expr bind

  (ConsLit b bs)     -> case expr of
    (Binary _ Colon e es) -> Binary unit Colon (evalToBinding env e b) (evalToBinding env es bs)
    (List _ (Cons e es))  -> evalToBinding env (Binary unit Colon e (List unit es)) bind
    _                     -> recurse env expr bind

  (ListLit bs)       -> case expr of
    (List _ es) -> if (length es == length bs) then List unit (zipWith (evalToBinding env) es bs) else expr
    _           -> recurse env expr bind

  (NTupleLit bs)     -> case expr of
    (NTuple _ es)  -> NTuple unit (zipWith (evalToBinding env) es bs)
    _              -> recurse env expr bind


recurse :: Env -> Expr -> Binding -> Expr
recurse env expr bind = if expr == eval1d then expr else evalToBinding env eval1d bind
  where
    eval1d :: Expr
    eval1d = either (const expr') id $ runEvalM $ eval1 env expr'
    expr' :: Expr
    expr' = case expr of
      (Binary _ op e1 e2)  ->
        Binary unit op (evalToBinding env e1 bind) (evalToBinding env e2 bind)
      (Unary _ op e)       ->
        Unary unit op (evalToBinding env e bind)
      (List _ es)          ->
        List unit ((\e -> evalToBinding env e bind) <$> es)
      (NTuple _ es)        ->
        NTuple unit ((\e -> evalToBinding env e bind) <$> es)
      (IfExpr _ c t e)     ->
        IfExpr unit (evalToBinding env c bind) t e
      (App _ f args)       -> do
        App unit (evalToBinding env f bind) args
      _                  ->
        expr

wrapLambda :: (List Binding) -> (List Expr) -> Expr -> Evaluator Expr
wrapLambda binds args body =
  case compare (length binds) (length args) of
    EQ -> return body
    GT -> return $ Lambda unit (drop (length args) binds) body
    LT -> return $ App unit body (drop (length binds) args)


binary :: Env -> Op -> Expr -> Expr -> Evaluator Expr
binary env op = case op of
  Power  -> aint Power (\i j -> product $ replicate j i)
  Mul    -> aint Mul (*)
  Add    -> aint Add (+)
  Sub    -> aint Sub (-)
  Colon  -> \e es -> case es of
    (List _ ls) -> return $ List unit $ e:ls
    _         -> throwError $ BinaryOpError Colon e es
  Append -> \es1 es2 -> case (Tuple es1 es2) of
    (Tuple (List _ ls1) (List _ ls2)) -> return $ List unit $ ls1 ++ ls2
    _                                 -> throwError $ BinaryOpError Append es1 es2
  Equ    -> ord Equ (==) (==) (==)
  Neq    -> ord Neq (/=) (/=) (/=)
  Leq    -> ord Leq (<=) (<=) (<=)
  Lt     -> ord Lt  (<)  (<)  (<)
  Geq    -> ord Geq (>=) (>=) (>=)
  Gt     -> ord Gt  (>)  (>)  (>)
  And    -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom _ (Bool false)) _                  )   -> return $ Atom unit $ Bool false
    (Tuple _                     (Atom _ (Bool false))) -> return $ Atom unit $ Bool false
    (Tuple (Atom _ (Bool true))  (Atom _ (Bool true)))  -> return $ Atom unit $ Bool true
    (Tuple _                   _                     )  -> throwError $ BinaryOpError And e1 e2
  Or     -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom _ (Bool true))  _                   )  -> return $ Atom unit $ Bool true
    (Tuple _                     (Atom _ (Bool true)))  -> return $ Atom unit $ Bool true
    (Tuple (Atom _ (Bool false)) (Atom _ (Bool false))) -> return $ Atom unit $ Bool false
    (Tuple _                     _                   )  -> throwError $ BinaryOpError And e1 e2
  Dollar -> (\f e -> return $ App unit f (singleton e))
  Composition -> \e1 e2 -> throwError $ BinaryOpError And e1 e2
  InfixFunc name -> \e1 e2 -> apply env name (e1 : e2 : Nil)
  where
    aint :: Op -> (Int -> Int -> Int) -> Expr -> Expr -> Evaluator Expr
    aint _   f (Atom _ (AInt i)) (Atom _ (AInt j)) = return $ Atom unit $ AInt $ f i j
    aint op  _ e1                e2                = throwError $ BinaryOpError op e1 e2

    ord :: Op -> (Int -> Int -> Boolean) -> (String -> String -> Boolean) -> (Boolean -> Boolean -> Boolean)-> Expr -> Expr -> Evaluator Expr
    ord _  fi _  _  (Atom _ (AInt i))  (Atom _ (AInt j))  = return $ Atom unit $ Bool $ fi i j
    ord _  _  fs _  (Atom _ (Char s1)) (Atom _ (Char s2)) = return $ Atom unit $ Bool $ fs s1 s2
    ord _  _  _  fb (Atom _ (Bool b1)) (Atom _ (Bool b2)) = return $ Atom unit $ Bool $ fb b1 b2
    ord op _  _  _  e1               e2               = throwError $ BinaryOpError op e1 e2


unary :: Env -> Op -> Expr -> Evaluator Expr
unary env Sub (Atom _ (AInt i)) = return $ Atom unit $ AInt (-i)
unary env op e = throwError $ UnaryOpError op e

apply :: Env -> String -> (List Expr) -> Evaluator Expr
apply env "div" (Cons e1 (Cons e2 _)) = division e1 e2 
apply env "mod" (Cons e1 (Cons e2 _)) = modulo e1 e2
apply env name args = case Map.lookup name env of
  Nothing    -> throwError $ UnknownFunction name
  Just cases -> tryAll env cases args name Nil

--builtin ipo
division :: Expr -> Expr -> Evaluator Expr 
division (Atom _ (AInt i)) (Atom _ (AInt 0)) = throwError DivByZero
division (Atom _ (AInt i)) (Atom _ (AInt j)) = return $ Atom unit $ AInt $ div i j
division e1 e2 = throwError $ BinaryOpError (InfixFunc "div") e1 e2

--builtin mod
modulo :: Expr -> Expr -> Evaluator Expr  
modulo (Atom _ (AInt i)) (Atom _ (AInt 0)) = throwError DivByZero
modulo (Atom _ (AInt i)) (Atom _ (AInt j)) = return $ Atom unit $ AInt $ mod i j
modulo e1 e2 = throwError $ BinaryOpError (InfixFunc "mod") e1 e2


tryAll :: Env -> (List (Tuple (List Binding) Expr)) -> (List Expr) -> String -> (List MatchingError) -> Evaluator Expr
tryAll _   Nil                        _    name errs = throwError $ NoMatchingFunction name errs
tryAll env (Cons (Tuple binds body) cases) args name errs | (length args) < (length binds) = tryAll env cases args name (errs ++ (singleton $ TooFewArguments binds args))
tryAll env (Cons (Tuple binds body) cases) args name errs = case runMatcherM $ matchls' env binds args of
  Right replMap                 -> replace' replMap body >>= wrapLambda binds args
  Left se@(StrictnessError _ _) -> throwError $ NoMatchingFunction name (errs ++ singleton se)
  Left err                      -> tryAll env cases args name (errs ++ singleton err)

whnf :: Expr -> Boolean
whnf (Atom _ (Name _)) = false
whnf (Atom _ _)        = true
whnf (List _ _)        = true
whnf (NTuple _ _)      = true
whnf _                 = false

checkStrictness :: Binding -> Expr -> MatchingError
checkStrictness bs es | whnf es   = MatchingError bs es
                      | otherwise = StrictnessError bs es


matchls' :: Env -> (List Binding) -> (List Expr) -> Matcher (StrMap Expr)
matchls' env bs es = execStateT (zipWithA (\b e -> match' b (evalToBinding env e b)) bs es) Map.empty

match' :: Binding -> Expr -> StateT (StrMap Expr) Matcher Unit
match' (Lit (Name name)) e                   = modify (Map.insert name e)
match' (Lit ba)          (Atom _ ea)         = case ba == ea of
                                                 true  -> return unit
                                                 false -> throwError $ MatchingError (Lit ba) (Atom unit ea)
match' (Lit b)           e                   = throwError $ checkStrictness (Lit b) e

match' (ConsLit b bs)    (Binary _ Colon e es) = match' b e *> match' bs es
match' (ConsLit b bs)    (List _ (Cons e es))  = match' (ConsLit b bs) (Binary unit Colon e (List unit es))
match' (ConsLit b bs)    (List _ Nil)          = throwError $ MatchingError (ConsLit b bs) (List unit Nil)
match' (ConsLit b bs)    e                     = throwError $ checkStrictness (ConsLit b bs) e

match' (ListLit (Cons b bs)) (Binary _ Colon e es) = match' b e *> match' (ListLit bs) es
match' (ListLit bs)      (List _ es)               = case length bs == length es of
                                                       true  -> void $ zipWithA match' bs es
                                                       false -> throwError $ MatchingError (ListLit bs) (List unit es)
match' (ListLit bs)      e                         = throwError $ checkStrictness (ListLit bs) e

match' (NTupleLit bs)    (NTuple _ es) = case length bs == length es of
                                           true  -> void $ zipWithA match' bs es
                                           false -> throwError $ MatchingError (NTupleLit bs) (NTuple unit es)
match' (NTupleLit bs)    e             = throwError $ checkStrictness (NTupleLit bs) e

replace' :: StrMap Expr -> Expr -> Evaluator Expr
replace' subs = go
  where
  go expr = case expr of
    a@(Atom _ (Name name)) -> case Map.lookup name subs of
      Just subExpr -> return subExpr
      Nothing      -> return a
    (List _ exprs)         -> List unit <$> (traverse go exprs)
    (NTuple _ exprs)       -> NTuple unit <$> (traverse go exprs)
    (Binary _ op e1 e2)    -> Binary unit <$> pure op <*> go e1 <*> go e2
    (Unary _ op e)         -> Unary unit <$> pure op <*> go e
    (SectL _ e op)         -> SectL unit <$> go e <*> pure op
    (SectR _ op e)         -> SectR unit <$> pure op <*> go e
    (IfExpr _ ce te ee)    -> IfExpr unit <$> go ce <*> go te <*> go ee
    (Lambda _ binds body)  -> (avoidCapture subs binds) *> (Lambda unit <$> pure binds <*> replace' (foldr Map.delete subs (boundNames' binds)) body)
    (App _ func exprs)     -> App unit <$> go func <*> traverse go exprs
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
