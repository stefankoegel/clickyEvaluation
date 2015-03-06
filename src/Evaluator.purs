module Evaluator where

import Data.Array    (head, mapMaybe)
import Data.StrMap   (StrMap(), empty, lookup, insert)
import Data.Tuple
import Data.Maybe
import Data.Foldable (foldl)

import Control.Apply ((*>))
import Control.Monad.State
import Control.Monad.State.Trans
import Control.Monad.State.Class
import Control.Monad.Trans

import AST

type Env = StrMap [Tuple [Binding] Expr]

defsToEnv :: [Definition] -> Env
defsToEnv = foldl insertDef empty

insertDef :: Env -> Definition -> Env
insertDef env (Def name bindings body) = case lookup name env of
  Nothing   -> insert name [Tuple bindings body] env
  Just defs -> insert name (defs ++ [Tuple bindings body]) env

eval1 :: Env -> Expr -> Maybe Expr
eval1 env expr = case expr of
  (Binary op e1 e2) -> binary op e1 e2
  (Unary op e)      -> unary op e
  (App name args)   -> apply env name args
  _                 -> Nothing

binary :: Op -> Expr -> Expr -> Maybe Expr
binary = go
  where
  go Add (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i + j
  go Sub (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i - j
  go Mul (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i * j
  go Div (Atom (Num i)) (Atom (Num 0)) = Nothing
  go Div (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ Math.floor (i / j)

  go And (Atom (Bool true))  b = Just b
  go And (Atom (Bool false)) _ = Just $ Atom $ Bool $ false
  go Or  (Atom (Bool true))  _ = Just $ Atom $ Bool $ true
  go Or  (Atom (Bool false)) b = Just b

  go Cons   e          (List es)  = Just $ List $ e:es
  go Append (List es1) (List es2) = Just $ List $ es1 ++ es2

  go _       _               _               = Nothing

unary :: Op -> Expr -> Maybe Expr
unary Sub (Atom (Num i)) = Just $ Atom $ Num (-i)
unary _   _              = Nothing

apply :: Env -> String -> [Expr] -> Maybe Expr
apply env name args = case lookup name env of
  Nothing    -> Nothing
  Just cases -> head $ mapMaybe app cases
    where
    app :: Tuple [Binding] Expr -> Maybe Expr
    app (Tuple binds body) = matchls binds args body

matchls :: [Binding] -> [Expr] -> Expr -> Maybe Expr
matchls []     []     expr = Just expr
matchls (b:bs) (e:es) expr = do
  expr' <- execStateT (match b e) expr
  matchls bs es expr'
matchls _ _ _ = Nothing

match :: Binding -> Expr -> StateT Expr Maybe Unit
match (Lit (Name x))   e                = modify (replace x e)
match (Lit (Num i))    (Atom (Num j))   | i == j  = return unit
match (Lit (Bool b))   (Atom (Bool b')) | b == b' = return unit
match (ConsLit b bs)   (List (e:es))    = match b e *> match bs (List es)
match (ListLit [])     (List [])        = return unit
match (ListLit (b:bs)) (List (e:es))    = match b e *> match (ListLit bs) (List es)
match _                _                = lift Nothing

replace :: String -> Expr -> Expr -> Expr
replace name value = go
  where
  go expr = case expr of
    a@(Atom (Name str)) -> if str == name then value else a
    (List exprs)        -> List (go <$> exprs)
    (Binary op e1 e2)   -> Binary op (go e1) (go e2)
    (Unary op e)        -> Unary op (go e)
    (SectL e op)        -> SectL (go e) op
    (SectR op e)        -> SectR op (go e)
    (App appName exprs) -> App appName (go <$> exprs)
    e                   -> e
