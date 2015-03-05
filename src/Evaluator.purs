module Evaluator where

import Data.StrMap
import Data.Tuple
import Data.Maybe

import AST

type Env = StrMap (Tuple [Binding] Expr)

defsToEnv :: [Definition] -> Env
defsToEnv _ = empty

eval1 :: Env -> Expr -> Expr
eval1 _ _ = Atom $ Name $ "not_implemented"

apply :: Env -> String -> [Expr] -> Maybe Expr
apply _ _ _ = Nothing

matchAndReplace :: [Binding] -> [Expr] -> Expr -> Maybe Expr
matchAndReplace _ _ _ = Nothing

replace :: String -> Expr -> Expr -> Expr
replace _ _ _ = Atom $ Name $ "not_implemented"
