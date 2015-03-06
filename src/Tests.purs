module Tests where

import Data.Either
import Data.Maybe

import AST
import Parser
import Evaluator


testEnv :: Env
testEnv = defsToEnv $ case (Parser.parseDefs defs) of Right env -> env
  where
  defs = """
    double x = x + x
    fact 0 = 1
    fact n = n * fact (n - 1)
    fib 0 a b = a
    fib n a b = fib (n - 1) b (a + b)
    """

testExpr :: String -> Expr
testExpr str = case (Parser.parseExpr str) of Right expr -> expr

test :: String -> Path -> Maybe Expr
test str path = evalPath1 testEnv path (testExpr str)
