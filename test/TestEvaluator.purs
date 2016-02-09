module Test.Evaluator where

import Prelude (Unit, bind, (++), ($), show, unit, return, (==), (<<<), (+), negate, (*))
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Data.StrMap as M
import Data.List (List, singleton)

import Text.Parsing.Parser (runParser)

import Control.Monad.Writer (Writer, tell)

import Parser (definitions, expression)
import Evaluator (eval, eval1, runEvalM, defsToEnv)

tell' :: forall a. a -> Writer (List a) Unit
tell' = tell <<< singleton

eval1test :: String -> String -> String -> Writer (List String) Unit
eval1test name input expected = case (Tuple (runParser input expression) (runParser expected expression)) of
  (Tuple (Right inExp) (Right expExp)) ->
    case runEvalM (eval1 M.empty inExp) of
      (Right eval1Exp) -> 
        if eval1Exp == expExp
          then return unit -- log $ "Eval success (" ++ name ++ ")"
          else tell' $ "Eval fail (" ++ name ++ "): " ++ show eval1Exp ++ " should be " ++ show expExp
      (Left err) -> tell' $ "Eval fail (" ++ name ++ "): " ++ show err ++ ")"
  _ -> tell' $ "Parse fail (" ++ name ++ ")"

eval1EnvTest :: String -> String -> String -> String -> Writer (List String) Unit
eval1EnvTest name env input expected = case (Tuple (Tuple (runParser input expression) (runParser expected expression)) (runParser env definitions)) of
  (Tuple (Tuple (Right inExp) (Right expExp)) (Right defs)) ->
    case runEvalM (eval1 (defsToEnv defs) inExp) of
      (Right eval1Exp) -> 
        if eval1Exp == expExp
          then return unit -- log $ "Eval success (" ++ name ++ ")"
          else tell' $ "Eval fail (" ++ name ++ "): " ++ show eval1Exp ++ " should be " ++ show expExp
      (Left err) -> tell' $ "Eval fail (" ++ name ++ "): " ++ show err ++ ")"
  _ -> tell' $ "Parse fail (" ++ name ++ ")"

evalEnvTest :: String -> String -> String -> String -> Writer (List String) Unit
evalEnvTest name env input expected = case (Tuple (Tuple (runParser input expression) (runParser expected expression)) (runParser env definitions)) of
  (Tuple (Tuple (Right inExp) (Right expExp)) (Right defs)) ->
    let evalExp = eval (defsToEnv defs) inExp in
      if evalExp == expExp
        then return unit -- log $ "Eval success (" ++ name ++ ")"
        else tell' $ "Eval fail (" ++ name ++ "): " ++ show evalExp ++ " should be " ++ show expExp
  (Tuple (Tuple pi pe) pd) -> tell' $ "Parse fail (" ++ name ++ "): (input: " ++ show pi ++ ", expected: " ++ show pe ++ ", definitions: " ++ show pd ++ ")"

runTests :: Writer (List String) Unit
runTests = do
  eval1test "add" "1+1" "2"
  eval1test "power" "2^10" "1024"
  eval1test "append" "[1] ++ [2]" "[1, 2]"
  eval1test "cons" "True:[]" "[True]"
  eval1test "lambda" "(\\a b -> a + b) 1 2" "1 + 2"
  eval1test "section1" "(*5) 7" "35"
  eval1test "section2" "(10<) 8" "False"
  eval1test "prefix" "(&&) True True" "True"
  eval1test "if_then_else" "if True then 42 else 0" "42"
  eval1test "pattern_matching1" "(\\(x:xs) -> x) [1, 2, 3]" "1"
  eval1test "pattern_matching2" "(\\[a, b, c] -> c) [1, 2, 3]" "3"
  eval1test "pattern_matching3" "(\\(a, b) (c, d, e) -> d) (1, 2) (3, 2*2, 5)" "2*2"
  eval1test "lambda2" "(\\x y -> [0, x, y, x + y]) 1 2" "[0, 1, 2, 1 + 2]"
  eval1test "string1" "\"as\" ++ \"df\"" "\"asdf\""
  eval1test "string2" "'a' : \"sdf\"" "\"asdf\""

  eval1EnvTest "double_func" "double x = x + x" "double 10" "10 + 10"
  eval1EnvTest "map_func1" "map f [] = []\nmap f (x:xs) = f x : map f xs" "map (^2) []" "[]"
  eval1EnvTest "map_func2" "map f [] = []\nmap f (x:xs) = f x : map f xs" "map (^2) [1, 2, 3]" "(^2) 1 : map (^2) [2, 3]"

  evalEnvTest "evalAll1" "" "1 + 2 + 3" "6"
  evalEnvTest "evalAll2" "" "(2^10) > (10^2)" "True"
  evalEnvTest "evalAll3" "" "3" "3"
  evalEnvTest "evalAll4" "" "x + y" "x + y"
  evalEnvTest "evalAll5" "" "(2 * 5) * x + 2 ^ 3" "10 * x + 8"
  evalEnvTest "evalAll6" "" "1 / 0" "1 / 0"

  evalEnvTest "evalNegNumber1" "" "(-3) - (-4)" "1"
  evalEnvTest "evalNegNumber2" "" "(-2) * (-2)" "4"
  evalEnvTest "evalNegNumber3" "" "-(-(5*5) + 6*6) + 7*7" (show (-(-(5*5) + 6*6) + 7*7)) -- 38
  evalEnvTest "evalNegNumber4" "" "-3 * 7 + 23" "2"


  evalEnvTest "if1" "" "if 10 > 5 then 10 else 5" "10"
  evalEnvTest "if2" "" "if 2 /= 2 then 1 else 0" "0"
  evalEnvTest "if3" "" "if x >= y then 5 * 5 else 6 * 6" "if x >= y then 5 * 5 else 6 * 6"

  evalEnvTest "env1" "x = 10" "x" "10"
  evalEnvTest "env2" "x = 10\ny = 20" "x * y" "200"
  evalEnvTest "env3" "double x = x + x" "double 10" "20"
  evalEnvTest "env4" "double x = x + x" "double (double (double 10))" "80"
  evalEnvTest "env5" "double x = x + x" "double $ double $ double 10" "80"
  evalEnvTest "env6" "double x = x + x" "(double . double . double) 10" "80"
  evalEnvTest "env6" "length (_:xs) = 1 + length xs\nlength [] = 0" "length [1, 2, 3, 4, 5]" "5"

  evalEnvTest "fix" "f x = f x" "f 10" "f 10"

  -- This test gets stuck in an endless loop,
  -- because (((((6 - 1) - 1 ) - 1 ) - 1) - 1) does not match the base case 1.
  -- evalEnvTest "fac" "fac 1 = 1\nfac n = n * fac (n - 1)" "fac 6" "720"

  evalEnvTest "string_third1" "thrd (_:(_:(x:_))) = x" "thrd \"1234\"" "'3'"
  evalEnvTest "string_third2" "thrd [_,_,x,_] = x" "thrd \"1234\"" "'3'"

  evalEnvTest "pattern_matching4" "f ( x :  y : z : rs  ) = (x + y + z) * length rs\nlength (_:xs) = 1 + length xs\nlength [] = 0" "f [2, 3, 5, 8, 11]" "20"
  evalEnvTest "pattern_matching5" "f ( [ x ] : [ y , z ] : [ ] ) = x + y + z" "f [[1],[2,3]]" "6"
  evalEnvTest "pattern_matching6" "f [  [ x ] , [ y , z ] ] = x + y + z" "f [[1],[2,3]]" "6"
  evalEnvTest "pattern_matching7" "f [(a:b:c:rs1), (x:y:z:rs2)] = a * x + b * y + c * z" "f [[1, 2, 3], [100, 10, 1]]" "123"
