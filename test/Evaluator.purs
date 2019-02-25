module Test.Evaluator where

import Prelude
import Data.Either (Either(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Map as M
import Data.List (List(Nil))

-- import Control.Monad.Writer (Writer, tell)

import Effect (Effect)
import Effect.Console (log)

import Parser (definitions, expression, runParserIndent)
import Evaluator (eval, eval1, runEvalM, defsToEnv,Env)
import Test.Parser (prelude, parsedPrelude, class Testable, equals, isValidlyIndexed)

import Test.Utils (tell, padLeft)

tell' :: String -> Effect Unit
tell' = tell

preludeEnv :: Env
preludeEnv = case runParserIndent definitions prelude of
  Right (Tuple env _) -> defsToEnv env
  Left _    -> defsToEnv Nil

eval1test :: String -> String -> String -> Effect Unit
eval1test name input expected = case (Tuple (runParserIndent expression input) (runParserIndent expression expected)) of
  (Tuple (Right (Tuple inExp i)) (Right (Tuple expExp _))) ->
    case runEvalM i (eval1 M.empty inExp) of
      (Right (Tuple eval1Exp _))
        | not (eval1Exp `equals` expExp) -> tell'
             $ "Eval fail (" <> name <> "):\n"
            <> "Input:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show eval1Exp) <> "\n"
            <> "Expected:\n"
            <> padLeft (show expExp)
        | not (isValidlyIndexed eval1Exp) -> tell'
             $ "Indexation fail (" <> name <> "):\n"
            <> "Input:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show eval1Exp) <> "\n"
            <> "Expected:\n"
            <> padLeft (show expExp)
        | otherwise -> log $ "Eval success (" <> name <> ")"
      (Left err) -> tell'
        $ "Eval fail (" <> name <> "):\n"
        <> padLeft (show err)
  _ -> tell' $ "Parse fail (" <> name <> ")"

eval1EnvTest :: String -> String -> String -> String -> Effect Unit
eval1EnvTest name env input expected = case (Tuple (Tuple (runParserIndent expression input) (runParserIndent expression expected)) (runParserIndent definitions env)) of
  (Tuple (Tuple (Right (Tuple inExp i)) (Right (Tuple expExp _))) (Right (Tuple defs _))) ->
    case runEvalM i (eval1 (defsToEnv defs) inExp) of
      (Right (Tuple eval1Exp _))
        | not (eval1Exp `equals` expExp) -> tell'
             $ "Eval fail (" <> name <> "):\n"
            <> "Input:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show eval1Exp) <> "\n"
            <> "Expected:\n"
            <> padLeft (show expExp)
        | not (isValidlyIndexed eval1Exp) -> tell'
             $ "Indexation fail (" <> name <> "):\n"
            <> "Input:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show eval1Exp) <> "\n"
            <> "Expected:\n"
            <> padLeft (show expExp)
        | otherwise -> log $ "Eval success (" <> name <> ")"
      (Left err) -> tell'
        $ "Eval fail (" <> name <> "):\n"
        <> padLeft (show err)
  _ -> tell' $ "Parse fail (" <> name <> ")"

evalEnvTest :: String -> String -> String -> String -> Effect Unit
evalEnvTest name env input expected = case (Tuple (Tuple (runParserIndent expression input) (runParserIndent expression expected)) (runParserIndent definitions env)) of
  (Tuple (Tuple (Right (Tuple inExp i)) (Right (Tuple expExp _))) (Right (Tuple defs _))) ->
    let evalExp = fst (eval i (defsToEnv defs) inExp) in
      if evalExp `equals` expExp
        then if isValidlyIndexed evalExp
                then log $ "Eval success (" <> name <> ")"
                else tell'
                  $ "Eval fail (" <> name <> "):\n"
                 <> "Input String:\n"
                 <> padLeft input <> "\n"
                 <> "Input Parsed:\n"
                 <> padLeft (show inExp) <> "\n"
                 <> "Output:\n"
                 <> padLeft (show evalExp) <> "\n"
                 <> "Expected String:\n"
                 <> padLeft expected <> "\n"
                 <> "Expected Parsed:\n"
                 <> padLeft (show expExp) <> "\n"
                 <> "Definitions String:\n"
                 <> padLeft env <> "\n"
                 <> "Definitions Parsed:\n"
                 <> padLeft (show defs)
        else tell'
             $ "Eval fail (" <> name <> "):\n"
            <> "Input String:\n"
            <> padLeft input <> "\n"
            <> "Input Parsed:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show evalExp) <> "\n"
            <> "Expected String:\n"
            <> padLeft expected <> "\n"
            <> "Expected Parsed:\n"
            <> padLeft (show expExp) <> "\n"
            <> "Definitions String:\n"
            <> padLeft env <> "\n"
            <> "Definitions Parsed:\n"
            <> padLeft (show defs)
  (Tuple (Tuple pi pe) pd) -> tell'
     $ "Parse fail (" <> name <> "):\n"
    <> "Input:\n"
    <> padLeft (show pi) <> "\n"
    <> "Expected:\n"
    <> padLeft (show pe) <> "\n"
    <> "Definitions:\n"
    <> padLeft (show pd)

evalTest :: String -> String -> String -> Effect Unit
evalTest n = evalEnvTest n ""


evalPreludeTest :: String -> String -> String -> Effect Unit
evalPreludeTest name input expected = case (Tuple (runParserIndent expression input) (runParserIndent expression expected)) of
  (Tuple (Right (Tuple inExp i)) (Right (Tuple expExp _))) ->
    let evalExp = fst (eval i preludeEnv inExp) in
      if evalExp `equals` expExp
        then if isValidlyIndexed evalExp
                then log $ "Eval success (" <> name <> ")"
                else tell'
                  $ "Eval fail (" <> name <> "):\n"
                 <> "Input String:\n"
                 <> padLeft input <> "\n"
                 <> "Input Parsed:\n"
                 <> padLeft (show inExp) <> "\n"
                 <> "Output:\n"
                 <> padLeft (show evalExp) <> "\n"
                 <> "Expected String:\n"
                 <> padLeft expected <> "\n"
                 <> "Expected Parsed:\n"
                 <> padLeft (show expExp) <> "\n"
                 <> "Definitions from Prelude!\n"

        else tell'
             $ "Eval fail (" <> name <> "):\n"
            <> "Input String:\n"
            <> padLeft input <> "\n"
            <> "Input Parsed:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show evalExp) <> "\n"
            <> "Expected String:\n"
            <> padLeft expected <> "\n"
            <> "Expected Parsed:\n"
            <> padLeft (show expExp) <> "\n"
            <> "Definitions from Prelude!\n"

  (Tuple pi pe) -> tell'
     $ "Parse fail (" <> name <> "):\n"
    <> "Input:\n"
    <> padLeft (show pi) <> "\n"
    <> "Expected:\n"
    <> padLeft (show pe) <> "\n"


runTests :: Effect Unit
runTests = do
  eval1test "add" "1+1" "2"
  eval1test "power" "2^10" "1024"
  eval1test "append" "[1] ++ [2]" "[1, 2]"
  eval1test "cons" "True:[]" "[True]"
  eval1test "lambda" "(\\a b -> a + b) 1 2" "1 + 2"
  eval1test "section1" "(*5) 7" "7 * 5"
  eval1test "section2" "(10<) 8" "10 < 8"
  eval1test "prefix" "(&&) True True" "True && True"
  eval1test "if_then_else" "if True then 42 else 0" "42"
  eval1test "pattern_matching1" "(\\(x:xs) -> x) [1, 2, 3]" "1"
  eval1test "pattern_matching2" "(\\[a, b, c] -> c) [1, 2, 3]" "3"
  eval1test "pattern_matching3" "(\\(a, b) (c, d, e) -> d) (1, 2) (3, 2*2, 5)" "2*2"
  eval1test "lambda2" "(\\x y -> [0, x, y, x + y]) 1 2" "[0, 1, 2, 1 + 2]"
  eval1test "lambda3" "(\\a -> a + a) 1" "1 + 1"
  eval1test "string1" "\"as\" ++ \"df\"" "\"asdf\""
  eval1test "string2" "'a' : \"sdf\"" "\"asdf\""
  eval1test "listComp1" "[x | x <-      [1..10]]"      "[x | x <- (1 : [2..10])]"
  eval1test "listComp2" "[x | x <- (1 : [2..10])]" "1 : [x | x <-      [2..10]]"
  eval1test "listComp3" "[x | x <-      [2..10]]"      "[x | x <- (2 : [3..10])]"
  eval1test "listComp4" "[x | x <- (2 : [3..10])]" "2 : [x | x <-      [3..10]]"


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

  evalEnvTest "eval_list" "" "[2 + 2, 3 * 3]" "[4, 9]"
  evalEnvTest "eval_tuple" "" "(2+2, 3 * 3)" "(4, 9)"

  -- This test gets stuck in an endless loop,
  -- evalEnvTest "fix" "f x = f x" "f 10" "f 10"

  evalEnvTest "fac" "fac 1 = 1\nfac n = n * fac (n - 1)" "fac 6" "720"
  evalPreludeTest "prelude" "sum (map (^2) [1,2,3,4])" "30"

  evalEnvTest "TAE2a"
    ( prelude <> "\n" <>
      "pair (x:y:rs) = (x, y) : pair (y:rs)\n" <>
      "pair _        = []")
    "pair [1, 2, 3, 4]"
    "[(1, 2), (2, 3), (3, 4)]"
  evalPreludeTest "TAE2b" "foldr (\\a b -> a + b * 10) 0 [3, 2, 1]" "123"
  evalEnvTest "TAE2c"
    (prelude <> "\nsublist f t ls = drop f (take (t + f) ls)\n")
    "sublist 1 3 [0, 1, 2, 3, 4]"
    "[1, 2, 3]"

  evalPreludeTest "TAE3a" "map (>= 2) [1, 2, 3]" "[False, True, True]"
  evalPreludeTest "TAE3b" "foldr (\\a b -> b ++ [a]) [] [1, 2, 3]" "[3, 2, 1]"
  evalPreludeTest "TAE3c" "take 3 (iterate (3*) 1)" "[1, 3, 9]"
  evalPreludeTest "TAE3d" "filter (const True) [1, 3, 5, 7]" "[1, 3, 5, 7]"
  evalPreludeTest "TAE3e" "map (length . snd) [(7, \"sieben\"), (1, \"eins\")]" "[6, 4]"
  evalPreludeTest "TAE3f" "foldr (:) [3, 4] [1, 2]" "[1, 2, 3, 4]"
  evalPreludeTest "TAE3g" "foldl (\\(i, c) s -> (i + 1, c + length s)) (0, 0) [\"a\", \"bc\", \"defg\"]" "(3, 7)"

  evalEnvTest "TAT2a"
    (prelude <> "\nnth ls n = head (drop n ls)\n")
    "nth [0, 1, 2, 3] 2"
    "2"
  evalEnvTest "TAT2b"
    ( prelude <> "\n" <>
      "smallest (x:y:rs) = if x < y then smallest (x:rs) else smallest (y:rs)\n" <>
      "smallest [x]      = x")
    "smallest [5, 3, 7]"
    "3"
  evalPreludeTest "TAT2c" "foldl (\\(s, p) i -> (i + s, i * p)) (0, 1) [2, 3, 4]" "(9, 24)"

  evalPreludeTest "TAT3a" "map (2^) [1, 2, 3]" "[2, 4, 8]"
  evalPreludeTest "TAT3b" "foldl (*) 1 [1, 2, 3, 4]" "24"
  evalPreludeTest "TAT3c" "map (== 3) [1, 2, 3, 4]" "[False, False, True, False]"
  evalPreludeTest "TAT3d" "filter (/= 's') \"asdf\"" "\"adf\""
  evalPreludeTest "TAT3e" "map (fst . head) [[(1, 2)], [(3, 4)]]" "[1, 3]"
  evalPreludeTest "TAT3f" "foldl (-) 10 [1, 2, 3]" "4"
  evalPreludeTest "TAT3g" "zipWith (\\a b -> map (+a) b) [1, 2] [[3, 4], [5, 6]]" "[[4, 5], [7, 8]]"

  evalEnvTest "string_third1" "thrd (_:(_:(x:_))) = x" "thrd \"1234\"" "'3'"
  evalEnvTest "string_third2" "thrd [_,_,x,_] = x" "thrd \"1234\"" "'3'"

  evalEnvTest "pattern_matching4" "f ( x :  y : z : rs  ) = (x + y + z) * length rs\nlength (_:xs) = 1 + length xs\nlength [] = 0" "f [2, 3, 5, 8, 11]" "20"
  evalEnvTest "pattern_matching5" "f ( [ x ] : [ y , z ] : [ ] ) = x + y + z" "f [[1],[2,3]]" "6"
  evalEnvTest "pattern_matching6" "f [  [ x ] , [ y , z ] ] = x + y + z" "f [[1],[2,3]]" "6"
  evalEnvTest "pattern_matching7" "f [(a:b:c:rs1), (x:y:z:rs2)] = a * x + b * y + c * z" "f [[1, 2, 3], [100, 10, 1]]" "123"

  evalEnvTest "eval_names" "nat = [1, 2, 3, 4, 5]" "nat" "[1, 2, 3, 4, 5]"

  evalPreludeTest "infix_functions_1" "3 `take` (2 `drop` [1, 2, 3, 4, 5, 6, 7])" "[3, 4, 5]"
  evalPreludeTest "infix_functions_2" "(\\x -> x `mod` 2 == 0) `filter` [1, 2, 3, 4, 5, 6]" "[2, 4, 6]"
  evalPreludeTest "infix_functions_3" "(*2) `map` [1, 2, 3]" "[2, 4, 6]"

  evalPreludeTest "arithmetic_sequences_1" "sum [1, 3 .. 100]" "2500"
  evalPreludeTest "arithmetic_sequences_3" "length [ 7 * 7, 8 * 8 .. 42 * 42]" "115"
  evalPreludeTest "arithmetic_sequences_5" "sum $ take 100 [500 ..]" "54950"
  evalPreludeTest "arithmetic_sequences_6" "[1, -1 .. 0]" "[1]"
  evalPreludeTest "arithmetic_sequences_7a" "[10, 9 .. -10]" "[10,9,8,7,6,5,4,3,2,1,0,-1,-2,-3,-4,-5,-6,-7,-8,-9,-10]"
  evalPreludeTest "arithmetic_sequences_7b" "sum [10, 9 .. -10]" "0"
  evalPreludeTest "arithmetic_sequences_8" "[True .. False]" "[]"
  evalPreludeTest "arithmetic_sequences_9" "[True, False ..]" "[True, False]"
  evalPreludeTest "arithmetic_sequences_11" "[False, True ..]" "[False, True]"
  evalPreludeTest "arithmetic_sequences_12" "[True, False ..]" "[True, False]"
  evalPreludeTest "arithmetic_sequences_13" "[1 .. 10]" "[1,2,3,4,5,6,7,8,9,10]"
  evalPreludeTest "arithmetic_sequences_14" "[5, 9 .. 20]" "[5, 9, 13, 17]"
  evalPreludeTest "arithmetic_sequences_15" "take 5 [3, -1 ..]" "[3, -1, -5, -9, -13]"
  evalPreludeTest "arithmetic_sequences_16" "take 11 [-5 ..]" "[-5, -4, -3, -2, -1, 0, 1, 2 ,3, 4, 5]"
  evalPreludeTest "arithmetic_sequences_17" "[2147483647 ..]" "[2147483647]"
  evalPreludeTest "arithmetic_sequences_18" "[2147483644, 2147483646 ..]" "[2147483644, 2147483646]"
  evalPreludeTest "arithmetic_sequences_19" "[-2147483648]" "[-2147483648]"
  evalPreludeTest "arithmetic_sequences_20" "[-2147483645, -2147483647 ..]" "[-2147483645, -2147483647]"

  evalPreludeTest "list_comprehension_1" "[ x | x <- [1 .. 10], even x]" "[2, 4, 6, 8, 10]"
  evalPreludeTest "list_comprehension_2" "[ (x, y) | x <- [1 .. 3], y <- [1 .. 3], x + y == 4]" "[(1,3), (2,2), (3,1)]"
  evalPreludeTest "list_comprehension_3" "(\\x -> [ x | let x = 1]) 2"    "[1]"
  evalPreludeTest "list_comprehension_4" "[ x | let x = 1, True, let x = 'a']" "['a']"
  evalPreludeTest "list_comprehension_5" "[ y | y <- [1 .. 10], y < y]"  "[]"
  evalPreludeTest "list_comprehension_6" "[ [ y | y <- reverse x] | x <- [[1 .. 5]]]" "[[5, 4, 3, 2, 1]]"
  evalPreludeTest "list_comprehension_7" "[ x | x <- [1 .. 5], y <- [x .. 5]]" "[1,1,1,1,1, 2,2,2,2, 3,3,3, 4,4, 5]"
  evalPreludeTest "list_comprehension_8" "[x | x <- \"wer misst zu viele gabeln\", elem x \"itzgw\"]" "\"witzig\""
  evalPreludeTest "list_comprehension_9" "[(x, z) | x <- [1 .. 5], z <- [y | y <- [1 .. 5], mod x y == 0] ]" "[(1,1), (2,1), (2,2), (3,1), (3,3), (4,1), (4,2), (4,4), (5,1), (5,5)]"
  evalPreludeTest "list_comprehension_10" "[z | let y = [True, True, False], z <- y, z]" "[True, True]"

  --should fail, due to overlapping defs
  --evalPreludeTest "let_expression_1" "let x = 1; x = 'c' in x" "'c'"
  evalPreludeTest "let_expression_2" "let (x, y) = (\\g -> g, \"Hello\") in x y" "\"Hello\""
  evalPreludeTest "let_expression_3" "let x = 1 ; y = x + 1; z = y + 1 in x + y + z" "6"
  evalPreludeTest "let_expression_4" "let x = 1 in let y = 2 in x + y" "3"
  --                                                                                                       should be: "True"
  evalPreludeTest "let_expression_5" "(let x = [1,2,3] in x) == (let x = 1; y = 2; z = 3 in [x,y,z])" "[1,2,3] == [1,2,3]"
  evalPreludeTest "let_expression_6" "let sum = \\x -> x ; y = sum [1,2,3] in y" "[1,2,3]"

  testsADT

testsADT :: Effect Unit
testsADT = do
{-
  eval1test "constr-1"
    "1 :+ 1"
    "1 :+ 1"
  eval1test "constr-2"
    "Foo"
    "Foo"
  eval1test "constr-3"
    "Foo 1"
    "Foo 1"
  eval1test "constr-4"
    "Foo 1 2"
    "Foo 1 2"
-}
  
  evalTest "constr-section-1"
    "(:+ 2) 1"
    "1 :+ 2"

  evalTest "constr-section-2"
    "(1 :+) 2"
    "1 :+ 2"

  eval1test "constr-5"
    "if True then Foo else Bar"
    "Foo"

  eval1test "constr-6"
    "if False then Foo else Bar"
    "Bar"

  eval1EnvTest "func-1"
    "foo (Foo x) = x"
    "foo (Foo 1)"
    "1"

  eval1EnvTest "func-2"
    "foo (Foo x y) = x + y"
    "foo (Foo 1 2)"
    "1 + 2"

  eval1EnvTest "map-func-3"
    "map f Nil = Nil\nmap f (Cons x xs) = Cons (f x) (map f xs)"
    "map (1 +) (Cons 1 (Cons 2 (Cons 3 Nil)))"
    "Cons ((1 +) 1) (map (1 +) (Cons 2 (Cons 3 Nil)))"

  eval1EnvTest "map-func-4"
    "map f Nil = Nil\nmap f (x::xs) = f x :: map f xs"
    "map (^2) Nil"
    "Nil"

  eval1EnvTest "map-func-5"
    "map f Nil = Nil\nmap f (x::xs) = f x :: map f xs"
    "map (^2) (1 :: (2 :: (3 :: Nil)))"
    "(^2) 1 :: map (^2) (2 :: (3 :: Nil))"

  eval1EnvTest "tuple-1"
    "fst (Tuple a _) = a\n"
    "fst (Tuple (Tuple 1 2) 3)"
    "Tuple 1 2"

  eval1EnvTest "tuple-2"
    "snd (Tuple _ a) = a\n"
    "snd (Tuple (Tuple 1 2) 3)"
    "3"

  eval1EnvTest "infix-1"
    "fst (a ::: _) = a"
    "fst (1 ::: 3)"
    "1"

  eval1EnvTest "infix-2"
    "snd (_ ::: a) = a"
    "snd (1 ::: 3)"
    "3"

  evalEnvTest "infix-3"
    "map f g (a :-: b) = f a :-: g b\ndouble = map (*2) (*2)"
    "double (2 :-: 3)"
    "4 :-: 6"

  evalEnvTest "prefix-1"
    "map f g (Tuple x y) = Tuple (f x) (g y)\ndouble = map (*2) (*2)"
    "double (Tuple 2 3)"
    "Tuple 4 6"

  evalEnvTest "constr-nested-1"
    "foo (Bar (Bar a) Foo) = Foo a a"
    "foo (Bar (Bar Foo) Foo)"
    "Foo Foo Foo"


  evalEnvTest "pdp1-a" envPdP1
    ("numParts " <> bspPdP1)
    "13"

  evalEnvTest "pdp1-b" envPdP1
    ("foldBauwerk Rechteck Spitze Split " <> bspPdP1)
    bspPdP1

  evalEnvTest "pdp1-c" envPdP1
    ("maxHoehe " <> bspPdP1)
    "87"

  evalEnvTest "pdp1-d" envPdP1
    ("numPeaks " <> bspPdP1)
    "5"

  evalEnvTest "pdp1-e" envPdP1
    ("wellformed " <> bspPdP1)
    "True"

  evalEnvTest "fp-a" envPdP2
    ("foldMixTree QuadSplit Split Color " <> bspPdP2)
    bspPdP2

  evalEnvTest "fp-b" envPdP2
    ("areas " <> bspPdP2)
    "22"

  evalEnvTest "fp-c" envPdP2
    ("wellformedTree " <> bspPdP2)
    "True"

  evalEnvTest "rose-fold" envRoseFold
    ("foldRoseTree Node Leaf " <> bspRoseFold)
    bspRoseFold

  evalEnvTest "bin-tree-fold-1" envBinTree
    ("foldBinTree Nil (:::) " <> bspBinTree)
    bspBinTree

  evalEnvTest "bin-tree-fold-2" envBinTree
    ("nils " <> bspBinTree)
    "6"

  evalEnvTest "bin-tree-fold-1" envBinTree
    ("foldBinTree Nil (:::) " <> bspBinTree2)
    bspBinTree2

  evalEnvTest "bin-tree-fold-2" envBinTree
    ("nils (" <> bspBinTree2 <> ")")
    "2"

envRoseFold :: String
envRoseFold = """
map _ [] = []
map f (x:xs) = f x : map f xs

foldRoseTree fN fL (Leaf a) = fL a
foldRoseTree fN fL (Node ts) = fN (map (foldRoseTree fN fL) ts)
"""

bspRoseFold :: String
bspRoseFold = """(Node
  [ Leaf 1
  , Leaf 2
  , Leaf 3
  , Node
    [ Leaf 4
    , Leaf 5
    , Leaf 6 ]])
"""

envBinTree :: String
envBinTree = """
foldBinTree fNil fNode Nil = fNil
foldBinTree fNil fNode (l ::: r) = fNode
  (foldBinTree fNil fNode l)
  (foldBinTree fNil fNode r)

nils = foldBinTree 1 (+)
"""

bspBinTree :: String
bspBinTree = "(((Nil ::: Nil) ::: Nil) ::: (Nil ::: (Nil ::: Nil)))"

bspBinTree2 :: String
bspBinTree2 = "Nil ::: Nil"

envPdP1 :: String
envPdP1 = """
foldBauwerk fRechteck fSpitze fSplit (Rechteck br ho bw)
  = fRechteck br ho (foldBauwerk fRechteck fSpitze fSplit bw)
foldBauwerk fRechteck fSpitze fSplit (Spitze br ho)
  = fSpitze br ho
foldBauwerk fRechteck fSpitze fSplit (Split l r)
  = fSplit (foldBauwerk fRechteck fSpitze fSplit l) (foldBauwerk fRechteck fSpitze fSplit r)

numParts (Rechteck _ _ bw) = 1 + numParts bw
numParts (Spitze _ _) = 1
numParts (Split l r)  = numParts l + numParts r

max a b = if a < b then b else a

maxHoehe = foldBauwerk
  (\_ ho hor -> ho + hor)
  (\_ h -> h)
  max

numPeaks = foldBauwerk (\_ _ ps -> ps) (\_ _ -> 1) (+)

wellformed
  = (> 0)
  . foldBauwerk
    (\br _ br' -> if br' < 0 || br' > br then -1 else br)
    (\br _ -> br)
    (\l r -> l + r)
"""

bspPdP1 :: String
bspPdP1 = """(Rechteck 50 20
  (Split
    (Rechteck 20 15
      (Split
        (Rechteck 10 20
          (Rechteck 8 18
            (Spitze 8 14)))
        (Rechteck 8 17
          (Spitze 8 14))))
    (Rechteck 20 15
      (Split
        (Rechteck 8 17
          (Spitze 8 14))
        (Rechteck 10 20
          (Split
            (Spitze 5 17)
            (Spitze 5 17)))))))
"""

envPdP2 :: String
envPdP2 = """
foldMixTree fQ fS fC (QuadSplit ro ru lu lo) = fQ
  (foldMixTree fQ fS fC ro)
  (foldMixTree fQ fS fC ru)
  (foldMixTree fQ fS fC lu)
  (foldMixTree fQ fS fC lo)
foldMixTree fQ fS fC (Split a ts)
  = fS a (map (\(d, t) -> (d, foldMixTree fQ fS fC t)) ts)
foldMixTree fQ fS fC (Color c) = fC c

wellformed xs = all (\(x,_) -> x > 0) xs && (10 == sum (map fst xs))

all _ [] = True
all p (x:xs) = if p x then all p xs else False

sum [] = 0
sum (x:xs) = x + sum xs

map f [] = []
map f (x:xs) = f x : map f xs

fst (x,_) = x
snd (_,x) = x

areas = foldMixTree
  (\ro ru lu lo -> ro + ru + lu + lo)
  (\_ -> sum . map snd)
  (\_ -> 1)

wellformedTree = foldMixTree
  (\ro ru lu lo -> ro && ru && lu && lo)
  (\_ -> wellformed)
  (\_ -> True)
"""

bspPdP2 :: String
bspPdP2 = """(Split H
  [ (2, Color White)
  , (2, Split V
      [ (3, Color White)
      , (2, QuadSplit
          (Color White)
          (Color DarkGrey)
          (Color White)
          (Color DarkGrey))
      , (2, Split H
          [ (5, Color White)
          , (5, Color LightGrey)])
      , (3, Color White)])
  , (1, Split V
      [ (4, Color Black)
      , (4, Color LightGrey)
      , (2, Color White) ])
  , (2, Split V
      [ (2, Color White)
      , (2, QuadSplit
          (Color DarkGrey)
          (Color White)
          (Color DarkGrey)
          (Color White))
      , (1, Color White)
      , (2, Split H
          [ (5, Color LightGrey)
          , (5, Color White) ])
      , (3, Color White)])
  , (3, Color White)])
"""


