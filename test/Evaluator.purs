module Test.Evaluator where

import Prelude
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Data.StrMap as M
-- import Data.List (List, singleton)

-- import Control.Monad.Writer (Writer, tell)

import Parser (definitions, expression, runParserIndent)
import Evaluator (eval, eval1, runEvalM, defsToEnv)
import Test.Parser (prelude)

import Test.Utils (Test, tell, padLeft)

tell' :: String -> Test Unit
tell' = tell

eval1test :: String -> String -> String -> Test Unit
eval1test name input expected = case (Tuple (runParserIndent expression input) (runParserIndent expression expected)) of
  (Tuple (Right inExp) (Right expExp)) ->
    case runEvalM (eval1 M.empty inExp) of
      (Right eval1Exp) -> 
        if eval1Exp == expExp
          then pure unit -- log $ "Eval success (" ++ name ++ ")"
          else tell'
             $ "Eval fail (" <> name <> "):\n"
            <> "Input:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show eval1Exp) <> "\n"
            <> "Expected:\n"
            <> padLeft (show expExp)
      (Left err) -> tell'
        $ "Eval fail (" <> name <> "):\n"
        <> padLeft (show err)
  _ -> tell' $ "Parse fail (" <> name <> ")"

eval1EnvTest :: String -> String -> String -> String -> Test Unit
eval1EnvTest name env input expected = case (Tuple (Tuple (runParserIndent expression input) (runParserIndent expression expected)) (runParserIndent definitions env)) of
  (Tuple (Tuple (Right inExp) (Right expExp)) (Right defs)) ->
    case runEvalM (eval1 (defsToEnv defs) inExp) of
      (Right eval1Exp) -> 
        if eval1Exp == expExp
          then pure unit -- log $ "Eval success (" <> name <> ")"
          else tell'
             $ "Eval fail (" <> name <> "):\n"
            <> "Input:\n"
            <> padLeft (show inExp) <> "\n"
            <> "Output:\n"
            <> padLeft (show eval1Exp) <> "\n"
            <> "Expected:\n"
            <> padLeft (show expExp)
      (Left err) -> tell'
        $ "Eval fail (" <> name <> "):\n"
        <> padLeft (show err)
  _ -> tell' $ "Parse fail (" <> name <> ")"

evalEnvTest :: String -> String -> String -> String -> Test Unit
evalEnvTest name env input expected = case (Tuple (Tuple (runParserIndent expression input) (runParserIndent expression expected)) (runParserIndent definitions env)) of
  (Tuple (Tuple (Right inExp) (Right expExp)) (Right defs)) ->
    let evalExp = eval (defsToEnv defs) inExp in
      if evalExp == expExp
        then pure unit -- log $ "Eval success (" ++ name ++ ")"
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



runTests :: Test Unit
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

  evalEnvTest "eval_list" "" "[2 + 2, 3 * 3]" "[4, 9]"
  evalEnvTest "eval_tuple" "" "(2+2, 3 * 3)" "(4, 9)"

  -- This test gets stuck in an endless loop,
  -- evalEnvTest "fix" "f x = f x" "f 10" "f 10"

  evalEnvTest "fac" "fac 1 = 1\nfac n = n * fac (n - 1)" "fac 6" "720"
  evalEnvTest "prelude" prelude "sum (map (^2) [1,2,3,4])" "30"

  evalEnvTest "TAE2a"
    ( prelude <> "\n" <>
      "pair (x:y:rs) = (x, y) : pair (y:rs)\n" <>
      "pair _        = []")
    "pair [1, 2, 3, 4]"
    "[(1, 2), (2, 3), (3, 4)]"
  evalEnvTest "TAE2b" prelude "foldr (\\a b -> a + b * 10) 0 [3, 2, 1]" "123"
  evalEnvTest "TAE2c"
    (prelude <> "\nsublist f t ls = drop f (take (t + f) ls)\n")
    "sublist 1 3 [0, 1, 2, 3, 4]"
    "[1, 2, 3]"

  evalEnvTest "TAE3a" prelude "map (>= 2) [1, 2, 3]" "[False, True, True]"
  evalEnvTest "TAE3b" prelude "foldr (\\a b -> b ++ [a]) [] [1, 2, 3]" "[3, 2, 1]"
  evalEnvTest "TAE3c" prelude "take 3 (iterate (3*) 1)" "[1, 3, 9]"
  evalEnvTest "TAE3d" prelude "filter (const True) [1, 3, 5, 7]" "[1, 3, 5, 7]"
  evalEnvTest "TAE3e" prelude "map (length . snd) [(7, \"sieben\"), (1, \"eins\")]" "[6, 4]"
  evalEnvTest "TAE3f" prelude "foldr (:) [3, 4] [1, 2]" "[1, 2, 3, 4]"
  evalEnvTest "TAE3g" prelude "foldl (\\(i, c) s -> (i + 1, c + length s)) (0, 0) [\"a\", \"bc\", \"defg\"]" "(3, 7)"

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
  evalEnvTest "TAT2c" prelude "foldl (\\(s, p) i -> (i + s, i * p)) (0, 1) [2, 3, 4]" "(9, 24)"

  evalEnvTest "TAT3a" prelude "map (2^) [1, 2, 3]" "[2, 4, 8]"
  evalEnvTest "TAT3b" prelude "foldl (*) 1 [1, 2, 3, 4]" "24"
  evalEnvTest "TAT3c" prelude "map (== 3) [1, 2, 3, 4]" "[False, False, True, False]"
  evalEnvTest "TAT3d" prelude "filter (/= 's') \"asdf\"" "\"adf\""
  evalEnvTest "TAT3e" prelude "map (fst . head) [[(1, 2)], [(3, 4)]]" "[1, 3]"
  evalEnvTest "TAT3f" prelude "foldl (-) 10 [1, 2, 3]" "4"
  evalEnvTest "TAT3g" prelude "zipWith (\\a b -> map (+a) b) [1, 2] [[3, 4], [5, 6]]" "[[4, 5], [7, 8]]"

  evalEnvTest "string_third1" "thrd (_:(_:(x:_))) = x" "thrd \"1234\"" "'3'"
  evalEnvTest "string_third2" "thrd [_,_,x,_] = x" "thrd \"1234\"" "'3'"

  evalEnvTest "pattern_matching4" "f ( x :  y : z : rs  ) = (x + y + z) * length rs\nlength (_:xs) = 1 + length xs\nlength [] = 0" "f [2, 3, 5, 8, 11]" "20"
  evalEnvTest "pattern_matching5" "f ( [ x ] : [ y , z ] : [ ] ) = x + y + z" "f [[1],[2,3]]" "6"
  evalEnvTest "pattern_matching6" "f [  [ x ] , [ y , z ] ] = x + y + z" "f [[1],[2,3]]" "6"
  evalEnvTest "pattern_matching7" "f [(a:b:c:rs1), (x:y:z:rs2)] = a * x + b * y + c * z" "f [[1, 2, 3], [100, 10, 1]]" "123"

  evalEnvTest "eval_names" "nat = [1, 2, 3, 4, 5]" "nat" "[1, 2, 3, 4, 5]"

  evalEnvTest "infix_functions_1" prelude "3 `take` (2 `drop` [1, 2, 3, 4, 5, 6, 7])" "[3, 4, 5]"
  evalEnvTest "infix_functions_2" prelude "(\\x -> x `mod` 2 == 0) `filter` [1, 2, 3, 4, 5, 6]" "[2, 4, 6]"
  evalEnvTest "infix_functions_3" prelude "(*2) `map` [1, 2, 3]" "[2, 4, 6]"

  evalEnvTest "arithmetic_sequences_1" prelude "sum [1, 3 .. 100]" "2500"
  evalEnvTest "arithmetic_sequences_3" prelude "length [ 7 * 7, 8 * 8 .. 42 * 42]" "115"
  evalEnvTest "arithmetic_sequences_5" prelude "sum $ take 100 [500 ..]" "54950"
  evalEnvTest "arithmetic_sequences_6" prelude "[1, -1 .. 0]" "[1]"
  evalEnvTest "arithmetic_sequences_7" prelude "sum [10, 9 .. -10]" "0"
  evalEnvTest "arithmetic_sequences_8" prelude "[True .. False]" "[]"
  evalEnvTest "arithmetic_sequences_9" prelude "[True, False ..]" "[True, False]"
  evalEnvTest "arithmetic_sequences_11" prelude "[False, True ..]" "[False, True]"
  evalEnvTest "arithmetic_sequences_12" prelude "[True, False ..]" "[True, False]"
  evalEnvTest "arithmetic_sequences_13" prelude "[1 .. 10]" "[1,2,3,4,5,6,7,8,9,10]"
  evalEnvTest "arithmetic_sequences_14" prelude "[5, 9 .. 20]" "[5, 9, 13, 17]"
  evalEnvTest "arithmetic_sequences_15" prelude "take 5 [3, -1 ..]" "[3, -1, -5, -9, -13]"
  evalEnvTest "arithmetic_sequences_16" prelude "take 11 [-5 ..]" "[-5, -4, -3, -2, -1, 0, 1, 2 ,3, 4, 5]"
  evalEnvTest "arithmetic_sequences_17" prelude "[2147483647 ..]" "[2147483647]"
  evalEnvTest "arithmetic_sequences_18" prelude "[2147483644, 2147483646 ..]" "[2147483644, 2147483646]"
  evalEnvTest "arithmetic_sequences_19" prelude "[-2147483648]" "[-2147483648]"
  evalEnvTest "arithmetic_sequences_20" prelude "[-2147483645, -2147483647 ..]" "[-2147483645, -2147483647]"

  evalEnvTest "list_comprehension_1" prelude "[ x | x <- [1 .. 10], even x]" "[2, 4, 6, 8, 10]"
  evalEnvTest "list_comprehension_2" prelude "[ (x, y) | x <- [1 .. 3], y <- [1 .. 3], x + y == 4]" "[(1,3), (2,2), (3,1)]"
  evalEnvTest "list_comprehension_3" prelude "(\\x -> [ x | let x = 1]) 2"    "[1]"
  evalEnvTest "list_comprehension_4" prelude "[ x | let x = 1, True, let x = 'a']" "['a']"
  evalEnvTest "list_comprehension_5" prelude "[ y | y <- [1 .. 10], y < y]"  "[]"
  evalEnvTest "list_comprehension_6" prelude "[ [ y | y <- reverse x] | x <- [[1 .. 10]]]" "[[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]]"
  evalEnvTest "list_comprehension_7" prelude "[ x | x <- [1 .. 5], y <- [x .. 5]]" "[1,1,1,1,1, 2,2,2,2, 3,3,3, 4,4, 5]"
  evalEnvTest "list_comprehension_8" prelude "[x | x <- \"wer misst zu viele gabeln\", elem x \"itzgw\"]" "\"witzig\""
  evalEnvTest "list_comprehension_9" prelude "[(x, z) | x <- [1 .. 5], z <- [y | y <- [1 .. 5], mod x y == 0] ]" "[(1,1), (2,1), (2,2), (3,1), (3,3), (4,1), (4,2), (4,4), (5,1), (5,5)]"
  evalEnvTest "list_comprehension_10" prelude "[z | let y = [True, True, False], z <- y, z]" "[True, True]"

  --should fail, due to overlapping defs
  --evalEnvTest "let_expression_1" prelude "let x = 1; x = 'c' in x" "'c'"
  evalEnvTest "let_expression_2" prelude "let (x, y) = (\\g -> g, \"Hello\") in x y" "\"Hello\""
  evalEnvTest "let_expression_3" prelude "let x = 1 ; y = x + 1; z = y + 1 in x + y + z" "6"
  evalEnvTest "let_expression_4" prelude "let x = 1 in let y = 2 in x + y" "3"
  --                                                                                                       should be: "True"
  evalEnvTest "let_expression_5" prelude "(let x = [1,2,3] in x) == (let x = 1; y = 2; z = 3 in [x,y,z])" "[1,2,3] == [1,2,3]"
  evalEnvTest "let_expression_6" prelude "let sum = \\x -> x ; y = sum [1,2,3] in y" "[1,2,3]"

  testsADT



testsADT :: Test Unit
testsADT = do
  eval1test "constr-1"
    "1 :+ 1"
    "1 :+ 1"
{-
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


