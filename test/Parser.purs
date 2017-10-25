module Test.Parser where

import Prelude
import Data.Either (Either(..))
import Data.List (List(..), singleton, (:), many)
import Data.Array ((..))
import Data.Array (length, zip, toUnfoldable, replicate) as Array
import Data.Tuple (Tuple(..))
import Data.String (toCharArray, null) as String
import Data.Maybe (Maybe(..))
import Data.Foldable (intercalate, for_)

import Text.Parsing.Parser (ParseState(..), parseErrorPosition, parseErrorMessage, fail)

-- import Control.Monad.Writer (Writer, tell)
import Control.Monad.State (get)

import Test.Utils (Test, tell, padLeft)
import JSHelpers (unsafeUndef)

import AST
  ( TypeTree
  , Tree(..)
  , Atom(..)
  , Binding(..)
  , Definition(Def)
  , Op(..)
  , QualTree(..)
  , toOpTuple
  , ADTDef(..)
  , DataConstr(..)
  , Associativity(..)
  , Type(..))
import Parser
  ( expression
  , atom
  , definitions
  , definition
  , binding
  , variable
  , bool
  , int
  , runParserIndent
  , typeDefinition
  , dataConstructorDefinition
  , infixDataConstrtructorDefinition
  , symbol
  , infixConstructor
  , types)
import IndentParser (IndentParser)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: String -> Test Unit
tell' = tell

padLeft' :: forall a. (Show a) => a -> String
padLeft' = show >>> padLeft

test :: forall a. (Show a, Eq a) => String -> IndentParser String a -> String -> a -> Test Unit
test name p input expected = case runParserIndent p input of
  Left parseError -> tell' $
    "Parse fail (" <> name <> "): "
    <> padLeft' (parseErrorPosition parseError) <> "\n"
    <> padLeft (parseErrorMessage parseError) <> "\n"
    <> "Input:\n"
    <> padLeft input
  Right result           ->
    if result == expected
      then pure unit --tell $ "Parse success (" <> name <> ")"
      else tell' $
        "Parse fail (" <> name <> "):\n"
        <> "Output:\n"
        <> padLeft' result <> "\n"
        <> "Expected:\n"
        <> padLeft' expected <> "\n"
        <> "Input:\n"
        <> padLeft input


rejectTest :: forall a . (Show a)
                      => String
                      -> IndentParser String a
                      -> String
                      -> Test Unit
rejectTest name parser input = case runParserIndent (parser <* inputIsEmpty) input of
  Left parserError -> pure unit
  Right result ->
    tell' $
      "Parser accepted " <> name <> "\n"
      <> "Input:\n"
      <> padLeft input <> "\n"
      <> "Output:\n"
      <> padLeft' result

rejectTests :: forall a . (Show a)
                       => String
                       -> IndentParser String a
                       -> Array String
                       -> Test Unit
rejectTests name parser inputs = do
  for_ ((1 .. Array.length inputs) `Array.zip` inputs) $ \(Tuple idx iput) ->
    rejectTest (name <> "-" <> show idx) parser iput

inputIsEmpty :: IndentParser String Unit
inputIsEmpty = do
  ParseState s _ _ <- get
  when (not (String.null s)) (fail $ "Leftover input:\n" <> padLeft s)

aint :: Int -> TypeTree
aint i = Atom Nothing $ AInt i

abool :: Boolean -> TypeTree
abool = Atom Nothing <<< Bool

aname :: String -> TypeTree
aname s = Atom Nothing $ Name s

runTests :: Test Unit
runTests = do
  test "0" int "0" (AInt 0)
  test "1" int "1" (AInt 1)
  test "all" int "0123456789" (AInt 123456789)
  test "high" int "2147483647" (AInt 2147483647)
  test "overflow" int "2147483648" (AInt (negate 2147483648))

  test "bool1" bool "True" (Bool true)
  test "bool2" bool "False" (Bool false)

  test "a" variable "a" (Name "a")
  test "lower" variable "a_bcdefghijklmnopqrstuvwxyz_" (Name "a_bcdefghijklmnopqrstuvwxyz_")
  test "upper" variable "a'BCDEFGHIJKLMNOPQRSTUVWXYZ'" (Name "a'BCDEFGHIJKLMNOPQRSTUVWXYZ'")
  test "special" variable "_____''''" (Name "_____''''")
  test "with_numbers1" variable "a1" (Name "a1")

  test "composition" expression "f . g" (Binary Nothing (toOpTuple Composition) (aname "f") (aname "g"))
  test "power" expression "2 ^ 10" (Binary Nothing (toOpTuple Power) (aint 2) (aint 10))
  test "mul" expression "2 * 2" (Binary Nothing (toOpTuple Mul) (aint 2) (aint 2))
  test "div" expression "13 `div` 3" (Binary Nothing (toOpTuple (InfixFunc "div")) (aint 13) (aint 3))
  test "mod" expression "13 `mod` 3" (Binary Nothing (toOpTuple (InfixFunc "mod")) (aint 13) (aint 3))
  test "add1" expression "1 + 1"  (Binary Nothing (toOpTuple Add) (aint 1) (aint 1))
  test "add2" expression "2+2" (Binary Nothing (toOpTuple Add) (aint 2) (aint 2))
  test "sub" expression "5 - 3" (Binary Nothing (toOpTuple Sub) (aint 5) (aint 3))
  test "colon" expression "x:xs" (Binary Nothing (toOpTuple Colon) (aname "x") (aname "xs"))
  test "append1" expression "xs ++ ys" (Binary Nothing (toOpTuple Append) (aname "xs") (aname "ys"))
  test "append2" expression "xs++ys"  (Binary Nothing (toOpTuple Append) (aname "xs") (aname "ys"))
  test "equ" expression "5 == 5" (Binary Nothing (toOpTuple Equ) (aint 5) (aint 5))
  test "neq" expression "1 /= 2" (Binary Nothing (toOpTuple Neq) (aint 1) (aint 2))
  test "lt1" expression "1 < 234" (Binary Nothing (toOpTuple Lt) (aint 1) (aint 234))
  test "lt2" expression "x<y" (Binary Nothing (toOpTuple Lt) (aname "x") (aname "y"))
  test "leq" expression "1 <= 234" (Binary Nothing (toOpTuple Leq) (aint 1) (aint 234))
  test "gt1" expression "567 > 1" (Binary Nothing (toOpTuple Gt) (aint 567) (aint 1))
  test "gt2" expression "x>y" (Binary Nothing (toOpTuple Gt) (aname "x") (aname "y"))
  test "geq" expression "567 >= 1" (Binary Nothing (toOpTuple Geq) (aint 567) (aint 1))
  test "and" expression "hot && cold" (Binary Nothing (toOpTuple And) (aname "hot") (aname "cold"))
  test "or" expression "be || notBe" (Binary Nothing (toOpTuple Or) (aname "be") (aname "notBe"))
  test "dollar" expression "f $ 1 + 2"  (Binary Nothing (toOpTuple Dollar) (aname "f") (Binary Nothing (toOpTuple Add) (aint 1) (aint 2)))

  test "unary_minus1" expression "- 10"  (aint (-10))
  test "unary_minus2" expression "- x"  (Unary Nothing (toOpTuple Sub) (aname "x"))
  test "unary_minus3" expression "-10"  (aint (-10))
  test "unary_minus4" expression "-x"  (Unary Nothing (toOpTuple Sub) (aname "x"))

  test "infix_operator1" expression "1 `max` 3" (Binary Nothing (toOpTuple (InfixFunc "max")) (aint 1) (aint 3))
  test "infix_operator2" expression "5 `max` 2 `min` 1" (Binary Nothing (toOpTuple (InfixFunc "min")) (Binary Nothing (toOpTuple (InfixFunc "max")) (aint 5) (aint 2)) (aint 1))
  test "infix_operator3" expression "True`tight`False" (Binary Nothing (toOpTuple (InfixFunc "tight")) (abool true) (abool false))

  test "1" expression "1" (aint 1)
  test "add" expression "1 + 2" (Binary Nothing (toOpTuple Add) (aint 1) (aint 2))
  test "precedence" expression "1 * 2 + 3 * 4" (Binary Nothing (toOpTuple Add)
                                    (Binary Nothing (toOpTuple Mul) (aint 1) (aint 2))
                                    (Binary Nothing (toOpTuple Mul) (aint 3) (aint 4)))
  test "whitespaces" expression
    "1   \t   -    \t   ( f   )    \t\t\t\t                                                                \t\t\t\t             `div`     _ignore"
    (Binary Nothing (toOpTuple Sub) (aint 1) (Binary Nothing (toOpTuple (InfixFunc "div")) (aname "f") (aname "_ignore")))
  test "brackets" expression "(  1  +  2  )  *  3" (Binary Nothing (toOpTuple Mul) (Binary Nothing (toOpTuple Add) (aint 1) (aint 2)) (aint 3))
  test "brackets2" expression "( (  1  +  2  - 3  )  *  4 * 5 * 6)"
    (Binary Nothing (toOpTuple Mul)
      (Binary Nothing (toOpTuple Mul)
        (Binary Nothing (toOpTuple Mul)
          (Binary Nothing (toOpTuple Sub)
            (Binary Nothing (toOpTuple Add) (aint 1) (aint 2))
            (aint 3))
          (aint 4))
        (aint 5))
      (aint 6))
  test "brackets3" expression "( ( ( 1 ) ) )" (aint 1)
  test "many brackets" expression "(   (( ((  f )) *  ( (17   )) ) ))" (Binary Nothing (toOpTuple Mul) (aname "f") (aint 17))

  test "if_then_else" expression "if x then y else z" (IfExpr Nothing (aname "x") (aname "y") (aname "z"))
  test "nested if" expression "if(if 1 then 2 else 3)then y else z" (IfExpr Nothing (IfExpr Nothing (aint 1) (aint 2) (aint 3)) (aname "y") (aname "z"))
  test "iffy1" expression "iffy" (aname "iffy")
  test "iffy2" expression "if 10 + 20 then iffy * iffy else ((7))"
    (IfExpr Nothing
      (Binary Nothing (toOpTuple Add) (aint 10) (aint 20))
      (Binary Nothing (toOpTuple Mul) (aname "iffy") (aname "iffy"))
      (aint 7))
  test "iffy3" expression "iffy + if iffy then iffy else iffy"
    (Binary Nothing (toOpTuple Add) (aname "iffy") (IfExpr Nothing (aname "iffy") (aname "iffy") (aname "iffy")))
  test "nested if 2" expression "if if x then y else z then if a then b else c else if i then j else k"
    (IfExpr Nothing
      (IfExpr Nothing (aname "x") (aname "y") (aname "z"))
      (IfExpr Nothing (aname "a") (aname "b") (aname "c"))
      (IfExpr Nothing (aname "i") (aname "j") (aname "k")))
  test "if2" expression "if bool then False else True" (IfExpr Nothing (aname "bool") (Atom Nothing (Bool false)) (Atom Nothing (Bool true)))

  test "apply1" expression "f 1" (App Nothing (aname "f") (singleton (aint 1)))
  test "apply2" expression "f x y z 12 (3 + 7)"
    (App Nothing (aname "f") (toList [aname "x", aname "y", aname "z", aint 12, Binary Nothing (toOpTuple Add) (aint 3) (aint 7)]))
  test "fibonacci" expression "fib (n - 1) + fib (n - 2)"
    (Binary Nothing (toOpTuple Add)
      (App Nothing (aname "fib") (toList [Binary Nothing (toOpTuple Sub) (aname "n") (aint 1)]))
      (App Nothing (aname "fib") (toList [Binary Nothing (toOpTuple Sub) (aname "n") (aint 2)])))
  test "predicate" expression "if p 10 then 10 else 20"
    (IfExpr Nothing
      (App Nothing (aname "p") (singleton (aint 10)))
      (aint 10)
      (aint 20))
  test "stuff" expression "f a (1 * 2) * 3"
    (Binary Nothing (toOpTuple Mul)
      (App Nothing (aname "f") (toList [aname "a", Binary Nothing (toOpTuple Mul) (aint 1) (aint 2)]))
      (aint 3))

  test "tuple" expression "(1, 2)" (NTuple Nothing (toList [aint 1, aint 2]))
  test "3tuple" expression "(1, 2, 3)" (NTuple Nothing (toList [aint 1, aint 2, aint 3]))
  test "4tuple" expression "(1, 2, 3, 4)" (NTuple Nothing (toList [aint 1, aint 2, aint 3, aint 4]))
  test "tuple_spaces" expression "(   1   , 2   )" (NTuple Nothing (toList [aint 1, aint 2]))
  test "3tuple_spaces" expression "(  1   , 2    , 3     )" (NTuple Nothing (toList [aint 1, aint 2, aint 3]))
  test "tuple_arith" expression "((1 + 2, (3)))" (NTuple Nothing (toList [Binary Nothing (toOpTuple Add) (aint 1) (aint 2), aint 3]))
  test "tuple_apply" expression "fmap f (snd (1,2), fst ( 1 , 2 ))"
    (App Nothing (aname "fmap") (toList
      [ (aname "f")
      , NTuple Nothing (toList
        [ App Nothing (aname "snd") (toList [NTuple Nothing (toList [aint 1, aint 2])])
        , App Nothing (aname "fst") (toList [NTuple Nothing (toList [aint 1, aint 2])])
        ])
      ]
    ))
  test "tuple_deep" expression "((((( ((((((1)),((2))),(3,((((4)))))),((5,6),(7,8))),(((9,(10)),(((11,12)))),((((13,14),(14,15)))))) )))))"
    (NTuple Nothing (Cons
      (NTuple Nothing (Cons
        (NTuple Nothing (Cons
          (NTuple Nothing (Cons (Atom Nothing (AInt 1)) (Cons (Atom Nothing (AInt 2)) (Nil))))
          (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 3)) (Cons (Atom Nothing (AInt 4)) (Nil)))) (Nil))))
        (Cons (NTuple Nothing
          (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 5)) (Cons (Atom Nothing (AInt 6)) (Nil))))
            (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 7)) (Cons (Atom Nothing (AInt 8)) (Nil)))) (Nil)))) (Nil))))
      (Cons (NTuple Nothing (Cons (NTuple Nothing (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 9)) (Cons (Atom Nothing (AInt 10)) (Nil))))
        (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 11)) (Cons (Atom Nothing (AInt 12)) (Nil)))) (Nil))))
      (Cons (NTuple Nothing (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 13)) (Cons (Atom Nothing (AInt 14)) (Nil))))
        (Cons (NTuple Nothing (Cons (Atom Nothing (AInt 14)) (Cons (Atom Nothing (AInt 15)) (Nil)))) (Nil)))) (Nil)))) (Nil))))

  test "list_empty" expression "[]" (List Nothing Nil)
  test "list1" expression "[1]" (List Nothing (toList [aint 1]))
  test "list2" expression "[  1  ]" (List Nothing (toList [aint 1]))
  test "list3" expression "[  1  ,2,3,     4    ,  5  ]" (List Nothing (toList [aint 1, aint 2, aint 3, aint 4, aint 5]))
  test "list_nested" expression "[ [1,2] , [ 3 , 4 ] ]" (List Nothing $ toList [(List Nothing $ toList [aint 1, aint 2]), (List Nothing $ toList [aint 3, aint 4])])
  test "list_complex" expression "[ 1 + 2 , 3 + 4 ] ++ []"
    (Binary Nothing (toOpTuple Append)
      (List Nothing $ toList [Binary Nothing (toOpTuple Add) (aint 1) (aint 2), Binary Nothing (toOpTuple Add) (aint 3) (aint 4)])
      (List Nothing Nil))

  test "binding_lit1" binding "x" (Lit Nothing (Name "x"))
  test "binding_lit2" binding "10" (Lit Nothing (AInt 10))
  test "lambda1" expression "(\\x -> x)" (Lambda Nothing (toList [Lit Nothing (Name "x")]) (aname "x"))
  test "lambda2" expression "( \\ x y z -> ( x , y , z ) )"
    (Lambda Nothing (toList [Lit Nothing (Name "x"), Lit Nothing (Name "y"), Lit Nothing (Name "z")])
      (NTuple Nothing (toList [aname "x", aname "y", aname "z"])))
  test "lambda3" expression "(  \\  x ->   (   \\    y ->    (   \\    z ->     f   x   y   z )  )  )"
    (Lambda Nothing (singleton $ Lit Nothing $ Name "x")
      (Lambda Nothing (singleton $ Lit Nothing $ Name "y")
        (Lambda Nothing (singleton $ Lit Nothing $ Name "z")
          (App Nothing (aname "f") (toList [aname "x", aname "y", aname "z"])))))
  test "lambda4" expression "(\\a b -> a + b) 1 2"
    (App Nothing
      (Lambda Nothing (toList [Lit Nothing (Name "a"), Lit Nothing (Name "b")])
        (Binary Nothing (toOpTuple Add) (aname "a") (aname "b")))
      (toList [aint 1, aint 2]))

  test "lambda5" expression "(\\a -> (\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> a + b + c + d + e + f + g))))))) 1 2 3 4 5 6 7"
    (App Nothing
      (Lambda Nothing (Cons (Lit Nothing (Name "a")) (Nil))
        (Lambda Nothing (Cons (Lit Nothing (Name "b")) (Nil))
          (Lambda Nothing (Cons (Lit Nothing (Name "c")) (Nil))
            (Lambda Nothing (Cons (Lit Nothing (Name "d")) (Nil))
              (Lambda Nothing (Cons (Lit Nothing (Name "e")) (Nil))
                (Lambda Nothing (Cons (Lit Nothing (Name "f")) (Nil))
                  (Lambda Nothing (Cons (Lit Nothing (Name "g")) (Nil))
                    (Binary Nothing (toOpTuple Add)
                      (Binary Nothing (toOpTuple Add)
                        (Binary Nothing (toOpTuple Add)
                          (Binary Nothing (toOpTuple Add)
                            (Binary Nothing (toOpTuple Add)
                              (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "a")) (Atom Nothing (Name "b")))
                              (Atom Nothing (Name "c")))
                            (Atom Nothing (Name "d")))
                          (Atom Nothing (Name "e")))
                        (Atom Nothing (Name "f")))
                      (Atom Nothing (Name "g"))))))))))
      (Cons (Atom Nothing (AInt 1)) (Cons (Atom Nothing (AInt 2)) (Cons (Atom Nothing (AInt 3)) (Cons (Atom Nothing (AInt 4)) (Cons (Atom Nothing (AInt 5)) (Cons (Atom Nothing (AInt 6)) (Cons (Atom Nothing (AInt 7)) (Nil)))))))))

  test "lambda6" expression "\\x -> x + 2"
      (Lambda Nothing
        (toList [Lit Nothing (Name "x")])
        (Binary Nothing (toOpTuple Add) (aname "x") (aint 2)))

  test "lambda7" definition "f a = \\b -> a + b"
    (Def "f"
      (toList [Lit Nothing (Name "a")])
      (Lambda Nothing
        (toList [Lit Nothing (Name "b")])
        (Binary Nothing (toOpTuple Add) (aname "a") (aname "b"))))

  test "sectR1" expression "(+1)" (SectR Nothing (toOpTuple Add) (aint 1))
  test "sectR2" expression "( ^ 2 )" (SectR Nothing (toOpTuple Power) (aint 2))
  test "sectR3" expression "(++ [1])" (SectR Nothing (toOpTuple Append) (List Nothing (toList [aint 1])))
  test "sectR4" expression "(<= (2 + 2))" (SectR Nothing (toOpTuple Leq) (Binary Nothing (toOpTuple Add) (aint 2) (aint 2)))
  test "sectR5" expression "(   >=  (  2 + 2  )  )" (SectR Nothing (toOpTuple Geq) (Binary Nothing (toOpTuple Add) (aint 2) (aint 2)))

  test "prefixOp1" expression "(+)" (PrefixOp Nothing (toOpTuple Add))
  test "prefixOp2" expression "( ++ )" (PrefixOp Nothing (toOpTuple Append))
  test "prefixOp3" expression "((^) 2 10)" (App Nothing (PrefixOp Nothing (toOpTuple Power)) (toList [aint 2, aint 10]))

  test "sectL1" expression "(1+)" (SectL Nothing (aint 1) (toOpTuple Add))
  test "sectL2" expression "( n `mod` )" (SectL Nothing (aname "n") (toOpTuple (InfixFunc "mod")))
  test "sectL3" expression "([1] ++)" (SectL Nothing (List Nothing $ toList [aint 1]) (toOpTuple Append))
  test "sectL4" expression "(   ( 2 +  2 )  <= )" (SectL Nothing (Binary Nothing (toOpTuple Add) (aint 2) (aint 2)) (toOpTuple Leq))

  test "let1" expression "let x = 1 in x + x" (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (aint 1)) Nil) (Binary Nothing (toOpTuple Add) (aname "x") (aname "x")))
  test "let2" expression "letty + let x = 1 in x" (Binary Nothing (toOpTuple Add) (aname "letty") (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (aint 1)) Nil) (aname "x")))
  test "let3" expression "let x = let y = 1 in y in let z = 2 in x + z" (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "y")) (Atom Nothing (AInt 1))) (Nil)) (Atom Nothing (Name "y")))) (Nil)) (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "z")) (Atom Nothing (AInt 2))) (Nil)) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "x")) (Atom Nothing (Name "z")))))
  test "let4" expression "let { x = 1; y = 2; z = 3} in x + y + z"              (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (Atom Nothing (AInt 1))) (Cons (Tuple (Lit Nothing (Name "y")) (Atom Nothing (AInt 2))) (Cons (Tuple (Lit Nothing (Name "z")) (Atom Nothing (AInt 3))) (Nil)))) (Binary Nothing (toOpTuple Add) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "x")) (Atom Nothing (Name "y"))) (Atom Nothing (Name "z"))))
  test "let5" expression "let x = 1; y = 2; z = 3 in x + y + z"                 (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (Atom Nothing (AInt 1))) (Cons (Tuple (Lit Nothing (Name "y")) (Atom Nothing (AInt 2))) (Cons (Tuple (Lit Nothing (Name "z")) (Atom Nothing (AInt 3))) (Nil)))) (Binary Nothing (toOpTuple Add) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "x")) (Atom Nothing (Name "y"))) (Atom Nothing (Name "z"))))
  test "let6" expression "let x = 1\n    y = 2\n    z = 3 in x + y + z"         (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (Atom Nothing (AInt 1))) (Cons (Tuple (Lit Nothing (Name "y")) (Atom Nothing (AInt 2))) (Cons (Tuple (Lit Nothing (Name "z")) (Atom Nothing (AInt 3))) (Nil)))) (Binary Nothing (toOpTuple Add) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "x")) (Atom Nothing (Name "y"))) (Atom Nothing (Name "z"))))
  test "let7" expression "let {\n  x = 1 ;\n  y = 2 ;\n  z = 3\n} in x + y + z" (LetExpr Nothing (Cons (Tuple (Lit Nothing (Name "x")) (Atom Nothing (AInt 1))) (Cons (Tuple (Lit Nothing (Name "y")) (Atom Nothing (AInt 2))) (Cons (Tuple (Lit Nothing (Name "z")) (Atom Nothing (AInt 3))) (Nil)))) (Binary Nothing (toOpTuple Add) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "x")) (Atom Nothing (Name "y"))) (Atom Nothing (Name "z"))))

  test "consLit1" binding "(x:xs)" (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs")))
  test "consLit2" binding "(x:(y:zs))" (ConsLit Nothing (Lit Nothing (Name "x")) (ConsLit Nothing (Lit Nothing (Name "y")) (Lit Nothing (Name "zs"))))
  test "consLit3" binding "(  x  :  (  666  :  zs  )   )" (ConsLit Nothing (Lit Nothing (Name "x")) (ConsLit Nothing (Lit Nothing (AInt 666)) (Lit Nothing (Name "zs"))))

  test "listLit1" binding "[]" (ListLit Nothing Nil)
  test "listLit2" binding "[    ]" (ListLit Nothing Nil)
  test "listLit3" binding "[  True ]" (ListLit Nothing (Cons (Lit Nothing (Bool true)) Nil))
  test "listLit4" binding "[  x   ,  y  ,   1337 ]" (ListLit Nothing (toList [Lit Nothing (Name "x"), Lit Nothing (Name "y"), Lit Nothing (AInt 1337)]))

  test "tupleLit1" binding "(a,b)" (NTupleLit Nothing (toList [Lit Nothing (Name "a"), Lit Nothing (Name "b")]))
  test "tupleLit2" binding "(   a   ,  b   ,   c   )" (NTupleLit Nothing (toList $ [Lit Nothing (Name "a"), Lit Nothing (Name "b"), Lit Nothing (Name "c")]))
  test "tupleLit3" binding "(  (  x  ,  y  )  , ( a  ,  b  )  , 10 )"
    (NTupleLit Nothing (toList
      [ NTupleLit Nothing (toList [Lit Nothing (Name "x"), Lit Nothing (Name "y")])
      , NTupleLit Nothing (toList [Lit Nothing (Name "a"), Lit Nothing (Name "b")])
      , (Lit Nothing (AInt 10))
      ]))

  test "binding" binding "( ( x , y ) : [ a , b ] )"
    (ConsLit Nothing
      (NTupleLit Nothing (toList [Lit Nothing (Name "x"), Lit Nothing (Name "y")]))
      (ListLit Nothing (toList [Lit Nothing (Name "a"), Lit Nothing (Name "b")])))

  test "def1" definition "x = 10" (Def "x" Nil (aint 10))
  test "def2" definition "double x = x + x" (Def "double" (Cons (Lit Nothing (Name "x")) Nil) (Binary Nothing (toOpTuple Add) (aname "x") (aname "x")))
  test "def3" definition "zip (x:xs) (y:ys) = (x,y) : zip xs ys"
    (Def "zip"
      (toList [ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs")), ConsLit Nothing (Lit Nothing (Name "y")) (Lit Nothing (Name "ys"))])
      (Binary Nothing (toOpTuple Colon)
        (NTuple Nothing (toList  [Atom Nothing (Name "x"), Atom Nothing (Name "y")]))
        (App Nothing (aname "zip") (toList [Atom Nothing (Name "xs"), Atom Nothing (Name "ys")]))))

  test "defs" definitions "\n\na   =   10 \n  \n \nb    =  20  \n\n  \n"
    (toList [Def "a" Nil (aint 10), Def "b" Nil (aint 20)])

  test "prelude" definitions prelude parsedPrelude
  test "expression" expression "sum (map (^2) [1, 2, 3, 4])"
    (App Nothing
      (Atom Nothing (Name "sum"))
      (Cons
        (App Nothing
          (Atom Nothing (Name "map"))
          (Cons (SectR Nothing (toOpTuple Power) (Atom Nothing (AInt 2)))
            (Cons (List Nothing (Cons (Atom Nothing (AInt 1)) (Cons (Atom Nothing (AInt 2)) (Cons (Atom Nothing (AInt 3)) (Cons (Atom Nothing (AInt 4)) (Nil))))))
              (Nil))))
        (Nil)))

  test "char_atom1" atom "'a'" (Char "a")
  test "char_atom2" atom "'\\\\'" (Char "\\")
  test "char_atom3" atom "'\\n'" (Char "\n")
  test "char_expr1" expression "'\\r'" (Atom Nothing (Char "\r"))
  test "char_expr2" expression "['\\\\', '\\'', '\\\"']" (List Nothing $ toList [Atom Nothing (Char "\\"), Atom Nothing (Char "'"), Atom Nothing (Char "\"")])

  test "string1" expression "\"asdf\"" (List Nothing $ toList [Atom Nothing (Char "a"), Atom Nothing (Char "s"), Atom Nothing (Char "d"), Atom Nothing (Char "f")])
  test "string2" expression "\"\\\\\\n\\\"\\\'\"" (List Nothing $ toList [Atom Nothing (Char "\\"), Atom Nothing (Char "\n"), Atom Nothing (Char "\""), Atom Nothing (Char "'")])

  test "listComp1" expression "[ x | x <- [1,2,3] ]" $ ListComp Nothing (Atom Nothing (Name "x")) (toList [Gen Nothing (Lit Nothing (Name "x")) (List Nothing (toList [Atom Nothing (AInt 1), Atom Nothing (AInt 2), Atom Nothing (AInt 3)]))])
  test "listComp2" expression "[ b + c | let b = 3, c <- [1 .. ]]" $ ListComp Nothing (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "b")) (Atom Nothing (Name ("c")))) $ toList [Let Nothing (Lit Nothing (Name "b")) (Atom Nothing (AInt 3)),
    Gen Nothing (Lit Nothing (Name "c")) (ArithmSeq Nothing (Atom Nothing (AInt 1)) Nothing Nothing)]
  test "listComp3" expression "[a*b|let a=5,let b=a+1]" $ ListComp Nothing (Binary Nothing (toOpTuple Mul) (Atom Nothing (Name "a")) (Atom Nothing (Name "b"))) $ toList [Let Nothing (Lit Nothing (Name "a")) (Atom Nothing (AInt 5)),
    Let Nothing (Lit Nothing (Name "b")) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "a")) (Atom Nothing (AInt 1)))]
  test "listComp4" expression "[ x | x <- [1..10], even x ]" $ ListComp Nothing (aname "x") $ toList [ Gen Nothing (Lit Nothing (Name "x")) (ArithmSeq Nothing (aint 1) Nothing (Just (aint 10))), Guard Nothing (App Nothing (aname "even") $ toList [aname "x"])]

  testConstructorsExpression
  testConstructorsDefinition
  testConstructorsBinding
  testTypes
  testTypeDefinition
  testSymbol
  testInfixDataConstrtructorDefinition
  testDataConstrtructorDefinition
  testInfixConstructor

parsedPrelude' :: List Definition
parsedPrelude' = case runParserIndent definitions prelude of
                      Left m -> unsafeUndef $ "Failed to parse prelude: " <> show m
                      Right r -> r

prelude :: String
prelude =
  "data Maybe a\n" <>
  "  = Nothing\n" <>
  "  | Just a\n" <>
  "\n" <>
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

parsedPrelude :: List Definition
parsedPrelude = toList [
  (Def "Nothing" Nil
    (Atom
      (Just
        (TTypeCons
          "Maybe"
          (Cons
            (TypVar "a")
            Nil)))
      (Constr "Nothing"))),
  (Def "Just" Nil
    (Atom
      (Just
        (TypArr
          (TypVar "a")
          (TTypeCons "Maybe" (Cons (TypVar "a") Nil))))
      (Constr "Just"))),
  (Def "and" (ConsLit Nothing (Lit Nothing (Bool true)) (Lit Nothing (Name "xs")) : Nil) (App Nothing (Atom Nothing (Name "and")) (Cons (Atom Nothing (Name "xs")) (Nil)))),
  (Def "and" (ConsLit Nothing (Lit Nothing (Bool false)) (Lit Nothing (Name "xs")) : Nil) (Atom Nothing (Bool false))),
  (Def "and" (ListLit Nothing Nil : Nil) (Atom Nothing (Bool true))),
  (Def "or" (ConsLit Nothing (Lit Nothing (Bool false)) (Lit Nothing (Name "xs")) : Nil) (App Nothing (Atom Nothing (Name "or")) (Cons (Atom Nothing (Name "xs")) (Nil)))),
  (Def "or" (ConsLit Nothing (Lit Nothing (Bool true)) (Lit Nothing (Name "xs")) : Nil) (Atom Nothing (Bool true))),
  (Def "or" (ListLit Nothing Nil : Nil) (Atom Nothing (Bool false))),
  (Def "all" (Lit Nothing (Name "p") : Nil) (Binary Nothing (toOpTuple Composition) (Atom Nothing (Name "and")) (App Nothing (Atom Nothing (Name "map")) (Cons (Atom Nothing (Name "p")) (Nil))))),
  (Def "any" (Lit Nothing (Name "p") : Nil) (Binary Nothing (toOpTuple Composition) (Atom Nothing (Name "or")) (App Nothing (Atom Nothing (Name "map")) (Cons (Atom Nothing (Name "p")) (Nil))))),
  (Def "head" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (Atom Nothing (Name "x"))),
  (Def "tail" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (Atom Nothing (Name "xs"))),
  (Def "take" (Cons (Lit Nothing (AInt 0)) (Cons (Lit Nothing (Name "xs")) (Nil))) (List Nothing (Nil))),
  (Def "take" (Cons (Lit Nothing (Name "n")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil))) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "take")) (Cons (Binary Nothing (toOpTuple Sub) (Atom Nothing (Name "n")) (Atom Nothing (AInt 1))) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "drop" (Cons (Lit Nothing (AInt 0)) (Cons (Lit Nothing (Name "xs")) (Nil))) (Atom Nothing (Name "xs"))),
  (Def "drop" (Cons (Lit Nothing (Name "n")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil))) (App Nothing (Atom Nothing (Name "drop")) (Cons (Binary Nothing (toOpTuple Sub) (Atom Nothing (Name "n")) (Atom Nothing (AInt 1))) (Cons (Atom Nothing (Name "xs")) (Nil))))),
  (Def "elem" (Cons (Lit Nothing (Name "e")) (Cons (ListLit Nothing (Nil)) (Nil))) (Atom Nothing (Bool false))),
  (Def "elem" (Cons (Lit Nothing (Name "e")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil))) (IfExpr Nothing (Binary Nothing (toOpTuple Equ) (Atom Nothing (Name "e")) (Atom Nothing (Name "x"))) (Atom Nothing (Bool true)) (App Nothing (Atom Nothing (Name "elem")) (Cons (Atom Nothing (Name "e")) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "max" (Cons (Lit Nothing (Name "a")) (Cons (Lit Nothing (Name "b")) (Nil))) (IfExpr Nothing (Binary Nothing (toOpTuple Geq) (Atom Nothing (Name "a")) (Atom Nothing (Name "b"))) (Atom Nothing (Name "a")) (Atom Nothing (Name "b")))),
  (Def "min" (Cons (Lit Nothing (Name "a")) (Cons (Lit Nothing (Name "b")) (Nil))) (IfExpr Nothing (Binary Nothing (toOpTuple Geq) (Atom Nothing (Name "b")) (Atom Nothing (Name "a"))) (Atom Nothing (Name "a")) (Atom Nothing (Name "b")))),
  (Def "maximum" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (App Nothing (Atom Nothing (Name "foldr")) (Cons (Atom Nothing (Name "max")) (Cons (Atom Nothing (Name "x")) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "minimum" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (App Nothing (Atom Nothing (Name "foldr")) (Cons (Atom Nothing (Name "min")) (Cons (Atom Nothing (Name "x")) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "length" (Cons (ListLit Nothing (Nil)) (Nil)) (Atom Nothing (AInt 0))),
  (Def "length" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (Binary Nothing (toOpTuple Add) (Atom Nothing (AInt 1)) (App Nothing (Atom Nothing (Name "length")) (Cons (Atom Nothing (Name "xs")) (Nil))))),
  (Def "zip" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Cons (ConsLit Nothing (Lit Nothing (Name "y")) (Lit Nothing (Name "ys"))) (Nil))) (Binary Nothing (toOpTuple Colon) (NTuple Nothing (Cons (Atom Nothing (Name "x")) (Cons (Atom Nothing (Name "y")) (Nil)))) (App Nothing (Atom Nothing (Name "zip")) (Cons (Atom Nothing (Name "xs")) (Cons (Atom Nothing (Name "ys")) (Nil)))))),
  (Def "zip" (Cons (ListLit Nothing (Nil)) (Cons (Lit Nothing (Name "_")) (Nil))) (List Nothing (Nil))),
  (Def "zip" (Cons (Lit Nothing (Name "_")) (Cons (ListLit Nothing (Nil)) (Nil))) (List Nothing (Nil))),
  (Def "zipWith" (Cons (Lit Nothing (Name "f")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Cons (ConsLit Nothing (Lit Nothing (Name "y")) (Lit Nothing (Name "ys"))) (Nil)))) (Binary Nothing (toOpTuple Colon) (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "x")) (Cons (Atom Nothing (Name "y")) (Nil)))) (App Nothing (Atom Nothing (Name "zipWith")) (Cons (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "xs")) (Cons (Atom Nothing (Name "ys")) (Nil))))))),
  (Def "zipWith" (Cons (Lit Nothing (Name "_")) (Cons (ListLit Nothing (Nil)) (Cons (Lit Nothing (Name "_")) (Nil)))) (List Nothing (Nil))),
  (Def "zipWith" (Cons (Lit Nothing (Name "_")) (Cons (Lit Nothing (Name "_")) (Cons (ListLit Nothing (Nil)) (Nil)))) (List Nothing (Nil))),
  (Def "unzip" (Cons (ListLit Nothing (Nil)) (Nil)) (NTuple Nothing (Cons (List Nothing (Nil)) (Cons (List Nothing (Nil)) (Nil))))),
  (Def "unzip" (Cons (ConsLit Nothing (NTupleLit Nothing (Cons (Lit Nothing (Name "a")) (Cons (Lit Nothing (Name "b")) (Nil)))) (Lit Nothing (Name "xs"))) (Nil)) (Binary Nothing (toOpTuple Dollar) (Lambda Nothing (Cons (NTupleLit Nothing (Cons (Lit Nothing (Name "as")) (Cons (Lit Nothing (Name "bs")) (Nil)))) (Nil)) (NTuple Nothing (Cons (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "a")) (Atom Nothing (Name "as"))) (Cons (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "b")) (Atom Nothing (Name "bs"))) (Nil))))) (App Nothing (aname "unzip") (Cons (aname "xs") Nil)))),
  (Def "fst" (Cons (NTupleLit Nothing (Cons (Lit Nothing (Name "x")) (Cons (Lit Nothing (Name "_")) (Nil)))) Nil) (Atom Nothing (Name "x"))),
  (Def "snd" (Cons (NTupleLit Nothing (Cons (Lit Nothing (Name "_")) (Cons (Lit Nothing (Name "x")) (Nil)))) Nil) (Atom Nothing (Name "x"))),
  (Def "curry" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "a")) (Cons (Lit Nothing (Name "b")) (Nil)))) (App Nothing (Atom Nothing (Name "f")) (Cons (NTuple Nothing (Cons (Atom Nothing (Name "a")) (Cons (Atom Nothing (Name "b")) (Nil)))) (Nil)))),
  (Def "uncurry" (Cons (Lit Nothing (Name "f")) (Cons (NTupleLit Nothing (Cons (Lit Nothing (Name "a")) (Cons (Lit Nothing (Name "b")) (Nil)))) (Nil))) (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "a")) (Cons (Atom Nothing (Name "b")) (Nil))))),
  (Def "repeat" (Cons (Lit Nothing (Name "x")) (Nil)) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "repeat")) (Cons (Atom Nothing (Name "x")) (Nil))))),
  (Def "replicate" (Cons (Lit Nothing (AInt 0)) (Cons (Lit Nothing (Name "_")) (Nil))) (List Nothing (Nil))),
  (Def "replicate" (Cons (Lit Nothing (Name "n")) (Cons (Lit Nothing (Name "x")) (Nil))) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "replicate")) (Cons (Binary Nothing (toOpTuple Sub) (Atom Nothing (Name "n")) (Atom Nothing (AInt 1))) (Cons (Atom Nothing (Name "x")) (Nil)))))),
  (Def "enumFromTo" (Cons (Lit Nothing (Name "a")) (Cons (Lit Nothing (Name "b")) (Nil))) (IfExpr Nothing (Binary Nothing (toOpTuple Leq) (Atom Nothing (Name "a")) (Atom Nothing (Name "b"))) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "a")) (App Nothing (Atom Nothing (Name "enumFromTo")) (Cons (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "a")) (Atom Nothing (AInt 1))) (Cons (Atom Nothing (Name "b")) (Nil))))) (List Nothing (Nil)))),
  (Def "sum" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (Binary Nothing (toOpTuple Add) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "sum")) (Cons (Atom Nothing (Name "xs")) (Nil))))),
  (Def "sum" (Cons (ListLit Nothing (Nil)) (Nil)) (Atom Nothing (AInt 0))),
  (Def "product" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (Binary Nothing (toOpTuple Mul) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "product")) (Cons (Atom Nothing (Name "xs")) (Nil))))),
  (Def "product" (Cons (ListLit Nothing (Nil)) (Nil)) (Atom Nothing (AInt 1))),
  (Def "reverse" (Cons (ListLit Nothing (Nil)) (Nil)) (List Nothing (Nil))),
  (Def "reverse" (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)) (Binary Nothing (toOpTuple Append) (App Nothing (Atom Nothing (Name "reverse")) (Cons (Atom Nothing (Name "xs")) (Nil))) (List Nothing (Cons (Atom Nothing (Name "x")) (Nil))))),
  (Def "concat" (Nil) (App Nothing (Atom Nothing (Name "foldr")) (Cons (PrefixOp Nothing (toOpTuple Append)) (Cons (List Nothing (Nil)) (Nil))))),
  (Def "map" (Cons (Lit Nothing (Name "f")) (Cons (ListLit Nothing (Nil)) (Nil))) (List Nothing (Nil))),
  (Def "map" (Cons (Lit Nothing (Name "f")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil))) (Binary Nothing (toOpTuple Colon) (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "x")) (Nil))) (App Nothing (Atom Nothing (Name "map")) (Cons (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "not" (Cons (Lit Nothing (Bool true)) (Nil)) (Atom Nothing (Bool false))),
  (Def "not" (Cons (Lit Nothing (Bool false)) (Nil)) (Atom Nothing (Bool true))),
  (Def "filter" (Cons (Lit Nothing (Name "p")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil))) (IfExpr Nothing (App Nothing (Atom Nothing (Name "p")) (Cons (Atom Nothing (Name "x")) (Nil))) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "filter")) (Cons (Atom Nothing (Name "p")) (Cons (Atom Nothing (Name "xs")) (Nil))))) (App Nothing (Atom Nothing (Name "filter")) (Cons (Atom Nothing (Name "p")) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "filter" (Cons (Lit Nothing (Name "p")) (Cons (ListLit Nothing (Nil)) (Nil))) (List Nothing (Nil))),
  (Def "foldr" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "ini")) (Cons (ListLit Nothing (Nil)) (Nil)))) (Atom Nothing (Name "ini"))),
  (Def "foldr" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "ini")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)))) (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "x")) (Cons (App Nothing (Atom Nothing (Name "foldr")) (Cons (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "ini")) (Cons (Atom Nothing (Name "xs")) (Nil))))) (Nil))))),
  (Def "foldl" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "acc")) (Cons (ListLit Nothing (Nil)) (Nil)))) (Atom Nothing (Name "acc"))),
  (Def "foldl" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "acc")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)))) (App Nothing (Atom Nothing (Name "foldl")) (Cons (Atom Nothing (Name "f")) (Cons (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "acc")) (Cons (Atom Nothing (Name "x")) (Nil)))) (Cons (Atom Nothing (Name "xs")) (Nil)))))),
  (Def "scanl" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "b")) (Cons (ListLit Nothing (Nil)) (Nil)))) (List Nothing (Cons (Atom Nothing (Name "b")) (Nil)))),
  (Def "scanl" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "b")) (Cons (ConsLit Nothing (Lit Nothing (Name "x")) (Lit Nothing (Name "xs"))) (Nil)))) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "b")) (App Nothing (Atom Nothing (Name "scanl")) (Cons (Atom Nothing (Name "f")) (Cons (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "b")) (Cons (Atom Nothing (Name "x")) (Nil)))) (Cons (Atom Nothing (Name "xs")) (Nil))))))),
  (Def "iterate" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "x")) (Nil))) (Binary Nothing (toOpTuple Colon) (Atom Nothing (Name "x")) (App Nothing (Atom Nothing (Name "iterate")) (Cons (Atom Nothing (Name "f")) (Cons (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "x")) (Nil))) (Nil)))))),
  (Def "id" (Cons (Lit Nothing (Name "x")) (Nil)) (Atom Nothing (Name "x"))),
  (Def "const" (Cons (Lit Nothing (Name "x")) (Cons (Lit Nothing (Name "_")) (Nil))) (Atom Nothing (Name "x"))),
  (Def "flip" (Cons (Lit Nothing (Name "f")) (Cons (Lit Nothing (Name "x")) (Cons (Lit Nothing (Name "y")) (Nil)))) (App Nothing (Atom Nothing (Name "f")) (Cons (Atom Nothing (Name "y")) (Cons (Atom Nothing (Name "x")) (Nil))))),
  (Def "even" (Cons (Lit Nothing (Name "n")) (Nil)) (Binary Nothing (toOpTuple Equ) (Binary Nothing (toOpTuple (InfixFunc "mod")) (Atom Nothing (Name "n")) (Atom Nothing (AInt 2))) (Atom Nothing (AInt 0)))),
  (Def "odd" (Cons (Lit Nothing (Name "n")) (Nil)) (Binary Nothing (toOpTuple Equ) (Binary Nothing (toOpTuple (InfixFunc "mod")) (Atom Nothing (Name "n")) (Atom Nothing (AInt 2))) (Atom Nothing (AInt 1)))),
  (Def "fix" (Cons (Lit Nothing (Name "f")) (Nil)) (App Nothing (Atom Nothing (Name "f")) (Cons (App Nothing (Atom Nothing (Name "fix")) (Cons (Atom Nothing (Name "f")) (Nil))) (Nil))))
  ]

stringToList :: String -> List Char
stringToList = Array.toUnfoldable <<< String.toCharArray

type MType = Maybe Type

econstr :: String -> TypeTree
econstr n = Atom Nothing (Constr n)

ename :: String -> TypeTree
ename n = Atom Nothing (Name n)

eint :: Int -> TypeTree
eint i = Atom Nothing (AInt i)

eapp :: TypeTree -> Array TypeTree -> TypeTree
eapp f as = App Nothing f (toList as)

ebin :: Op -> TypeTree -> TypeTree -> TypeTree
ebin o l r = Binary Nothing (Tuple o Nothing) l r

def :: String -> Array (Binding MType) -> TypeTree -> Definition
def n bs e = Def n (toList bs) e

testConstructorsExpression :: Test Unit
testConstructorsExpression = do
  test "simple-expr-1" expression
    "Foo"
    (econstr "Foo")

  test "simple-expr-2" expression
    "Foo 1"
    (eapp
      (econstr "Foo")
      [eint 1])

  test "simple-expr-3" expression
    "Foo 1 (1 + 2)"
    (eapp
      (econstr "Foo")
      [ eint 1
      , ebin Add
        (eint 1)
        (eint 2)])

  test "nested-expr-1" expression
    "Foo Bar"
    (eapp
      (econstr "Foo")
      [ econstr "Bar" ])

  test "nested-expr-2" expression
    "Foo bar"
    (eapp
      (econstr "Foo")
      [ ename "bar"])

  test "nested-expr-3" expression
    "foo Bar"
    (eapp
      (ename "foo")
      [econstr "Bar"])

  test "nested-deep-expr-1" expression
    "Foo1 (Foo2 (Foo3 bar))"
    (eapp (econstr "Foo1")
      [ eapp (econstr "Foo2")
        [ eapp (econstr "Foo3")
          [ ename "bar" ]]])

  test "nested-expr-4" expression
    "Bar || Foo"
    (ebin Or
      (econstr "Bar")
      (econstr "Foo"))

  test "nested-expr-5" expression
    "Bar 1 :- Foo 2 3"
    (ebin (InfixConstr ":-")
      (eapp (econstr "Bar") [eint 1])
      (eapp (econstr "Foo") [eint 2, eint 3]))

  test "nested-expr-6" expression
    "Bar 1 (Foo ::: Foo 2)"
    (eapp (econstr "Bar")
      [ eint 1
      , ebin (InfixConstr ":::")
        (econstr "Foo")
        (eapp (econstr "Foo") [eint 2])])


testConstructorsDefinition :: Test Unit
testConstructorsDefinition = do
  test "definition-1" definition
    "foo (Bar a b) = Foo a b"
    (def "foo"
      [prefixDataConstr "Bar" [litname "a", litname "b"]]
      (eapp (econstr "Foo")
        [ename "a", ename "b"]))

  test "definition-2" definition
    "foo (r :+ i) = r :- i"
    (def "foo"
      [infixDataConstr ":+" (litname "r") (litname "i")]
      (ebin (InfixConstr ":-")
        (ename "r")
        (ename "i")))

  rejectTests "invalid-definition" definition
    [ "foo a :- b = a b"
    , "foo (x :-) b = x b"
    ]



litname :: String -> Binding MType
litname = Lit Nothing <<< Name

litint :: Int -> Binding MType
litint = Lit Nothing <<< AInt

litlist :: Array (Binding MType) -> Binding MType
litlist = ListLit Nothing <<< toList

bpair :: Binding MType -> Binding MType -> Binding MType
bpair l r = NTupleLit Nothing (Cons l (Cons r Nil))

prefixDataConstr :: String -> Array (Binding MType) -> Binding MType
prefixDataConstr name [] = (Lit Nothing (Constr name))
prefixDataConstr name args = ConstrLit Nothing (PrefixDataConstr name (Array.length args) (toList args))

infixDataConstr :: String -> Binding MType -> Binding MType -> Binding MType
infixDataConstr op l r = ConstrLit Nothing (InfixDataConstr op LEFTASSOC 9 l r)

litcons :: Binding MType -> Binding MType -> Binding MType
litcons = ConsLit Nothing

testConstructorsBinding :: Test Unit
testConstructorsBinding = do
  test "binding-simple-0" binding
    "_"
    (litname "_")

  test "binding-simple-1" binding
    "(Foo a b)"
    (prefixDataConstr "Foo" [litname "a", litname "b"])

  test "binding-simple-2" binding
    "(Foo)"
    (prefixDataConstr "Foo" [])

  test "binding-simple-3" binding
    "Foo"
    (prefixDataConstr "Foo" [])

  test "binding-simple-4" binding
    "a"
    (litname "a")

  test "binding-nested-1" binding
    "(Foo Foo 1)"
    (prefixDataConstr "Foo"
      [ prefixDataConstr "Foo" []
      , litint 1 ])

  test "binding-nested-2" binding
    "(Foo (Foo 1) (Foo 2 3))"
    (prefixDataConstr "Foo"
      [ prefixDataConstr "Foo"
        [ litint 1 ]
      , prefixDataConstr "Foo"
        [ litint 2
        , litint 3 ]])

  test "binding-nested-3" binding
    "(Foo (1,2))"
    (prefixDataConstr "Foo"
      [ bpair (litint 1) (litint 2) ])

  test "binding-nested-4" binding
    "([a,c],b)"
    (bpair
      (ListLit Nothing (Cons (litname "a") (Cons (litname "c") Nil)))
      (litname "b"))

  test "binding-nested-5" binding
    "(Foo foo, Bar bar)"
    (bpair
      (prefixDataConstr "Foo" [litname "foo"])
      (prefixDataConstr "Bar" [litname "bar"]))

  test "binding-nested-6" binding
    "(foo :- bar, bar :+ foo)"
    (bpair
      (infixDataConstr ":-" (litname "foo") (litname "bar"))
      (infixDataConstr ":+" (litname "bar") (litname "foo")))

  test "binding-nested-7" binding
    "(Foo foo :- Bar bar)"
    (infixDataConstr ":-"
      (prefixDataConstr "Foo" [litname "foo"])
      (prefixDataConstr "Bar" [litname "bar"]))

  test "binding-nested-8" binding
    "(Foo (foo :- bar))"
    (prefixDataConstr "Foo"
      [ infixDataConstr ":-"
        (litname "foo")
        (litname "bar") ])

  test "list-binding-nested-1" binding
    "[Foo a b]"
    (litlist
      [ prefixDataConstr "Foo"
        [ litname "a"
        , litname "b" ]])

  test "list-binding-nested-2" binding
    "[Foo a, a :- b]"
    (litlist
      [ prefixDataConstr "Foo"
        [ litname "a" ]
      , infixDataConstr ":-"
        (litname "a")
        (litname "b") ])

  test "list-binding-nested-3" binding
    "[ Foo foo\n , Bar bar\n , foo :-: bar ]"
    (litlist
      [ prefixDataConstr "Foo" [litname "foo"]
      , prefixDataConstr "Bar" [litname "bar"]
      , infixDataConstr ":-:"
        (litname "foo")
        (litname "bar") ])

  test "list-binding-nested-4" binding
    "[ [ 1, 2 ]\n , [ 3, 4 ]\n , [Foo 2 3] ]"
    (litlist
      [ litlist [litint 1, litint 2]
      , litlist [litint 3, litint 4]
      , litlist [prefixDataConstr "Foo" [litint 2, litint 3]]])

  test "list-binding-nested-5" binding
    "[1:2:3:[], Foo 3]"
    (litlist
      [ litcons (litint 1)
        (litcons (litint 2)
          (litcons (litint 3)
            (litlist [])))
      , prefixDataConstr "Foo" [litint 3]])

  test "list-binding-nested-6" binding
    "[[[[1]]]]"
    (litlist
      [litlist
        [litlist
          [litlist [litint 1]]]])

  test "cons-binding-nested-1" binding
    "(_:_)"
    (litcons
      (litname "_")
      (litname "_"))

  test "cons-binding-nested-2" binding
    "(_:a)"
    (litcons
      (litname "_")
      (litname "a"))
      
  test "cons-binding-nested-3" binding
    "(a:_)"
    (litcons
      (litname "a")
      (litname "_"))

  test "cons-binding-nested-4" binding
    "(a:a)"
    (litcons
      (litname "a")
      (litname "a"))

  test "cons-binding-nested-5" binding
    "(_:(_:(x:_)))"
    (litcons
      (litname "_")
      (litcons
        (litname "_")
        (litcons
          (litname "x")
          (litname "_"))))

  test "cons-binding-nested-6" binding
    "(_:_:+_)"
    (litcons
      (litname "_")
      (infixDataConstr ":+"
        (litname "_")
        (litname "_")))

  test "infix-constr-binding-1" binding
    "(a :- b :- c)"
    (infixDataConstr ":-"
      (infixDataConstr ":-"
        (litname "a")
        (litname "b"))
      (litname "c"))

  test "infix-constr-binding-2" binding
    "(a :- b :+ c :- d)"
    (infixDataConstr ":-"
      (infixDataConstr ":+"
        (infixDataConstr ":-"
          (litname "a")
          (litname "b"))
        (litname "c"))
      (litname "d"))

  rejectTests "invalid-infix-operator" binding
    [ "(a :-) b"
    , "(:-) a b"
    , ":- a"
    , "b :-"
    , ":- a b"
    ]

  rejectTests "invalid-prefix-operator" binding
    [ "a Foo"
    , "foo a"
    ]




testTypes :: Test Unit
testTypes = do
  test "types1" types
    "a"
    (TypVar "a")
  test "types2" types
    "A"
    (TTypeCons "A" Nil)
  test "types3" types
    "Int" (TypCon "Int")
  test "types4" types
    "Char" (TypCon "Char")
  test "types5" types
    "Bool" (TypCon "Bool")
  test "types6" types
    "A a b c"
    (TTypeCons "A" (toList [TypVar "a", TypVar "b", TypVar "c"]))
  test "types7" types
    "A Int b Bool"
    (TTypeCons "A" (toList [TypCon "Int", TypVar "b", TypCon "Bool"]))
  test "types8" types
    "A (B c)"
    (TTypeCons "A"
        (toList
          [TTypeCons "B"
              (toList [TypVar "c"])]))
  test "types9" types
    "A (B Char)"
    (TTypeCons "A"
        (toList
          [TTypeCons "B"
              (toList [TypCon "Char"])]))
  test "types10" types
    "A (B c) (C d)"
      (TTypeCons "A"
        (toList
          [ TTypeCons "B"
              (toList [TypVar "c"])
          , TTypeCons "C"
              (toList [TypVar "d"])]))

  test "types11" types
    "B"
    (TTypeCons "B" Nil)
  test "types12" types
    "C"
    (TTypeCons "C" Nil)
  test "types13" types
    "I"
    (TTypeCons "I" Nil)
  test "function1" types
    "Int -> Int"
    (TypArr (TypCon "Int") (TypCon "Int"))
  test "function1'" types
    "(Int -> Int)"
    (TypArr (TypCon "Int") (TypCon "Int"))
  test "function2" types
    "Int -> Int -> Int"
    (TypArr (TypCon "Int") (TypArr (TypCon "Int") (TypCon "Int")))
  test "function2'" types
    "(Int -> Int -> Int)"
    (TypArr (TypCon "Int") (TypArr (TypCon "Int") (TypCon "Int")))

  test "function3" types
    "(Int -> Int) -> Int"
    (TypArr
      (TypArr (TypCon "Int") (TypCon "Int"))
      (TypCon "Int"))

  test "function4" types
    "((a -> a) -> a) -> a"
    (((TypVar "a" `TypArr` TypVar "a") `TypArr` TypVar "a") `TypArr` TypVar "a")

  test "function5" types
    "a\n\t-> a\n\t ->a"
    (TypArr (TypVar "a") (TypArr (TypVar "a") (TypVar "a")))

  for_ (2 .. 8) $ \i -> do
    test (show i <> "-tuple") types
      ("(" <> intercalate ", " (Array.replicate i "Int") <> ")")
      (TTuple
          (toList (Array.replicate i (TypCon "Int"))))

  test "tuple-space" types
    " (Int, Int)"
    (TTuple
        (toList [TypCon "Int", TypCon "Int"]))

  test "tuples1" types
    "((Int, Int), (Int, Int))"
    (TTuple
        (toList
          [ TTuple (toList [(TypCon "Int"), (TypCon "Int")])
          , TTuple (toList [(TypCon "Int"), (TypCon "Int")])]))

  test "tuples2" types
    "(Maybe a, a, b)"
    (TTuple
        (toList
          [ TTypeCons "Maybe" (toList [TypVar "a"])
          , TypVar "a"
          , TypVar "b"]))

  test "simple-list1" types
    "[Int]"
    (TList (TypCon "Int"))

  test "simple-list2" types
    "[a]"
    (TList (TypVar "a"))

  test "list1" types
    "[a -> b]"
    (TList
        (TypArr
          (TypVar "a")
          (TypVar "b")))

  test "list2" types
    "[Either a Int]"
    (TList
      (TTypeCons "Either"
        (toList
          [ TypVar "a", TypCon "Int" ])))

  test "(list2)" types
    "([Either a Int])"
    (TList
      (TTypeCons "Either"
        (toList
          [ TypVar "a", TypCon "Int" ])))

  test "((list2))" types
    "(([Either a Int]))"
      (TList
          (TTypeCons "Either"
            (toList
              [ TypVar "a", TypCon "Int" ])))

  test "list3" types
    "[Maybe a -> Either a b]"
    (TList
      (TypArr
        (TTypeCons "Maybe"
          (toList [TypVar "a"]))
        (TTypeCons "Either"
          (toList [TypVar "a", TypVar "b"]))))

  test "list4" types
    "[a] -> [b] -> [c]"
    (TypArr
      (TList (TypVar "a"))
      (TypArr
        (TList (TypVar "b"))
        (TList (TypVar "c"))))

  rejectTests "typesMisindented" types
    [ "Foo\na\nb\nc"
    , " Foo\na"
    , " a\n->b"
    , " (a\n,b\n,c)"
    ]

  rejectTests "typesBracketMismatch" types
    [ "[a"
    , "a]"
    , "[[a]"
    , "[a -> b]]"
    , "(a -> b))"
    , "(a -> b"
    , "a -> b)"
    , "Foo (a b"
    , "Foo a b)"
    , "(Foo a b"
    ]

testTypeDefinition :: Test Unit
testTypeDefinition = do
  test "definition1" typeDefinition
    ("data Tree a\n"
     <> "  = Node Int\n"
     <> "  | Leaf (Tree a) (Tree a)")
    (ADTDef "Tree" (toList ["a"])
      (toList
        [ PrefixDataConstr "Node" 1 (Cons (TypCon "Int") Nil)
        , PrefixDataConstr "Leaf" 2
          (toList
            [ TTypeCons "Tree" (Cons (TypVar "a") Nil)
            , TTypeCons "Tree" (Cons (TypVar "a") Nil)])]))

  test "definition2" typeDefinition
    ("data Test a b\n"
     <> "  = T1 a [b]\n"
     <> "  | T2 [a] (a,b)\n"
     <> "  | T3 [(a,a->b)]\n"
     <> "  | a :+ [b]")
    (ADTDef "Test" (toList ["a","b"])
      (toList
        [ PrefixDataConstr "T1" 2
          (toList
            [ TypVar "a"
            , TList (TypVar "b")])
        , PrefixDataConstr "T2" 2
          (toList
            [ TList (TypVar "a")
            , TTuple (toList [TypVar "a", TypVar "b"])])
        , PrefixDataConstr "T3" 1
          (toList
            [ TList
              (TTuple
                (toList
                  [ TypVar "a"
                  , TypArr (TypVar "a") (TypVar "b")]))])
        , InfixDataConstr ":+" LEFTASSOC 9 (TypVar "a") (TList (TypVar "b"))]))

  test "void" typeDefinition
    "data Void\n"
    (ADTDef "Void" Nil Nil)

  test "none" typeDefinition
    "data None a b c"
    (ADTDef "None"
      (toList ["a", "b", "c"])
      Nil)

  test "id" typeDefinition
    "data Ident a = Ident a"
    (ADTDef "Ident" (toList ["a"])
      (toList
        [ PrefixDataConstr "Ident" 1 (toList [TypVar "a"])]))

  test "maybe" typeDefinition
    "data Maybe a = Nothing | Just a"
    (ADTDef "Maybe" (toList ["a"])
      (toList
        [ PrefixDataConstr "Nothing" 0 Nil
        , PrefixDataConstr "Just" 1 (toList [TypVar "a"])]))

  test "maybe1" typeDefinition
    "data Maybe a\n  = Nothing\n  | Just a"
    (ADTDef "Maybe" (toList ["a"])
      (toList
        [ PrefixDataConstr "Nothing" 0 Nil
        , PrefixDataConstr "Just" 1 (toList [TypVar "a"])]))

  test "list1" typeDefinition
    "data InfixStuff a = a :+ a | a :- a | Prefix a"
    (ADTDef "InfixStuff" (toList ["a"])
      (toList
        [ InfixDataConstr ":+" LEFTASSOC 9 (TypVar "a") (TypVar "a")
        , InfixDataConstr ":-" LEFTASSOC 9 (TypVar "a") (TypVar "a")
        , PrefixDataConstr "Prefix" 1 (Cons (TypVar "a") Nil)]))

  rejectTests "typdefMisindented" typeDefinition
    [ "data Foo\n=Foo"
    , "data Foo a\n =Foo\na"
    , "data Foo\na b c=Foo a b c"
    , "data Foo\n| Foo\n| Bar"
    , "data Foo\n | Foo\n| Bar"
    , "data\nFoo\na = Foo a"
    ]

testSymbol :: Test Unit
testSymbol = do
  test "symbol" symbol
    "!"
    '!'

  test "symbols" (many symbol)
    "!#$%&*+./<>=?@\\^|-~°"
    (stringToList "!#$%&*+./<>=?@\\^|-~°")

testInfixDataConstrtructorDefinition :: Test Unit
testInfixDataConstrtructorDefinition = do
  test "infixConstructor1" infixDataConstrtructorDefinition
    "a :+ b"
    (InfixDataConstr ":+" LEFTASSOC 9 (TypVar "a") (TypVar "b"))

  test "infixConstructor2" infixDataConstrtructorDefinition
    "a :::::: b"
    (InfixDataConstr "::::::" LEFTASSOC 9 (TypVar "a") (TypVar "b"))

testDataConstrtructorDefinition :: Test Unit
testDataConstrtructorDefinition = do
  test "nil" dataConstructorDefinition
    "Nil"
    (PrefixDataConstr "Nil" 0 Nil)

  test "cons" dataConstructorDefinition
    "Cons a b"
    (PrefixDataConstr "Cons" 2
      (toList
        [ TypVar "a"
        , TypVar "b"]))


testInfixConstructor :: Test Unit
testInfixConstructor = do
  test "infixConstructor1" infixConstructor
    ":+"
    ":+"

  test "infixConstructor2" infixConstructor
    ":@"
    ":@"

  test "infixConstructor3" infixConstructor
    ":<>=?"
    ":<>=?"

  test "infixConstructor4" infixConstructor
    ":-"
    ":-"

  rejectTests "invalidInfixConstructors" infixConstructor
    [ ":_"
    , "_:_"
    , ".:"
    , "."
    , "+"
    , ":a"
    , "_"
    , "__"
    , "_:::_" ]
