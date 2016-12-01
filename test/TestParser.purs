module Test.Parser where

import Prelude (class Eq, class Show, Unit, (<>), ($), bind, show, unit, pure, (==), (<<<), negate)
import Data.Either (Either(..))
import Data.List (List(..), singleton)
import Data.Array (toUnfoldable) as Array
import Data.Tuple (Tuple(..))
import Data.Maybe (Maybe(..))

import Text.Parsing.Parser (parseErrorPosition, parseErrorMessage)

import Control.Monad.Writer (Writer, tell)

import AST (Atom(..), Binding(..), Definition(Def), Expr(..), Op(..), Qual(..))
import Parser (expression, atom, definitions, definition, binding, variable, bool, int, runParserIndent)
import IndentParser (IndentParser)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: forall a. a -> Writer (List a) Unit
tell' = tell <<< singleton

test :: forall a. (Show a, Eq a) => String -> IndentParser String a -> String -> a -> Writer (List String) Unit
test name p input expected = case runParserIndent p input of
  Left parseError -> tell' $ "Parse fail (" <> name <> "): " <> show (parseErrorPosition parseError) <> " " <> parseErrorMessage parseError
  Right result           -> 
    if result == expected
      then pure unit --tell $ "Parse success (" <> name <> ")"
      else tell' $ "Parse fail (" <> name <> "): " <> show result <> " /= " <> show expected

aint :: Int -> Expr
aint = Atom <<< AInt

abool :: Boolean -> Expr
abool = Atom <<< Bool

aname :: String -> Expr
aname = Atom <<< Name

runTests :: Writer (List String) Unit
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

  test "composition" expression "f . g" (Binary Composition (aname "f") (aname "g"))
  test "power" expression "2 ^ 10" (Binary Power (aint 2) (aint 10))
  test "mul" expression "2 * 2" (Binary Mul (aint 2) (aint 2))
  test "div" expression "13 `div` 3" (Binary (InfixFunc "div") (aint 13) (aint 3))
  test "mod" expression "13 `mod` 3" (Binary (InfixFunc "mod") (aint 13) (aint 3))
  test "add1" expression "1 + 1"  (Binary Add (aint 1) (aint 1))
  test "add2" expression "2+2" (Binary Add (aint 2) (aint 2))
  test "sub" expression "5 - 3" (Binary Sub (aint 5) (aint 3))
  test "colon" expression "x:xs" (Binary Colon (aname "x") (aname "xs"))
  test "append1" expression "xs ++ ys" (Binary Append (aname "xs") (aname "ys"))
  test "append2" expression "xs++ys"  (Binary Append (aname "xs") (aname "ys"))
  test "equ" expression "5 == 5" (Binary Equ (aint 5) (aint 5))
  test "neq" expression "1 /= 2" (Binary Neq (aint 1) (aint 2))
  test "lt1" expression "1 < 234" (Binary Lt (aint 1) (aint 234))
  test "lt2" expression "x<y" (Binary Lt (aname "x") (aname "y"))
  test "leq" expression "1 <= 234" (Binary Leq (aint 1) (aint 234))
  test "gt1" expression "567 > 1" (Binary Gt (aint 567) (aint 1))
  test "gt2" expression "x>y" (Binary Gt (aname "x") (aname "y"))
  test "geq" expression "567 >= 1" (Binary Geq (aint 567) (aint 1))
  test "and" expression "hot && cold" (Binary And (aname "hot") (aname "cold"))
  test "or" expression "be || notBe" (Binary Or (aname "be") (aname "notBe"))
  test "dollar" expression "f $ 1 + 2"  (Binary Dollar (aname "f") (Binary Add (aint 1) (aint 2)))

  test "unary_minus1" expression "- 10"  (aint (-10))
  test "unary_minus2" expression "- x"  (Unary Sub (aname "x"))
  test "unary_minus3" expression "-10"  (aint (-10))
  test "unary_minus4" expression "-x"  (Unary Sub (aname "x"))

  test "infix_operator1" expression "1 `max` 3" (Binary (InfixFunc "max") (aint 1) (aint 3))
  test "infix_operator2" expression "5 `max` 2 `min` 1" (Binary (InfixFunc "min") (Binary (InfixFunc "max") (aint 5) (aint 2)) (aint 1))
  test "infix_operator3" expression "True`tight`False" (Binary (InfixFunc "tight") (abool true) (abool false))

  test "1" expression "1" (aint 1)
  test "add" expression "1 + 2" (Binary Add (aint 1) (aint 2))
  test "precedence" expression "1 * 2 + 3 * 4" (Binary Add 
                                    (Binary Mul (aint 1) (aint 2))
                                    (Binary Mul (aint 3) (aint 4)))
  test "whitespaces" expression 
    "1   \t   -    \t   ( f   )    \t\t\t\t                                                                \t\t\t\t             `div`     _ignore"
    (Binary Sub (aint 1) (Binary (InfixFunc "div") (aname "f") (aname "_ignore")))
  test "brackets" expression "(  1  +  2  )  *  3" (Binary Mul (Binary Add (aint 1) (aint 2)) (aint 3))
  test "brackets2" expression "( (  1  +  2  - 3  )  *  4 * 5 * 6)"
    (Binary Mul 
      (Binary Mul
        (Binary Mul
          (Binary Sub 
            (Binary Add (aint 1) (aint 2))
            (aint 3))
          (aint 4))
        (aint 5))
      (aint 6))
  test "brackets3" expression "( ( ( 1 ) ) )" (aint 1)
  test "many brackets" expression "(   (( ((  f )) *  ( (17   )) ) ))" (Binary Mul (aname "f") (aint 17))

  test "if_then_else" expression "if x then y else z" (IfExpr (aname "x") (aname "y") (aname "z"))
  test "nested if" expression "if(if 1 then 2 else 3)then y else z" (IfExpr (IfExpr (aint 1) (aint 2) (aint 3)) (aname "y") (aname "z"))
  test "iffy1" expression "iffy" (aname "iffy")
  test "iffy2" expression "if 10 + 20 then iffy * iffy else ((7))"
    (IfExpr 
      (Binary Add (aint 10) (aint 20))
      (Binary Mul (aname "iffy") (aname "iffy"))
      (aint 7))
  test "iffy3" expression "iffy + if iffy then iffy else iffy"
    (Binary Add (aname "iffy") (IfExpr (aname "iffy") (aname "iffy") (aname "iffy")))
  test "nested if 2" expression "if if x then y else z then if a then b else c else if i then j else k"
    (IfExpr
      (IfExpr (aname "x") (aname "y") (aname "z"))
      (IfExpr (aname "a") (aname "b") (aname "c"))
      (IfExpr (aname "i") (aname "j") (aname "k")))
  test "if2" expression "if bool then False else True" (IfExpr (aname "bool") (Atom (Bool false)) (Atom (Bool true)))

  test "apply1" expression "f 1" (App (aname "f") (singleton (aint 1)))
  test "apply2" expression "f x y z 12 (3 + 7)"
    (App (aname "f") (toList [aname "x", aname "y", aname "z", aint 12, Binary Add (aint 3) (aint 7)]))
  test "fibonacci" expression "fib (n - 1) + fib (n - 2)"
    (Binary Add
      (App (aname "fib") (toList [Binary Sub (aname "n") (aint 1)]))
      (App (aname "fib") (toList [Binary Sub (aname "n") (aint 2)])))
  test "predicate" expression "if p 10 then 10 else 20"
    (IfExpr
      (App (aname "p") (singleton (aint 10)))
      (aint 10)
      (aint 20))
  test "stuff" expression "f a (1 * 2) * 3"
    (Binary Mul
      (App (aname "f") (toList [aname "a", Binary Mul (aint 1) (aint 2)]))
      (aint 3))

  test "tuple" expression "(1, 2)" (NTuple (toList [aint 1, aint 2]))
  test "3tuple" expression "(1, 2, 3)" (NTuple (toList [aint 1, aint 2, aint 3]))
  test "4tuple" expression "(1, 2, 3, 4)" (NTuple (toList [aint 1, aint 2, aint 3, aint 4]))
  test "tuple_spaces" expression "(   1   , 2   )" (NTuple (toList [aint 1, aint 2]))
  test "3tuple_spaces" expression "(  1   , 2    , 3     )" (NTuple (toList [aint 1, aint 2, aint 3]))
  test "tuple_arith" expression "((1 + 2, (3)))" (NTuple (toList [Binary Add (aint 1) (aint 2), aint 3]))
  test "tuple_apply" expression "fmap f (snd (1,2), fst ( 1 , 2 ))"
    (App (aname "fmap") (toList
      [ (aname "f")
      , NTuple (toList
        [ App (aname "snd") (toList [NTuple (toList [aint 1, aint 2])])
        , App (aname "fst") (toList [NTuple (toList [aint 1, aint 2])])
        ])
      ]
    ))
  test "tuple_deep" expression "((((( ((((((1)),((2))),(3,((((4)))))),((5,6),(7,8))),(((9,(10)),(((11,12)))),((((13,14),(14,15)))))) )))))"
    (NTuple (Cons 
      (NTuple (Cons 
        (NTuple (Cons 
          (NTuple (Cons (Atom (AInt 1)) (Cons (Atom (AInt 2)) (Nil))))
          (Cons (NTuple (Cons (Atom (AInt 3)) (Cons (Atom (AInt 4)) (Nil)))) (Nil))))
        (Cons (NTuple
          (Cons (NTuple (Cons (Atom (AInt 5)) (Cons (Atom (AInt 6)) (Nil))))
            (Cons (NTuple (Cons (Atom (AInt 7)) (Cons (Atom (AInt 8)) (Nil)))) (Nil)))) (Nil))))
      (Cons (NTuple (Cons (NTuple (Cons (NTuple (Cons (Atom (AInt 9)) (Cons (Atom (AInt 10)) (Nil))))
        (Cons (NTuple (Cons (Atom (AInt 11)) (Cons (Atom (AInt 12)) (Nil)))) (Nil))))
      (Cons (NTuple (Cons (NTuple (Cons (Atom (AInt 13)) (Cons (Atom (AInt 14)) (Nil))))
        (Cons (NTuple (Cons (Atom (AInt 14)) (Cons (Atom (AInt 15)) (Nil)))) (Nil)))) (Nil)))) (Nil))))

  test "list_empty" expression "[]" (List Nil)
  test "list1" expression "[1]" (List (toList [aint 1]))
  test "list2" expression "[  1  ]" (List (toList [aint 1]))
  test "list3" expression "[  1  ,2,3,     4    ,  5  ]" (List (toList [aint 1, aint 2, aint 3, aint 4, aint 5]))
  test "list_nested" expression "[ [1,2] , [ 3 , 4 ] ]" (List $ toList [(List $ toList [aint 1, aint 2]), (List $ toList [aint 3, aint 4])])
  test "list_complex" expression "[ 1 + 2 , 3 + 4 ] ++ []"
    (Binary Append 
      (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4)])
      (List Nil))

  test "binding_lit1" binding "x" (Lit (Name "x"))
  test "binding_lit2" binding "10" (Lit (AInt 10))
  test "lambda1" expression "(\\x -> x)" (Lambda (toList [Lit (Name "x")]) (aname "x"))
  test "lambda2" expression "( \\ x y z -> ( x , y , z ) )"
    (Lambda (toList [Lit (Name "x"), Lit (Name "y"), Lit (Name "z")])
      (NTuple (toList [aname "x", aname "y", aname "z"])))
  test "lambda3" expression "(  \\  x ->   (   \\    y ->    (   \\    z ->     f   x   y   z )  )  )"
    (Lambda (singleton $ Lit $ Name "x")
      (Lambda (singleton $ Lit $ Name "y")
        (Lambda (singleton $ Lit $ Name "z")
          (App (aname "f") (toList [aname "x", aname "y", aname "z"])))))
  test "lambda4" expression "(\\a b -> a + b) 1 2"
    (App 
      (Lambda (toList [Lit (Name "a"), Lit (Name "b")])
        (Binary Add (aname "a") (aname "b")))
      (toList [aint 1, aint 2]))

  test "lambda5" expression "(\\a -> (\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> a + b + c + d + e + f + g))))))) 1 2 3 4 5 6 7"
    (App 
      (Lambda (Cons (Lit (Name "a")) (Nil)) 
        (Lambda (Cons (Lit (Name "b")) (Nil))
          (Lambda (Cons (Lit (Name "c")) (Nil))
            (Lambda (Cons (Lit (Name "d")) (Nil))
              (Lambda (Cons (Lit (Name "e")) (Nil))
                (Lambda (Cons (Lit (Name "f")) (Nil))
                  (Lambda (Cons (Lit (Name "g")) (Nil))
                    (Binary Add
                      (Binary Add
                        (Binary Add
                          (Binary Add
                            (Binary Add
                              (Binary Add (Atom (Name "a")) (Atom (Name "b")))
                              (Atom (Name "c")))
                            (Atom (Name "d")))
                          (Atom (Name "e")))
                        (Atom (Name "f")))
                      (Atom (Name "g"))))))))))
      (Cons (Atom (AInt 1)) (Cons (Atom (AInt 2)) (Cons (Atom (AInt 3)) (Cons (Atom (AInt 4)) (Cons (Atom (AInt 5)) (Cons (Atom (AInt 6)) (Cons (Atom (AInt 7)) (Nil)))))))))

  test "lambda6" expression "\\x -> x + 2"
      (Lambda
        (toList [Lit (Name "x")])
        (Binary Add (aname "x") (aint 2)))

  test "lambda7" definition "f a = \\b -> a + b"
    (Def "f"
      (toList [Lit (Name "a")])
      (Lambda
        (toList [Lit (Name "b")])
        (Binary Add (aname "a") (aname "b"))))

  test "sectR1" expression "(+1)" (SectR Add (aint 1))
  test "sectR2" expression "( ^ 2 )" (SectR Power (aint 2))
  test "sectR3" expression "(++ [1])" (SectR Append (List (toList [aint 1])))
  test "sectR4" expression "(<= (2 + 2))" (SectR Leq (Binary Add (aint 2) (aint 2)))
  test "sectR5" expression "(   >=  (  2 + 2  )  )" (SectR Geq (Binary Add (aint 2) (aint 2)))

  test "prefixOp1" expression "(+)" (PrefixOp Add)
  test "prefixOp2" expression "( ++ )" (PrefixOp Append)
  test "prefixOp3" expression "((^) 2 10)" (App (PrefixOp Power) (toList [aint 2, aint 10]))

  test "sectL1" expression "(1+)" (SectL (aint 1) Add)
  test "sectL2" expression "( n `mod` )" (SectL (aname "n") (InfixFunc "mod"))
  test "sectL3" expression "([1] ++)" (SectL (List $ toList [aint 1]) Append)
  test "sectL4" expression "(   ( 2 +  2 )  <= )" (SectL (Binary Add (aint 2) (aint 2)) Leq)

  test "let1" expression "let x = 1 in x + x" (LetExpr (Cons (Tuple (Lit (Name "x")) (aint 1)) Nil) (Binary Add (aname "x") (aname "x")))
  test "let2" expression "letty + let x = 1 in x" (Binary Add (aname "letty") (LetExpr (Cons (Tuple (Lit (Name "x")) (aint 1)) Nil) (aname "x")))
  test "let3" expression "let x = let y = 1 in y in let z = 2 in x + z" (LetExpr (Cons (Tuple (Lit (Name "x")) (LetExpr (Cons (Tuple (Lit (Name "y")) (Atom (AInt 1))) (Nil)) (Atom (Name "y")))) (Nil)) (LetExpr (Cons (Tuple (Lit (Name "z")) (Atom (AInt 2))) (Nil)) (Binary Add (Atom (Name "x")) (Atom (Name "z")))))
  test "let4" expression "let { x = 1; y = 2; z = 3} in x + y + z"              (LetExpr (Cons (Tuple (Lit (Name "x")) (Atom (AInt 1))) (Cons (Tuple (Lit (Name "y")) (Atom (AInt 2))) (Cons (Tuple (Lit (Name "z")) (Atom (AInt 3))) (Nil)))) (Binary Add (Binary Add (Atom (Name "x")) (Atom (Name "y"))) (Atom (Name "z"))))
  test "let5" expression "let x = 1; y = 2; z = 3 in x + y + z"                 (LetExpr (Cons (Tuple (Lit (Name "x")) (Atom (AInt 1))) (Cons (Tuple (Lit (Name "y")) (Atom (AInt 2))) (Cons (Tuple (Lit (Name "z")) (Atom (AInt 3))) (Nil)))) (Binary Add (Binary Add (Atom (Name "x")) (Atom (Name "y"))) (Atom (Name "z"))))
  test "let6" expression "let x = 1\n    y = 2\n    z = 3 in x + y + z"         (LetExpr (Cons (Tuple (Lit (Name "x")) (Atom (AInt 1))) (Cons (Tuple (Lit (Name "y")) (Atom (AInt 2))) (Cons (Tuple (Lit (Name "z")) (Atom (AInt 3))) (Nil)))) (Binary Add (Binary Add (Atom (Name "x")) (Atom (Name "y"))) (Atom (Name "z"))))
  test "let7" expression "let {\n  x = 1 ;\n  y = 2 ;\n  z = 3\n} in x + y + z" (LetExpr (Cons (Tuple (Lit (Name "x")) (Atom (AInt 1))) (Cons (Tuple (Lit (Name "y")) (Atom (AInt 2))) (Cons (Tuple (Lit (Name "z")) (Atom (AInt 3))) (Nil)))) (Binary Add (Binary Add (Atom (Name "x")) (Atom (Name "y"))) (Atom (Name "z"))))

  test "consLit1" binding "(x:xs)" (ConsLit (Lit (Name "x")) (Lit (Name "xs")))
  test "consLit2" binding "(x:(y:zs))" (ConsLit (Lit (Name "x")) (ConsLit (Lit (Name "y")) (Lit (Name "zs"))))
  test "consLit3" binding "(  x  :  (  666  :  zs  )   )" (ConsLit (Lit (Name "x")) (ConsLit (Lit (AInt 666)) (Lit (Name "zs"))))

  test "listLit1" binding "[]" (ListLit Nil)
  test "listLit2" binding "[    ]" (ListLit Nil)
  test "listLit3" binding "[  True ]" (ListLit (Cons (Lit (Bool true)) Nil))
  test "listLit4" binding "[  x   ,  y  ,   1337 ]" (ListLit (toList [Lit (Name "x"), Lit (Name "y"), Lit (AInt 1337)]))

  test "tupleLit1" binding "(a,b)" (NTupleLit (toList [Lit (Name "a"), Lit (Name "b")]))
  test "tupleLit2" binding "(   a   ,  b   ,   c   )" (NTupleLit (toList $ [Lit (Name "a"), Lit (Name "b"), Lit (Name "c")]))
  test "tupleLit3" binding "(  (  x  ,  y  )  , ( a  ,  b  )  , 10 )"
    (NTupleLit (toList
      [ NTupleLit (toList [Lit (Name "x"), Lit (Name "y")])
      , NTupleLit (toList [Lit (Name "a"), Lit (Name "b")])
      , (Lit (AInt 10))
      ]))

  test "binding" binding "( ( x , y ) : [ a , b ] )"
    (ConsLit
      (NTupleLit (toList [Lit (Name "x"), Lit (Name "y")]))
      (ListLit (toList [Lit (Name "a"), Lit (Name "b")])))

  test "def1" definition "x = 10" (Def "x" Nil (aint 10))
  test "def2" definition "double x = x + x" (Def "double" (Cons (Lit (Name "x")) Nil) (Binary Add (aname "x") (aname "x")))
  test "def3" definition "zip (x:xs) (y:ys) = (x,y) : zip xs ys"
    (Def "zip"
      (toList [ConsLit (Lit (Name "x")) (Lit (Name "xs")), ConsLit (Lit (Name "y")) (Lit (Name "ys"))])
      (Binary Colon
        (NTuple (toList  [Atom (Name "x"), Atom (Name "y")]))
        (App (aname "zip") (toList [Atom (Name "xs"), Atom (Name "ys")]))))

  test "defs" definitions "\n\na   =   10 \n  \n \nb    =  20  \n\n  \n"
    (toList [Def "a" Nil (aint 10), Def "b" Nil (aint 20)])

  test "prelude" definitions prelude parsedPrelude
  test "expression" expression "sum (map (^2) [1, 2, 3, 4])"
    (App 
      (Atom (Name "sum"))
      (Cons 
        (App 
          (Atom (Name "map"))
          (Cons (SectR Power (Atom (AInt 2)))
            (Cons (List (Cons (Atom (AInt 1)) (Cons (Atom (AInt 2)) (Cons (Atom (AInt 3)) (Cons (Atom (AInt 4)) (Nil))))))
              (Nil))))
        (Nil)))

  test "char_atom1" atom "'a'" (Char "a")
  test "char_atom2" atom "'\\\\'" (Char "\\")
  test "char_atom3" atom "'\\n'" (Char "\n")
  test "char_expr1" expression "'\\r'" (Atom (Char "\r"))
  test "char_expr2" expression "['\\\\', '\\'', '\\\"']" (List $ toList [Atom (Char "\\"), Atom (Char "'"), Atom (Char "\"")])

  test "string1" expression "\"asdf\"" (List $ toList [Atom (Char "a"), Atom (Char "s"), Atom (Char "d"), Atom (Char "f")])
  test "string2" expression "\"\\\\\\n\\\"\\\'\"" (List $ toList [Atom (Char "\\"), Atom (Char "\n"), Atom (Char "\""), Atom (Char "'")])

  test "listComp1" expression "[ x | x <- [1,2,3] ]" $ ListComp (Atom (Name "x")) (toList [Gen (Lit (Name "x")) (List (toList [Atom (AInt 1), Atom (AInt 2), Atom (AInt 3)]))])
  test "listComp2" expression "[ b + c | let b = 3, c <- [1 .. ]]" $ ListComp (Binary Add (Atom (Name "b")) (Atom (Name ("c")))) $ toList [Let (Lit (Name "b")) (Atom (AInt 3)),
    Gen (Lit (Name "c")) (ArithmSeq (Atom (AInt 1)) Nothing Nothing)]
  test "listComp3" expression "[a*b|let a=5,let b=a+1]" $ ListComp (Binary Mul (Atom (Name "a")) (Atom (Name "b"))) $ toList [Let (Lit (Name "a")) (Atom (AInt 5)),
    Let (Lit (Name "b")) (Binary Add (Atom (Name "a")) (Atom (AInt 1)))]

prelude :: String
prelude =
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
  (Def "and" (Cons (ConsLit (Lit (Bool true)) (Lit (Name "xs"))) (Nil)) (App (Atom (Name "and")) (Cons (Atom (Name "xs")) (Nil)))),
  (Def "and" (Cons (ConsLit (Lit (Bool false)) (Lit (Name "xs"))) (Nil)) (Atom (Bool false))),
  (Def "and" (Cons (ListLit (Nil)) (Nil)) (Atom (Bool true))),
  (Def "or" (Cons (ConsLit (Lit (Bool false)) (Lit (Name "xs"))) (Nil)) (App (Atom (Name "or")) (Cons (Atom (Name "xs")) (Nil)))),
  (Def "or" (Cons (ConsLit (Lit (Bool true)) (Lit (Name "xs"))) (Nil)) (Atom (Bool true))),
  (Def "or" (Cons (ListLit (Nil)) (Nil)) (Atom (Bool false))),
  (Def "all" (Cons (Lit (Name "p")) (Nil)) (Binary Composition (Atom (Name "and")) (App (Atom (Name "map")) (Cons (Atom (Name "p")) (Nil))))),
  (Def "any" (Cons (Lit (Name "p")) (Nil)) (Binary Composition (Atom (Name "or")) (App (Atom (Name "map")) (Cons (Atom (Name "p")) (Nil))))),
  (Def "head" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Atom (Name "x"))),
  (Def "tail" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Atom (Name "xs"))),
  (Def "take" (Cons (Lit (AInt 0)) (Cons (Lit (Name "xs")) (Nil))) (List (Nil))),
  (Def "take" (Cons (Lit (Name "n")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (Binary Colon (Atom (Name "x")) (App (Atom (Name "take")) (Cons (Binary Sub (Atom (Name "n")) (Atom (AInt 1))) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "drop" (Cons (Lit (AInt 0)) (Cons (Lit (Name "xs")) (Nil))) (Atom (Name "xs"))),
  (Def "drop" (Cons (Lit (Name "n")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (App (Atom (Name "drop")) (Cons (Binary Sub (Atom (Name "n")) (Atom (AInt 1))) (Cons (Atom (Name "xs")) (Nil))))),
  (Def "elem" (Cons (Lit (Name "e")) (Cons (ListLit (Nil)) (Nil))) (Atom (Bool false))),
  (Def "elem" (Cons (Lit (Name "e")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (IfExpr (Binary Equ (Atom (Name "e")) (Atom (Name "x"))) (Atom (Bool true)) (App (Atom (Name "elem")) (Cons (Atom (Name "e")) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "max" (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil))) (IfExpr (Binary Geq (Atom (Name "a")) (Atom (Name "b"))) (Atom (Name "a")) (Atom (Name "b")))),
  (Def "min" (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil))) (IfExpr (Binary Geq (Atom (Name "b")) (Atom (Name "a"))) (Atom (Name "a")) (Atom (Name "b")))),
  (Def "maximum" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (App (Atom (Name "foldr")) (Cons (Atom (Name "max")) (Cons (Atom (Name "x")) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "minimum" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (App (Atom (Name "foldr")) (Cons (Atom (Name "min")) (Cons (Atom (Name "x")) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "length" (Cons (ListLit (Nil)) (Nil)) (Atom (AInt 0))),
  (Def "length" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary Add (Atom (AInt 1)) (App (Atom (Name "length")) (Cons (Atom (Name "xs")) (Nil))))),
  (Def "zip" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Cons (ConsLit (Lit (Name "y")) (Lit (Name "ys"))) (Nil))) (Binary Colon (NTuple (Cons (Atom (Name "x")) (Cons (Atom (Name "y")) (Nil)))) (App (Atom (Name "zip")) (Cons (Atom (Name "xs")) (Cons (Atom (Name "ys")) (Nil)))))),
  (Def "zip" (Cons (ListLit (Nil)) (Cons (Lit (Name "_")) (Nil))) (List (Nil))),
  (Def "zip" (Cons (Lit (Name "_")) (Cons (ListLit (Nil)) (Nil))) (List (Nil))),
  (Def "zipWith" (Cons (Lit (Name "f")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Cons (ConsLit (Lit (Name "y")) (Lit (Name "ys"))) (Nil)))) (Binary Colon (App (Atom (Name "f")) (Cons (Atom (Name "x")) (Cons (Atom (Name "y")) (Nil)))) (App (Atom (Name "zipWith")) (Cons (Atom (Name "f")) (Cons (Atom (Name "xs")) (Cons (Atom (Name "ys")) (Nil))))))),
  (Def "zipWith" (Cons (Lit (Name "_")) (Cons (ListLit (Nil)) (Cons (Lit (Name "_")) (Nil)))) (List (Nil))),
  (Def "zipWith" (Cons (Lit (Name "_")) (Cons (Lit (Name "_")) (Cons (ListLit (Nil)) (Nil)))) (List (Nil))),
  (Def "unzip" (Cons (ListLit (Nil)) (Nil)) (NTuple (Cons (List (Nil)) (Cons (List (Nil)) (Nil))))),
  (Def "unzip" (Cons (ConsLit (NTupleLit (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (Lit (Name "xs"))) (Nil)) (Binary Dollar (Lambda (Cons (NTupleLit (Cons (Lit (Name "as")) (Cons (Lit (Name "bs")) (Nil)))) (Nil)) (NTuple (Cons (Binary Colon (Atom (Name "a")) (Atom (Name "as"))) (Cons (Binary Colon (Atom (Name "b")) (Atom (Name "bs"))) (Nil))))) (App (aname "unzip") (Cons (aname "xs") Nil)))),
  (Def "fst" (Cons (NTupleLit (Cons (Lit (Name "x")) (Cons (Lit (Name "_")) (Nil)))) Nil) (Atom (Name "x"))),
  (Def "snd" (Cons (NTupleLit (Cons (Lit (Name "_")) (Cons (Lit (Name "x")) (Nil)))) Nil) (Atom (Name "x"))),
  (Def "curry" (Cons (Lit (Name "f")) (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (App (Atom (Name "f")) (Cons (NTuple (Cons (Atom (Name "a")) (Cons (Atom (Name "b")) (Nil)))) (Nil)))),
  (Def "uncurry" (Cons (Lit (Name "f")) (Cons (NTupleLit (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (Nil))) (App (Atom (Name "f")) (Cons (Atom (Name "a")) (Cons (Atom (Name "b")) (Nil))))),
  (Def "repeat" (Cons (Lit (Name "x")) (Nil)) (Binary Colon (Atom (Name "x")) (App (Atom (Name "repeat")) (Cons (Atom (Name "x")) (Nil))))),
  (Def "replicate" (Cons (Lit (AInt 0)) (Cons (Lit (Name "_")) (Nil))) (List (Nil))),
  (Def "replicate" (Cons (Lit (Name "n")) (Cons (Lit (Name "x")) (Nil))) (Binary Colon (Atom (Name "x")) (App (Atom (Name "replicate")) (Cons (Binary Sub (Atom (Name "n")) (Atom (AInt 1))) (Cons (Atom (Name "x")) (Nil)))))),
  (Def "enumFromTo" (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil))) (IfExpr (Binary Leq (Atom (Name "a")) (Atom (Name "b"))) (Binary Colon (Atom (Name "a")) (App (Atom (Name "enumFromTo")) (Cons (Binary Add (Atom (Name "a")) (Atom (AInt 1))) (Cons (Atom (Name "b")) (Nil))))) (List (Nil)))),
  (Def "sum" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary Add (Atom (Name "x")) (App (Atom (Name "sum")) (Cons (Atom (Name "xs")) (Nil))))),
  (Def "sum" (Cons (ListLit (Nil)) (Nil)) (Atom (AInt 0))),
  (Def "product" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary Mul (Atom (Name "x")) (App (Atom (Name "product")) (Cons (Atom (Name "xs")) (Nil))))),
  (Def "product" (Cons (ListLit (Nil)) (Nil)) (Atom (AInt 1))),
  (Def "reverse" (Cons (ListLit (Nil)) (Nil)) (List (Nil))),
  (Def "reverse" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary Append (App (Atom (Name "reverse")) (Cons (Atom (Name "xs")) (Nil))) (List (Cons (Atom (Name "x")) (Nil))))),
  (Def "concat" (Nil) (App (Atom (Name "foldr")) (Cons (PrefixOp Append) (Cons (List (Nil)) (Nil))))),
  (Def "map" (Cons (Lit (Name "f")) (Cons (ListLit (Nil)) (Nil))) (List (Nil))),
  (Def "map" (Cons (Lit (Name "f")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (Binary Colon (App (Atom (Name "f")) (Cons (Atom (Name "x")) (Nil))) (App (Atom (Name "map")) (Cons (Atom (Name "f")) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "not" (Cons (Lit (Bool true)) (Nil)) (Atom (Bool false))),
  (Def "not" (Cons (Lit (Bool false)) (Nil)) (Atom (Bool true))),
  (Def "filter" (Cons (Lit (Name "p")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (IfExpr (App (Atom (Name "p")) (Cons (Atom (Name "x")) (Nil))) (Binary Colon (Atom (Name "x")) (App (Atom (Name "filter")) (Cons (Atom (Name "p")) (Cons (Atom (Name "xs")) (Nil))))) (App (Atom (Name "filter")) (Cons (Atom (Name "p")) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "filter" (Cons (Lit (Name "p")) (Cons (ListLit (Nil)) (Nil))) (List (Nil))),
  (Def "foldr" (Cons (Lit (Name "f")) (Cons (Lit (Name "ini")) (Cons (ListLit (Nil)) (Nil)))) (Atom (Name "ini"))),
  (Def "foldr" (Cons (Lit (Name "f")) (Cons (Lit (Name "ini")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (App (Atom (Name "f")) (Cons (Atom (Name "x")) (Cons (App (Atom (Name "foldr")) (Cons (Atom (Name "f")) (Cons (Atom (Name "ini")) (Cons (Atom (Name "xs")) (Nil))))) (Nil))))),
  (Def "foldl" (Cons (Lit (Name "f")) (Cons (Lit (Name "acc")) (Cons (ListLit (Nil)) (Nil)))) (Atom (Name "acc"))),
  (Def "foldl" (Cons (Lit (Name "f")) (Cons (Lit (Name "acc")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (App (Atom (Name "foldl")) (Cons (Atom (Name "f")) (Cons (App (Atom (Name "f")) (Cons (Atom (Name "acc")) (Cons (Atom (Name "x")) (Nil)))) (Cons (Atom (Name "xs")) (Nil)))))),
  (Def "scanl" (Cons (Lit (Name "f")) (Cons (Lit (Name "b")) (Cons (ListLit (Nil)) (Nil)))) (List (Cons (Atom (Name "b")) (Nil)))),
  (Def "scanl" (Cons (Lit (Name "f")) (Cons (Lit (Name "b")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (Binary Colon (Atom (Name "b")) (App (Atom (Name "scanl")) (Cons (Atom (Name "f")) (Cons (App (Atom (Name "f")) (Cons (Atom (Name "b")) (Cons (Atom (Name "x")) (Nil)))) (Cons (Atom (Name "xs")) (Nil))))))),
  (Def "iterate" (Cons (Lit (Name "f")) (Cons (Lit (Name "x")) (Nil))) (Binary Colon (Atom (Name "x")) (App (Atom (Name "iterate")) (Cons (Atom (Name "f")) (Cons (App (Atom (Name "f")) (Cons (Atom (Name "x")) (Nil))) (Nil)))))),
  (Def "id" (Cons (Lit (Name "x")) (Nil)) (Atom (Name "x"))),
  (Def "const" (Cons (Lit (Name "x")) (Cons (Lit (Name "_")) (Nil))) (Atom (Name "x"))),
  (Def "flip" (Cons (Lit (Name "f")) (Cons (Lit (Name "x")) (Cons (Lit (Name "y")) (Nil)))) (App (Atom (Name "f")) (Cons (Atom (Name "y")) (Cons (Atom (Name "x")) (Nil))))),
  (Def "even" (Cons (Lit (Name "n")) (Nil)) (Binary Equ (Binary (InfixFunc "mod") (Atom (Name "n")) (Atom (AInt 2))) (Atom (AInt 0)))),
  (Def "odd" (Cons (Lit (Name "n")) (Nil)) (Binary Equ (Binary (InfixFunc "mod") (Atom (Name "n")) (Atom (AInt 2))) (Atom (AInt 1)))),
  (Def "fix" (Cons (Lit (Name "f")) (Nil)) (App (Atom (Name "f")) (Cons (App (Atom (Name "fix")) (Cons (Atom (Name "f")) (Nil))) (Nil))))
  ]
