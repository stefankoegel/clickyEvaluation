module Test.Main where

import AST
import Parser

import Prelude
import Data.Either
import Data.List

import Text.Parsing.StringParser

import Control.Monad.Eff
import Control.Monad.Eff.Console

test :: forall a eff. (Show a, Eq a) => String -> Parser a -> String -> a -> Eff (console :: CONSOLE | eff ) Unit
test name p input expected = case runParser p input of
  Left  (ParseError err) -> print $ "Fail (" ++ name ++ "): " ++ err
  Right result           -> 
    if result == expected
      then print $ "Succes (" ++ name ++ ")"
      else print $ "Fail (" ++ name ++ "): " ++ show result ++ " /= " ++ show expected

aint :: Int -> Expr
aint i = Atom $ AInt i

aname :: String -> Expr
aname s = Atom $ Name s

main :: forall eff. Eff (console :: CONSOLE | eff) Unit
main = do
  print "Running tests:"

  test "0" int "0" (AInt 0)
  test "1" int "1" (AInt 1)
  test "all" int "0123456789" (AInt 123456789)
  test "high" int "999999999999999999" (AInt 2147483647)

  test "a" variable "a" (Name "a")
  test "lower" variable "a_bcdefghijklmnopqrstuvwxyz_" (Name "a_bcdefghijklmnopqrstuvwxyz_")
  test "upper" variable "a'BCDEFGHIJKLMNOPQRSTUVWXYZ'" (Name "a'BCDEFGHIJKLMNOPQRSTUVWXYZ'")
  test "special" variable "_____''''" (Name "_____''''")

  test "composition" expression "f . g" (Binary Composition (aname "f") (aname "g"))
  test "power" expression "2 ^ 10" (Binary Power (aint 2) (aint 10))
  test "mul" expression "2 * 2" (Binary Mul (aint 2) (aint 2))
  test "div" expression "13 `div` 3" (Binary Div (aint 13) (aint 3))
  test "mod" expression "13 `mod` 3" (Binary Mod (aint 13) (aint 3))
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

  test "1" expression "1" (aint 1)
  test "add" expression "1 + 2" (Binary Add (aint 1) (aint 2))
  test "precedence" expression "1 * 2 + 3 * 4" (Binary Add 
                                    (Binary Mul (aint 1) (aint 2))
                                    (Binary Mul (aint 3) (aint 4)))
  test "whitespaces" expression 
    "1   \n   -    \t   ( f   )    \t\t\t\t                                                                 \n\n\n             `div`     _ignore"
    (Binary Sub (aint 1) (Binary Div (aname "f") (aname "_ignore")))
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
  -- This test leads to a stack overflow. I don't know how to optimize it away...
  -- test "tuple_deep" expression "((((( ((((((1)),((2))),(3,((((4)))))),((5,6),(7,8))),(((9,(10)),(((11,12)))),((((13,14),(14,15)))))) )))))" (aname "stackOverflow")

  test "list_empty" expression "[]" (List Nil)
  test "list1" expression "[1]" (List (toList [aint 1]))
  test "list2" expression "[  1  ]" (List (toList [aint 1]))
  test "list3" expression "[  1  ,2,3,     4    ,  5  ]" (List (toList [aint 1, aint 2, aint 3, aint 4, aint 5]))
  test "list_nested" expression "[ [1,2] , [ 3 , 4 ] ]" (List $ toList [(List $ toList [aint 1, aint 2]), (List $ toList [aint 3, aint 4])])
  test "list_complex" expression "[ 1 + 2 , 3 + 4 ] ++ []"
    (Binary Append 
      (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4)])
      (List Nil))

  test "binding1" binding "x" (Lit (Name "x"))
  test "binding2" binding "10" (Lit (AInt 10))
  test "lambda1" expression "(\\x -> x)" (Lambda (toList [Lit (Name "x")]) (aname "x"))
  test "lambda2" expression "( \\ x y z -> ( x , y , z ) )"
    (Lambda (toList [Lit (Name "x"), Lit (Name "y"), Lit (Name "z")])
      (NTuple (toList [aname "x", aname "y", aname "z"])))
  test "lambda3" expression "(  \\  x ->   (   \\    y ->    (   \\    z ->     f   x   y   z )  )  )"
    (Lambda (singleton $ Lit $ Name "x")
      (Lambda (singleton $ Lit $ Name "y")
        (Lambda (singleton $ Lit $ Name "z")
          (App (aname "f") (toList [aname "x", aname "y", aname "z"])))))

  test "sectR1" expression "(+1)" (SectR Add (aint 1))
  test "sectR2" expression "( ^ 2 )" (SectR Power (aint 2))
  test "sectR3" expression "(++ [1])" (SectR Append (List (toList [aint 1])))
  test "sectR4" expression "(<= (2 + 2))" (SectR Leq (Binary Add (aint 2) (aint 2)))
  test "sectR5" expression "(   >=  (  2 + 2  )  )" (SectR Geq (Binary Add (aint 2) (aint 2)))

  test "prefixOp1" expression "(+)" (PrefixOp Add)
  test "prefixOp2" expression "( ++ )" (PrefixOp Append)
  test "prefixOp3" expression "((^) 2 10)" (App (PrefixOp Power) (toList [aint 2, aint 10]))

  test "sectL1" expression "(1+)" (SectL (aint 1) Add)
  test "sectL2" expression "( n `mod` )" (SectL (aname "n") Mod)
  test "sectL3" expression "([1] ++)" (SectL (List $ toList [aint 1]) Append)
  test "sectL4" expression "(   ( 2 +  2 )  <= )" (SectL (Binary Add (aint 2) (aint 2)) Leq)

  test "let1" expression "let x = 1 in x + x" (LetExpr (Lit (Name "x")) (aint 1) (Binary Add (aname "x") (aname "x")))
  test "let2" expression "letty + let x = 1 in x" (Binary Add (aname "letty") (LetExpr (Lit (Name "x")) (aint 1) (aname "x")))
  test "let3" expression "let x = let y = 1 in y in let z = 2 in x + z"
    (LetExpr
      (Lit (Name "x"))
      (LetExpr
        (Lit (Name "y"))
        (aint 1)
        (aname "y"))
      (LetExpr
        (Lit (Name "z"))
        (aint 2)
        (Binary Add (aname "x") (aname "z"))))

