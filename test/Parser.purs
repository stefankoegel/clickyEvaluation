module Test.Parser where

import Prelude
import Data.Either (Either(..))
import Data.List (List(..), toList, singleton)

import Text.Parsing.Parser  (Parser, ParseError(ParseError), runParser)

import Control.Monad.Writer (Writer, tell)

import AST (Expr, Tree(..), Atom(..), Binding(..), Definition(Def), Op(..))
import Parser (expression, atom, definitions, definition, binding, variable, bool, int)

tell' :: forall a. a -> Writer (List a) Unit
tell' = tell <<< singleton

test :: forall a. (Show a, Eq a) => String -> Parser String a -> String -> a -> Writer (List String) Unit
test name p input expected = case runParser input p of
  Left  (ParseError { position = p, message = m }) -> tell' $ "Parse fail (" ++ name ++ "): " ++ show p ++ " " ++ m
  Right result           -> 
    if result == expected
      then return unit --tell $ "Parse success (" ++ name ++ ")"
      else tell' $ "Parse fail (" ++ name ++ "): " ++ show result ++ " /= " ++ show expected

aint :: Int -> Expr
aint i = Atom unit $ AInt i

abool :: Boolean -> Expr
abool = Atom unit <<< Bool

aname :: String -> Expr
aname s = Atom unit $ Name s

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

  test "composition" expression "f . g" (Binary unit Composition (aname "f") (aname "g"))
  test "power" expression "2 ^ 10" (Binary unit Power (aint 2) (aint 10))
  test "mul" expression "2 * 2" (Binary unit Mul (aint 2) (aint 2))
  test "div" expression "13 `div` 3" (Binary unit (InfixFunc "div") (aint 13) (aint 3))
  test "mod" expression "13 `mod` 3" (Binary unit (InfixFunc "mod") (aint 13) (aint 3))
  test "add1" expression "1 + 1"  (Binary unit Add (aint 1) (aint 1))
  test "add2" expression "2+2" (Binary unit Add (aint 2) (aint 2))
  test "sub" expression "5 - 3" (Binary unit Sub (aint 5) (aint 3))
  test "colon" expression "x:xs" (Binary unit Colon (aname "x") (aname "xs"))
  test "append1" expression "xs ++ ys" (Binary unit Append (aname "xs") (aname "ys"))
  test "append2" expression "xs++ys"  (Binary unit Append (aname "xs") (aname "ys"))
  test "equ" expression "5 == 5" (Binary unit Equ (aint 5) (aint 5))
  test "neq" expression "1 /= 2" (Binary unit Neq (aint 1) (aint 2))
  test "lt1" expression "1 < 234" (Binary unit Lt (aint 1) (aint 234))
  test "lt2" expression "x<y" (Binary unit Lt (aname "x") (aname "y"))
  test "leq" expression "1 <= 234" (Binary unit Leq (aint 1) (aint 234))
  test "gt1" expression "567 > 1" (Binary unit Gt (aint 567) (aint 1))
  test "gt2" expression "x>y" (Binary unit Gt (aname "x") (aname "y"))
  test "geq" expression "567 >= 1" (Binary unit Geq (aint 567) (aint 1))
  test "and" expression "hot && cold" (Binary unit And (aname "hot") (aname "cold"))
  test "or" expression "be || notBe" (Binary unit Or (aname "be") (aname "notBe"))
  test "dollar" expression "f $ 1 + 2"  (Binary unit Dollar (aname "f") (Binary unit Add (aint 1) (aint 2)))

  test "unary_minus1" expression "- 10"  (aint (-10))
  test "unary_minus2" expression "- x"  (Unary unit Sub (aname "x"))
  test "unary_minus3" expression "-10"  (aint (-10))
  test "unary_minus4" expression "-x"  (Unary unit Sub (aname "x"))

  test "infix_operator1" expression "1 `max` 3" (Binary unit (InfixFunc "max") (aint 1) (aint 3))
  test "infix_operator2" expression "5 `max` 2 `min` 1" (Binary unit (InfixFunc "min") (Binary unit (InfixFunc "max") (aint 5) (aint 2)) (aint 1))
  test "infix_operator3" expression "True`tight`False" (Binary unit (InfixFunc "tight") (abool true) (abool false))

  test "1" expression "1" (aint 1)
  test "add" expression "1 + 2" (Binary unit Add (aint 1) (aint 2))
  test "precedence" expression "1 * 2 + 3 * 4" (Binary unit Add 
                                    (Binary unit Mul (aint 1) (aint 2))
                                    (Binary unit Mul (aint 3) (aint 4)))
  test "whitespaces" expression 
    "1   \t   -    \t   ( f   )    \t\t\t\t                                                                \t\t\t\t             `div`     _ignore"
    (Binary unit Sub (aint 1) (Binary unit (InfixFunc "div") (aname "f") (aname "_ignore")))
  test "brackets" expression "(  1  +  2  )  *  3" (Binary unit Mul (Binary unit Add (aint 1) (aint 2)) (aint 3))
  test "brackets2" expression "( (  1  +  2  - 3  )  *  4 * 5 * 6)"
    (Binary unit Mul 
      (Binary unit Mul
        (Binary unit Mul
          (Binary unit Sub 
            (Binary unit Add (aint 1) (aint 2))
            (aint 3))
          (aint 4))
        (aint 5))
      (aint 6))
  test "brackets3" expression "( ( ( 1 ) ) )" (aint 1)
  test "many brackets" expression "(   (( ((  f )) *  ( (17   )) ) ))" (Binary unit Mul (aname "f") (aint 17))

  test "if_then_else" expression "if x then y else z" (IfExpr unit (aname "x") (aname "y") (aname "z"))
  test "nested if" expression "if(if 1 then 2 else 3)then y else z" (IfExpr unit (IfExpr unit (aint 1) (aint 2) (aint 3)) (aname "y") (aname "z"))
  test "iffy1" expression "iffy" (aname "iffy")
  test "iffy2" expression "if 10 + 20 then iffy * iffy else ((7))"
    (IfExpr unit 
      (Binary unit Add (aint 10) (aint 20))
      (Binary unit Mul (aname "iffy") (aname "iffy"))
      (aint 7))
  test "iffy3" expression "iffy + if iffy then iffy else iffy"
    (Binary unit Add (aname "iffy") (IfExpr unit (aname "iffy") (aname "iffy") (aname "iffy")))
  test "nested if 2" expression "if if x then y else z then if a then b else c else if i then j else k"
    (IfExpr unit
      (IfExpr unit (aname "x") (aname "y") (aname "z"))
      (IfExpr unit (aname "a") (aname "b") (aname "c"))
      (IfExpr unit (aname "i") (aname "j") (aname "k")))
  test "if2" expression "if bool then False else True" (IfExpr unit (aname "bool") (Atom unit (Bool false)) (Atom unit (Bool true)))

  test "apply1" expression "f 1" (App unit (aname "f") (singleton (aint 1)))
  test "apply2" expression "f x y z 12 (3 + 7)"
    (App unit (aname "f") (toList [aname "x", aname "y", aname "z", aint 12, Binary unit Add (aint 3) (aint 7)]))
  test "fibonacci" expression "fib (n - 1) + fib (n - 2)"
    (Binary unit Add
      (App unit (aname "fib") (toList [Binary unit Sub (aname "n") (aint 1)]))
      (App unit (aname "fib") (toList [Binary unit Sub (aname "n") (aint 2)])))
  test "predicate" expression "if p 10 then 10 else 20"
    (IfExpr unit
      (App unit (aname "p") (singleton (aint 10)))
      (aint 10)
      (aint 20))
  test "stuff" expression "f a (1 * 2) * 3"
    (Binary unit Mul
      (App unit (aname "f") (toList [aname "a", Binary unit Mul (aint 1) (aint 2)]))
      (aint 3))

  test "tuple" expression "(1, 2)" (NTuple unit (toList [aint 1, aint 2]))
  test "3tuple" expression "(1, 2, 3)" (NTuple unit (toList [aint 1, aint 2, aint 3]))
  test "4tuple" expression "(1, 2, 3, 4)" (NTuple unit (toList [aint 1, aint 2, aint 3, aint 4]))
  test "tuple_spaces" expression "(   1   , 2   )" (NTuple unit (toList [aint 1, aint 2]))
  test "3tuple_spaces" expression "(  1   , 2    , 3     )" (NTuple unit (toList [aint 1, aint 2, aint 3]))
  test "tuple_arith" expression "((1 + 2, (3)))" (NTuple unit (toList [Binary unit Add (aint 1) (aint 2), aint 3]))
  test "tuple_apply" expression "fmap f (snd (1,2), fst ( 1 , 2 ))"
    (App unit (aname "fmap") (toList
      [ (aname "f")
      , NTuple unit (toList
        [ App unit (aname "snd") (toList [NTuple unit (toList [aint 1, aint 2])])
        , App unit (aname "fst") (toList [NTuple unit (toList [aint 1, aint 2])])
        ])
      ]
    ))
  test "tuple_deep" expression "((((( ((((((1)),((2))),(3,((((4)))))),((5,6),(7,8))),(((9,(10)),(((11,12)))),((((13,14),(14,15)))))) )))))"
    (NTuple unit (Cons 
      (NTuple unit (Cons 
        (NTuple unit (Cons 
          (NTuple unit (Cons (Atom unit (AInt 1)) (Cons (Atom unit (AInt 2)) (Nil))))
          (Cons (NTuple unit (Cons (Atom unit (AInt 3)) (Cons (Atom unit (AInt 4)) (Nil)))) (Nil))))
        (Cons (NTuple unit
          (Cons (NTuple unit (Cons (Atom unit (AInt 5)) (Cons (Atom unit (AInt 6)) (Nil))))
            (Cons (NTuple unit (Cons (Atom unit (AInt 7)) (Cons (Atom unit (AInt 8)) (Nil)))) (Nil)))) (Nil))))
      (Cons (NTuple unit (Cons (NTuple unit (Cons (NTuple unit (Cons (Atom unit (AInt 9)) (Cons (Atom unit (AInt 10)) (Nil))))
        (Cons (NTuple unit (Cons (Atom unit (AInt 11)) (Cons (Atom unit (AInt 12)) (Nil)))) (Nil))))
      (Cons (NTuple unit (Cons (NTuple unit (Cons (Atom unit (AInt 13)) (Cons (Atom unit (AInt 14)) (Nil))))
        (Cons (NTuple unit (Cons (Atom unit (AInt 14)) (Cons (Atom unit (AInt 15)) (Nil)))) (Nil)))) (Nil)))) (Nil))))

  test "list_empty" expression "[]" (List unit Nil)
  test "list1" expression "[1]" (List unit (toList [aint 1]))
  test "list2" expression "[  1  ]" (List unit (toList [aint 1]))
  test "list3" expression "[  1  ,2,3,     4    ,  5  ]" (List unit (toList [aint 1, aint 2, aint 3, aint 4, aint 5]))
  test "list_nested" expression "[ [1,2] , [ 3 , 4 ] ]" (List unit $ toList [(List unit $ toList [aint 1, aint 2]), (List unit $ toList [aint 3, aint 4])])
  test "list_complex" expression "[ 1 + 2 , 3 + 4 ] ++ []"
    (Binary unit Append 
      (List unit $ toList [Binary unit Add (aint 1) (aint 2), Binary unit Add (aint 3) (aint 4)])
      (List unit Nil))

  test "binding_lit1" binding "x" (Lit (Name "x"))
  test "binding_lit2" binding "10" (Lit (AInt 10))
  test "lambda1" expression "(\\x -> x)" (Lambda unit (toList [Lit (Name "x")]) (aname "x"))
  test "lambda2" expression "( \\ x y z -> ( x , y , z ) )"
    (Lambda unit (toList [Lit (Name "x"), Lit (Name "y"), Lit (Name "z")])
      (NTuple unit (toList [aname "x", aname "y", aname "z"])))
  test "lambda3" expression "(  \\  x ->   (   \\    y ->    (   \\    z ->     f   x   y   z )  )  )"
    (Lambda unit (singleton $ Lit $ Name "x")
      (Lambda unit (singleton $ Lit $ Name "y")
        (Lambda unit (singleton $ Lit $ Name "z")
          (App unit (aname "f") (toList [aname "x", aname "y", aname "z"])))))
  test "lambda4" expression "(\\a b -> a + b) 1 2"
    (App unit 
      (Lambda unit (toList [Lit (Name "a"), Lit (Name "b")])
        (Binary unit Add (aname "a") (aname "b")))
      (toList [aint 1, aint 2]))

  test "lambda5" expression "(\\a -> (\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> a + b + c + d + e + f + g))))))) 1 2 3 4 5 6 7"
    (App unit 
      (Lambda unit (Cons (Lit (Name "a")) (Nil)) 
        (Lambda unit (Cons (Lit (Name "b")) (Nil))
          (Lambda unit (Cons (Lit (Name "c")) (Nil))
            (Lambda unit (Cons (Lit (Name "d")) (Nil))
              (Lambda unit (Cons (Lit (Name "e")) (Nil))
                (Lambda unit (Cons (Lit (Name "f")) (Nil))
                  (Lambda unit (Cons (Lit (Name "g")) (Nil))
                    (Binary unit Add
                      (Binary unit Add
                        (Binary unit Add
                          (Binary unit Add
                            (Binary unit Add
                              (Binary unit Add (Atom unit (Name "a")) (Atom unit (Name "b")))
                              (Atom unit (Name "c")))
                            (Atom unit (Name "d")))
                          (Atom unit (Name "e")))
                        (Atom unit (Name "f")))
                      (Atom unit (Name "g"))))))))))
      (Cons (Atom unit (AInt 1)) (Cons (Atom unit (AInt 2)) (Cons (Atom unit (AInt 3)) (Cons (Atom unit (AInt 4)) (Cons (Atom unit (AInt 5)) (Cons (Atom unit (AInt 6)) (Cons (Atom unit (AInt 7)) (Nil)))))))))

  test "lambda6" expression "\\x -> x + 2"
      (Lambda unit
        (toList [Lit (Name "x")])
        (Binary unit Add (aname "x") (aint 2)))

  test "lambda7" definition "f a = \\b -> a + b"
    (Def "f"
      (toList [Lit (Name "a")])
      (Lambda unit
        (toList [Lit (Name "b")])
        (Binary unit Add (aname "a") (aname "b"))))

  test "sectR1" expression "(+1)" (SectR unit Add (aint 1))
  test "sectR2" expression "( ^ 2 )" (SectR unit Power (aint 2))
  test "sectR3" expression "(++ [1])" (SectR unit Append (List unit (toList [aint 1])))
  test "sectR4" expression "(<= (2 + 2))" (SectR unit Leq (Binary unit Add (aint 2) (aint 2)))
  test "sectR5" expression "(   >=  (  2 + 2  )  )" (SectR unit Geq (Binary unit Add (aint 2) (aint 2)))

  test "prefixOp1" expression "(+)" (PrefixOp unit Add)
  test "prefixOp2" expression "( ++ )" (PrefixOp unit Append)
  test "prefixOp3" expression "((^) 2 10)" (App unit (PrefixOp unit Power) (toList [aint 2, aint 10]))

  test "sectL1" expression "(1+)" (SectL unit (aint 1) Add)
  test "sectL2" expression "( n `mod` )" (SectL unit (aname "n") (InfixFunc "mod"))
  test "sectL3" expression "([1] ++)" (SectL unit (List unit $ toList [aint 1]) Append)
  test "sectL4" expression "(   ( 2 +  2 )  <= )" (SectL unit (Binary unit Add (aint 2) (aint 2)) Leq)

  test "let1" expression "let x = 1 in x + x" (LetExpr unit (Lit (Name "x")) (aint 1) (Binary unit Add (aname "x") (aname "x")))
  test "let2" expression "letty + let x = 1 in x" (Binary unit Add (aname "letty") (LetExpr unit (Lit (Name "x")) (aint 1) (aname "x")))
  test "let3" expression "let x = let y = 1 in y in let z = 2 in x + z"
    (LetExpr unit
      (Lit (Name "x"))
      (LetExpr unit
        (Lit (Name "y"))
        (aint 1)
        (aname "y"))
      (LetExpr unit
        (Lit (Name "z"))
        (aint 2)
        (Binary unit Add (aname "x") (aname "z"))))

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
  test "def2" definition "double x = x + x" (Def "double" (Cons (Lit (Name "x")) Nil) (Binary unit Add (aname "x") (aname "x")))
  test "def3" definition "zip (x:xs) (y:ys) = (x,y) : zip xs ys"
    (Def "zip"
      (toList [ConsLit (Lit (Name "x")) (Lit (Name "xs")), ConsLit (Lit (Name "y")) (Lit (Name "ys"))])
      (Binary unit Colon
        (NTuple unit (toList  [Atom unit (Name "x"), Atom unit (Name "y")]))
        (App unit (aname "zip") (toList [Atom unit (Name "xs"), Atom unit (Name "ys")]))))

  test "defs" definitions "\n\na   =   10 \n  \n \nb    =  20  \n\n  \n"
    (toList [Def "a" Nil (aint 10), Def "b" Nil (aint 20)])

  test "prelude" definitions prelude parsedPrelude
  test "expression" expression "sum (map (^2) [1, 2, 3, 4])"
    (App unit 
      (Atom unit (Name "sum"))
      (Cons 
        (App unit 
          (Atom unit (Name "map"))
          (Cons (SectR unit Power (Atom unit (AInt 2)))
            (Cons (List unit (Cons (Atom unit (AInt 1)) (Cons (Atom unit (AInt 2)) (Cons (Atom unit (AInt 3)) (Cons (Atom unit (AInt 4)) (Nil))))))
              (Nil))))
        (Nil)))

  test "char_atom1" atom "'a'" (Char "a")
  test "char_atom2" atom "'\\\\'" (Char "\\")
  test "char_atom3" atom "'\\n'" (Char "\n")
  test "char_expr1" expression "'\\r'" (Atom unit (Char "\r"))
  test "char_expr2" expression "['\\\\', '\\'', '\\\"']" (List unit $ toList [Atom unit (Char "\\"), Atom unit (Char "'"), Atom unit (Char "\"")])

  test "string1" expression "\"asdf\"" (List unit $ toList [Atom unit (Char "a"), Atom unit (Char "s"), Atom unit (Char "d"), Atom unit (Char "f")])
  test "string2" expression "\"\\\\\\n\\\"\\\'\"" (List unit $ toList [Atom unit (Char "\\"), Atom unit (Char "\n"), Atom unit (Char "\""), Atom unit (Char "'")])

prelude :: String
prelude =
  "and (True:xs)  = and xs\n" ++
  "and (False:xs) = False\n" ++
  "and []         = True\n" ++
  "\n" ++
  "or (False:xs) = or xs\n" ++
  "or (True:xs)  = True\n" ++
  "or []         = False\n" ++
  "\n" ++
  "all p = and . map p\n" ++
  "any p = or . map p\n" ++
  "\n" ++
  "head (x:xs) = x\n" ++
  "tail (x:xs) = xs\n" ++
  "\n" ++
  "take 0 xs     = []\n" ++
  "take n (x:xs) = x : take (n - 1) xs\n" ++
  "\n" ++
  "drop 0 xs     = xs\n" ++
  "drop n (x:xs) = drop (n - 1) xs\n" ++
  "\n" ++
  "elem e []     = False\n" ++
  "elem e (x:xs) = if e == x then True else elem e xs\n" ++
  "\n" ++
  "max a b = if a >= b then a else b\n" ++
  "min a b = if b >= a then a else b\n" ++
  "\n" ++
  "maximum (x:xs) = foldr max x xs\n" ++
  "minimum (x:xs) = foldr min x xs\n" ++
  "\n" ++
  "length []     = 0\n" ++
  "length (x:xs) = 1 + length xs\n" ++
  "\n" ++
  "zip (x:xs) (y:ys) = (x, y) : zip xs ys\n" ++
  "zip []      _     = []\n" ++
  "zip _       []    = []\n" ++
  "\n" ++
  "zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys\n" ++
  "zipWith _ []     _      = []\n" ++
  "zipWith _ _      []     = []\n" ++
  "\n" ++
  "unzip []          = ([], [])\n" ++
  "unzip ((a, b):xs) = (\\(as, bs) -> (a:as, b:bs)) $ unzip xs\n" ++
  "\n" ++
  "fst (x,_) = x\n" ++
  "snd (_,x) = x\n" ++
  "\n" ++
  "curry f a b = f (a, b)\n" ++
  "uncurry f (a, b) = f a b\n" ++
  "\n" ++
  "repeat x = x : repeat x\n" ++
  "\n" ++
  "replicate 0 _ = []\n" ++
  "replicate n x = x : replicate (n - 1) x\n" ++
  "\n" ++
  "enumFromTo a b = if a <= b then a : enumFromTo (a + 1) b else []\n" ++
  "\n" ++
  "sum (x:xs) = x + sum xs\n" ++
  "sum [] = 0\n" ++
  "\n" ++
  "product (x:xs) = x * product xs\n" ++
  "product [] = 1\n" ++
  "\n" ++
  "reverse []     = []\n" ++
  "reverse (x:xs) = reverse xs ++ [x]\n" ++
  "\n" ++
  "concat = foldr (++) []\n" ++
  "\n" ++
  "map f []     = []\n" ++
  "map f (x:xs) = f x : map f xs\n" ++
  "\n" ++
  "not True  = False\n" ++
  "not False = True\n" ++
  "\n" ++
  "filter p (x:xs) = if p x then x : filter p xs else filter p xs\n" ++
  "filter p []     = []\n" ++
  "\n" ++
  "foldr f ini []     = ini\n" ++
  "foldr f ini (x:xs) = f x (foldr f ini xs)\n" ++
  "\n" ++
  "foldl f acc []     = acc\n" ++
  "foldl f acc (x:xs) = foldl f (f acc x) xs\n" ++
  "\n" ++
  "scanl f b []     = [b]\n" ++
  "scanl f b (x:xs) = b : scanl f (f b x) xs\n" ++
  "\n" ++
  "iterate f x = x : iterate f (f x)\n" ++
  "\n" ++
  "id x = x\n" ++
  "\n" ++
  "const x _ = x\n" ++
  "\n" ++
  "flip f x y = f y x\n" ++
  "\n" ++
  "even n = (n `mod` 2) == 0\n" ++
  "odd n = (n `mod` 2) == 1\n" ++
  "\n" ++
  "fix f = f (fix f)\n"

parsedPrelude :: List Definition
parsedPrelude = toList [
  (Def "and" (Cons (ConsLit (Lit (Bool true)) (Lit (Name "xs"))) (Nil)) (App unit (Atom unit (Name "and")) (Cons (Atom unit (Name "xs")) (Nil)))),
  (Def "and" (Cons (ConsLit (Lit (Bool false)) (Lit (Name "xs"))) (Nil)) (Atom unit (Bool false))),
  (Def "and" (Cons (ListLit (Nil)) (Nil)) (Atom unit (Bool true))),
  (Def "or" (Cons (ConsLit (Lit (Bool false)) (Lit (Name "xs"))) (Nil)) (App unit (Atom unit (Name "or")) (Cons (Atom unit (Name "xs")) (Nil)))),
  (Def "or" (Cons (ConsLit (Lit (Bool true)) (Lit (Name "xs"))) (Nil)) (Atom unit (Bool true))),
  (Def "or" (Cons (ListLit (Nil)) (Nil)) (Atom unit (Bool false))),
  (Def "all" (Cons (Lit (Name "p")) (Nil)) (Binary unit Composition (Atom unit (Name "and")) (App unit (Atom unit (Name "map")) (Cons (Atom unit (Name "p")) (Nil))))),
  (Def "any" (Cons (Lit (Name "p")) (Nil)) (Binary unit Composition (Atom unit (Name "or")) (App unit (Atom unit (Name "map")) (Cons (Atom unit (Name "p")) (Nil))))),
  (Def "head" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Atom unit (Name "x"))),
  (Def "tail" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Atom unit (Name "xs"))),
  (Def "take" (Cons (Lit (AInt 0)) (Cons (Lit (Name "xs")) (Nil))) (List unit (Nil))),
  (Def "take" (Cons (Lit (Name "n")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (Binary unit Colon (Atom unit (Name "x")) (App unit (Atom unit (Name "take")) (Cons (Binary unit Sub (Atom unit (Name "n")) (Atom unit (AInt 1))) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "drop" (Cons (Lit (AInt 0)) (Cons (Lit (Name "xs")) (Nil))) (Atom unit (Name "xs"))),
  (Def "drop" (Cons (Lit (Name "n")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (App unit (Atom unit (Name "drop")) (Cons (Binary unit Sub (Atom unit (Name "n")) (Atom unit (AInt 1))) (Cons (Atom unit (Name "xs")) (Nil))))),
  (Def "elem" (Cons (Lit (Name "e")) (Cons (ListLit (Nil)) (Nil))) (Atom unit (Bool false))),
  (Def "elem" (Cons (Lit (Name "e")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (IfExpr unit (Binary unit Equ (Atom unit (Name "e")) (Atom unit (Name "x"))) (Atom unit (Bool true)) (App unit (Atom unit (Name "elem")) (Cons (Atom unit (Name "e")) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "max" (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil))) (IfExpr unit (Binary unit Geq (Atom unit (Name "a")) (Atom unit (Name "b"))) (Atom unit (Name "a")) (Atom unit (Name "b")))),
  (Def "min" (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil))) (IfExpr unit (Binary unit Geq (Atom unit (Name "b")) (Atom unit (Name "a"))) (Atom unit (Name "a")) (Atom unit (Name "b")))),
  (Def "maximum" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (App unit (Atom unit (Name "foldr")) (Cons (Atom unit (Name "max")) (Cons (Atom unit (Name "x")) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "minimum" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (App unit (Atom unit (Name "foldr")) (Cons (Atom unit (Name "min")) (Cons (Atom unit (Name "x")) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "length" (Cons (ListLit (Nil)) (Nil)) (Atom unit (AInt 0))),
  (Def "length" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary unit Add (Atom unit (AInt 1)) (App unit (Atom unit (Name "length")) (Cons (Atom unit (Name "xs")) (Nil))))),
  (Def "zip" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Cons (ConsLit (Lit (Name "y")) (Lit (Name "ys"))) (Nil))) (Binary unit Colon (NTuple unit (Cons (Atom unit (Name "x")) (Cons (Atom unit (Name "y")) (Nil)))) (App unit (Atom unit (Name "zip")) (Cons (Atom unit (Name "xs")) (Cons (Atom unit (Name "ys")) (Nil)))))),
  (Def "zip" (Cons (ListLit (Nil)) (Cons (Lit (Name "_")) (Nil))) (List unit (Nil))),
  (Def "zip" (Cons (Lit (Name "_")) (Cons (ListLit (Nil)) (Nil))) (List unit (Nil))),
  (Def "zipWith" (Cons (Lit (Name "f")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Cons (ConsLit (Lit (Name "y")) (Lit (Name "ys"))) (Nil)))) (Binary unit Colon (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "x")) (Cons (Atom unit (Name "y")) (Nil)))) (App unit (Atom unit (Name "zipWith")) (Cons (Atom unit (Name "f")) (Cons (Atom unit (Name "xs")) (Cons (Atom unit (Name "ys")) (Nil))))))),
  (Def "zipWith" (Cons (Lit (Name "_")) (Cons (ListLit (Nil)) (Cons (Lit (Name "_")) (Nil)))) (List unit (Nil))),
  (Def "zipWith" (Cons (Lit (Name "_")) (Cons (Lit (Name "_")) (Cons (ListLit (Nil)) (Nil)))) (List unit (Nil))),
  (Def "unzip" (Cons (ListLit (Nil)) (Nil)) (NTuple unit (Cons (List unit (Nil)) (Cons (List unit (Nil)) (Nil))))),
  (Def "unzip" (Cons (ConsLit (NTupleLit (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (Lit (Name "xs"))) (Nil)) (Binary unit Dollar (Lambda unit (Cons (NTupleLit (Cons (Lit (Name "as")) (Cons (Lit (Name "bs")) (Nil)))) (Nil)) (NTuple unit (Cons (Binary unit Colon (Atom unit (Name "a")) (Atom unit (Name "as"))) (Cons (Binary unit Colon (Atom unit (Name "b")) (Atom unit (Name "bs"))) (Nil))))) (App unit (aname "unzip") (Cons (aname "xs") Nil)))),
  (Def "fst" (Cons (NTupleLit (Cons (Lit (Name "x")) (Cons (Lit (Name "_")) (Nil)))) Nil) (Atom unit (Name "x"))),
  (Def "snd" (Cons (NTupleLit (Cons (Lit (Name "_")) (Cons (Lit (Name "x")) (Nil)))) Nil) (Atom unit (Name "x"))),
  (Def "curry" (Cons (Lit (Name "f")) (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (App unit (Atom unit (Name "f")) (Cons (NTuple unit (Cons (Atom unit (Name "a")) (Cons (Atom unit (Name "b")) (Nil)))) (Nil)))),
  (Def "uncurry" (Cons (Lit (Name "f")) (Cons (NTupleLit (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (Nil))) (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "a")) (Cons (Atom unit (Name "b")) (Nil))))),
  (Def "repeat" (Cons (Lit (Name "x")) (Nil)) (Binary unit Colon (Atom unit (Name "x")) (App unit (Atom unit (Name "repeat")) (Cons (Atom unit (Name "x")) (Nil))))),
  (Def "replicate" (Cons (Lit (AInt 0)) (Cons (Lit (Name "_")) (Nil))) (List unit (Nil))),
  (Def "replicate" (Cons (Lit (Name "n")) (Cons (Lit (Name "x")) (Nil))) (Binary unit Colon (Atom unit (Name "x")) (App unit (Atom unit (Name "replicate")) (Cons (Binary unit Sub (Atom unit (Name "n")) (Atom unit (AInt 1))) (Cons (Atom unit (Name "x")) (Nil)))))),
  (Def "enumFromTo" (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil))) (IfExpr unit (Binary unit Leq (Atom unit (Name "a")) (Atom unit (Name "b"))) (Binary unit Colon (Atom unit (Name "a")) (App unit (Atom unit (Name "enumFromTo")) (Cons (Binary unit Add (Atom unit (Name "a")) (Atom unit (AInt 1))) (Cons (Atom unit (Name "b")) (Nil))))) (List unit (Nil)))),
  (Def "sum" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary unit Add (Atom unit (Name "x")) (App unit (Atom unit (Name "sum")) (Cons (Atom unit (Name "xs")) (Nil))))),
  (Def "sum" (Cons (ListLit (Nil)) (Nil)) (Atom unit (AInt 0))),
  (Def "product" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary unit Mul (Atom unit (Name "x")) (App unit (Atom unit (Name "product")) (Cons (Atom unit (Name "xs")) (Nil))))),
  (Def "product" (Cons (ListLit (Nil)) (Nil)) (Atom unit (AInt 1))),
  (Def "reverse" (Cons (ListLit (Nil)) (Nil)) (List unit (Nil))),
  (Def "reverse" (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)) (Binary unit Append (App unit (Atom unit (Name "reverse")) (Cons (Atom unit (Name "xs")) (Nil))) (List unit (Cons (Atom unit (Name "x")) (Nil))))),
  (Def "concat" (Nil) (App unit (Atom unit (Name "foldr")) (Cons (PrefixOp unit Append) (Cons (List unit (Nil)) (Nil))))),
  (Def "map" (Cons (Lit (Name "f")) (Cons (ListLit (Nil)) (Nil))) (List unit (Nil))),
  (Def "map" (Cons (Lit (Name "f")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (Binary unit Colon (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "x")) (Nil))) (App unit (Atom unit (Name "map")) (Cons (Atom unit (Name "f")) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "not" (Cons (Lit (Bool true)) (Nil)) (Atom unit (Bool false))),
  (Def "not" (Cons (Lit (Bool false)) (Nil)) (Atom unit (Bool true))),
  (Def "filter" (Cons (Lit (Name "p")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil))) (IfExpr unit (App unit (Atom unit (Name "p")) (Cons (Atom unit (Name "x")) (Nil))) (Binary unit Colon (Atom unit (Name "x")) (App unit (Atom unit (Name "filter")) (Cons (Atom unit (Name "p")) (Cons (Atom unit (Name "xs")) (Nil))))) (App unit (Atom unit (Name "filter")) (Cons (Atom unit (Name "p")) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "filter" (Cons (Lit (Name "p")) (Cons (ListLit (Nil)) (Nil))) (List unit (Nil))),
  (Def "foldr" (Cons (Lit (Name "f")) (Cons (Lit (Name "ini")) (Cons (ListLit (Nil)) (Nil)))) (Atom unit (Name "ini"))),
  (Def "foldr" (Cons (Lit (Name "f")) (Cons (Lit (Name "ini")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "x")) (Cons (App unit (Atom unit (Name "foldr")) (Cons (Atom unit (Name "f")) (Cons (Atom unit (Name "ini")) (Cons (Atom unit (Name "xs")) (Nil))))) (Nil))))),
  (Def "foldl" (Cons (Lit (Name "f")) (Cons (Lit (Name "acc")) (Cons (ListLit (Nil)) (Nil)))) (Atom unit (Name "acc"))),
  (Def "foldl" (Cons (Lit (Name "f")) (Cons (Lit (Name "acc")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (App unit (Atom unit (Name "foldl")) (Cons (Atom unit (Name "f")) (Cons (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "acc")) (Cons (Atom unit (Name "x")) (Nil)))) (Cons (Atom unit (Name "xs")) (Nil)))))),
  (Def "scanl" (Cons (Lit (Name "f")) (Cons (Lit (Name "b")) (Cons (ListLit (Nil)) (Nil)))) (List unit (Cons (Atom unit (Name "b")) (Nil)))),
  (Def "scanl" (Cons (Lit (Name "f")) (Cons (Lit (Name "b")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (Binary unit Colon (Atom unit (Name "b")) (App unit (Atom unit (Name "scanl")) (Cons (Atom unit (Name "f")) (Cons (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "b")) (Cons (Atom unit (Name "x")) (Nil)))) (Cons (Atom unit (Name "xs")) (Nil))))))),
  (Def "iterate" (Cons (Lit (Name "f")) (Cons (Lit (Name "x")) (Nil))) (Binary unit Colon (Atom unit (Name "x")) (App unit (Atom unit (Name "iterate")) (Cons (Atom unit (Name "f")) (Cons (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "x")) (Nil))) (Nil)))))),
  (Def "id" (Cons (Lit (Name "x")) (Nil)) (Atom unit (Name "x"))),
  (Def "const" (Cons (Lit (Name "x")) (Cons (Lit (Name "_")) (Nil))) (Atom unit (Name "x"))),
  (Def "flip" (Cons (Lit (Name "f")) (Cons (Lit (Name "x")) (Cons (Lit (Name "y")) (Nil)))) (App unit (Atom unit (Name "f")) (Cons (Atom unit (Name "y")) (Cons (Atom unit (Name "x")) (Nil))))),
  (Def "even" (Cons (Lit (Name "n")) (Nil)) (Binary unit Equ (Binary unit (InfixFunc "mod") (Atom unit (Name "n")) (Atom unit (AInt 2))) (Atom unit (AInt 0)))),
  (Def "odd" (Cons (Lit (Name "n")) (Nil)) (Binary unit Equ (Binary unit (InfixFunc "mod") (Atom unit (Name "n")) (Atom unit (AInt 2))) (Atom unit (AInt 1)))),
  (Def "fix" (Cons (Lit (Name "f")) (Nil)) (App unit (Atom unit (Name "f")) (Cons (App unit (Atom unit (Name "fix")) (Cons (Atom unit (Name "f")) (Nil))) (Nil))))
  ]
