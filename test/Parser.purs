module Test.Parser where

import Prelude
import Data.Either (Either(..))
import Data.List (List(..), singleton, (:), many, zipWith, nub, length)
import Data.Array ((..))
import Data.Array (length, zip, toUnfoldable, replicate) as Array
import Data.Tuple (Tuple(..), snd)
import Data.String (null)
import Data.String.CodeUnits (toCharArray)
import Data.Maybe (Maybe(..))
import Data.Foldable (intercalate, for_, and, all)

import Text.Parsing.Parser (ParseState(..), parseErrorPosition, parseErrorMessage, fail)

import Control.Monad.Writer (Writer, tell, execWriter) as W
import Control.Monad.State (get)
import Effect (Effect)
import Effect.Console (log)

import Test.Utils (tell, padLeft)
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
  , Type(..)
  , Meta (..)
  , emptyMeta
  , emptyMeta'
  , getMetaIndex
  , eq'
  , eq'Def
  , eq'Binding
  , traverseTree
  , traverseBinding)
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
  , types
  , IndentParser)


isValidlyIndexed :: TypeTree -> Boolean
isValidlyIndexed tree = length indices > 0 && (all (\x -> x >= 0) indices) && (length indices == length (nub indices))
  where
    indices :: List Int
    indices = W.execWriter (isValidlyIndexed' tree)

    tell' :: forall a. a -> W.Writer (List a) Unit
    tell' = singleton >>> W.tell

    void :: forall m a. (Monad m) => m a -> m Unit
    void _ = pure unit

    isValidlyIndexed' :: TypeTree -> W.Writer (List Int) (Tree Atom Unit Unit Unit)
    isValidlyIndexed' = traverseTree
      (traverseBinding (getMetaIndex >>> tell') >>> void)
      (snd >>> getMetaIndex >>> tell')
      (getMetaIndex >>> tell')


toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: String -> Effect Unit
tell' = tell

padLeft' :: forall a. (Show a) => a -> String
padLeft' = show >>> padLeft


class (Show a) <= Testable a where
  equals :: a -> a -> Boolean
  
instance testableTypeTree :: Testable (Tree Atom (Binding Meta) (Tuple Op Meta) Meta) where
  equals = eq'
  
instance testableDefinition :: Testable Definition where
  equals = eq'Def
  
instance testableBinding :: Testable (Binding Meta) where
  equals = eq'Binding
  
instance testableAtom :: Testable Atom where
  equals = eq
  
instance testableType :: Testable Type where
  equals = eq

instance testableDataConstrType :: Testable (DataConstr Type) where
  equals = eq

instance testableString :: Testable String where
  equals = eq

instance testableChar :: Testable Char where
  equals = eq

instance testableADTDef :: Testable ADTDef where
  equals = eq

instance testableList :: (Testable a) => Testable (List a) where
  equals as bs = length as == length bs && (and $ zipWith equals as bs)

test' :: forall a. (Testable a)
      => (a -> Boolean)
      -> String
      -> IndentParser String a
      -> String
      -> a
      -> Effect Unit
test' predicate name p input expected = case runParserIndent p input of
  Left parseError -> tell' $
    "Parse fail (" <> name <> "): "
    <> padLeft' (parseErrorPosition parseError) <> "\n"
    <> padLeft (parseErrorMessage parseError) <> "\n"
    <> "Input:\n"
    <> padLeft input
  Right (Tuple result _)
    | not (result `equals` expected) -> tell' $
        "Parse fail (" <> name <> "):\n"
        <> "Output:\n"
        <> padLeft' result <> "\n"
        <> "Expected:\n"
        <> padLeft' expected <> "\n"
        <> "Input:\n"
        <> padLeft input
    | not (predicate result) -> tell' $
        "Predicate fail (" <> name <> "):\n"
        <> "Output:\n"
        <> padLeft' result <> "\n"
        <> "Expected:\n"
        <> padLeft' expected <> "\n"
        <> "Input:\n"
        <> padLeft input
    | otherwise -> log $ "Parse success (" <> name <> ")"

test = test' (const true)

testTypeTree = test' isValidlyIndexed

rejectTest :: forall a . (Show a)
                      => String
                      -> IndentParser String a
                      -> String
                      -> Effect Unit
rejectTest name parser input = case runParserIndent (parser <* inputIsEmpty) input of
  Left parserError -> log $ "rejectTest passed (" <> name <> ")"
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
                       -> Effect Unit
rejectTests name parser inputs = do
  for_ ((1 .. Array.length inputs) `Array.zip` inputs) $ \(Tuple idx iput) ->
    rejectTest (name <> "-" <> show idx) parser iput

inputIsEmpty :: IndentParser String Unit
inputIsEmpty = do
  ParseState s _ _ <- get
  when (not (null s)) (fail $ "Leftover input:\n" <> padLeft s)

aint :: Int -> TypeTree
aint i = Atom emptyMeta $ AInt i

abool :: Boolean -> TypeTree
abool = Atom emptyMeta <<< Bool

aname :: String -> TypeTree
aname s = Atom emptyMeta $ Name s

runTests :: Effect Unit
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

  testTypeTree "composition" expression "f . g" (Binary emptyMeta (toOpTuple Composition) (aname "f") (aname "g"))
  testTypeTree "power" expression "2 ^ 10" (Binary emptyMeta (toOpTuple Power) (aint 2) (aint 10))
  testTypeTree "mul" expression "2 * 2" (Binary emptyMeta (toOpTuple Mul) (aint 2) (aint 2))
  testTypeTree "div" expression "13 `div` 3" (Binary emptyMeta (toOpTuple (InfixFunc "div")) (aint 13) (aint 3))
  testTypeTree "mod" expression "13 `mod` 3" (Binary emptyMeta (toOpTuple (InfixFunc "mod")) (aint 13) (aint 3))
  testTypeTree "add1" expression "1 + 1"  (Binary emptyMeta (toOpTuple Add) (aint 1) (aint 1))
  testTypeTree "add2" expression "2+2" (Binary emptyMeta (toOpTuple Add) (aint 2) (aint 2))
  testTypeTree "sub" expression "5 - 3" (Binary emptyMeta (toOpTuple Sub) (aint 5) (aint 3))
  testTypeTree "colon" expression "x:xs" (Binary emptyMeta (toOpTuple Colon) (aname "x") (aname "xs"))
  testTypeTree "append1" expression "xs ++ ys" (Binary emptyMeta (toOpTuple Append) (aname "xs") (aname "ys"))
  testTypeTree "append2" expression "xs++ys"  (Binary emptyMeta (toOpTuple Append) (aname "xs") (aname "ys"))
  testTypeTree "equ" expression "5 == 5" (Binary emptyMeta (toOpTuple Equ) (aint 5) (aint 5))
  testTypeTree "neq" expression "1 /= 2" (Binary emptyMeta (toOpTuple Neq) (aint 1) (aint 2))
  testTypeTree "lt1" expression "1 < 234" (Binary emptyMeta (toOpTuple Lt) (aint 1) (aint 234))
  testTypeTree "lt2" expression "x<y" (Binary emptyMeta (toOpTuple Lt) (aname "x") (aname "y"))
  testTypeTree "leq" expression "1 <= 234" (Binary emptyMeta (toOpTuple Leq) (aint 1) (aint 234))
  testTypeTree "gt1" expression "567 > 1" (Binary emptyMeta (toOpTuple Gt) (aint 567) (aint 1))
  testTypeTree "gt2" expression "x>y" (Binary emptyMeta (toOpTuple Gt) (aname "x") (aname "y"))
  testTypeTree "geq" expression "567 >= 1" (Binary emptyMeta (toOpTuple Geq) (aint 567) (aint 1))
  testTypeTree "and" expression "hot && cold" (Binary emptyMeta (toOpTuple And) (aname "hot") (aname "cold"))
  testTypeTree "or" expression "be || notBe" (Binary emptyMeta (toOpTuple Or) (aname "be") (aname "notBe"))
  testTypeTree "dollar" expression "f $ 1 + 2"  (Binary emptyMeta (toOpTuple Dollar) (aname "f") (Binary emptyMeta (toOpTuple Add) (aint 1) (aint 2)))

  testTypeTree "unary_minus1" expression "- 10"  (aint (-10))
  testTypeTree "unary_minus2" expression "- x"  (Unary emptyMeta (toOpTuple Sub) (aname "x"))
  testTypeTree "unary_minus3" expression "-10"  (aint (-10))
  testTypeTree "unary_minus4" expression "-x"  (Unary emptyMeta (toOpTuple Sub) (aname "x"))

  testTypeTree "infix_operator1" expression "1 `max` 3" (Binary emptyMeta (toOpTuple (InfixFunc "max")) (aint 1) (aint 3))
  testTypeTree "infix_operator2" expression "5 `max` 2 `min` 1" (Binary emptyMeta (toOpTuple (InfixFunc "min")) (Binary emptyMeta (toOpTuple (InfixFunc "max")) (aint 5) (aint 2)) (aint 1))
  testTypeTree "infix_operator3" expression "True`tight`False" (Binary emptyMeta (toOpTuple (InfixFunc "tight")) (abool true) (abool false))

  testTypeTree "1" expression "1" (aint 1)
  testTypeTree "add" expression "1 + 2" (Binary emptyMeta (toOpTuple Add) (aint 1) (aint 2))
  testTypeTree "precedence" expression "1 * 2 + 3 * 4" (Binary emptyMeta (toOpTuple Add)
                                    (Binary emptyMeta (toOpTuple Mul) (aint 1) (aint 2))
                                    (Binary emptyMeta (toOpTuple Mul) (aint 3) (aint 4)))
  testTypeTree "whitespaces" expression
    "1   \t   -    \t   ( f   )    \t\t\t\t                                                                \t\t\t\t             `div`     _ignore"
    (Binary emptyMeta (toOpTuple Sub) (aint 1) (Binary emptyMeta (toOpTuple (InfixFunc "div")) (aname "f") (aname "_ignore")))
  testTypeTree "brackets" expression "(  1  +  2  )  *  3" (Binary emptyMeta (toOpTuple Mul) (Binary emptyMeta (toOpTuple Add) (aint 1) (aint 2)) (aint 3))
  testTypeTree "brackets2" expression "( (  1  +  2  - 3  )  *  4 * 5 * 6)"
    (Binary emptyMeta (toOpTuple Mul)
      (Binary emptyMeta (toOpTuple Mul)
        (Binary emptyMeta (toOpTuple Mul)
          (Binary emptyMeta (toOpTuple Sub)
            (Binary emptyMeta (toOpTuple Add) (aint 1) (aint 2))
            (aint 3))
          (aint 4))
        (aint 5))
      (aint 6))
  testTypeTree "brackets3" expression "( ( ( 1 ) ) )" (aint 1)
  testTypeTree "many brackets" expression "(   (( ((  f )) *  ( (17   )) ) ))" (Binary emptyMeta (toOpTuple Mul) (aname "f") (aint 17))

  testTypeTree "if_then_else" expression "if x then y else z" (IfExpr emptyMeta (aname "x") (aname "y") (aname "z"))
  testTypeTree "nested if" expression "if(if 1 then 2 else 3)then y else z" (IfExpr emptyMeta (IfExpr emptyMeta (aint 1) (aint 2) (aint 3)) (aname "y") (aname "z"))
  testTypeTree "iffy1" expression "iffy" (aname "iffy")
  testTypeTree "iffy2" expression "if 10 + 20 then iffy * iffy else ((7))"
    (IfExpr emptyMeta
      (Binary emptyMeta (toOpTuple Add) (aint 10) (aint 20))
      (Binary emptyMeta (toOpTuple Mul) (aname "iffy") (aname "iffy"))
      (aint 7))
  testTypeTree "iffy3" expression "iffy + if iffy then iffy else iffy"
    (Binary emptyMeta (toOpTuple Add) (aname "iffy") (IfExpr emptyMeta (aname "iffy") (aname "iffy") (aname "iffy")))
  testTypeTree "nested if 2" expression "if if x then y else z then if a then b else c else if i then j else k"
    (IfExpr emptyMeta
      (IfExpr emptyMeta (aname "x") (aname "y") (aname "z"))
      (IfExpr emptyMeta (aname "a") (aname "b") (aname "c"))
      (IfExpr emptyMeta (aname "i") (aname "j") (aname "k")))
  testTypeTree "if2" expression "if bool then False else True" (IfExpr emptyMeta (aname "bool") (Atom emptyMeta (Bool false)) (Atom emptyMeta (Bool true)))

  testTypeTree "apply1" expression "f 1" (App emptyMeta (aname "f") (singleton (aint 1)))
  testTypeTree "apply2" expression "f x y z 12 (3 + 7)"
    (App emptyMeta (aname "f") (toList [aname "x", aname "y", aname "z", aint 12, Binary emptyMeta (toOpTuple Add) (aint 3) (aint 7)]))
  testTypeTree "fibonacci" expression "fib (n - 1) + fib (n - 2)"
    (Binary emptyMeta (toOpTuple Add)
      (App emptyMeta (aname "fib") (toList [Binary emptyMeta (toOpTuple Sub) (aname "n") (aint 1)]))
      (App emptyMeta (aname "fib") (toList [Binary emptyMeta (toOpTuple Sub) (aname "n") (aint 2)])))
  testTypeTree "predicate" expression "if p 10 then 10 else 20"
    (IfExpr emptyMeta
      (App emptyMeta (aname "p") (singleton (aint 10)))
      (aint 10)
      (aint 20))
  testTypeTree "stuff" expression "f a (1 * 2) * 3"
    (Binary emptyMeta (toOpTuple Mul)
      (App emptyMeta (aname "f") (toList [aname "a", Binary emptyMeta (toOpTuple Mul) (aint 1) (aint 2)]))
      (aint 3))

  testTypeTree "tuple" expression "(1, 2)" (NTuple emptyMeta (toList [aint 1, aint 2]))
  testTypeTree "3tuple" expression "(1, 2, 3)" (NTuple emptyMeta (toList [aint 1, aint 2, aint 3]))
  testTypeTree "4tuple" expression "(1, 2, 3, 4)" (NTuple emptyMeta (toList [aint 1, aint 2, aint 3, aint 4]))
  testTypeTree "tuple_spaces" expression "(   1   , 2   )" (NTuple emptyMeta (toList [aint 1, aint 2]))
  testTypeTree "3tuple_spaces" expression "(  1   , 2    , 3     )" (NTuple emptyMeta (toList [aint 1, aint 2, aint 3]))
  testTypeTree "tuple_arith" expression "((1 + 2, (3)))" (NTuple emptyMeta (toList [Binary emptyMeta (toOpTuple Add) (aint 1) (aint 2), aint 3]))
  testTypeTree "tuple_apply" expression "fmap f (snd (1,2), fst ( 1 , 2 ))"
    (App emptyMeta (aname "fmap") (toList
      [ (aname "f")
      , NTuple emptyMeta (toList
        [ App emptyMeta (aname "snd") (toList [NTuple emptyMeta (toList [aint 1, aint 2])])
        , App emptyMeta (aname "fst") (toList [NTuple emptyMeta (toList [aint 1, aint 2])])
        ])
      ]
    ))
  testTypeTree "tuple_deep" expression "((((( ((((((1)),((2))),(3,((((4)))))),((5,6),(7,8))),(((9,(10)),(((11,12)))),((((13,14),(14,15)))))) )))))"
    (NTuple emptyMeta (Cons
      (NTuple emptyMeta (Cons
        (NTuple emptyMeta (Cons
          (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 1)) (Cons (Atom emptyMeta (AInt 2)) (Nil))))
          (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 3)) (Cons (Atom emptyMeta (AInt 4)) (Nil)))) (Nil))))
        (Cons (NTuple emptyMeta
          (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 5)) (Cons (Atom emptyMeta (AInt 6)) (Nil))))
            (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 7)) (Cons (Atom emptyMeta (AInt 8)) (Nil)))) (Nil)))) (Nil))))
      (Cons (NTuple emptyMeta (Cons (NTuple emptyMeta (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 9)) (Cons (Atom emptyMeta (AInt 10)) (Nil))))
        (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 11)) (Cons (Atom emptyMeta (AInt 12)) (Nil)))) (Nil))))
      (Cons (NTuple emptyMeta (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 13)) (Cons (Atom emptyMeta (AInt 14)) (Nil))))
        (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (AInt 14)) (Cons (Atom emptyMeta (AInt 15)) (Nil)))) (Nil)))) (Nil)))) (Nil))))

  testTypeTree "list_empty" expression "[]" (List emptyMeta Nil)
  testTypeTree "list1" expression "[1]" (List emptyMeta (toList [aint 1]))
  testTypeTree "list2" expression "[  1  ]" (List emptyMeta (toList [aint 1]))
  testTypeTree "list3" expression "[  1  ,2,3,     4    ,  5  ]" (List emptyMeta (toList [aint 1, aint 2, aint 3, aint 4, aint 5]))
  testTypeTree "list_nested" expression "[ [1,2] , [ 3 , 4 ] ]" (List emptyMeta $ toList [(List emptyMeta $ toList [aint 1, aint 2]), (List emptyMeta $ toList [aint 3, aint 4])])
  testTypeTree "list_complex" expression "[ 1 + 2 , 3 + 4 ] ++ []"
    (Binary emptyMeta (toOpTuple Append)
      (List emptyMeta $ toList [Binary emptyMeta (toOpTuple Add) (aint 1) (aint 2), Binary emptyMeta (toOpTuple Add) (aint 3) (aint 4)])
      (List emptyMeta Nil))

  test "binding_lit1" binding "x" (Lit emptyMeta (Name "x"))
  test "binding_lit2" binding "10" (Lit emptyMeta (AInt 10))
  testTypeTree "lambda1" expression "(\\x -> x)" (Lambda emptyMeta (toList [Lit emptyMeta (Name "x")]) (aname "x"))
  testTypeTree "lambda2" expression "( \\ x y z -> ( x , y , z ) )"
    (Lambda emptyMeta (toList [Lit emptyMeta (Name "x"), Lit emptyMeta (Name "y"), Lit emptyMeta (Name "z")])
      (NTuple emptyMeta (toList [aname "x", aname "y", aname "z"])))
  testTypeTree "lambda3" expression "(  \\  x ->   (   \\    y ->    (   \\    z ->     f   x   y   z )  )  )"
    (Lambda emptyMeta (singleton $ Lit emptyMeta $ Name "x")
      (Lambda emptyMeta (singleton $ Lit emptyMeta $ Name "y")
        (Lambda emptyMeta (singleton $ Lit emptyMeta $ Name "z")
          (App emptyMeta (aname "f") (toList [aname "x", aname "y", aname "z"])))))
  testTypeTree "lambda4" expression "(\\a b -> a + b) 1 2"
    (App emptyMeta
      (Lambda emptyMeta (toList [Lit emptyMeta (Name "a"), Lit emptyMeta (Name "b")])
        (Binary emptyMeta (toOpTuple Add) (aname "a") (aname "b")))
      (toList [aint 1, aint 2]))

  testTypeTree "lambda5" expression "(\\a -> (\\b -> (\\c -> (\\d -> (\\e -> (\\f -> (\\g -> a + b + c + d + e + f + g))))))) 1 2 3 4 5 6 7"
    (App emptyMeta
      (Lambda emptyMeta (Cons (Lit emptyMeta (Name "a")) (Nil))
        (Lambda emptyMeta (Cons (Lit emptyMeta (Name "b")) (Nil))
          (Lambda emptyMeta (Cons (Lit emptyMeta (Name "c")) (Nil))
            (Lambda emptyMeta (Cons (Lit emptyMeta (Name "d")) (Nil))
              (Lambda emptyMeta (Cons (Lit emptyMeta (Name "e")) (Nil))
                (Lambda emptyMeta (Cons (Lit emptyMeta (Name "f")) (Nil))
                  (Lambda emptyMeta (Cons (Lit emptyMeta (Name "g")) (Nil))
                    (Binary emptyMeta (toOpTuple Add)
                      (Binary emptyMeta (toOpTuple Add)
                        (Binary emptyMeta (toOpTuple Add)
                          (Binary emptyMeta (toOpTuple Add)
                            (Binary emptyMeta (toOpTuple Add)
                              (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "b")))
                              (Atom emptyMeta (Name "c")))
                            (Atom emptyMeta (Name "d")))
                          (Atom emptyMeta (Name "e")))
                        (Atom emptyMeta (Name "f")))
                      (Atom emptyMeta (Name "g"))))))))))
      (Cons (Atom emptyMeta (AInt 1)) (Cons (Atom emptyMeta (AInt 2)) (Cons (Atom emptyMeta (AInt 3)) (Cons (Atom emptyMeta (AInt 4)) (Cons (Atom emptyMeta (AInt 5)) (Cons (Atom emptyMeta (AInt 6)) (Cons (Atom emptyMeta (AInt 7)) (Nil)))))))))

  testTypeTree "lambda6" expression "\\x -> x + 2"
      (Lambda emptyMeta
        (toList [Lit emptyMeta (Name "x")])
        (Binary emptyMeta (toOpTuple Add) (aname "x") (aint 2)))

  test "lambda7" definition "f a = \\b -> a + b"
    (Def "f"
      (toList [Lit emptyMeta (Name "a")])
      (Lambda emptyMeta
        (toList [Lit emptyMeta (Name "b")])
        (Binary emptyMeta (toOpTuple Add) (aname "a") (aname "b"))))

  testTypeTree "sectR1" expression "(+1)" (SectR emptyMeta (toOpTuple Add) (aint 1))
  testTypeTree "sectR2" expression "( ^ 2 )" (SectR emptyMeta (toOpTuple Power) (aint 2))
  testTypeTree "sectR3" expression "(++ [1])" (SectR emptyMeta (toOpTuple Append) (List emptyMeta (toList [aint 1])))
  testTypeTree "sectR4" expression "(<= (2 + 2))" (SectR emptyMeta (toOpTuple Leq) (Binary emptyMeta (toOpTuple Add) (aint 2) (aint 2)))
  testTypeTree "sectR5" expression "(   >=  (  2 + 2  )  )" (SectR emptyMeta (toOpTuple Geq) (Binary emptyMeta (toOpTuple Add) (aint 2) (aint 2)))

  testTypeTree "prefixOp1" expression "(+)" (PrefixOp emptyMeta (toOpTuple Add))
  testTypeTree "prefixOp2" expression "( ++ )" (PrefixOp emptyMeta (toOpTuple Append))
  testTypeTree "prefixOp3" expression "((^) 2 10)" (App emptyMeta (PrefixOp emptyMeta (toOpTuple Power)) (toList [aint 2, aint 10]))

  testTypeTree "sectL1" expression "(1+)" (SectL emptyMeta (aint 1) (toOpTuple Add))
  testTypeTree "sectL2" expression "( n `mod` )" (SectL emptyMeta (aname "n") (toOpTuple (InfixFunc "mod")))
  testTypeTree "sectL3" expression "([1] ++)" (SectL emptyMeta (List emptyMeta $ toList [aint 1]) (toOpTuple Append))
  testTypeTree "sectL4" expression "(   ( 2 +  2 )  <= )" (SectL emptyMeta (Binary emptyMeta (toOpTuple Add) (aint 2) (aint 2)) (toOpTuple Leq))

  testTypeTree "let1" expression "let x = 1 in x + x" (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (aint 1)) Nil) (Binary emptyMeta (toOpTuple Add) (aname "x") (aname "x")))
  testTypeTree "let2" expression "letty + let x = 1 in x" (Binary emptyMeta (toOpTuple Add) (aname "letty") (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (aint 1)) Nil) (aname "x")))
  testTypeTree "let3" expression "let x = let y = 1 in y in let z = 2 in x + z" (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "y")) (Atom emptyMeta (AInt 1))) (Nil)) (Atom emptyMeta (Name "y")))) (Nil)) (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "z")) (Atom emptyMeta (AInt 2))) (Nil)) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "x")) (Atom emptyMeta (Name "z")))))
  testTypeTree "let4" expression "let { x = 1; y = 2; z = 3} in x + y + z"              (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (Atom emptyMeta (AInt 1))) (Cons (Tuple (Lit emptyMeta (Name "y")) (Atom emptyMeta (AInt 2))) (Cons (Tuple (Lit emptyMeta (Name "z")) (Atom emptyMeta (AInt 3))) (Nil)))) (Binary emptyMeta (toOpTuple Add) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "x")) (Atom emptyMeta (Name "y"))) (Atom emptyMeta (Name "z"))))
  testTypeTree "let5" expression "let x = 1; y = 2; z = 3 in x + y + z"                 (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (Atom emptyMeta (AInt 1))) (Cons (Tuple (Lit emptyMeta (Name "y")) (Atom emptyMeta (AInt 2))) (Cons (Tuple (Lit emptyMeta (Name "z")) (Atom emptyMeta (AInt 3))) (Nil)))) (Binary emptyMeta (toOpTuple Add) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "x")) (Atom emptyMeta (Name "y"))) (Atom emptyMeta (Name "z"))))
  testTypeTree "let6" expression "let x = 1\n    y = 2\n    z = 3 in x + y + z"         (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (Atom emptyMeta (AInt 1))) (Cons (Tuple (Lit emptyMeta (Name "y")) (Atom emptyMeta (AInt 2))) (Cons (Tuple (Lit emptyMeta (Name "z")) (Atom emptyMeta (AInt 3))) (Nil)))) (Binary emptyMeta (toOpTuple Add) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "x")) (Atom emptyMeta (Name "y"))) (Atom emptyMeta (Name "z"))))
  testTypeTree "let7" expression "let {\n  x = 1 ;\n  y = 2 ;\n  z = 3\n} in x + y + z" (LetExpr emptyMeta (Cons (Tuple (Lit emptyMeta (Name "x")) (Atom emptyMeta (AInt 1))) (Cons (Tuple (Lit emptyMeta (Name "y")) (Atom emptyMeta (AInt 2))) (Cons (Tuple (Lit emptyMeta (Name "z")) (Atom emptyMeta (AInt 3))) (Nil)))) (Binary emptyMeta (toOpTuple Add) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "x")) (Atom emptyMeta (Name "y"))) (Atom emptyMeta (Name "z"))))

  test "consLit1" binding "(x:xs)" (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs")))
  test "consLit2" binding "(x:(y:zs))" (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (ConsLit emptyMeta (Lit emptyMeta (Name "y")) (Lit emptyMeta (Name "zs"))))
  test "consLit3" binding "(  x  :  (  666  :  zs  )   )" (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (ConsLit emptyMeta (Lit emptyMeta (AInt 666)) (Lit emptyMeta (Name "zs"))))

  test "listLit1" binding "[]" (ListLit emptyMeta Nil)
  test "listLit2" binding "[    ]" (ListLit emptyMeta Nil)
  test "listLit3" binding "[  True ]" (ListLit emptyMeta (Cons (Lit emptyMeta (Bool true)) Nil))
  test "listLit4" binding "[  x   ,  y  ,   1337 ]" (ListLit emptyMeta (toList [Lit emptyMeta (Name "x"), Lit emptyMeta (Name "y"), Lit emptyMeta (AInt 1337)]))

  test "tupleLit1" binding "(a,b)" (NTupleLit emptyMeta (toList [Lit emptyMeta (Name "a"), Lit emptyMeta (Name "b")]))
  test "tupleLit2" binding "(   a   ,  b   ,   c   )" (NTupleLit emptyMeta (toList $ [Lit emptyMeta (Name "a"), Lit emptyMeta (Name "b"), Lit emptyMeta (Name "c")]))
  test "tupleLit3" binding "(  (  x  ,  y  )  , ( a  ,  b  )  , 10 )"
    (NTupleLit emptyMeta (toList
      [ NTupleLit emptyMeta (toList [Lit emptyMeta (Name "x"), Lit emptyMeta (Name "y")])
      , NTupleLit emptyMeta (toList [Lit emptyMeta (Name "a"), Lit emptyMeta (Name "b")])
      , (Lit emptyMeta (AInt 10))
      ]))

  test "binding" binding "( ( x , y ) : [ a , b ] )"
    (ConsLit emptyMeta
      (NTupleLit emptyMeta (toList [Lit emptyMeta (Name "x"), Lit emptyMeta (Name "y")]))
      (ListLit emptyMeta (toList [Lit emptyMeta (Name "a"), Lit emptyMeta (Name "b")])))

  test "def1" definition "x = 10" (Def "x" Nil (aint 10))
  test "def2" definition "double x = x + x" (Def "double" (Cons (Lit emptyMeta (Name "x")) Nil) (Binary emptyMeta (toOpTuple Add) (aname "x") (aname "x")))
  test "def3" definition "zip (x:xs) (y:ys) = (x,y) : zip xs ys"
    (Def "zip"
      (toList [ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs")), ConsLit emptyMeta (Lit emptyMeta (Name "y")) (Lit emptyMeta (Name "ys"))])
      (Binary emptyMeta (toOpTuple Colon)
        (NTuple emptyMeta (toList  [Atom emptyMeta (Name "x"), Atom emptyMeta (Name "y")]))
        (App emptyMeta (aname "zip") (toList [Atom emptyMeta (Name "xs"), Atom emptyMeta (Name "ys")]))))

  test "defs" definitions "\n\na   =   10 \n  \n \nb    =  20  \n\n  \n"
    (toList [Def "a" Nil (aint 10), Def "b" Nil (aint 20)])

  test "prelude" definitions prelude parsedPrelude
  testTypeTree "expression" expression "sum (map (^2) [1, 2, 3, 4])"
    (App emptyMeta
      (Atom emptyMeta (Name "sum"))
      (Cons
        (App emptyMeta
          (Atom emptyMeta (Name "map"))
          (Cons (SectR emptyMeta (toOpTuple Power) (Atom emptyMeta (AInt 2)))
            (Cons (List emptyMeta (Cons (Atom emptyMeta (AInt 1)) (Cons (Atom emptyMeta (AInt 2)) (Cons (Atom emptyMeta (AInt 3)) (Cons (Atom emptyMeta (AInt 4)) (Nil))))))
              (Nil))))
        (Nil)))

  test "char_atom1" atom "'a'" (Char "a")
  test "char_atom2" atom "'\\\\'" (Char "\\")
  test "char_atom3" atom "'\\n'" (Char "\n")
  testTypeTree "char_expr1" expression "'\\r'" (Atom emptyMeta (Char "\r"))
  testTypeTree "char_expr2" expression "['\\\\', '\\'', '\\\"']" (List emptyMeta $ toList [Atom emptyMeta (Char "\\"), Atom emptyMeta (Char "'"), Atom emptyMeta (Char "\"")])

  testTypeTree "string1" expression "\"asdf\"" (List emptyMeta $ toList [Atom emptyMeta (Char "a"), Atom emptyMeta (Char "s"), Atom emptyMeta (Char "d"), Atom emptyMeta (Char "f")])
  testTypeTree "string2" expression "\"\\\\\\n\\\"\\\'\"" (List emptyMeta $ toList [Atom emptyMeta (Char "\\"), Atom emptyMeta (Char "\n"), Atom emptyMeta (Char "\""), Atom emptyMeta (Char "'")])

  testTypeTree "listComp1" expression "[ x | x <- [1,2,3] ]" $ ListComp emptyMeta (Atom emptyMeta (Name "x")) (toList [Gen emptyMeta (Lit emptyMeta (Name "x")) (List emptyMeta (toList [Atom emptyMeta (AInt 1), Atom emptyMeta (AInt 2), Atom emptyMeta (AInt 3)]))])
  testTypeTree "listComp2" expression "[ b + c | let b = 3, c <- [1 .. ]]" $ ListComp emptyMeta (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "b")) (Atom emptyMeta (Name ("c")))) $ toList [Let emptyMeta (Lit emptyMeta (Name "b")) (Atom emptyMeta (AInt 3)),
    Gen emptyMeta (Lit emptyMeta (Name "c")) (ArithmSeq emptyMeta (Atom emptyMeta (AInt 1)) Nothing Nothing)]
  testTypeTree "listComp3" expression "[a*b|let a=5,let b=a+1]" $ ListComp emptyMeta (Binary emptyMeta (toOpTuple Mul) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "b"))) $ toList [Let emptyMeta (Lit emptyMeta (Name "a")) (Atom emptyMeta (AInt 5)),
    Let emptyMeta (Lit emptyMeta (Name "b")) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "a")) (Atom emptyMeta (AInt 1)))]
  testTypeTree "listComp4" expression "[ x | x <- [1..10], even x ]" $ ListComp emptyMeta (aname "x") $ toList [ Gen emptyMeta (Lit emptyMeta (Name "x")) (ArithmSeq emptyMeta (aint 1) Nothing (Just (aint 10))), Guard emptyMeta (App emptyMeta (aname "even") $ toList [aname "x"])]

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
                      Right (Tuple r _) -> r

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
      (Meta $ emptyMeta' {mtype = Just
          (TTypeCons
            "Maybe"
            (Cons
              (TypVar "a")
              Nil))})
      (Constr "Nothing"))),

  (Def "Just" Nil
    (Atom
      (Meta $ emptyMeta' {mtype = Just
          (TypArr
            (TypVar "a")
            (TTypeCons "Maybe" (Cons (TypVar "a") Nil)))})
      (Constr "Just"))),

  (Def "and" (ConsLit emptyMeta (Lit emptyMeta (Bool true)) (Lit emptyMeta (Name "xs")) : Nil) (App emptyMeta (Atom emptyMeta (Name "and")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))),
  (Def "and" (ConsLit emptyMeta (Lit emptyMeta (Bool false)) (Lit emptyMeta (Name "xs")) : Nil) (Atom emptyMeta (Bool false))),
  (Def "and" (ListLit emptyMeta Nil : Nil) (Atom emptyMeta (Bool true))),
  (Def "or" (ConsLit emptyMeta (Lit emptyMeta (Bool false)) (Lit emptyMeta (Name "xs")) : Nil) (App emptyMeta (Atom emptyMeta (Name "or")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))),
  (Def "or" (ConsLit emptyMeta (Lit emptyMeta (Bool true)) (Lit emptyMeta (Name "xs")) : Nil) (Atom emptyMeta (Bool true))),
  (Def "or" (ListLit emptyMeta Nil : Nil) (Atom emptyMeta (Bool false))),
  (Def "all" (Lit emptyMeta (Name "p") : Nil) (Binary emptyMeta (toOpTuple Composition) (Atom emptyMeta (Name "and")) (App emptyMeta (Atom emptyMeta (Name "map")) (Cons (Atom emptyMeta (Name "p")) (Nil))))),
  (Def "any" (Lit emptyMeta (Name "p") : Nil) (Binary emptyMeta (toOpTuple Composition) (Atom emptyMeta (Name "or")) (App emptyMeta (Atom emptyMeta (Name "map")) (Cons (Atom emptyMeta (Name "p")) (Nil))))),
  (Def "head" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (Atom emptyMeta (Name "x"))),
  (Def "tail" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (Atom emptyMeta (Name "xs"))),
  (Def "take" (Cons (Lit emptyMeta (AInt 0)) (Cons (Lit emptyMeta (Name "xs")) (Nil))) (List emptyMeta (Nil))),
  (Def "take" (Cons (Lit emptyMeta (Name "n")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil))) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "take")) (Cons (Binary emptyMeta (toOpTuple Sub) (Atom emptyMeta (Name "n")) (Atom emptyMeta (AInt 1))) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "drop" (Cons (Lit emptyMeta (AInt 0)) (Cons (Lit emptyMeta (Name "xs")) (Nil))) (Atom emptyMeta (Name "xs"))),
  (Def "drop" (Cons (Lit emptyMeta (Name "n")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil))) (App emptyMeta (Atom emptyMeta (Name "drop")) (Cons (Binary emptyMeta (toOpTuple Sub) (Atom emptyMeta (Name "n")) (Atom emptyMeta (AInt 1))) (Cons (Atom emptyMeta (Name "xs")) (Nil))))),
  (Def "elem" (Cons (Lit emptyMeta (Name "e")) (Cons (ListLit emptyMeta (Nil)) (Nil))) (Atom emptyMeta (Bool false))),
  (Def "elem" (Cons (Lit emptyMeta (Name "e")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil))) (IfExpr emptyMeta (Binary emptyMeta (toOpTuple Equ) (Atom emptyMeta (Name "e")) (Atom emptyMeta (Name "x"))) (Atom emptyMeta (Bool true)) (App emptyMeta (Atom emptyMeta (Name "elem")) (Cons (Atom emptyMeta (Name "e")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "max" (Cons (Lit emptyMeta (Name "a")) (Cons (Lit emptyMeta (Name "b")) (Nil))) (IfExpr emptyMeta (Binary emptyMeta (toOpTuple Geq) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "b"))) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "b")))),
  (Def "min" (Cons (Lit emptyMeta (Name "a")) (Cons (Lit emptyMeta (Name "b")) (Nil))) (IfExpr emptyMeta (Binary emptyMeta (toOpTuple Geq) (Atom emptyMeta (Name "b")) (Atom emptyMeta (Name "a"))) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "b")))),
  (Def "maximum" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (App emptyMeta (Atom emptyMeta (Name "foldr")) (Cons (Atom emptyMeta (Name "max")) (Cons (Atom emptyMeta (Name "x")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "minimum" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (App emptyMeta (Atom emptyMeta (Name "foldr")) (Cons (Atom emptyMeta (Name "min")) (Cons (Atom emptyMeta (Name "x")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "length" (Cons (ListLit emptyMeta (Nil)) (Nil)) (Atom emptyMeta (AInt 0))),
  (Def "length" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (AInt 1)) (App emptyMeta (Atom emptyMeta (Name "length")) (Cons (Atom emptyMeta (Name "xs")) (Nil))))),
  (Def "zip" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "y")) (Lit emptyMeta (Name "ys"))) (Nil))) (Binary emptyMeta (toOpTuple Colon) (NTuple emptyMeta (Cons (Atom emptyMeta (Name "x")) (Cons (Atom emptyMeta (Name "y")) (Nil)))) (App emptyMeta (Atom emptyMeta (Name "zip")) (Cons (Atom emptyMeta (Name "xs")) (Cons (Atom emptyMeta (Name "ys")) (Nil)))))),
  (Def "zip" (Cons (ListLit emptyMeta (Nil)) (Cons (Lit emptyMeta (Name "_")) (Nil))) (List emptyMeta (Nil))),
  (Def "zip" (Cons (Lit emptyMeta (Name "_")) (Cons (ListLit emptyMeta (Nil)) (Nil))) (List emptyMeta (Nil))),
  (Def "zipWith" (Cons (Lit emptyMeta (Name "f")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "y")) (Lit emptyMeta (Name "ys"))) (Nil)))) (Binary emptyMeta (toOpTuple Colon) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "x")) (Cons (Atom emptyMeta (Name "y")) (Nil)))) (App emptyMeta (Atom emptyMeta (Name "zipWith")) (Cons (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "xs")) (Cons (Atom emptyMeta (Name "ys")) (Nil))))))),
  (Def "zipWith" (Cons (Lit emptyMeta (Name "_")) (Cons (ListLit emptyMeta (Nil)) (Cons (Lit emptyMeta (Name "_")) (Nil)))) (List emptyMeta (Nil))),
  (Def "zipWith" (Cons (Lit emptyMeta (Name "_")) (Cons (Lit emptyMeta (Name "_")) (Cons (ListLit emptyMeta (Nil)) (Nil)))) (List emptyMeta (Nil))),
  (Def "unzip" (Cons (ListLit emptyMeta (Nil)) (Nil)) (NTuple emptyMeta (Cons (List emptyMeta (Nil)) (Cons (List emptyMeta (Nil)) (Nil))))),
  (Def "unzip" (Cons (ConsLit emptyMeta (NTupleLit emptyMeta (Cons (Lit emptyMeta (Name "a")) (Cons (Lit emptyMeta (Name "b")) (Nil)))) (Lit emptyMeta (Name "xs"))) (Nil)) (Binary emptyMeta (toOpTuple Dollar) (Lambda emptyMeta (Cons (NTupleLit emptyMeta (Cons (Lit emptyMeta (Name "as")) (Cons (Lit emptyMeta (Name "bs")) (Nil)))) (Nil)) (NTuple emptyMeta (Cons (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "as"))) (Cons (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "b")) (Atom emptyMeta (Name "bs"))) (Nil))))) (App emptyMeta (aname "unzip") (Cons (aname "xs") Nil)))),
  (Def "fst" (Cons (NTupleLit emptyMeta (Cons (Lit emptyMeta (Name "x")) (Cons (Lit emptyMeta (Name "_")) (Nil)))) Nil) (Atom emptyMeta (Name "x"))),
  (Def "snd" (Cons (NTupleLit emptyMeta (Cons (Lit emptyMeta (Name "_")) (Cons (Lit emptyMeta (Name "x")) (Nil)))) Nil) (Atom emptyMeta (Name "x"))),
  (Def "curry" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "a")) (Cons (Lit emptyMeta (Name "b")) (Nil)))) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (NTuple emptyMeta (Cons (Atom emptyMeta (Name "a")) (Cons (Atom emptyMeta (Name "b")) (Nil)))) (Nil)))),
  (Def "uncurry" (Cons (Lit emptyMeta (Name "f")) (Cons (NTupleLit emptyMeta (Cons (Lit emptyMeta (Name "a")) (Cons (Lit emptyMeta (Name "b")) (Nil)))) (Nil))) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "a")) (Cons (Atom emptyMeta (Name "b")) (Nil))))),
  (Def "repeat" (Cons (Lit emptyMeta (Name "x")) (Nil)) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "repeat")) (Cons (Atom emptyMeta (Name "x")) (Nil))))),
  (Def "replicate" (Cons (Lit emptyMeta (AInt 0)) (Cons (Lit emptyMeta (Name "_")) (Nil))) (List emptyMeta (Nil))),
  (Def "replicate" (Cons (Lit emptyMeta (Name "n")) (Cons (Lit emptyMeta (Name "x")) (Nil))) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "replicate")) (Cons (Binary emptyMeta (toOpTuple Sub) (Atom emptyMeta (Name "n")) (Atom emptyMeta (AInt 1))) (Cons (Atom emptyMeta (Name "x")) (Nil)))))),
  (Def "enumFromTo" (Cons (Lit emptyMeta (Name "a")) (Cons (Lit emptyMeta (Name "b")) (Nil))) (IfExpr emptyMeta (Binary emptyMeta (toOpTuple Leq) (Atom emptyMeta (Name "a")) (Atom emptyMeta (Name "b"))) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "a")) (App emptyMeta (Atom emptyMeta (Name "enumFromTo")) (Cons (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "a")) (Atom emptyMeta (AInt 1))) (Cons (Atom emptyMeta (Name "b")) (Nil))))) (List emptyMeta (Nil)))),
  (Def "sum" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (Binary emptyMeta (toOpTuple Add) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "sum")) (Cons (Atom emptyMeta (Name "xs")) (Nil))))),
  (Def "sum" (Cons (ListLit emptyMeta (Nil)) (Nil)) (Atom emptyMeta (AInt 0))),
  (Def "product" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (Binary emptyMeta (toOpTuple Mul) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "product")) (Cons (Atom emptyMeta (Name "xs")) (Nil))))),
  (Def "product" (Cons (ListLit emptyMeta (Nil)) (Nil)) (Atom emptyMeta (AInt 1))),
  (Def "reverse" (Cons (ListLit emptyMeta (Nil)) (Nil)) (List emptyMeta (Nil))),
  (Def "reverse" (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)) (Binary emptyMeta (toOpTuple Append) (App emptyMeta (Atom emptyMeta (Name "reverse")) (Cons (Atom emptyMeta (Name "xs")) (Nil))) (List emptyMeta (Cons (Atom emptyMeta (Name "x")) (Nil))))),
  (Def "concat" (Nil) (App emptyMeta (Atom emptyMeta (Name "foldr")) (Cons (PrefixOp emptyMeta (toOpTuple Append)) (Cons (List emptyMeta (Nil)) (Nil))))),
  (Def "map" (Cons (Lit emptyMeta (Name "f")) (Cons (ListLit emptyMeta (Nil)) (Nil))) (List emptyMeta (Nil))),
  (Def "map" (Cons (Lit emptyMeta (Name "f")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil))) (Binary emptyMeta (toOpTuple Colon) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "x")) (Nil))) (App emptyMeta (Atom emptyMeta (Name "map")) (Cons (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "not" (Cons (Lit emptyMeta (Bool true)) (Nil)) (Atom emptyMeta (Bool false))),
  (Def "not" (Cons (Lit emptyMeta (Bool false)) (Nil)) (Atom emptyMeta (Bool true))),
  (Def "filter" (Cons (Lit emptyMeta (Name "p")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil))) (IfExpr emptyMeta (App emptyMeta (Atom emptyMeta (Name "p")) (Cons (Atom emptyMeta (Name "x")) (Nil))) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "filter")) (Cons (Atom emptyMeta (Name "p")) (Cons (Atom emptyMeta (Name "xs")) (Nil))))) (App emptyMeta (Atom emptyMeta (Name "filter")) (Cons (Atom emptyMeta (Name "p")) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "filter" (Cons (Lit emptyMeta (Name "p")) (Cons (ListLit emptyMeta (Nil)) (Nil))) (List emptyMeta (Nil))),
  (Def "foldr" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "ini")) (Cons (ListLit emptyMeta (Nil)) (Nil)))) (Atom emptyMeta (Name "ini"))),
  (Def "foldr" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "ini")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)))) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "x")) (Cons (App emptyMeta (Atom emptyMeta (Name "foldr")) (Cons (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "ini")) (Cons (Atom emptyMeta (Name "xs")) (Nil))))) (Nil))))),
  (Def "foldl" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "acc")) (Cons (ListLit emptyMeta (Nil)) (Nil)))) (Atom emptyMeta (Name "acc"))),
  (Def "foldl" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "acc")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)))) (App emptyMeta (Atom emptyMeta (Name "foldl")) (Cons (Atom emptyMeta (Name "f")) (Cons (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "acc")) (Cons (Atom emptyMeta (Name "x")) (Nil)))) (Cons (Atom emptyMeta (Name "xs")) (Nil)))))),
  (Def "scanl" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "b")) (Cons (ListLit emptyMeta (Nil)) (Nil)))) (List emptyMeta (Cons (Atom emptyMeta (Name "b")) (Nil)))),
  (Def "scanl" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "b")) (Cons (ConsLit emptyMeta (Lit emptyMeta (Name "x")) (Lit emptyMeta (Name "xs"))) (Nil)))) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "b")) (App emptyMeta (Atom emptyMeta (Name "scanl")) (Cons (Atom emptyMeta (Name "f")) (Cons (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "b")) (Cons (Atom emptyMeta (Name "x")) (Nil)))) (Cons (Atom emptyMeta (Name "xs")) (Nil))))))),
  (Def "iterate" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "x")) (Nil))) (Binary emptyMeta (toOpTuple Colon) (Atom emptyMeta (Name "x")) (App emptyMeta (Atom emptyMeta (Name "iterate")) (Cons (Atom emptyMeta (Name "f")) (Cons (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "x")) (Nil))) (Nil)))))),
  (Def "id" (Cons (Lit emptyMeta (Name "x")) (Nil)) (Atom emptyMeta (Name "x"))),
  (Def "const" (Cons (Lit emptyMeta (Name "x")) (Cons (Lit emptyMeta (Name "_")) (Nil))) (Atom emptyMeta (Name "x"))),
  (Def "flip" (Cons (Lit emptyMeta (Name "f")) (Cons (Lit emptyMeta (Name "x")) (Cons (Lit emptyMeta (Name "y")) (Nil)))) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (Atom emptyMeta (Name "y")) (Cons (Atom emptyMeta (Name "x")) (Nil))))),
  (Def "even" (Cons (Lit emptyMeta (Name "n")) (Nil)) (Binary emptyMeta (toOpTuple Equ) (Binary emptyMeta (toOpTuple (InfixFunc "mod")) (Atom emptyMeta (Name "n")) (Atom emptyMeta (AInt 2))) (Atom emptyMeta (AInt 0)))),
  (Def "odd" (Cons (Lit emptyMeta (Name "n")) (Nil)) (Binary emptyMeta (toOpTuple Equ) (Binary emptyMeta (toOpTuple (InfixFunc "mod")) (Atom emptyMeta (Name "n")) (Atom emptyMeta (AInt 2))) (Atom emptyMeta (AInt 1)))),
  (Def "fix" (Cons (Lit emptyMeta (Name "f")) (Nil)) (App emptyMeta (Atom emptyMeta (Name "f")) (Cons (App emptyMeta (Atom emptyMeta (Name "fix")) (Cons (Atom emptyMeta (Name "f")) (Nil))) (Nil))))
  ]

stringToList :: String -> List Char
stringToList = Array.toUnfoldable <<< toCharArray

type MType = Maybe Type

econstr :: String -> TypeTree
econstr n = Atom emptyMeta (Constr n)

ename :: String -> TypeTree
ename n = Atom emptyMeta (Name n)

eint :: Int -> TypeTree
eint i = Atom emptyMeta (AInt i)

eapp :: TypeTree -> Array TypeTree -> TypeTree
eapp f as = App emptyMeta f (toList as)

ebin :: Op -> TypeTree -> TypeTree -> TypeTree
ebin o l r = Binary emptyMeta (Tuple o emptyMeta) l r

def :: String -> Array (Binding Meta) -> TypeTree -> Definition
def n bs e = Def n (toList bs) e

testConstructorsExpression :: Effect Unit
testConstructorsExpression = do
  testTypeTree "simple-expr-1" expression
    "Foo"
    (econstr "Foo")

  testTypeTree "simple-expr-2" expression
    "Foo 1"
    (eapp
      (econstr "Foo")
      [eint 1])

  testTypeTree "simple-expr-3" expression
    "Foo 1 (1 + 2)"
    (eapp
      (econstr "Foo")
      [ eint 1
      , ebin Add
        (eint 1)
        (eint 2)])

  testTypeTree "nested-expr-1" expression
    "Foo Bar"
    (eapp
      (econstr "Foo")
      [ econstr "Bar" ])

  testTypeTree "nested-expr-2" expression
    "Foo bar"
    (eapp
      (econstr "Foo")
      [ ename "bar"])

  testTypeTree "nested-expr-3" expression
    "foo Bar"
    (eapp
      (ename "foo")
      [econstr "Bar"])

  testTypeTree "nested-deep-expr-1" expression
    "Foo1 (Foo2 (Foo3 bar))"
    (eapp (econstr "Foo1")
      [ eapp (econstr "Foo2")
        [ eapp (econstr "Foo3")
          [ ename "bar" ]]])

  testTypeTree "nested-expr-4" expression
    "Bar || Foo"
    (ebin Or
      (econstr "Bar")
      (econstr "Foo"))

  testTypeTree "nested-expr-5" expression
    "Bar 1 :- Foo 2 3"
    (ebin (InfixConstr ":-")
      (eapp (econstr "Bar") [eint 1])
      (eapp (econstr "Foo") [eint 2, eint 3]))

  testTypeTree "nested-expr-6" expression
    "Bar 1 (Foo ::: Foo 2)"
    (eapp (econstr "Bar")
      [ eint 1
      , ebin (InfixConstr ":::")
        (econstr "Foo")
        (eapp (econstr "Foo") [eint 2])])


testConstructorsDefinition :: Effect Unit
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



litname :: String -> Binding Meta
litname = Lit emptyMeta <<< Name

litint :: Int -> Binding Meta
litint = Lit emptyMeta <<< AInt

litlist :: Array (Binding Meta) -> Binding Meta
litlist = ListLit emptyMeta <<< toList

bpair :: Binding Meta -> Binding Meta -> Binding Meta
bpair l r = NTupleLit emptyMeta (Cons l (Cons r Nil))

prefixDataConstr :: String -> Array (Binding Meta) -> Binding Meta
prefixDataConstr name [] = (Lit emptyMeta (Constr name))
prefixDataConstr name args = ConstrLit emptyMeta (PrefixDataConstr name (Array.length args) (toList args))

infixDataConstr :: String -> Binding Meta -> Binding Meta -> Binding Meta
infixDataConstr op l r = ConstrLit emptyMeta (InfixDataConstr op LEFTASSOC 9 l r)

litcons :: Binding Meta -> Binding Meta -> Binding Meta
litcons = ConsLit emptyMeta

testConstructorsBinding :: Effect Unit
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
      (ListLit emptyMeta (Cons (litname "a") (Cons (litname "c") Nil)))
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




testTypes :: Effect Unit
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

testTypeDefinition :: Effect Unit
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

testSymbol :: Effect Unit
testSymbol = do
  test "symbol" symbol
    "!"
    '!'

  test "symbols" (many symbol)
    "!#$%&*+./<>=?@\\^|-~°"
    (stringToList "!#$%&*+./<>=?@\\^|-~°")

testInfixDataConstrtructorDefinition :: Effect Unit
testInfixDataConstrtructorDefinition = do
  test "infixConstructor1" infixDataConstrtructorDefinition
    "a :+ b"
    (InfixDataConstr ":+" LEFTASSOC 9 (TypVar "a") (TypVar "b"))

  test "infixConstructor2" infixDataConstrtructorDefinition
    "a :::::: b"
    (InfixDataConstr "::::::" LEFTASSOC 9 (TypVar "a") (TypVar "b"))

testDataConstrtructorDefinition :: Effect Unit
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


testInfixConstructor :: Effect Unit
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
