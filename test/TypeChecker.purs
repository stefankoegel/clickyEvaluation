module Test.TypeChecker where

import AST
import TypeChecker (Scheme(Forall), inferGroup, inferType, inferDef, emptyTypeEnv, runInfer, typeProgramn, eqScheme, normalizeTypeTree, typeTreeProgram)
import Parser (parseExpr, parseDefs)
import Test.Parser (parsedPrelude)

import Prelude (Unit, bind, map, pure, show, unit, ($), (==), (<>), (<<<))
import Control.Monad.Writer (Writer, tell)
import Data.Array (toUnfoldable) as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.List (List(..), (:), singleton)
import Data.Tuple (Tuple(..))
import Text.Parsing.Parser (ParseError, parseErrorMessage)

-- | The result of the type inference procedure.
type InferResult = Either TypeError Scheme

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: forall a. a -> Writer (List a) Unit
tell' = tell <<< singleton

-- | Construct a list of type [typCon] given the name of the type constants.
typConList :: String -> Type
typConList name = AD $ TList (TypCon name)

-- | Construct a tuple type given a list of type constant names.
typConNTuple:: List String -> Type
typConNTuple names = AD $ TTuple (map TypCon names)

-- | Construct a list of type [a] given the type variable name a.
typVarList :: TVar -> Type
typVarList tv = AD $ TList (TypVar tv)

-- | Generate an arrow type from two given type variable names.
typVarArrow :: TVar -> TVar -> Type
typVarArrow tv1 tv2 = TypVar tv1 `TypArr` TypVar tv2

-- | Report a parse error.
reportParseError :: String -> ParseError -> Writer (List String) Unit
reportParseError testName parseError = tell' $ "Parse error for test case "
  <> testName <> ": "
  <> parseErrorMessage parseError
  <> "\nNote that this is not a failing test but rather an error in the test definition."

testInferExpr :: String -> String -> InferResult -> Writer (List String) Unit
testInferExpr name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> compareSchemes name expected $ runInfer $ inferType emptyTypeEnv expression

testInferDef :: String -> String -> InferResult -> Writer (List String) Unit
testInferDef name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right (definition:_) -> compareSchemes name expected $ runInfer $ inferDef emptyTypeEnv definition
  _ -> tell' $ "Parse error for test case " <> name <> ": Expected only a single definition case"
    <> "\nNote that this is not a failing test but rather an error in the test definition."

testInferDefs :: String -> String -> InferResult -> Writer (List String) Unit
testInferDefs name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right definitions -> compareSchemes name expected $ runInfer $ inferGroup emptyTypeEnv definitions

testInferExprWithPrelude :: String -> String -> InferResult -> Writer (List String) Unit
testInferExprWithPrelude name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> compareSchemes name expected (typeProgramn parsedPrelude expression)

-- | Test type inference on expression trees. Here not only the expected type of the whole
-- | expression is checked, but also the type of every subexpression.
testInferTT :: String -> TypeTree -> TypeTree -> Writer (List String) Unit
testInferTT name untypedTree expectedTypedTree = case typeTreeProgram parsedPrelude untypedTree of
  Left typeError -> tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                            "Encountered type error: " <> prettyPrintTypeError typeError
  Right typedTree -> if expectedTypedTree == typedTree
    then pure unit
    else tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                 "Expected type tree: " <> show expectedTypedTree <> "\n" <>
                 "Actual type tree: " <> show typedTree <> "\n"

-- | Test type tree normalization.
testNormalizeTT :: String -> TypeTree -> TypeTree -> Writer (List String) Unit
testNormalizeTT name tt normalizedTT = if (normalizeTypeTree tt) == normalizedTT
  then pure unit
  else tell' $ "Type tree normalization failed in test case `" <> name <> "`:\n" <>
               "Expected type tree: " <> show normalizedTT <> "\n" <>
               "Actual type tree: " <> show tt <> "\n"

compareSchemes :: String -> InferResult -> InferResult -> Writer (List String) Unit
compareSchemes name expected actual = if eqInferResult expected actual
  then pure unit
  else tell' $ "\n \n Typing fail in test case `" <> name <> "`:"
    <> "\nExpected: " <> show expected <> " - pretty printed: " <> prettyPrint expected
    <> "\nActual: " <> show actual <> " - pretty printed: " <> prettyPrint actual

eqInferResult :: InferResult -> InferResult -> Boolean
eqInferResult (Left a) (Left a') = (a == a')
eqInferResult (Right a) (Right a') = eqScheme a a'
eqInferResult _ _ = false

prettyPrint :: InferResult -> String
prettyPrint error@(Left _) = show error
prettyPrint (Right (Forall xs t)) = show xs <> " " <> prettyPrintType t

-- | Typed type tree representing `[1]`.
listOne :: TypeTree
listOne = List (Just $ typConList "Int") (Atom (Just $ TypCon "Int") (AInt 1) : Nil)

-- | Untyped type tree representing `[1]`.
untypedListOne :: TypeTree
untypedListOne = List Nothing (Atom Nothing (AInt 1) : Nil)

intType :: Type
intType = TypCon "Int"

charType :: Type
charType = TypCon "Char"

runTests :: Writer (List String) Unit
runTests = do
  testInferExpr "SectL" "(3^)" (Right $ Forall Nil $ TypArr (TypCon "Int") (TypCon "Int"))
  testInferExpr "SectR" "(^3)" (Right $ Forall Nil $ TypArr (TypCon "Int") (TypCon "Int"))
  testInferExpr "Lambda1" "\\a b c d -> a b c d"  (Right $ Forall (toList ["b", "c", "d", "e"]) (TypArr (TypArr (TypVar "b") (TypArr (TypVar "c") (TypArr (TypVar "d") (TypVar "e")))) (TypArr ( TypVar "b")  ((TypArr (TypVar "c") (TypArr (TypVar "d") (TypVar "e")))))))
  testInferExpr "Lambda2" "\\a b -> a b" (Right $ Forall ("t_3" : "t_4" : Nil) (TypArr (TypArr (TypVar "t_3") (TypVar "t_4")) (TypArr (TypVar "t_3") (TypVar "t_4"))))
  testInferExpr "List1" "[1, 2, 3, 4, 5]" (Right $ Forall (Nil) (AD (TList (TypCon "Int"))))
  testInferExpr "List2" "[1 + 2, 3 + 4]" (Right $ Forall (Nil) (AD (TList (TypCon "Int"))))
  testInferExpr "List3" "[(+), 4]" (Left ((UnificationFail (TypCon "Int") (TypArr (TypCon "Int") (TypArr (TypCon "Int") (TypCon "Int"))))))
  testInferExpr "Empty list" "[]" (Right (Forall ("t_0" : Nil) (AD (TList (TypVar "t_0")))))
  testInferExpr "Append" "[1 + 2, 3 + 4] ++ []" (Right (Forall (Nil) (AD (TList (TypCon "Int")))))
  testInferExpr "Colon" "3 : [1 + 2, 3 + 4, \"Hallo\"]" (Left ((UnificationFail (AD $ TList $ TypCon "Char") (TypCon "Int"))))
  testInferExpr "NTuple" "(1 + 2, 3)" (Right (Forall (Nil) (AD (TTuple (Cons ((TypCon "Int")) (Cons ((TypCon "Int")) (Nil)))))))
  testInferExpr "SectR colon" "(:[3])" (Right (Forall (Nil) (TypArr (TypCon "Int") (AD (TList (TypCon "Int"))))))
  testInferExpr "Lambda wildcard" "\\_ _ -> 5" (Right (Forall ("t_1" : "t_3" : Nil) (TypArr (TypVar "t_1") (TypArr (TypVar "t_3") (TypCon "Int")))))
  testInferExpr "Lambda cons binding" "\\(x:xs) -> x" (Right (Forall ("t_2" : Nil) (TypArr (AD (TList (TypVar "t_2"))) (TypVar "t_2"))))
  testInferExpr "Let expression" "let x = 3 in \\_ _ -> x" (Right (Forall ("t_2" : "t_4" : Nil) (TypArr (TypVar "t_2") (TypArr (TypVar "t_4") (TypCon "Int")))))
  testInferExpr "Binding tuple in let expression" "let (a, b) = (\\f -> f, \"Hello\") in a b" (Right (Forall (Nil) (AD $ TList $ TypCon "Char")))
  testInferExpr "Lambda application" "(\\f a b -> f a b) (+) 3 4" (Right (Forall (Nil) (TypCon "Int")))
  -- ((\xs -> [ x | x <- xs ]) [1]) :: [Int]
  testInferExpr "List comprehension inside lambda" "(\\xs -> [ x | x <- xs ]) [1]" (Right (Forall (Nil) (AD $ TList $ TypCon "Int")))

  testInferDef "Define app" "app f xs = app f xs" (Right (Forall ("t_2" : "t_4" : "t_5" : Nil) (TypArr (TypVar "t_2") (TypArr (TypVar "t_4") (TypVar "t_5")))))
  testInferDef "Define single map" "map f (x:xs) = f x : map f xs" (Right (Forall ("t_11" : "t_5" : Nil) (TypArr (TypArr (TypVar "t_5") (TypVar "t_11")) (TypArr (AD (TList (TypVar "t_5"))) (AD (TList (TypVar "t_11")))))))
  testInferDef "Define foldr" "foldr f ini (x:xs) = f x (foldr f ini xs)" (Right (Forall ("t_5" : "t_4" : "t_7" : Nil) (TypArr (TypArr (TypVar "t_7") (TypArr (TypVar "t_4") (TypVar "t_4"))) (TypArr (TypVar "t_5") (TypArr (AD (TList (TypVar "t_7"))) (TypVar "t_4"))))))
  testInferDef "Conslit binding 1" "list (x:xs:xss) = x" (Right (Forall ("t_2" : Nil) (TypArr (AD (TList (TypVar "t_2"))) (TypVar "t_2"))))
  testInferDef "Conslit binding 2" "list (x:xs:xss) = xs" (Right (Forall ("t_2" : Nil) (TypArr (AD (TList (TypVar "t_2"))) (TypVar "t_2"))))
  testInferDef "Conslit binding 3" "list (x:xs:xss) = xss" (Right (Forall ("t_2" : Nil) (TypArr (AD (TList (TypVar "t_2"))) (AD (TList (TypVar "t_2"))))))
  testInferDef "Binding tuple 1" "fst (a, b) = a" (Right (Forall ("t_2" : "t_3" : Nil) (TypArr (AD (TTuple $ Cons ((TypVar "t_2")) (Cons ((TypVar "t_3")) (Nil)))) (TypVar "t_2"))))
  testInferDef "Binding tuple 2" "snd (a, b) = b" (Right (Forall ("t_2" : "t_3" : Nil) (TypArr (AD (TTuple (Cons ((TypVar "t_2")) (Cons ((TypVar "t_3")) (Nil))))) (TypVar "t_3"))))
  testInferDef "Binding tuple 3" "f (a, b, c) = a b c" (Right (Forall ("t_3" : "t_4" : "t_5" : Nil) (TypArr (AD (TTuple (Cons ((TypArr (TypVar "t_3") (TypArr (TypVar "t_4") (TypVar "t_5")))) (Cons ((TypVar "t_3")) (Cons ((TypVar "t_4")) (Nil)))))) (TypVar "t_5"))))
  testInferDef "Listlit binding" "list [a, b, c] = a b c" (Left ((InfiniteType "a" (TypArr (TypVar "a") (TypVar "b")))))

  testInferDefs "zipWith"
    ("zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys\n" <>
     "zipWith _ [] _ = []\n" <>
     "zipWith _ _ [] = []")
    (Right (Forall ("t_23" : "t_33" : "t_34" : Nil) (TypArr (TypArr (TypVar "t_23") (TypArr (TypVar "t_33") (TypVar "t_34"))) (TypArr (AD (TList (TypVar "t_23"))) (TypArr (AD (TList (TypVar "t_33"))) (AD (TList (TypVar "t_34"))))))))

  testInferDefs "foldr"
    ("foldr f ini [] = ini\n" <>
     "foldr f ini (x:xs) = f x (foldr f ini xs)")
    (Right (Forall ("t_4" : "t_7" : Nil) (TypArr (TypArr (TypVar "t_7") (TypArr (TypVar "t_4") (TypVar "t_4"))) (TypArr (TypVar "t_4") (TypArr (AD (TList (TypVar "t_7"))) (TypVar "t_4"))))))

  testInferDefs "scanl"
    ("scanl f b []     = [b]\n" <>
     "scanl f b (x:xs) = b : scanl f (f b x) xs")
    (Right (Forall ("t_39" : "t_48" : Nil) (TypArr (TypArr (TypVar "t_48") (TypArr (TypVar "t_39") (TypVar "t_48"))) (TypArr (TypVar "t_48") (TypArr (AD (TList (TypVar "t_39"))) (AD (TList (TypVar "t_48"))))))))

  testInferExprWithPrelude "Prelude with exp" "sum (map (^2) [1, 2, 3, 4])" (Right (Forall (Nil) (TypCon "Int")))

  -- Check that \f x -> f x and all the subexpressions are typed correctly.
  testInferTT "Apply function"
    (Lambda Nothing
      ((Lit Nothing (Name "f")) : (Lit Nothing (Name "x")) : Nil)
      (App
        Nothing
        (Atom Nothing (Name "f"))
        ((Atom Nothing (Name "x")) : Nil)))
    (Lambda
      (Just (typVarArrow "a" "b" `TypArr` typVarArrow "a" "b"))
      (
        (Lit (Just (typVarArrow "a" "b")) (Name "f")) :
        (Lit (Just (TypVar  "a")) (Name "x")) :
        Nil
      )
      (App
        (Just (TypVar  "b"))
        (Atom (Just (typVarArrow "a" "b")) (Name "f"))
        ((Atom (Just (TypVar  "a")) (Name "x")) : Nil)))

  -- Check that [1, 1 + 1, length [1]] and all the subexpressions are typed correctly.
  testInferTT "List"
    (List
      Nothing
      (
        (Atom Nothing (AInt 1)) :
        (Binary
          Nothing
          (Tuple Add Nothing)
          (Atom Nothing (AInt 1))
          (Atom Nothing (AInt 1))) :
        (App
          Nothing
          (Atom
            Nothing
            (Name "length"))
          (untypedListOne : Nil)) :
        Nil
      )
    )
    (List
      (Just (typConList "Int"))
      (
        (Atom (Just (TypCon "Int")) (AInt 1)) :
        (Binary
          (Just (TypCon "Int"))
          (Tuple Add (Just (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int"))))
          (Atom (Just (TypCon "Int")) (AInt 1))
          (Atom (Just (TypCon "Int")) (AInt 1))) :
        (App
          (Just (TypCon "Int"))
          (Atom
            (Just (typConList "Int" `TypArr` TypCon "Int"))
            (Name "length"))
          (listOne : Nil)) :
        Nil
      )
    )

  -- Check that (\(x:xs) -> x) [1] and all the subexpressions are typed correctly.
  testInferTT "ConsLit"
    (App
      Nothing
      (Lambda
        Nothing
        ((ConsLit
          Nothing
          (Lit Nothing (Name "x"))
          (Lit Nothing (Name "xs"))) : Nil)
        (Atom Nothing (Name "x")))
      (untypedListOne : Nil))
    (App
      (Just $ TypCon "Int")
      (Lambda
        (Just $ typConList "Int" `TypArr` TypCon "Int")
        ((ConsLit
          (Just $ typConList "Int")
          (Lit (Just $ TypCon "Int") (Name "x"))
          (Lit (Just $ typConList "Int") (Name "xs"))) : Nil)
        (Atom (Just $ TypCon "Int") (Name "x")))
      (listOne : Nil))

  -- Check that let x = [1] in [x] :: [[Int]] and all the subexpressions are typed correctly.
  testInferTT "Let"
    (LetExpr
      Nothing
      (Tuple (Lit Nothing (Name "x")) untypedListOne : Nil)
      (List Nothing (Atom Nothing (Name "x") : Nil)))
    (LetExpr
      (Just $ AD $ TList $ typConList "Int")
      (Tuple (Lit (Just $ typConList "Int") (Name "x")) listOne : Nil)
      (List
        (Just $ AD $ TList $ typConList "Int")
        (Atom (Just $ typConList "Int") (Name "x") : Nil)))

-- lit "a"
-- intLit "a"

  -- The type (Char, Int, Int)
  let charIntTupleType = typConNTuple ("Char" : "Int" : "Int" : Nil)
  -- The type (Int, Int)
  let intTupleType = typConNTuple ("Int" : "Int" : Nil)

  -- Check that (\(a,b) -> ('1',b,a)) (1,2) :: (Char, Int, Int) and all the subexpressions are
  -- typed correctly.
  testInferTT "Tuple and NTupleLit"
    (App
      Nothing
      (Lambda
        Nothing
        ((NTupleLit Nothing (
            Lit Nothing (Name "a") :
            Lit Nothing (Name "b") :
            Nil)) :
          Nil)
        (NTuple Nothing (
          Atom Nothing (Char "1") :
          Atom Nothing (Name "b") :
          Atom Nothing (Name "a") :
          Nil)))
      (NTuple Nothing (
          Atom Nothing (AInt 1) :
          Atom Nothing (AInt 2) :
          Nil) :
        Nil))
    (App
      (Just $ charIntTupleType)
      (Lambda
        (Just $ intTupleType `TypArr` charIntTupleType)
        ((NTupleLit (Just intTupleType) (
            Lit (Just intType) (Name "a") :
            Lit (Just intType) (Name "b") :
            Nil)) :
          Nil)
        (NTuple (Just charIntTupleType) (
          Atom (Just charType) (Char "1") :
          Atom (Just intType) (Name "b") :
          Atom (Just intType) (Name "a") :
          Nil)))
      (NTuple (Just intTupleType) (
          Atom (Just intType) (AInt 1) :
          Atom (Just intType) (AInt 2) :
          Nil) :
        Nil))

  -- Check that x :: t_42 == x :: a.
  testNormalizeTT "Atom"
    (Atom (Just $ TypVar "t_42") (Name "x"))
    (Atom (Just $ TypVar "a") (Name "x"))

  -- Check that an untyped atom stays untyped.
  testNormalizeTT "Untyped atom"
    (Atom Nothing (Name "x"))
    (Atom Nothing (Name "x"))

  -- Check that (\x -> x) :: t_2 -> t_2 == (\x -> x) :: a -> a.
  testNormalizeTT "Identity function"
    (Lambda
      (Just $ typVarArrow "t_2" "t_2")
      ((Lit (Just $ TypVar "t_2") (Name "x")) : Nil)
      (Atom (Just $ TypVar "t_2") (Name "x")))
    (Lambda
      (Just $ typVarArrow "a" "a")
      ((Lit (Just $ TypVar "a") (Name "x")) : Nil)
      (Atom (Just $ TypVar "a") (Name "x")))

  -- Check that (\f x -> f x) :: (t_4 -> t_45) -> t_4 -> t_45
  --         == (\f x -> f x) :: (a -> b) -> a -> b
  testNormalizeTT "Apply function"
    (Lambda
      (Just (typVarArrow "t_4" "t_45" `TypArr` typVarArrow "t_4" "t_45"))
      (
        (Lit (Just (typVarArrow "t_4" "t_45")) (Name "f")) :
        (Lit (Just (TypVar  "t_4")) (Name "x")) :
        Nil
      )
      (App
        (Just (TypVar  "t_45"))
        (Atom (Just (typVarArrow "t_4" "t_45")) (Name "f"))
        ((Atom (Just (TypVar  "t_4")) (Name "x")) : Nil)))
    (Lambda
      (Just (typVarArrow "a" "b" `TypArr` typVarArrow "a" "b"))
      (
        (Lit (Just (typVarArrow "a" "b")) (Name "f")) :
        (Lit (Just (TypVar  "a")) (Name "x")) :
        Nil
      )
      (App
        (Just (TypVar  "b"))
        (Atom (Just (typVarArrow "a" "b")) (Name "f"))
        ((Atom (Just (TypVar  "a")) (Name "x")) : Nil)))
