module Test.TypeChecker where

import AST
import TypeChecker (Scheme(Forall), inferGroup, inferType, inferDef, emptyTyenv, runInfer, typeProgramn, eqScheme, normalizeTypeTree)
import Parser (parseExpr, parseDefs)
import Test.Parser (parsedPrelude)

import Prelude (Unit, bind, pure, show, unit, ($), (==), (<>), (<<<))
import Control.Monad.Writer (Writer, tell)
import Data.Array (toUnfoldable) as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.List (List(..), (:), singleton)
import Text.Parsing.Parser (ParseError, parseErrorMessage)

-- | The result of the type inference procedure.
type InferResult = Either TypeError Scheme

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: forall a. a -> Writer (List a) Unit
tell' = tell <<< singleton

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
  Right expression -> compareSchemes name expected $ runInfer $ inferType emptyTyenv expression

testInferDef :: String -> String -> InferResult -> Writer (List String) Unit
testInferDef name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right (definition:_) -> compareSchemes name expected $ runInfer $ inferDef emptyTyenv definition
  _ -> tell' $ "Parse error for test case " <> name <> ": Expected only a single definition case"
    <> "\nNote that this is not a failing test but rather an error in the test definition."

testInferDefs :: String -> String -> InferResult -> Writer (List String) Unit
testInferDefs name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right definitions -> compareSchemes name expected $ runInfer $ inferGroup emptyTyenv definitions

testInferExprWithPrelude :: String -> String -> InferResult -> Writer (List String) Unit
testInferExprWithPrelude name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> compareSchemes name expected (typeProgramn parsedPrelude expression)

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
