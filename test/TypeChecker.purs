module Test.TypeChecker where

import AST
import TypeChecker (Scheme(Forall), inferGroup, inferType, inferDef, inferDefinition, inferDefinitions, emptyTypeEnv, runInfer, inferTypeNew, typeProgramn, normalizeTypeTree, typeTreeProgram,
    intType, intToIntType, intToIntToIntType, charType, ppScheme, schemeToType, runInferNew')
import Parser (parseExpr, parseDefs)
import Test.Parser (parsedPrelude)

import Prelude (Unit, bind, map, pure, show, unit, ($), (==), (<>), (<<<), (>>=))
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

-- | Construct a tuple type given a list of type variable names.
typVarTuple :: List TVar -> Type
typVarTuple tvs = AD $ TTuple (map TypVar tvs)

-- | Construct a list of type [a] given the type variable name a.
typVarList :: TVar -> Type
typVarList tv = AD $ TList (TypVar tv)

-- | Generate an arrow type from two given type variable names.
typVarArrow :: TVar -> TVar -> Type
typVarArrow tv1 tv2 = TypVar tv1 `TypArr` TypVar tv2

-- The type (Char, Int, Int)
charIntTupleType = typConNTuple ("Char" : "Int" : "Int" : Nil)
-- The type (Int, Int)
intTupleType = typConNTuple ("Int" : "Int" : Nil)

intList = AD $ TList $ TypCon "Int"

-- | Report a parse error.
reportParseError :: String -> ParseError -> Writer (List String) Unit
reportParseError testName parseError = tell' $ "Parse error for test case "
  <> testName <> ": "
  <> parseErrorMessage parseError
  <> "\nNote that this is not a failing test but rather an error in the test definition."

-- | Report a type error.
reportTypeError :: String -> TypeError -> Writer (List String) Unit
reportTypeError testName typeError = tell' $ "Type inference failed in test case `"
  <> testName <> "`:\n"
  <> "Encountered type error: "
  <> prettyPrintTypeError typeError

-- | Try to infer the type of a given expression and compare the result with the expected type.
testInferExpr :: String -> String -> Type -> Writer (List String) Unit
testInferExpr name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> case runInferNew' emptyTypeEnv true (inferAndConvertToType expression) of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t
  where
  inferAndConvertToType expr = inferTypeNew emptyTypeEnv expr >>= schemeToType

-- | Try to infer the type of a given expression and expect a type error to occur.
testInferExprFail :: String -> String -> TypeError -> Writer (List String) Unit
testInferExprFail name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> case runInferNew' emptyTypeEnv true (inferAndConvertToType expression) of
    Right t -> tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                       "Expected type error: " <> prettyPrintTypeError expected <> "\n" <>
                       "Found type: " <> prettyPrintType t <> "\n"
    Left typeError -> if typeError == expected
      then pure unit
      else tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                   "Expected type error: " <> prettyPrintTypeError typeError <> "\n" <>
                   "Actual type error: " <> prettyPrintTypeError expected <> "\n"
  where
  inferAndConvertToType expr = inferTypeNew emptyTypeEnv expr >>= schemeToType

-- | Compare the given two types and report an error if they are not equal.
compareTypes :: String -> Type -> Type -> Writer (List String) Unit
compareTypes testName expected actual = if expected == actual
  then pure unit
  else tell' $ "Type inference failed in test case `" <> testName <> "`:\n" <>
               "Expected type: " <> prettyPrintType expected <> "\n" <>
               "Actual type: " <> prettyPrintType actual

testInferDef :: String -> String -> Type -> Writer (List String) Unit
testInferDef name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right (def:_) -> case runInferNew' emptyTypeEnv true (inferAndConvertToType def) of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t
  _ -> tell' $ "Expected to parse definition in test case `" <> name <> "`\n" <>
               "\nNote that this is not a failing test but rather an error in the test definition."
  where
  inferAndConvertToType def = inferDefinition emptyTypeEnv def >>= schemeToType

testInferDefFail :: String -> String -> TypeError -> Writer (List String) Unit
testInferDefFail name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right (def:_) -> case runInferNew' emptyTypeEnv true (inferAndConvertToType def) of
    Left typeError -> if typeError == expected
      then pure unit
      else tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                   "Expected type error: " <> prettyPrintTypeError typeError <> "\n" <>
                   "Actual type error: " <> prettyPrintTypeError expected <> "\n"
    Right t -> tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                       "Expected type error: " <> prettyPrintTypeError expected <> "\n" <>
                       "Found type: " <> prettyPrintType t <> "\n"
  _ -> tell' $ "Expected to parse definition in test case `" <> name <> "`\n" <>
               "\nNote that this is not a failing test but rather an error in the test definition."
  where
  inferAndConvertToType def = inferDefinition emptyTypeEnv def >>= schemeToType

testInferDefGroup :: String -> String -> Type -> Writer (List String) Unit
testInferDefGroup name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right definitions -> case runInferNew' emptyTypeEnv true (inferAndConvertToType definitions) of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t
  where
  inferAndConvertToType defs = inferDefinitions emptyTypeEnv defs >>= schemeToType

testInferExprWithPrelude :: String -> String -> InferResult -> Writer (List String) Unit
testInferExprWithPrelude name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> compareSchemes name expected (typeProgramn parsedPrelude expression)

-- | Test type inference on expression trees, given an expression string as well as the expected
-- | resulting typed tree.
testInferTT' :: String -> String -> TypeTree -> Writer (List String) Unit
testInferTT' name unparsedTree expectedTypeTree = case parseExpr unparsedTree of
  Left parseError -> reportParseError name parseError
  Right expression -> testInferTT name expression expectedTypeTree

-- | Test type inference on expression trees. Here not only the expected type of the whole
-- | expression is checked, but also the type of every subexpression.
testInferTT :: String -> TypeTree -> TypeTree -> Writer (List String) Unit
testInferTT name untypedTree expectedTypedTree = case typeTreeProgram parsedPrelude untypedTree of
  Left typeError -> reportTypeError name typeError
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
eqInferResult (Left a) (Left a') = a == a'
eqInferResult (Right a) (Right a') = a == a'
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

runTests :: Writer (List String) Unit
runTests = do

  -- +--------------------------------------------------+
  -- | Test the inferred types of arbitrary expressions |
  -- +--------------------------------------------------+

  -- (3^) :: Int -> Int
  testInferExpr "SectL" "(3^)" intToIntType
  -- (^3) :: Int -> Int
  testInferExpr "SectR" "(^3)" intToIntType
  -- (\a b c d -> a b c d) :: (a -> b -> c -> d) -> a -> b -> c -> d
  testInferExpr "Lambda1" "\\a b c d -> a b c d"
    ((TypVar "a" `TypArr` (TypVar "b" `TypArr` (TypVar "c" `TypArr` TypVar "d"))) `TypArr`
      (TypVar "a" `TypArr` (TypVar "b" `TypArr` (TypVar "c" `TypArr` (TypVar "d")))))
  testInferExpr "Lambda2" "\\a b -> a b"
    (TypArr (TypArr (TypVar "a") (TypVar "b")) (TypArr (TypVar "a") (TypVar "b")))
  testInferExpr "List1" "[1, 2, 3, 4, 5]" intList
  testInferExpr "List2" "[1 + 2, 3 + 4]" intList
  testInferExpr "Empty list" "[]" (typVarList "a")
  testInferExpr "Append" "[1 + 2, 3 + 4] ++ []" intList
  testInferExpr "NTuple" "(1 + 2, 3)" (typConNTuple ("Int" : "Int" : Nil))
  testInferExpr "SectR colon" "(:[3])" (TypCon "Int" `TypArr` intList)
  testInferExpr "Lambda wildcard" "\\_ _ -> 5" (TypVar "a" `TypArr` (TypVar "b" `TypArr` intType))
  testInferExpr "Lambda cons binding" "\\(x:xs) -> x" (typVarList "a" `TypArr` TypVar "a")
  testInferExpr "Let expression" "let x = 3 in \\_ _ -> x"
    (TypVar "a" `TypArr` (TypVar "b" `TypArr` intType))
  testInferExpr "Binding tuple in let expression" "let (a, b) = (\\f -> f, \"Hello\") in a b"
    (typConList "Char")
  testInferExpr "Lambda application" "(\\f a b -> f a b) (+) 3 4" intType
  -- ((\xs -> [ x | x <- xs ]) [1]) :: [Int]
  testInferExpr "List comprehension inside lambda" "(\\xs -> [ x | x <- xs ]) [1]" intList

  -- testInferExprFail "List3" "[(+), 4]" (UnificationFail (TypCon "Int") (TypArr (TypCon "Int") (TypArr (TypCon "Int") (TypCon "Int"))))
  -- testInferExprFail "Colon" "3 : [1 + 2, 3 + 4, \"Hallo\"]" (Left ((UnificationFail (AD $ TList $ TypCon "Char") (TypCon "Int"))))

  -- +-----------------------------------------------+
  -- | Test the inferred types of single definitions |
  -- +-----------------------------------------------+

  testInferDef "Define app" "app f xs = app f xs"
    (TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "c"))
  testInferDef "Define single map" "map f (x:xs) = f x : map f xs"
    ((TypVar "a" `TypArr` TypVar "b") `TypArr` (typVarList "a" `TypArr` typVarList "b"))
  testInferDef "Define foldr" "foldr f ini (x:xs) = f x (foldr f ini xs)"
    ((TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "b")) `TypArr`
      (TypVar "c" `TypArr` (typVarList "a" `TypArr` TypVar "b")))
  testInferDef "Conslit binding 1" "list (x:xs:xss) = x" (typVarList "a" `TypArr` TypVar "a")
  testInferDef "Conslit binding 2" "list (x:xs:xss) = xs" (typVarList "a" `TypArr` TypVar "a")
  testInferDef "Conslit binding 3" "list (x:xs:xss) = xss" (typVarList "a" `TypArr` typVarList "a")
  testInferDef "Binding tuple 1" "fst (a, b) = a"
    (typVarTuple ("a" : "b" : Nil) `TypArr` TypVar "a")
  testInferDef "Binding tuple 2" "snd (a, b) = b"
    (typVarTuple ("a" : "b" : Nil) `TypArr` TypVar "b")
  testInferDef "Binding tuple 3" "f (a, b, c) = a b c"
    ((AD $ TTuple
      (TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "c") : TypVar "a" : TypVar "b" : Nil))
        `TypArr` TypVar "c")

  --testInferDef "Listlit binding" "list [a, b, c] = a b c" intType
    --(InfiniteType "a" (TypVar "a" `TypArr` TypVar "b"))

  -- +----------------------------------------------+
  -- | Test the inferred types of definition groups |
  -- +----------------------------------------------+

  let zipWithDef = "zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys\n" <>
                   "zipWith _ [] _ = []\n" <>
                   "zipWith _ _ [] = []"
  testInferDefGroup "zipWith" zipWithDef
    ((TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "c")) `TypArr`
      (typVarList "a" `TypArr` (typVarList "b" `TypArr` typVarList "c")))

  let foldrDef = "foldr f ini [] = ini\n" <>
                 "foldr f ini (x:xs) = f x (foldr f ini xs)"
  testInferDefGroup "foldr" foldrDef
    ((TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "b"))
      `TypArr` (TypVar "b" `TypArr` (typVarList "a" `TypArr` TypVar "b")))

  let scanlDef = "scanl f b []     = [b]\n" <>
                 "scanl f b (x:xs) = b : scanl f (f b x) xs"
  testInferDefGroup "scanl" scanlDef
    ((TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "a"))
      `TypArr` (TypVar "a" `TypArr` (typVarList "b" `TypArr` typVarList "a")))

  -- +-------------------------------------------------------------------+
  -- | Test the inferred types of expressions in the prelude environment |
  -- +-------------------------------------------------------------------+

  -- TODO:
  -- testInferExprWithPrelude "Prelude with exp" "sum (map (^2) [1, 2, 3, 4])" intType

  -- +----------------------------------------+
  -- | Test the type inference on whole trees |
  -- +----------------------------------------+

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

  -- +-----------------------------+
  -- | Test the tree normalization |
  -- +-----------------------------+

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
