module Test.TypeChecker where

import AST
import TypeChecker as TC
import TypeChecker (Scheme(..), TVarMappings, boolType, charType, intType,
  intToIntType, intToIntToIntType)
import Parser (parseExpr, parseDefs)
import Test.Parser (parsedPrelude)

import Prelude (Unit, bind, map, pure, show, unit, ($), (==), (<>), (>>=), (<$>))
-- import Control.Monad.Writer (Writer, tell)
import Data.Array as Array
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)
import Data.Foldable (intercalate)
import Text.Parsing.Parser (ParseError, parseErrorMessage)

import Control.Semigroupoid ((>>>), (<<<))

import Test.Utils (Test, tell)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: String -> Test Unit
tell' = tell

-- | Construct a list of type [typCon] given the name of the type constants.
typConList :: String -> Type
typConList name = TList (TypCon name)

-- | Construct a tuple type given a list of type constant names.
typConNTuple:: List String -> Type
typConNTuple names = TTuple (map TypCon names)

-- | Construct a tuple type given a list of type variable names.
typVarTuple :: List TVar -> Type
typVarTuple tvs = TTuple (map TypVar tvs)

-- | Construct a list of type [a] given the type variable name a.
typVarList :: TVar -> Type
typVarList tv = TList (TypVar tv)

-- | Generate an arrow type from two given type variable names.
typVarArrow :: TVar -> TVar -> Type
typVarArrow tv1 tv2 = TypVar tv1 `TypArr` TypVar tv2

-- | The type (Char, Int, Int)
charIntTupleType :: Type
charIntTupleType = typConNTuple ("Char" : "Int" : "Int" : Nil)

-- | The type (Int, Int)
intTupleType :: Type
intTupleType = typConNTuple ("Int" : "Int" : Nil)

-- | The type [Int]
intList :: Type
intList = TList $ TypCon "Int"

-- | Report a parse error.
reportParseError :: String -> ParseError -> Test Unit
reportParseError testName parseError = tell' $ "Parse error for test case "
  <> testName <> ": "
  <> parseErrorMessage parseError
  <> "\nNote that this is not a failing test but rather an error in the test definition."

-- | Report a type error.
reportTypeError :: String -> TypeError -> Test Unit
reportTypeError testName typeError = tell' $ "Type inference failed in test case `"
  <> testName <> "`:\n"
  <> "Encountered type error: "
  <> prettyPrintTypeError typeError

reportTypeErrorWithNote :: String -> TypeError -> String -> Test Unit
reportTypeErrorWithNote testName typeError note =
  tell' $ "Type inference failed in test case `"
    <> testName <> "`:\n"
    <> "Encountered Type error: "
    <> prettyPrintTypeError typeError
    <> "Additional Note: \n"
    <> note

-- | Compare the given two types and report an error if they are not equal.
compareTypes :: String -> Type -> Type -> Test Unit
compareTypes testName expected actual = if expected == actual
  then pure unit
  else tell' $ "Type inference failed in test case `" <> testName <> "`:\n" <>
               "Expected type: " <> prettyPrintType expected <> "\n" <>
               "Actual type: " <> prettyPrintType actual

compareTypesWithNote :: String -> Type -> Type -> String -> Test Unit
compareTypesWithNote testName expected actual note = if expected == actual
  then pure unit
  else tell' $ "Type inference failed in test case `" <> testName <> "`:\n" <>
               "Expected type: " <> prettyPrintType expected <> "\n" <>
               "Actual type: " <> prettyPrintType actual <> "\n" <>
               "Additional note: \n" <> note

-- | Compare the given type errors and report an error if they are not equal.
compareTypeError :: String -> TypeError -> TypeError -> Test Unit
compareTypeError testName expected actual = if expected == actual
  then pure unit
  else tell' $ "Type inference failed in test case `" <> testName <> "`:\n" <>
               "Expected type error: " <> prettyPrintTypeError expected <> "\n" <>
               "Actual type error: " <> prettyPrintTypeError actual <> "\n"

-- | Try to infer the type of a given expression and compare the result with the expected type.
testInferExpr :: String -> String -> Type -> Test Unit
testInferExpr name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> case TC.runInfer true (TC.inferExprToType expression) of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t

-- | Try to infer the type of a given expression and expect a type error to occur.
testInferExprFail :: String -> String -> TypeError -> Test Unit
testInferExprFail name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> case TC.runInfer true (TC.inferExprToType expression) of
    Right t -> tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                       "Expected type error: " <> prettyPrintTypeError expected <> "\n" <>
                       "Found type: " <> prettyPrintType t <> "\n"
    Left typeError -> compareTypeError name expected typeError

testInferDef :: String -> String -> Type -> Test Unit
testInferDef name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right (def:_) -> case TC.runInfer true (inferAndConvertToType def) of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t
  _ -> tell' $ "Expected to parse definition in test case `" <> name <> "`\n" <>
               "\nNote that this is not a failing test but rather an error in the test definition."
  where
  inferAndConvertToType def = TC.schemeOfDefinition def >>= TC.schemeToType

testInferDefFail :: String -> String -> TypeError -> Test Unit
testInferDefFail name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right (def:_) -> case TC.runInfer true (inferAndConvertToType def) of
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
  inferAndConvertToType def = TC.schemeOfDefinition def >>= TC.schemeToType

testInferDefGroup :: String -> String -> Type -> Test Unit
testInferDefGroup name definitionString expected = case parseDefs definitionString of
  Left parseError -> reportParseError name parseError
  Right definitions -> case TC.runInfer true (inferAndConvertToType definitions) of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t
  where
  inferAndConvertToType defs = TC.schemeOfDefinitionGroup defs >>= TC.schemeToType

-- | Infer the type of the given expression in the context of the prelude.
testInferExprWithPrelude :: String -> String -> Type -> Test Unit
testInferExprWithPrelude name expressionString expected = case parseExpr expressionString of
  Left parseError -> reportParseError name parseError
  Right expression -> case TC.tryInferTypeInContext parsedPrelude expression of
    Left typeError -> reportTypeError name typeError
    Right t -> compareTypes name expected t
    

-- | Infer the type of the given expression in the context of a custom prelude.
testInferExprWithCustomPrelude :: String -> String -> String -> Type -> Test Unit
testInferExprWithCustomPrelude name prelude expressionString expected =
  case parseDefs prelude of
    Left parseError -> reportParseError name parseError
    Right parsedPrelude ->
      case parseExpr expressionString of
        Left parseError -> reportParseError name parseError
        Right expression -> case TC.tryInferTypeInContext parsedPrelude expression of
          Left typeError -> do
            reportTypeError name typeError
          Right t -> compareTypesWithNote name expected t
            (case TC.ppTypeEnv <$> TC.tryInferEnvironment parsedPrelude of
              Left msg -> show msg
              Right msg -> msg)

-- | Test type inference on expression trees, given an expression string as well as the expected
-- | resulting typed tree.
testInferTT' :: String -> String -> TypeTree -> Test Unit
testInferTT' name unparsedTree expectedTypeTree = case parseExpr unparsedTree of
  Left parseError -> reportParseError name parseError
  Right expression -> testInferTT name expression expectedTypeTree

testInferTTWithCustomPrelude' :: String -> String -> String -> TypeTree -> Test Unit
testInferTTWithCustomPrelude' name prelude unparsedTree expectedTypeTree =
  case parseDefs prelude of
    Left parseError -> reportParseError name parseError
    Right parsedPrelude -> case parseExpr unparsedTree of
      Left parseError -> reportParseError name parseError
      Right expression -> testInferTTWithCustomPrelude name parsedPrelude expression expectedTypeTree

-- | Test type inference on expression trees. Here not only the expected type of the whole
-- | expression is checked, but also the type of every subexpression.
testInferTT :: String -> TypeTree -> TypeTree -> Test Unit
testInferTT name untypedTree expectedTypedTree =
  case TC.tryInferExprInContext parsedPrelude untypedTree of
    Left typeError -> reportTypeError name typeError
    Right typedTree -> if expectedTypedTree == typedTree
      then pure unit
      else tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                   "Expected type tree: " <> show expectedTypedTree <> "\n" <>
                   "Actual type tree: " <> show typedTree <> "\n"

testInferTTWithCustomPrelude :: String -> List Definition -> TypeTree -> TypeTree -> Test Unit
testInferTTWithCustomPrelude name parsedPrelude untypedTree expectedTypedTree =
  case TC.tryInferExprInContext parsedPrelude untypedTree of
    Left typeError -> reportTypeError name typeError
    Right typedTree -> if expectedTypedTree == typedTree
      then pure unit
      else tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
                   "Expected type tree: " <> show expectedTypedTree <> "\n" <>
                   "Actual type tree: " <> show typedTree <> "\n"

testInferTTFail :: String -> TypeTree -> TypeError -> Test Unit
testInferTTFail name expr expectedError =
  case TC.tryInferExprInContext parsedPrelude expr of
    Left typeError -> compareTypeError name expectedError typeError
    Right typedExpr ->
      tell' $ "Type inference failed in test case `" <> name <> "`:\n" <>
              "Expected type error: " <> prettyPrintTypeError expectedError <> "\n" <>
              "Found type tree: " <> show typedExpr <> "\n"

-- | Test type tree normalization.
testNormalizeTT :: String -> TypeTree -> TypeTree -> Test Unit
testNormalizeTT name tt normalizedTT = if (TC.normalizeTypeTree tt) == normalizedTT
  then pure unit
  else tell' $ "Type tree normalization failed in test case `" <> name <> "`:\n" <>
               "Expected type tree: " <> show normalizedTT <> "\n" <>
               "Actual type tree: " <> show tt <> "\n"

-- | Test the function `mapSchemeOnTVarMappings`.
testMapSchemeOnTVarMappings :: String -> Scheme -> IndexedTypedBinding
                            -> TVarMappings -> Test Unit
testMapSchemeOnTVarMappings name scheme binding expected =
  case TC.runInfer true (fst <$> TC.mapSchemeOnTVarMappings binding scheme) of
    Left typeError -> reportTypeError name typeError
    Right result -> if result == expected
      then pure unit
      else tell' $
        "The function `mapSchemeOnTVarMappings` failed in test case `" <> name <> "`:\n" <>
        "Expected type variable mapping: " <> TC.ppTVarMappings expected <> "\n" <>
        "Actual type variable mapping: " <> TC.ppTVarMappings result <> "\n"

-- | Test the function `mapSchemeOnTVarMappings`.
testMapSchemeOnTVarMappings' :: String -> String -> Scheme -> IndexedTypedBinding
                            -> TVarMappings -> Test Unit
testMapSchemeOnTVarMappings' name prelude scheme binding expected =
  case parseDefs prelude of
    Left parseError -> reportParseError name parseError
    Right parsedPrelude -> case TC.tryInferEnvironment parsedPrelude of
      Left typeError -> reportTypeError name typeError
      Right env -> case TC.runInferWith env true (fst <$> TC.mapSchemeOnTVarMappings binding scheme) of
        Left typeError -> reportTypeError name typeError
        Right result -> if result == expected
          then pure unit
          else tell' $
            "The function `mapSchemeOnTVarMappings` failed in test case `" <> name <> "`:\n" <>
            "Scheme: " <> TC.ppScheme scheme <> "\n" <>
            "Binding: " <> prettyPrintBinding binding <> "\n" <>
            "Expected type variable mapping: " <> TC.ppTVarMappings expected <> "\n" <>
            "Actual type variable mapping: " <> TC.ppTVarMappings result <> "\n" <>
            "Environment:\n" <> TC.ppTypeEnv env <> "\n"

-- | Typed type tree representing `[1]`.
listOne :: TypeTree
listOne = List (Just $ typConList "Int") (Atom (Just $ TypCon "Int") (AInt 1) : Nil)

-- | Untyped type tree representing `[1]`.
untypedListOne :: TypeTree
untypedListOne = List Nothing (Atom Nothing (AInt 1) : Nil)

partiallyTypedExprTests :: Test Unit
partiallyTypedExprTests = do
  -- Test that ((2 :: Int) + 4) is typed correctly.
  testInferTT "Partially typed"
    (Binary
      Nothing
      (Tuple Add Nothing)
      (Atom (Just intType) (AInt 2))
      (Atom Nothing (AInt 4))
    )
    (Binary
      (Just (TypCon "Int"))
      (Tuple Add (Just (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int"))))
      (Atom (Just intType) (AInt 2))
      (Atom (Just intType) (AInt 4))
    )

  -- Test that ((2 :: Char) + 4) results in a type error.
  testInferTTFail "Partially typed"
    (Binary
      Nothing
      (Tuple Add Nothing)
      (Atom (Just charType) (AInt 2))
      (Atom Nothing (AInt 4))
    )
    (UnificationFail intType charType)

  -- Test that `let (f :: Int -> Int) = \x -> x in f True` results in a type error.
  testInferTTFail "Partially typed let expression 1"
    (LetExpr
      Nothing
      (
        Tuple (Lit (Just intToIntType) (Name "f"))
          (Lambda Nothing
            ((Lit Nothing (Name "x")) : Nil)
            (Atom Nothing (Name "x"))) :
        Nil
      )
      (App
        Nothing
        (Atom Nothing (Name "f"))
        ((Atom Nothing (Bool true)) : Nil)
      )
    )
    (UnificationFail intType boolType)

  -- Test that `let f = ((\x -> x) :: Int -> Int) in f True` results in a type error.
  testInferTTFail "Partially typed let expression 2"
    (LetExpr
      Nothing
      (
        Tuple (Lit Nothing (Name "f"))
          (Lambda (Just intToIntType)
            ((Lit Nothing (Name "x")) : Nil)
            (Atom Nothing (Name "x"))) :
        Nil
      )
      (App
        Nothing
        (Atom Nothing (Name "f"))
        ((Atom Nothing (Bool true)) : Nil)
      )
    )
    (UnificationFail intType boolType)

  -- Test that `(\(a :: Bool) b -> a)) 'x'` results in a type error.
  testInferTTFail "Partially typed lambda expression 1"
    (App
      Nothing
      (Lambda
        Nothing
        ((Lit (Just boolType) (Name "a")) : (Lit Nothing (Name "b")) : Nil)
        (Atom Nothing (Name "a"))
      )
      ((Atom Nothing (Char "x")) : Nil)
    )
    (UnificationFail boolType charType)

  -- Test that `(\(x:(y :: Char):ys) -> mod x y)` results in a type error.
  testInferTTFail "Partially typed lambda expression 1"
    (Lambda
      Nothing
        (
          (ConsLit
            Nothing
            (Lit Nothing (Name "x"))
            (ConsLit
              Nothing
              (Lit (Just charType) (Name "y"))
              (Lit Nothing (Name "ys"))
            ) : Nil
          )
        )
        (App
          Nothing
          (Atom Nothing (Name "mod"))
          (Atom Nothing (Name "x") : Atom Nothing (Name "y") : Nil)
        )
    )
    (UnificationFail intType charType)

runTests :: Test Unit
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

  -- Check that let polymorphism works: `let f = \x -> x in (f True, f 42)` :: (Bool, Int).
  testInferExpr "Let polymorphism" "let f = \\x -> x in (f True, f 42)"
    (TTuple (boolType : intType : Nil))

  testInferExprFail "List unification fail" "[(+), 4]" (UnificationFail intToIntToIntType intType)
  testInferExprFail "Cons unification fail"
    "let str = \"Hallo\" in 3 : [1 + 2, 3 + 4, str]"
    (UnificationFail intType (TList charType))

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
    ((TTuple
      (TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "c") : TypVar "a" : TypVar "b" : Nil))
        `TypArr` TypVar "c")

  testInferDefFail "Listlit binding" "list [a, b, c] = a b c"
    (InfiniteType "a" (TypVar "a" `TypArr` (TypVar "b" `TypArr` TypVar "c")))

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

  testInferExprWithPrelude "Prelude with exp" "sum (map (^2) [1, 2, 3, 4])" intType

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
      (Just $ TList $ typConList "Int")
      (Tuple (Lit (Just $ typConList "Int") (Name "x")) listOne : Nil)
      (List
        (Just $ TList $ typConList "Int")
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

  -- Check that (\(x, y) -> x) :: (t_10, t_2) -> t_10
  --         == (\(x, y) -> x) :: (a, b) -> a
  testNormalizeTT "Normalization: Tuple binding in lambda"
    (Lambda
      (Just (typVarTuple ("t_10" : "t_2" : Nil) `TypArr` TypVar "t_10"))
      (
        (NTupleLit (Just (typVarTuple ("t_10" : "t_2" : Nil)))
          (
            (Lit (Just (TypVar "t_10")) (Name "x")) :
            (Lit (Just (TypVar "t_2")) (Name "y")) :
            Nil
          )
        ) : Nil
      )
      (Atom (Just (TypVar "t_10")) (Name "x"))
    )
    (Lambda
      (Just (typVarTuple ("a" : "b" : Nil) `TypArr` TypVar "a"))
      (
        (NTupleLit (Just (typVarTuple ("a" : "b" : Nil)))
          (
            (Lit (Just (TypVar "a")) (Name "x")) :
            (Lit (Just (TypVar "b")) (Name "y")) :
            Nil
          )
        ) : Nil
      )
      (Atom (Just (TypVar "a")) (Name "x"))
    )

  -- Check that (\(x:xs) [a,b] (u,v,w) -> x) :: [t_4] -> [t_2] -> (t_1, t_3, t_5) -> t_4
  --         == (\(x:xs) [a,b] (u,v,w) -> x) :: [a] -> [b] -> (c, d, e) -> a
  testNormalizeTT "Normalization: Tuple binding in lambda"
    (Lambda
      -- :: [t_4] -> [t_2] -> (t_1, t_3, t_5) -> t_4
      (Just
        (typVarList "t_4" `TypArr`
          (typVarList "t_2" `TypArr`
            (typVarTuple ("t_1" : "t_3" : "t_5" : Nil)) `TypArr`
              TypVar "t_4")))
      (
        -- (x:xs) [a,b] (u,v,w)
        (ConsLit (Just (typVarList "t_4"))
          (Lit (Just (TypVar "t_4")) (Name "x"))
          (Lit (Just (typVarList "t_4")) (Name "xs"))
        ) :
        (ListLit (Just (typVarList "t_2"))
          (
            (Lit (Just (TypVar "t_2")) (Name "a")) :
            (Lit (Just (TypVar "t_2")) (Name "b")) :
            Nil
          )
        ) :
        (NTupleLit (Just (typVarTuple ("t_1" : "t_3" : "t_5" : Nil)))
          (
            (Lit (Just (TypVar "t_1")) (Name "u")) :
            (Lit (Just (TypVar "t_3")) (Name "v")) :
            (Lit (Just (TypVar "t_5")) (Name "w")) :
            Nil
          )
        ) :
        Nil
      )
      (Atom (Just (TypVar "t_4")) (Name "x"))
    )
    (Lambda
      -- :: [a] -> [b] -> (c, d, e) -> a
      (Just
        (typVarList "a" `TypArr`
          (typVarList "b" `TypArr`
            (typVarTuple ("c" : "d" : "e" : Nil)) `TypArr`
              TypVar "a")))
      (
        -- (x:xs) [a,b] (u,v,w)
        (ConsLit (Just (typVarList "a"))
          (Lit (Just (TypVar "a")) (Name "x"))
          (Lit (Just (typVarList "a")) (Name "xs"))
        ) :
        (ListLit (Just (typVarList "b"))
          (
            (Lit (Just (TypVar "b")) (Name "a")) :
            (Lit (Just (TypVar "b")) (Name "b")) :
            Nil
          )
        ) :
        (NTupleLit (Just (typVarTuple ("c" : "d" : "e" : Nil)))
          (
            (Lit (Just (TypVar "c")) (Name "u")) :
            (Lit (Just (TypVar "d")) (Name "v")) :
            (Lit (Just (TypVar "e")) (Name "w")) :
            Nil
          )
        ) :
        Nil
      )
      (Atom (Just (TypVar "a")) (Name "x"))
    )

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
        ((Atom (Just (TypVar  "t_4")) (Name "x")) : Nil)
      )
    )
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
        ((Atom (Just (TypVar  "a")) (Name "x")) : Nil)
      )
    )

  -- Map scheme `Int` on `x`. We expect the type variable mapping { x = Int }.
  testMapSchemeOnTVarMappings
    "Map scheme on literal binding"
    (Forall Nil intType)
    (Lit (Tuple Nothing 0) (Name "x"))
    (Tuple "x" (Forall Nil intType) : Nil)

  -- Map scheme `forall t_4. (t_4 -> t_4, (Int, Bool)) on `(f, (n, b))`. We expect the mapping
  -- { f = forall t_4. t_4 -> t_4, n = Int, b = Bool }.
  testMapSchemeOnTVarMappings
    "Map scheme on tuple"
    -- The scheme: forall t_4. (t_4 -> t_4, (Int, Bool))
    (Forall ("t_4" : Nil)
      (TTuple (typVarArrow "t_4" "t_4" :
        (TTuple (intType : boolType : Nil)) : Nil))
    )
    -- The binding: (f, (n, b))
    (NTupleLit (Tuple Nothing 1)
      (
        (Lit (Tuple Nothing 2) (Name "f")) :
        (NTupleLit (Tuple Nothing 3)
          (
            (Lit (Tuple Nothing 4) (Name "n")) :
            (Lit (Tuple Nothing 5) (Name "b")) :
            Nil
          )
        ) :
        Nil
      )
    )
    -- The expected result: { f = forall t_4. t_4 -> t_4, n = Int, b = Bool }
    (
      (Tuple "f" (Forall ("t_4" : Nil) (typVarArrow "t_4" "t_4"))) :
      (Tuple "n" (Forall Nil intType)) :
      (Tuple "b" (Forall Nil boolType)) :
      Nil
    )


  partiallyTypedExprTests
  adtTests

adtPrelude :: String
adtPrelude = """
data Unit = Unit

data Bool = T | F

useless T = Unit
useless F = Unit

data Tuple a b = Tuple a b

data Maybe a = Just a | Nothing

tuple a b = (a,b)

fst (Tuple a b) = a
snd (Tuple a b) = b

data Id a = Id a

id a = a

tuple' a = Tuple a a

data Complex a
  = a :+ a
"""

myTuple idx l r = ConstrLit (Tuple Nothing idx) (PrefixDataConstr "Tuple" 2 (l:r:Nil))
myTupleT l r = TTypeCons "Tuple" (l:r:Nil)

myId idx c = ConstrLit (Tuple Nothing idx) (PrefixDataConstr "Id" 1 (c:Nil))
myIdT c = TTypeCons "Id" (c:Nil)

myMaybeT c = TTypeCons "Maybe" (c:Nil)

myComplexT c = TTypeCons "Complex" (c:Nil)

myComplex idx a b =
  ConstrLit
    (Tuple Nothing idx)
    (InfixDataConstr ":+" LEFTASSOC 9 a b)

adtTests :: Test Unit
adtTests = do
  testInferTTWithCustomPrelude' "adt-params-3-1"
    adtPrelude
    "Id"
    (Atom
      (Just
        (TypArr
          (TypVar "a")
          (TTypeCons "Id" (TypVar "a":Nil))))
      (Constr "Id"))

  testInferExprWithCustomPrelude "adt-0-ary-1"
    adtPrelude
    "Unit"
    (TTypeCons "Unit" Nil)

  testInferExprWithCustomPrelude "adt-0-ary-2"
    adtPrelude
    "T"
    (TTypeCons "Bool" Nil)

  testInferExprWithCustomPrelude "adt-0-ary-3"
    adtPrelude
    "F"
    (TTypeCons "Bool" Nil)

  testInferExprWithCustomPrelude "adt-0-ary-4"
    adtPrelude
    "useless"
    (TypArr (TTypeCons "Bool" Nil) (TTypeCons "Unit" Nil))

  testInferExprWithCustomPrelude "adt-params-1-1"
    adtPrelude
    "fst (Tuple T F)"
    (TTypeCons "Bool" Nil)

  testInferExprWithCustomPrelude "adt-params-1-2"
    adtPrelude
    "snd (Tuple T F)"
    (TTypeCons "Bool" Nil)

  testInferExprWithCustomPrelude "adt-params-1-3"
    adtPrelude
    "snd (Tuple 1 2)"
    intType

  testInferExprWithCustomPrelude "adt-params-1-4"
    adtPrelude
    "fst"
    (TypArr
      (TTypeCons "Tuple" (TypVar "a" : TypVar "b" : Nil))
      (TypVar "a"))

  testInferExprWithCustomPrelude "adt-params-1-5"
    adtPrelude
    "snd"
    (TypArr
      (TTypeCons "Tuple" (TypVar "a" : TypVar "b" : Nil))
      (TypVar "b"))

  testInferExprWithCustomPrelude "adt-params-1-6"
    adtPrelude
    "Tuple 1 2"
    (TTypeCons "Tuple" (intType : intType : Nil))

  testInferExprWithCustomPrelude "adt-params-1-7"
    adtPrelude
    "Tuple 1"
    (TypArr
      (TypVar "a")
      (TTypeCons "Tuple" (intType : TypVar "a" : Nil)))

  testInferExprWithCustomPrelude "adt-params-1-8"
    adtPrelude
    "Tuple Unit Unit"
    (TTypeCons "Tuple" (TTypeCons "Unit" Nil:TTypeCons "Unit" Nil:Nil))

  testInferExprWithCustomPrelude "adt-params-1-9"
    adtPrelude
    "Nothing"
    (myMaybeT (TypVar "a"))

  testInferExprWithCustomPrelude "adt-params-1-10"
    adtPrelude
    "Just"
    (TypArr
      (TypVar "a")
      (myMaybeT (TypVar "a")))

  testInferExprWithCustomPrelude "adt-params-1-11"
    adtPrelude
    "Just Nothing"
    (myMaybeT (myMaybeT (TypVar "a")))

  testInferExprWithCustomPrelude "adt-params-1-12"
    adtPrelude
    "Just (1,2)"
    (myMaybeT (TTuple (intType:intType:Nil)))

  testInferExprWithCustomPrelude "adt-params-2-1"
    adtPrelude
    "Tuple"
    (TypArr
      (TypVar "a")
      (TypArr
        (TypVar "b")
        (TTypeCons "Tuple"
          (Cons (TypVar "a")
            (Cons (TypVar "b") Nil)))))

  testInferExprWithCustomPrelude "adt-params-2-2"
    adtPrelude
    "Id"
    (TypArr (TypVar "a") (TTypeCons "Id" (TypVar "a":Nil)))

  testInferExprWithCustomPrelude "adt-params-2-3"
    adtPrelude
    "Id id"
    (TTypeCons "Id" (TypArr (TypVar "a") (TypVar "a"):Nil))

  testInferExprWithCustomPrelude "adt-params-2-4"
    adtPrelude
    "tuple'"
    (TypArr (TypVar "a") (TTypeCons "Tuple" (TypVar "a":TypVar "a":Nil)))

  testInferExprWithCustomPrelude "adt-params-2-5"
    adtPrelude
    "tuple' 1"
    (TTypeCons "Tuple" (intType:intType:Nil))

  testInferExprWithCustomPrelude "adt-params-2-6"
    adtPrelude
    "Id Tuple"
    (myIdT
      (TypArr
        (TypVar "a")
        (TypArr
          (TypVar "b")
          (myTupleT (TypVar "a") (TypVar "b")))))


  testMapSchemeOnTVarMappings' "adt-map-scheme-1-1"
    adtPrelude
    (Forall ("t_1":Nil)
      (TTypeCons "Id" (TypVar "t_1":Nil)))
    (ConstrLit
      (Tuple Nothing 0)
      (PrefixDataConstr "Id" 1
        (Lit
          (Tuple Nothing 1)
          (Name "x")
        :Nil)))
    (Tuple "x" (Forall ("t_1":Nil) (TypVar "t_1"))
    :Nil)

  testMapSchemeOnTVarMappings' "adt-map-scheme-1-2"
    adtPrelude
    (Forall Nil
      (TTypeCons "Id" (TTypeCons "Unit" Nil:Nil)))
    (ConstrLit
      (Tuple Nothing 0)
      (PrefixDataConstr "Id" 1
        (Lit
          (Tuple Nothing 1)
          (Name "x")
        :Nil)))
    (Tuple "x" (Forall Nil (TTypeCons "Unit" Nil))
    :Nil)

  testMapSchemeOnTVarMappings' "adt-map-scheme-1-3"
    adtPrelude
    (Forall Nil
    (TTypeCons "Id" (intType:Nil)))
    (ConstrLit
      (Tuple Nothing 0)
      (PrefixDataConstr "Id" 1
        (Lit
          (Tuple Nothing 1)
          (Name "x")
        :Nil)))
    (Tuple "x" (Forall Nil intType)
    :Nil)

  testMapSchemeOnTVarMappings' "adt-map-scheme-1-4"
    adtPrelude
    (Forall ("id":Nil)
      (TypArr
        (TypVar "id")
        (TTypeCons "Id" (TypVar "id":Nil))))

    (Lit (Tuple Nothing 0) (Name "id"))

    (Tuple "id"
      (Forall ("id":Nil)
        (TypArr
          (TypVar "id")
          (TTypeCons "Id" (TypVar "id":Nil))))
    :Nil)
    
  testMapSchemeOnTVarMappings' "adt-map-scheme-1-5"
    adtPrelude
    -- The scheme: forall t_4. Tuple (t_4 -> t_4) (Tuple Int Bool)
    (Forall ("t_4" : Nil)
      (myTupleT
        (typVarArrow "t_4" "t_4")
        (myTupleT intType boolType)))
    -- The binding: (f, (n, b))
    (myTuple 1
        (Lit (Tuple Nothing 2) (Name "f"))
        (myTuple 2
          (Lit (Tuple Nothing 4) (Name "n"))
          (Lit (Tuple Nothing 5) (Name "b"))))
    -- The expected result: { f = forall t_4. t_4 -> t_4, n = Int, b = Bool }
    ( Tuple "f" (Forall ("t_4" : Nil) (typVarArrow "t_4" "t_4"))
    : Tuple "n" (Forall Nil intType)
    : Tuple "b" (Forall Nil boolType)
    : Nil )

  testMapSchemeOnTVarMappings' "adt-map-scheme-1-6"
    adtPrelude
    (Forall ("t_1": Nil)
      (myIdT
        (myIdT (TypVar "t_1"))))
    (myId 0
      (myId 1
        (Lit (Tuple Nothing 3) (Name "x"))))
    ( Tuple "x" (Forall ("t_1":Nil) (TypVar "t_1"))
    : Nil )

  testMapSchemeOnTVarMappings' "adt-infix-map-scheme-1-1"
    adtPrelude
    (Forall ("t_1": Nil)
      (myComplexT
        (TypVar "t_1")))
    (myComplex 0
      (Lit (Tuple Nothing 1) (Name "x"))
      (Lit (Tuple Nothing 2) (Name "y")))
    (Tuple "x" (Forall ("t_1":Nil) (TypVar "t_1"))
    :Tuple "y" (Forall ("t_1":Nil) (TypVar "t_1"))
    :Nil)

  testInferExprWithCustomPrelude "adt-infix-params-1-1"
    adtPrelude
    "1 :+ 1"
    (myComplexT intType)

  testInferExprWithCustomPrelude "adt-infix-params-1-2"
    adtPrelude
    "(1 :+)"
    (TypArr intType (myComplexT intType))

  testInferExprWithCustomPrelude "adt-infix-params-1-3"
    adtPrelude
    "(:+ 1)"
    (TypArr intType (myComplexT intType))

  testInferExprWithCustomPrelude "adt-infix-params-1-4"
    adtPrelude
    "(:+)"
    (TypArr
      (TypVar "a")
      (TypArr
        (TypVar "a")
        (myComplexT (TypVar "a"))))
