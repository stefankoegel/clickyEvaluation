module Test.AST where

import Prelude
import Data.List (List, singleton)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- import Control.Monad.Writer (Writer, tell)

import AST (Tree(..), Atom(..), Binding(..), Op(..), QualTree(..), TypeTree, MType, toOpTuple)

import Test.Utils (tell, Test)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: String -> Test Unit
tell' = tell

test :: forall a. (Show a, Eq a) => String -> a -> a -> Test Unit
test name input expected = case input == expected of
  false -> tell' $ "AST fail (" <> name <> "): " <> show input <> " should be " <> show expected
  true  -> pure unit

runTests :: Test Unit
runTests = do
--   test "idFoldTree_atom" (idFoldTree atom) atom
--   test "idFoldTree_list" (idFoldTree list) list
--   test "idFoldTree_ntuple" (idFoldTree ntuple) ntuple
--   test "idFoldTree_binary" (idFoldTree binary) binary
--   test "idFoldTree_unary" (idFoldTree unary) unary
--   test "idFoldTree_sectl" (idFoldTree sectl) sectl
--   test "idFoldTree_sectr" (idFoldTree sectr) sectr
--   test "idFoldTree_prefixop" (idFoldTree prefixop) prefixop
--   test "idFoldTree_ifexpr" (idFoldTree ifexpr) ifexpr
--   test "idFoldTree_arithmseq" (idFoldTree arithmseq) arithmseq
--   test "idFoldTree_letexpr" (idFoldTree letexpr) letexpr
--   test "idFoldTree_lambda" (idFoldTree lambda) lambda
--   test "idFoldTree_app" (idFoldTree app) app
--   test "idFoldTree_listcomp" (idFoldTree listcomp) listcomp

  test "map_atom" (map id atom) atom
  test "map_list" (map id list) list
  test "map_ntuple" (map id ntuple) ntuple
  test "map_binary" (map id binary) binary
  test "map_unary" (map id unary) unary
  test "map_sectl" (map id sectl) sectl
  test "map_sectr" (map id sectr) sectr
  test "map_prefixop" (map id prefixop) prefixop
  test "map_ifexpr" (map id ifexpr) ifexpr
  test "map_arithmseq" (map id arithmseq) arithmseq
  test "map_letexpr" (map id letexpr) letexpr
  test "map_lambda" (map id lambda) lambda
  test "map_app" (map id app) app
  test "map_listcomp" (map id listcomp) listcomp


atom :: TypeTree
atom = Atom Nothing (Name "x")

list :: TypeTree
list = List Nothing $ toList [atom, atom]

ntuple :: TypeTree
ntuple = NTuple Nothing $ toList [atom, atom]

binary :: TypeTree
binary = Binary Nothing (toOpTuple Add) atom atom

unary :: TypeTree
unary = Unary Nothing (toOpTuple Sub) atom

sectl :: TypeTree
sectl = SectL Nothing atom (toOpTuple Add)

sectr :: TypeTree
sectr = SectR Nothing (toOpTuple Add) atom

prefixop :: TypeTree
prefixop = PrefixOp Nothing (toOpTuple Add)

ifexpr :: TypeTree
ifexpr = IfExpr Nothing atom atom atom

arithmseq :: TypeTree
arithmseq = ArithmSeq Nothing atom (Just atom) (Just atom)

binding :: Binding MType
binding = Lit Nothing (Name "x")

letexpr :: TypeTree
letexpr = LetExpr Nothing (toList [Tuple binding atom]) atom

lambda :: TypeTree
lambda = Lambda Nothing (toList [binding]) atom

app :: TypeTree
app = App Nothing atom (toList [atom, atom])

listcomp :: TypeTree
listcomp = ListComp Nothing atom (toList [Gen Nothing binding atom, Let Nothing binding atom, Guard Nothing atom])
