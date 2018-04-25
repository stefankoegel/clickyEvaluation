module Test.AST where

import Prelude
import Data.List (List)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- import Control.Monad.Writer (Writer, tell)
import Control.Monad.Eff.Console (log)

import AST (Tree(..), Atom(..), Binding(..), Op(..), QualTree(..), TypeTree, toOpTuple, emptyMeta, Meta)

import Test.Utils (tell, Test)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: String -> Test Unit
tell' = tell

test :: forall a. (Show a, Eq a) => String -> a -> a -> Test Unit
test name input expected = case input == expected of
  false -> tell' $ "AST fail (" <> name <> "): " <> show input <> " should be " <> show expected
  true  -> log $ "Test success (" <> name <> ")"

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
atom = Atom emptyMeta (Name "x")

list :: TypeTree
list = List emptyMeta $ toList [atom, atom]

ntuple :: TypeTree
ntuple = NTuple emptyMeta $ toList [atom, atom]

binary :: TypeTree
binary = Binary emptyMeta (toOpTuple Add) atom atom

unary :: TypeTree
unary = Unary emptyMeta (toOpTuple Sub) atom

sectl :: TypeTree
sectl = SectL emptyMeta atom (toOpTuple Add)

sectr :: TypeTree
sectr = SectR emptyMeta (toOpTuple Add) atom

prefixop :: TypeTree
prefixop = PrefixOp emptyMeta (toOpTuple Add)

ifexpr :: TypeTree
ifexpr = IfExpr emptyMeta atom atom atom

arithmseq :: TypeTree
arithmseq = ArithmSeq emptyMeta atom (Just atom) (Just atom)

binding :: Binding Meta
binding = Lit emptyMeta (Name "x")

letexpr :: TypeTree
letexpr = LetExpr emptyMeta (toList [Tuple binding atom]) atom

lambda :: TypeTree
lambda = Lambda emptyMeta (toList [binding]) atom

app :: TypeTree
app = App emptyMeta atom (toList [atom, atom])

listcomp :: TypeTree
listcomp = ListComp emptyMeta atom (toList [Gen emptyMeta binding atom, Let emptyMeta binding atom, Guard emptyMeta atom])
