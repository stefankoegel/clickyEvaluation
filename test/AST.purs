module Test.AST where

import Prelude
import Data.List (List)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- import Control.Monad.Writer (Writer, tell)
import Effect (Effect)
import Effect.Console (log)

import AST (Tree(..), Atom(..), Binding(..), Op(..), QualTree(..), TypeTree, emptyMeta, Meta)

import Test.Utils (tell)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: String -> Effect Unit
tell' = tell

test :: forall a. Show a => Eq a => String -> a -> a -> Effect Unit
test name input expected = case input == expected of
  false -> tell' $ "AST fail (" <> name <> "): " <> show input <> " should be " <> show expected
  true  -> log $ "Test success (" <> name <> ")"

runTests :: Effect Unit
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

  test "map_atom" (map identity atom) atom
  test "map_list" (map identity list) list
  test "map_ntuple" (map identity ntuple) ntuple
  test "map_binary" (map identity binary) binary
  test "map_unary" (map identity unary) unary
  test "map_sectl" (map identity sectl) sectl
  test "map_sectr" (map identity sectr) sectr
  test "map_prefixop" (map identity prefixop) prefixop
  test "map_ifexpr" (map identity ifexpr) ifexpr
  test "map_arithmseq" (map identity arithmseq) arithmseq
  test "map_letexpr" (map identity letexpr) letexpr
  test "map_lambda" (map identity lambda) lambda
  test "map_app" (map identity app) app
  test "map_listcomp" (map identity listcomp) listcomp


atom :: TypeTree
atom = Atom emptyMeta (Name "x")

list :: TypeTree
list = List emptyMeta $ toList [atom, atom]

ntuple :: TypeTree
ntuple = NTuple emptyMeta $ toList [atom, atom]

binary :: TypeTree
binary = Binary emptyMeta (Tuple Add emptyMeta) atom atom

unary :: TypeTree
unary = Unary emptyMeta (Tuple Sub emptyMeta) atom

sectl :: TypeTree
sectl = SectL emptyMeta atom (Tuple Add emptyMeta)

sectr :: TypeTree
sectr = SectR emptyMeta (Tuple Add emptyMeta) atom

prefixop :: TypeTree
prefixop = PrefixOp emptyMeta (Tuple Add emptyMeta)

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
