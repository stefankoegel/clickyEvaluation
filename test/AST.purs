module Test.AST where

import Prelude
import Data.List (List, singleton)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

import Control.Monad.Writer (Writer, tell)

import AST (Tree(..), Atom(..), Binding(..), Op(..), QualTree(..), idFoldTree, Expr)

toList :: forall a. Array a -> List a
toList = Array.toUnfoldable

tell' :: forall a. a -> Writer (List a) Unit
tell' = tell <<< singleton

test :: forall a. (Show a, Eq a) => String -> a -> a -> Writer (List String) Unit
test name input expected = case input == expected of
  false -> tell' $ "AST fail (" <> name <> "): " <> show input <> " should be " <> show expected
  true  -> pure unit

runTests :: Writer (List String) Unit
runTests = do
  test "idFoldTree_atom" (idFoldTree atom) atom
  test "idFoldTree_list" (idFoldTree list) list
  test "idFoldTree_ntuple" (idFoldTree ntuple) ntuple
  test "idFoldTree_binary" (idFoldTree binary) binary
  test "idFoldTree_unary" (idFoldTree unary) unary
  test "idFoldTree_sectl" (idFoldTree sectl) sectl
  test "idFoldTree_sectr" (idFoldTree sectr) sectr
  test "idFoldTree_prefixop" (idFoldTree prefixop) prefixop
  test "idFoldTree_ifexpr" (idFoldTree ifexpr) ifexpr
  test "idFoldTree_arithmseq" (idFoldTree arithmseq) arithmseq
  test "idFoldTree_letexpr" (idFoldTree letexpr) letexpr
  test "idFoldTree_lambda" (idFoldTree lambda) lambda
  test "idFoldTree_app" (idFoldTree app) app
  test "idFoldTree_listcomp" (idFoldTree listcomp) listcomp

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


atom :: Expr
atom = Atom unit (Name "x")

list :: Expr
list = List unit $ toList [atom, atom]

ntuple :: Expr
ntuple = NTuple unit $ toList [atom, atom]

binary :: Expr
binary = Binary unit Add atom atom

unary :: Expr
unary = Unary unit Sub atom

sectl :: Expr
sectl = SectL unit atom Add

sectr :: Expr
sectr = SectR unit Add atom

prefixop :: Expr
prefixop = PrefixOp unit Add

ifexpr :: Expr
ifexpr = IfExpr unit atom atom atom

arithmseq :: Expr
arithmseq = ArithmSeq unit atom (Just atom) (Just atom)

binding :: Binding Unit
binding = Lit unit (Name "x")

letexpr :: Expr
letexpr = LetExpr unit (toList [Tuple binding atom]) atom

lambda :: Expr
lambda = Lambda unit (toList [binding]) atom

app :: Expr
app = App unit atom (toList [atom, atom])

listcomp :: Expr
listcomp = ListComp unit atom (toList [Gen unit binding atom, Let unit binding atom, Guard unit atom])
