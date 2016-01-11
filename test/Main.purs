module Test.Main where

import Prelude

import Test.Parser as P
import Test.Evaluator as E
import Test.TypeChecker as T

import Control.Monad.Eff
import Control.Monad.Eff.Console

main :: forall eff. Eff (console :: CONSOLE | eff) Unit
main = do
  P.runTests
  E.runTests
  T.runTests
