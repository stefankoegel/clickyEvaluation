module Test.Main where

import Prelude
import Data.Array (length)
import Data.Traversable (for)

import Test.Parser as Parser
import Test.Evaluator as Evaluator
import Test.AST as AST
import Test.TypeChecker as TypeChecker

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)

import Node.Process (PROCESS, exit)

import Test.Utils (withWriterLog, WRITERLOG, padLeft)

import Partial.Unsafe (unsafePartial)

report :: forall eff. String -> Eff (console :: CONSOLE | eff) Unit
report = padLeft >>> (\x -> x <> "\n") >>> log

main :: forall eff.
        Eff
          ( console :: CONSOLE
          , process :: PROCESS
          , writerlog :: WRITERLOG | eff)
          Unit
main = do
  log $ "Running parser tests..."
  parserLog <- withWriterLog (unsafePartial Parser.runTests)
  log $ " ...found " <> show (length parserLog) <> " errors"
  for parserLog report

  log $ "Running AST tests..."
  astLog <- withWriterLog (unsafePartial AST.runTests)
  log $ " ...found " <> show (length astLog) <> " errors"
  for astLog report

  log $ "Running evaluator tests..."
  evaluatorLog <- withWriterLog (unsafePartial Evaluator.runTests)
  log $ " ...found " <> show (length evaluatorLog) <> " errors"
  for evaluatorLog report

  log $ "Running type checker tests..."
  typeCheckerLog <- withWriterLog (unsafePartial TypeChecker.runTests)
  log $ " ...found " <> show (length typeCheckerLog) <> " errors"
  for typeCheckerLog report

  let errorCount = length parserLog + length evaluatorLog +  length astLog + length typeCheckerLog
  if errorCount == 0
    then do
      log $ "All tests succesfull"
      exit 0
    else do
      log $ "Found " <> show errorCount <> " errors!"
      exit 1
