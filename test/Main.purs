module Test.Main where

import Prelude
import Data.Array (length)
import Data.Traversable (for_)

import Test.Parser as Parser
import Test.Evaluator as Evaluator
import Test.AST as AST
import Test.TypeChecker as TypeChecker

import Effect (Effect)
import Effect.Console (log)

import Node.Process (exit)

import Test.Utils (withWriterLog, padLeft)

import Partial.Unsafe (unsafePartial)

report :: String -> Effect Unit
report = padLeft >>> (\x -> x <> "\n") >>> log

main :: Effect Unit
main = do
  log $ "Running parser tests..."
  parserLog <- withWriterLog (unsafePartial Parser.runTests)
  log $ " ...found " <> show (length parserLog) <> " errors"
  for_ parserLog report

  log $ "Running AST tests..."
  astLog <- withWriterLog (unsafePartial AST.runTests)
  log $ " ...found " <> show (length astLog) <> " errors"
  for_ astLog report

  log $ "Running evaluator tests..."
  evaluatorLog <- withWriterLog (unsafePartial Evaluator.runTests)
  log $ " ...found " <> show (length evaluatorLog) <> " errors"
  for_ evaluatorLog report

  log $ "Running type checker tests..."
  typeCheckerLog <- withWriterLog (unsafePartial TypeChecker.runTests)
  log $ " ...found " <> show (length typeCheckerLog) <> " errors"
  for_ typeCheckerLog report

  let errorCount = length parserLog + length evaluatorLog +  length astLog + length typeCheckerLog
  if errorCount == 0
    then do
      log $ "All tests succesfull"
      exit 0
    else do
      log $ "Found " <> show errorCount <> " errors!"
      exit 1
