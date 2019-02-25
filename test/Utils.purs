module Test.Utils where

import Prelude

import Effect (Effect)
import Data.String (Pattern(..), split) as String
import Data.Foldable (intercalate)

foreign import resetLog :: Effect Unit
foreign import getLog :: Effect (Array String)
foreign import tell :: String -> Effect Unit

unlines :: Array String -> String
unlines = intercalate "\n"

lines :: String -> Array String
lines = String.split (String.Pattern "\n")

padLeft :: String -> String
padLeft = lines >>> map (\x -> "  " <> x) >>> unlines

withWriterLog :: forall a. Effect a -> Effect (Array String)
withWriterLog tests = do
  resetLog
  _ <- tests
  getLog
