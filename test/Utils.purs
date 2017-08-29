module Test.Utils where

import Prelude

import Control.Monad.Eff (Eff)
import Data.String (Pattern(..), split) as String
import Data.Foldable (intercalate)

foreign import data WRITERLOG :: !
foreign import resetLog :: Test Unit
foreign import getLog :: Test (Array String)
foreign import tell :: String -> Test Unit

type Test a = forall eff. Eff (writerlog :: WRITERLOG | eff) a

unlines :: Array String -> String
unlines = intercalate "\n"

lines :: String -> Array String
lines = String.split (String.Pattern "\n")

padLeft :: String -> String
padLeft = lines >>> map (\x -> "  " <> x) >>> unlines

withWriterLog :: forall a. Test a -> Test (Array String)
withWriterLog tests = do
  resetLog
  tests
  getLog
