module Test.Utils where

import Prelude

import Control.Monad.Eff (Eff)

foreign import data WRITERLOG :: !
foreign import resetLog :: Test Unit
foreign import getLog :: Test (Array String)
foreign import tell :: String -> Test Unit

type Test a = forall eff. Eff (writerlog :: WRITERLOG | eff) a

withWriterLog :: forall a. Test a -> Test (Array String)
withWriterLog tests = do
  resetLog
  tests
  getLog
