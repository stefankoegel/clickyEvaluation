module Test.Utils where

import Prelude

import Data.Unit (Unit)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)

type Test a = forall eff. Eff (console :: CONSOLE | eff) a

tell :: String -> Test Unit
tell msg = log msg
