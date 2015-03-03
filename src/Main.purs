module Main where

import qualified Control.Monad.JQuery as J
import           Control.Monad.Eff

import Debug.Trace

main = J.ready $ do
  print "Hello world!"
