module TypeChecker where

import Prelude
import Control.Monad.Eff
import Control.Monad.Eff.Console

import Data.Either
import Data.List

import Text.Parsing.StringParser

import AST
