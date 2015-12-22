module Test.TypeChecker where

import Prelude
import Control.Monad.Eff
import Control.Monad.Eff.Console

import Data.Either
import Data.List

import Text.Parsing.StringParser

import AST
import Parser
import TypeChecker (runInfer, emptyTyenv, infer)


-- debug env
parseExpr:: String -> Either ParseError Expr
parseExpr = runParser expression

-- parseDefinitions:: String -> Either ParseError (List Definition)
-- parseDefinitions = runParser defs

definitions = """
  and (True:xs)  = and xs
  and (False:xs) = False
  and []         = True

  or (False:xs) = or xs
  or (True:xs)  = True
  or []         = False

  all p = and . map p
  any p = or . map p

  head (x:xs) = x
  tail (x:xs) = xs

  take 0 xs     = []
  take n (x:xs) = x : take (n - 1) xs

  drop 0 xs     = xs
  drop n (x:xs) = drop (n - 1) xs

  elem e []     = False
  elem e (x:xs) = if e == x then True else elem e xs

  max a b = if a >= b then a else b
  min a b = if b >= a then a else b

  maximum (x:xs) = foldr max x xs
  minimum (x:xs) = foldr min x xs

  length []     = 0
  length (x:xs) = 1 + length xs

  zip (x:xs) (y:ys) = (x, y) : zip xs ys
  zip []      _     = []
  zip _       []    = []

  zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys
  zipWith _ []     _      = []
  zipWith _ _      []     = []

  unzip []          = ([], [])
  unzip ((a, b):xs) = (\(as, bs) -> (a:as, b:bs)) $ unzip xs

  curry f a b = f (a, b)
  uncurry f (a, b) = f a b

  repeat x = x : repeat x

  replicate 0 _ = []
  replicate n x = x : replicate (n - 1) x

  enumFromTo a b = if a <= b then a : enumFromTo (a + 1) b else []

  sum (x:xs) = x + sum xs
  sum [] = 0

  product (x:xs) = x * product xs
  product [] = 1

  reverse []     = []
  reverse (x:xs) = reverse xs ++ [x]

  concat = foldr (++) []

  map f []     = []
  map f (x:xs) = f x : map f xs

  not True  = False
  not False = True

  filter p (x:xs) = if p x then x : filter p xs else filter p xs
  filter p []     = []

  foldr f ini []     = ini
  foldr f ini (x:xs) = f x (foldr f ini xs)

  foldl f acc []     = acc
  foldl f acc (x:xs) = foldl f (f acc x) xs

  scanl f b []     = [b]
  scanl f b (x:xs) = b : scanl f (f b x) xs

  iterate f x = x : iterate f (f x)

  id x = x

  const x _ = x

  flip f x y = f y x

  even n = (n `mod` 2) == 0
  odd n = (n `mod` 2) == 1

  fix f = f (fix f)
  """



aname :: String -> Expr
aname s = Atom $ Name s

aint :: Int -> Expr
aint i = Atom $ AInt i

testExp = (Lambda (toList $ [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c",Lit $ Name "d"]) (App (aname "a") (toList [aname "b", aname "c", aname "d"])))
testExp2 = (Lambda (toList [Lit $ Name "a", Lit $ Name "b"]) (App (aname "a") (toList [aname "b"])))
testExp3 = (SectL (aint 3) Power)
testExp4 = (SectR  Power (aint 3))

test = runInfer $ infer emptyTyenv testExp4

-- debug end
