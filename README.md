# Clicky Evaluation

[![Build Status](https://travis-ci.org/stefankoegel/clickyEvaluation.svg?branch=master)](https://travis-ci.org/stefankoegel/clickyEvaluation)

## Description

*Clicky Evaluation* parses simple *Haskell-like* expressions and function
definitions and renders them as HTML.
The user can then choose which subexpressions to evaluate for one step by
clicking on them.
This is intended as a simple learning tool for beginners,
which shows them how their Haskell code **might** be evaluated.

You can try it [here](http://stefankoegel.github.io/clickyEvaluation/html/).

The projects name is a play on *lazy evaluation* and *clicking* to evaluate an expression.

## Supported Features

* Bool
* Char
* Int
* String
* List
* Tupel
* Arithmetic operators `[(+), (-), (*), ('div'), ('mod'), (^)]`
* Comparsion operators `[(==), (/=), (<=), (<), (>), (>=)]`
* Boolean operators `[(&&), (||), (not)]`
* Other operators `[($), (.), (:), (++)]`
* Infix to prefix conversion `a + b <=> (+) a b`
* Pattern matching on atoms (numbers, ...), lists and tuples
* Anonymous functions (lambdas)
* Sections `(^2) 4 => 4^2 => 16`
* Most of the simple Prelude functions on lists `head, map, foldr, scanr, filter, all, ...`

## Missing Features

Everything not on the above list. Especially:
* Guards
* `case`, `where`, `let`
* Multi-line expressions, significant whitespace
* Floating point numbers
* Types (and other sanity checks)
* ADTs
* Comments
* List comprehensions

## Building

You will need to install the Haskell Platform (7.6.3 should be enough), nodejs and npm.
This project won't work with purescript-0.7.0 or higher (I will fix this soon),
that's why the following instructions use an older version.

```
cabal update
cabal sandbox init
cabal install purescript-0.9.5
npm install
$(npm bin)/bower update
PATH=.cabal-sandbox/bin:$PATH $(npm bin)/grunt
```

Run with:

```
<your_browser> html/index.html
```
