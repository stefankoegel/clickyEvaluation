# Clicky Evaluation

[![Build Status](https://travis-ci.org/stefankoegel/clickyEvaluation.svg?branch=master)](https://travis-ci.org/stefankoegel/clickyEvaluation)
[![Dependency Status](https://www.versioneye.com/user/projects/56b075193d82b9003761e3e6/badge.svg?style=flat)](https://www.versioneye.com/user/projects/56b075193d82b9003761e3e6)

## Description

*Clicky Evaluation* parses simple *Haskell-like* expressions and function
definitions and renders them as HTML.
The user can then choose which subexpressions to evaluate for one step by
clicking on them.
This is intended as a simple learning tool for beginners,
which shows them how their Haskell code **might** be evaluated.

You can try it [here](http://srechenberger.github.io/clickyEvaluation/).

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
* Types for Bool, Char, Int, List, Tupel and Prelude functions
* Type inference for user defined functions and expressions

## Missing Features

Everything not on the above list. Especially:
* Guards
* `case`, `where`, `let`
* Multi-line expressions, significant whitespace
* Floating point numbers
* ADTs
* Comments
* List comprehensions
* Type classes

## Building

Install `npm` and `purescript` (at least 0.8.0).
You can get `purescript` via `cabal install purescript` or `npm install purescript`.
Then run:
```
npm install
npm run build
```
For the unit tests you can also run:
```
npm run test
```

After a successful build use:

```
<your_browser> html/index.html
```

## Hosting

You can build and host a specific version of ClickyEvaluation yourself by providing the following files on your webserver:
* index.html
* source.css
* Main.js (generated with `npm run test` or `pulp build --to Main.js`)

Or you can link to the most recent version [here](http://stefankoegel.github.io/clickyEvaluation/).
