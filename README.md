# Clicky Evaluation

## Description

*Clicky Evaluation* parses simple *Haskell-like* expressions and function
definitions and renders them as HTML.
The user can then choose which subexpressions to evaluate for one step by
clicking on them.
This is intended as a simple learning tool for beginners,
which shows them how their Haskell code **might** be evaluated.

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

```
cabal update && cabal install purescript
npm install
$(npm bin)/bower update
$(npm bin)/grunt
```

Run with:

```
<your_browser> html/index.html
```
