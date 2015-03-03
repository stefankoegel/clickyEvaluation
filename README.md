# Clicky Evaluation

## Description

*Clicky Evaluation* parses simple *Haskell-like* expressions and function
definitions and renders them as HTML.
The user can then choose which subexpressions to evaluate for one step by
clicking on them.
This is intended as a simple learning tool for beginners,
which shows them how their Haskell code **might** be evaluated.

## Building

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
