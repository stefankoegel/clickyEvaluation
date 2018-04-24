module IndentParser (
    -- $doc
    -- * Types
    IndentParser, IndentParserT, runIndent,
    -- * Blocks
    withBlock, withBlock', block, block1,
    -- * Indentation Checking
    indented, indented', sameLine, sameOrIndented, checkIndent, withPos,
    -- * Paired characters
    -- indentBrackets, indentAngles, indentBraces, indentParens,
    -- * Line Fold Chaining
    -- | Any chain using these combinators must used with 'withPos'
    indentAp, (<+/>), indentNoAp, (<-/>), indentMany, (<*/>), indentOp, (<?/>), OptionalT(..), Optional
) where
      
import Prelude (class Monad, Unit, id, ap, const, ($), flip, unit, (==), bind, (<=), (>>=))
import Data.List (List(..), many)
import Data.Maybe (Maybe(..))
import Data.Identity (Identity(..))

import Control.Alt ((<|>))
import Control.Apply ((*>), lift2)
import Control.Applicative (pure)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (StateT, State, evalState)
import Control.Monad.State.Trans (get, put)

import Text.Parsing.Parser (ParserT, ParseState(ParseState), fail)
import Text.Parsing.Parser.Combinators
import Text.Parsing.Parser.Pos (Position(..), initialPos)
import Text.Parsing.Parser.String (string, oneOf)

-- $doc
-- This is purescript-port of Text.Parsing.Indent
-- https://hackage.haskell.org/package/indents-0.3.3/docs/Text-Parsec-Indent.html, 05.07.2016

-- A module to construct indentation aware parsers. Many programming
-- language have indentation based syntax rules e.g. python and Haskell.
-- This module exports combinators to create such parsers. 
-- 
-- The input source can be thought of as a list of tokens. Abstractly
-- each token occurs at a line and a column and has a width. The column
-- number of a token measures is indentation. If t1 and t2 are two tokens
-- then we say that indentation of t1 is more than t2 if the column
-- number of occurrence of t1 is greater than that of t2.
-- 
-- Currently this module supports two kind of indentation based syntactic
-- structures which we now describe:
-- 
-- [Block] --A block of indentation /c/ is a sequence of tokens with
-- indentation at least /c/.  Examples for a block is a where clause of
-- Haskell with no explicit braces.
-- 
-- [Line fold] A line fold starting at line /l/ and indentation /c/ is a
-- sequence of tokens that start at line /l/ and possibly continue to
-- subsequent lines as long as the indentation is greater than /c/. Such
-- a sequence of lines need to be /folded/ to a single line. An example
-- is MIME headers. Line folding based binding separation is used in
-- Haskell as well.

-- | Indentation sensitive parser type. Usually @ m @ will
--   be @ Identity @ as with any @ ParserT @
type IndentParserT s m = ParserT s (StateT Position m)
type IndentParser s = IndentParserT s Identity

-- | @ getPosition @ returns current position
--   should probably be added to Text.Parsing.Parser.Pos
getPosition :: forall m s. (Monad m) => ParserT s m Position
getPosition = get >>= \(ParseState _ pos _) -> pure pos

-- | simple helper function to avoid typ-problems with MonadState instance
get' :: forall m s. (Monad m) => IndentParserT s m Position
get' = do
  g <- lift get
  pure g

-- | simple helper function to avoid typ-problems with MonadState instance
put' :: forall m s. (Monad m) => Position -> IndentParserT s m Unit
put' p = lift (put p)

sourceColumn :: Position -> Int
sourceColumn (Position {line: _, column: c}) = c

sourceLine :: Position -> Int 
sourceLine (Position {line: l, column: _}) = l

setSourceLine :: Position -> Int -> Position
setSourceLine (Position {line: _, column: c}) l = Position {line: l, column: c}

biAp :: forall a b c. (a -> b) -> (b -> b -> c) -> a -> a -> c
biAp f c v1 v2 = c (f v1) (f v2)

-- | @ many1 @ should prabably be inside Text.Parsing.Parser.Combinators
many1 :: forall s m a. (Monad m) => ParserT s m a -> ParserT s m (List a)
many1 p = lift2 Cons p (many p) 

symbol :: forall m. (Monad m) => String -> ParserT String m String
symbol name = (many $ oneOf [' ','\t']) *> (string name)

----------------------------------------------------------------------

-- | @ 'withBlock' f a p @ parses @ a @
--   followed by an indented block of @ p @
--   combining them with @ f @
withBlock :: forall m a b c s. (Monad m) => (a -> List b -> c) -> IndentParserT s m a -> IndentParserT s m b -> IndentParserT s m c
withBlock f a p = withPos $ do
    r1 <- a
    r  <- optionMaybe $ indented *> block p
    case r of 
      Nothing -> pure (f r1 Nil)
      Just r2 -> pure (f r1 r2)

-- | Like 'withBlock', but throws away initial parse result
withBlock' :: forall m a b s. (Monad m) => IndentParserT s m a -> IndentParserT s m b -> IndentParserT s m (List b)
withBlock' = withBlock (flip const)

-- | Parses only when indented past the level of the reference
indented :: forall m s. (Monad m) => IndentParserT s m Unit
indented = do
    pos <- getPosition
    s <- get'
    if biAp sourceColumn (<=) pos s then fail "not indented" else do
        put' $ setSourceLine s (sourceLine pos)
        pure unit

-- | same as 'indented', but does not change the indent state
indented' :: forall m s. (Monad m) => IndentParserT s m Unit
indented' = do
    pos <- getPosition
    s <- get'
    if biAp sourceColumn (<=) pos s then fail "not indented" else pure unit

-- | Parses only when indented past the level of the reference or on the same line
sameOrIndented :: forall m s. (Monad m) => IndentParserT s m Unit
sameOrIndented = sameLine <|> indented

-- | Parses only on the same line as the reference
sameLine :: forall m s. (Monad m) => IndentParserT s m Unit
sameLine = do
    pos <- getPosition
    s   <- get'
    if biAp sourceLine (==) pos s then pure unit else fail "over one line"

-- | Parses a block of lines at the same indentation level
block1 :: forall m s a. (Monad m) => IndentParserT s m a -> IndentParserT s m (List a)
block1 p = withPos $ do
    r <- many1 $ checkIndent *> p
    pure r

-- | Parses a block of lines at the same indentation level , empty Blocks allowed
block :: forall m s a. (Monad m) => IndentParserT s m a -> IndentParserT s m (List a)
block p = withPos $ do
    r <- many $ checkIndent *> p
    pure r

-- | Parses using the current location for indentation reference
withPos :: forall m s a. (Monad m) => IndentParserT s m a -> IndentParserT s m a
withPos x = do
    a <- get'
    p <- getPosition
    r <- put' p *> x
    put' a *> pure r

-- | Ensures the current indentation level matches that of the reference
checkIndent :: forall m s. (Monad m) => IndentParserT s m Unit
checkIndent = do
    s <- get'
    p <- getPosition
    if biAp sourceColumn (==) p s then pure unit else fail "indentation doesn't match"

-- | Run the result of an indentation sensitive parse
runIndent :: forall a. State Position a -> a
runIndent = flip evalState initialPos

-- | '<+/>' is to indentation sensitive parsers what 'ap' is to monads
indentAp :: forall m s a b. (Monad m) => IndentParserT s m (a -> b) -> IndentParserT s m a -> IndentParserT s m b
indentAp a b = ap a $ sameOrIndented *> b

infixl 9 indentAp as <+/>

-- | Like '<+/>' but doesn't apply the function to the parsed value
indentNoAp :: forall m s a b. (Monad m) => IndentParserT s m a -> IndentParserT s m b -> IndentParserT s m a
indentNoAp a b = lift2 const a $ sameOrIndented *> b

infixl 10 indentNoAp as <-/>

-- | Like '<+/>' but applies the second parser many times
indentMany :: forall m s a b. (Monad m) => IndentParserT s m (List a -> b) -> IndentParserT s m a -> IndentParserT s m b
indentMany a b = ap a (many (sameOrIndented *> b))

infixl 11 indentMany as <*/>

-- | Datatype used to optional parsing
data OptionalT s m a = Opt a (IndentParserT s m a)
type Optional s a = OptionalT s Identity a

-- | Like '<+/>' but applies the second parser optionally using the 'Optional' datatype
indentOp :: forall m s a b. (Monad m) => IndentParserT s m (a -> b) -> (OptionalT s m a) -> IndentParserT s m b
indentOp a (Opt b c) = ap a (option b (sameOrIndented *> c))

infixl 12 indentOp as <?/>

-- | parses with surrounding brackets
indentBrackets :: forall m a. (Monad m) => IndentParserT String m a -> IndentParserT String m a
indentBrackets p = withPos $ pure id <-/> symbol "[" <+/> p <-/> symbol "]"

-- | parses with surrounding angle brackets
indentAngles :: forall m a. (Monad m) => IndentParserT String m a -> IndentParserT String m a
indentAngles p = withPos $ pure id <-/> symbol "<" <+/> p <-/> symbol ">"

-- | parses with surrounding braces
indentBraces :: forall m a. (Monad m) => IndentParserT String m a -> IndentParserT String m a
indentBraces p = withPos $ pure id <-/> symbol "{" <+/> p <-/> symbol "}"

-- | parses with surrounding parentheses 
indentParens :: forall m a. (Monad m) => IndentParserT String m a -> IndentParserT String m a
indentParens p = withPos $ pure id <-/> symbol "(" <+/> p <-/> symbol ")"
