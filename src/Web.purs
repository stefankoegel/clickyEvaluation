module Web
  ( exprToJQuery
  , Handler ()
  ) where

import Control.Monad.Eff
import qualified Control.Monad.JQuery as J
import DOM

import Data.Traversable (for, zipWithA)
import Data.Maybe
import Data.Array ((..), length)
import Control.Apply ((*>))

import AST
import Evaluator

type Handler = forall eff. Expr -> Eff (dom :: DOM | eff) Unit

exprToJQuery :: forall eff. Expr -> Handler -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery expr handler = go Start expr
  where
  addHandler :: Path -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
  addHandler p j = J.on "click" (\je _ -> J.stopImmediatePropagation je *> evaluate p expr handler) j
  go :: (Path -> Path) -> Expr -> Eff (dom :: DOM | eff) J.JQuery
  go p expr = case expr of
    Atom a          -> atom a
    Binary op e1 e2 -> do
      j1 <- go (p <<< Fst) e1
      j2 <- go (p <<< Snd) e2
      binary op j1 j2 >>= addHandler (p End)
    List es -> do
      js <- zipWithA (\i e -> go (p <<< Nth i) e) (0 .. (length es - 1)) es
      list js >>= addHandler (p End)

atom :: forall eff. Atom -> Eff (dom :: DOM | eff) J.JQuery
atom (Num n)  = makeDiv (show n) ["atom", "num"]
atom (Bool b) = makeDiv (show b) ["atom", "bool"]
atom (Name s) = makeDiv s        ["atom", "name"]

binary :: forall eff. Op -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
binary op j1 j2 = do
  dBin <- makeDiv "" ["binary"]
  J.append j1 dBin
  dOp <- makeDiv (show op) ["op"]
  J.append dOp dBin
  J.append j2 dBin
  return dBin

list :: forall eff. [J.JQuery] -> Eff (dom :: DOM | eff) J.JQuery
list js = do
  dls <- makeDiv "List" ["list"]
  for js (flip J.append dls)
  return dls

type Class = String

makeDiv :: forall eff. String -> [Class] -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for classes (flip J.addClass d)
  return d

evaluate :: forall eff. Path -> Expr -> Handler -> Eff (dom :: DOM | eff) Unit
evaluate p expr handler = case evalPath1 Data.StrMap.empty p expr of
  Nothing    -> return unit
  Just expr' -> handler expr'
