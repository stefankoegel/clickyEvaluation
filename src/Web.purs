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
import Data.StrMap (lookup)
import Data.Tuple
import Control.Apply ((*>))

import AST
import Evaluator

type Handler = forall eff. Env -> Path -> Expr -> Eff (dom :: DOM | eff) Unit

exprToJQuery :: forall eff. Env -> Expr -> Handler -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery env expr handler = go Start expr
  where
  addHandler :: Path -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
  addHandler p j = case evalPath1 env p expr of
    Nothing -> return j
    Just _  -> do
      J.on "click" (\je _ -> J.stopImmediatePropagation je *> handler env p expr) j
      J.addClass "clickable" j
  go :: (Path -> Path) -> Expr -> Eff (dom :: DOM | eff) J.JQuery
  go p expr = case expr of
    Atom a -> atom a >>= addHandler (p End)
    Binary op e1 e2 -> do
      j1 <- go (p <<< Fst) e1
      j2 <- go (p <<< Snd) e2
      binary op j1 j2 >>= addHandler (p End)
    List es -> do
      js <- zipWithA (\i e -> go (p <<< Nth i) e) (0 .. (length es - 1)) es
      list js
    SectL e op -> do
      j <- go (p <<< Fst) e
      jop <- makeDiv (show op) ["op"]
      section j jop
    SectR op e -> do
      jop <- makeDiv (show op) ["op"]
      j <- go (p <<< Fst) e
      section jop j
    Prefix op -> makeDiv ("(" ++ show op ++ ")") ["prefix", "op"]
    Lambda binds body -> do
      jBinds <- for binds binding
      jBody <- go (p <<< Fst) body
      lambda jBinds jBody >>= addHandler (p End)
    App func args -> do
      jFunc <- go (p <<< Fst) func
      jArgs <- zipWithA (\i e -> go (p <<< Nth i) e) (0 .. (length args - 1)) args
      app jFunc jArgs >>= addHandler (p End)

atom :: forall eff. Atom -> Eff (dom :: DOM | eff) J.JQuery
atom (Num n)      = makeDiv (show n) ["atom", "num"]
atom (Bool true)  = makeDiv "True"  ["atom", "bool"]
atom (Bool false) = makeDiv "False" ["atom", "bool"]
atom (Name name)  = makeDiv name ["atom", "name"]

binding :: forall eff. Binding -> Eff (dom :: DOM | eff) J.JQuery
binding b = case b of
  Lit (Num n)     -> makeDiv (show n) ["atom", "name"]
  Lit (Bool true) -> makeDiv "True" ["atom", "name"]
  Lit (Bool false)-> makeDiv "False" ["atom", "name"]
  Lit (Name name) -> makeDiv name ["atom", "name"]
  ConsLit b bs -> do
    jCons <- makeDiv "" []
    makeDiv "(" ["brace"] >>= flip J.append jCons
    binding b             >>= flip J.append jCons
    makeDiv ":" ["brace"] >>= flip J.append jCons
    binding bs            >>= flip J.append jCons
    makeDiv ")" ["brace"] >>= flip J.append jCons
  ListLit bs -> do
    jList <- makeDiv "" []
    makeDiv "[" ["brace"] >>= flip J.append jList
    for bs $ \b -> do
      binding b >>= flip J.append jList
      makeDiv "," ["comma"] >>= flip J.append jList
    makeDiv "]" ["brace"] >>= flip J.append jList

lambda :: forall eff. [J.JQuery] -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
lambda jBinds jBody = do
  jLam <- makeDiv "" ["lambda"]
  open <- makeDiv "(" ["brace"]
  J.append open jLam
  bs <- makeDiv "\\" ["backslash"]
  J.append bs jLam
  for jBinds (flip J.append jLam)
  arrow <- makeDiv "->" ["arrow"]
  J.append arrow jLam
  J.append jBody jLam
  close <- makeDiv ")" ["brace"]
  J.append close jLam
  return jLam

binary :: forall eff. Op -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
binary op j1 j2 = do
  dBin <- makeDiv "" ["binary"]
  J.append j1 dBin
  dOp <- makeDiv (show op) ["op"]
  J.append dOp dBin
  J.append j2 dBin
  return dBin

section :: forall eff. J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
section j1 j2 = do
  jSect <- makeDiv "" ["section"]
  open <- makeDiv "(" ["brace"]
  J.append open jSect
  J.append j1 jSect
  J.append j2 jSect
  close <- makeDiv ")" ["brace"]
  J.append close jSect
  return jSect

list :: forall eff. [J.JQuery] -> Eff (dom :: DOM | eff) J.JQuery
list js = do
  dls <- makeDiv "" ["list"]
  open <- makeDiv "[" ["brace"]
  J.append open dls
  sep js dls
  close <- makeDiv "]" ["brace"]
  J.append close dls
  return dls
  where
  sep []     dls = return unit
  sep [j]    dls = void $ J.append j dls
  sep (j:js) dls = do
    J.append j dls
    comma <- makeDiv "," ["comma"]
    J.append comma dls
    sep js dls


app :: forall eff. J.JQuery -> [J.JQuery] -> Eff (dom :: DOM | eff) J.JQuery
app jFunc jArgs = do
  dApp <- makeDiv "" ["app"]
  J.addClass "func" jFunc
  J.append jFunc dApp
  for jArgs (flip J.append dApp)
  return dApp

type Class = String

makeDiv :: forall eff. String -> [Class] -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for classes (flip J.addClass d)
  return d
