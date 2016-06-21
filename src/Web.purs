module Web
  ( exprToDiv
  , divToJQuery
  , RoseTree
  , Callback
  ) where

import Prelude
import Data.Traversable (for)
import Data.Foldable (class Foldable)
import Data.List (List(..), snoc, toList)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

import Control.Bind ((>=>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import DOM (DOM)

import AST (Expr, Tree(..), Binding(..), Atom(..), Op, pPrintOp)

data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple Expr (Expr -> Expr)) }

type DivHole = Expr -> (Expr -> Expr) -> Div


nodeHole :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Expr -> (Expr -> Expr) -> Div
nodeHole content classes children expr hole =
  Node
    { content: content
    , classes: (toList classes)
    , zipper: (Just (Tuple expr hole))
    }
    (toList children)


node :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Div
node content classes children =
  Node
    { content: content
    , classes: (toList classes)
    , zipper: Nothing
    }
    (toList children)

zipList :: ((Expr -> Expr) -> Expr -> Div) -> (List Expr -> Expr) -> List Expr -> List Div
zipList zipp hole Nil = Nil
zipList zipp hole (Cons x xs) = Cons (zipp (\x -> hole $ Cons x xs) x) (zipList zipp (hole <<< Cons x) xs)

exprToDiv:: Expr -> Div
exprToDiv expr = go id expr
  where
    go :: (Expr -> Expr) -> Expr -> Div
    go hole      (Atom _ a)            = atom a
    go hole expr@(List _ ls)           = list (zipList go (hole <<< List unit) ls) expr hole
    go hole expr@(NTuple _ ls)         = ntuple (zipList go (hole <<< NTuple unit) ls) expr hole
    go hole expr@(Binary _ op e1 e2)   = binary op
                                           (go (\e1 -> hole $ Binary unit op e1 e2) e1)
                                           (go (\e2 -> hole $ Binary unit op e1 e2) e2)
                                           expr hole
    go hole expr@(Unary _ op e)        = unary op (go (hole <<< Unary unit op) e) expr hole
    go hole expr@(SectL _ e op)        = sectl (go (\e -> hole $ SectL unit e op) e) op expr hole
    go hole expr@(SectR _ op e)        = sectr op (go (hole <<< SectR unit op) e) expr hole
    go hole      (PrefixOp _ op)       = prefixOp op
    go hole expr@(IfExpr _ ce te ee)   = ifexpr
                                           (go (\ce -> hole $ IfExpr unit ce te ee) ce)
                                           (go (\te -> hole $ IfExpr unit ce te ee) te)
                                           (go (\ee -> hole $ IfExpr unit ce te ee) ee)
                                           expr hole
    go hole (LetExpr _ b v e)     = letexpr (binding b) (go hole v) (go hole e) -- TODO
    go hole expr@(Lambda _ binds body) = lambda (binding <$> binds) (go (hole <<< Lambda unit binds) body) expr hole
    go hole expr@(App _ func args)     = app (go funcHole func) argsDivs expr hole
      where
        funcHole func = hole $ App unit func args
        argsDivs = zipList go (hole <<< App unit func) args

atom :: Atom -> Div
atom (AInt n) = node (show n) ["atom", "num"] [] 
atom (Bool b) = node (if b then "True" else "False") ["atom", "bool"] [] 
atom (Char c) = node ("'" ++ c ++ "'") ["atom", "char"] [] 
atom (Name n) = node n ["atom", "name"] [] 

interleave :: forall a. a -> List a -> List a
interleave _ Nil          = Nil
interleave _ (Cons x Nil) = Cons x Nil
interleave a (Cons x xs)  = Cons x $ Cons a $ interleave a xs

listify :: String -> String -> String -> List Div -> List Div
listify b s e ls = (Cons begin (snoc (interleave sep ls) end))
  where
    begin = node b ["brace"] []
    sep = node s ["brace"] []
    end = node e ["comma"] []

list :: List Div -> DivHole
list ls = nodeHole "" ["list"] $ listify "[" "," "]" ls

ntuple :: List Div -> DivHole
ntuple ls = nodeHole "" ["tuple"] $ listify "(" "," ")" ls

opToDiv :: Op -> Div
opToDiv op = node (pPrintOp op) ["op"] []

binary :: Op -> Div -> Div -> DivHole
binary op d1 d2 = nodeHole "" ["binary"] [d1, opToDiv op, d2]

openBrace :: Div
openBrace = node "(" ["brace"] []

closeBrace :: Div
closeBrace = node ")" ["brace"] []

unary :: Op -> Div -> DivHole
unary op div = nodeHole "" ["unary"] [openBrace, opToDiv op, div, closeBrace]

sectl :: Div -> Op -> DivHole
sectl div op = nodeHole "" ["section"] [openBrace, div, opToDiv op, closeBrace]

sectr :: Op -> Div -> DivHole
sectr op div = nodeHole "" ["section"] [openBrace, opToDiv op, div, closeBrace]

prefixOp :: Op -> Div
prefixOp op = node "" ["prefixOp"] [openBrace, opToDiv op, closeBrace]

ifexpr :: Div -> Div -> Div -> DivHole
ifexpr cd td ed = nodeHole "" ["if"] [ifDiv, cd, thenDiv, td, elseDiv, ed]
  where
    ifDiv = node "if" ["keyword"] []
    thenDiv = node "then" ["keyword"] []
    elseDiv = node "else" ["keyword"] []

letexpr :: Div -> Div -> Div -> Div
letexpr _ _ _ = node "" [] []

lambda :: List Div -> Div -> DivHole
lambda params body = nodeHole "" ["lambda"] (Cons open (Cons bslash (params ++ (Cons arrow (Cons body (Cons close Nil))))))
  where
    open = node "(" ["brace"] []
    bslash = node "\\" ["backslash"] []
    arrow = node "->" ["arrow"] []
    close = node ")" ["brace"] []

app :: Div -> List Div -> DivHole
app func args = nodeHole "" ["app"] (Cons func args)

binding :: Binding -> Div
binding (Lit a)         = node "" ["binding", "lit"] [atom a]
binding (ConsLit b1 b2) = node "" ["binding", "conslit"] $ listify "(" ":" ")" (Cons (binding b1) (Cons (binding b2) Nil))
binding (ListLit ls)    = node "" ["binding", "listlit"] $ listify "[" "," "]" (binding <$> ls)
binding (NTupleLit ls)   = node "" ["binding", "tuplelit"] $ listify "(" "," ")" (binding <$> ls)

type Callback = forall eff. Expr -> (Expr -> Expr) -> (J.JQueryEvent -> J.JQuery -> Eff (dom :: DOM | eff) Unit)

divToJQuery :: forall eff. Callback -> Div -> Eff (dom :: DOM | eff) J.JQuery
divToJQuery callback (Node { content: content, classes: classes, zipper: zipper } children) = do
  div <- makeDiv content classes
  for children (divToJQuery callback >=> flip J.append div)
  case zipper of
    Nothing                -> return unit
    Just (Tuple expr hole) -> do
      J.on "click" (callback expr hole) div
      J.on "mouseover" (callback expr hole) div
      J.on "mouseout" (callback expr hole) div
      return unit
  return div

makeDiv :: forall eff. String -> List String -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for classes (flip J.addClass d)
  return d

