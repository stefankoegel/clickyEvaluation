module Web
  ( exprToDiv
  , divToJQuery
  , RoseTree
  , Callback
  ) where

import Prelude
import Data.Foldable (all)
import Data.Traversable (for, traverse)
import Data.Foldable (Foldable)
import Data.String (joinWith)
import Data.List (List(Nil, Cons), singleton, fromList, toList, length, zip, (..), zipWithA, snoc)
import Data.Foreign (unsafeFromForeign, isUndefined)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import Control.Monad.State (State, put, get, runState)
import DOM (DOM)


import AST (Expr, Tree(..), Binding(..), Expr(..), Atom(..), Op(..), pPrintOp, Path(..))

data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple Expr (Expr -> Expr)) }

type DivHole = Expr -> (Expr -> Expr) -> Div


node' :: forall a f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Expr -> (Expr -> Expr) -> Div
node' content classes children expr hole =
  Node
    { content: content
    , classes: (toList classes)
    , zipper: (Just (Tuple expr hole))
    }
    (toList children)


node :: forall a f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Div
node content classes children =
  Node
    { content: content
    , classes: (toList classes)
    , zipper: Nothing
    }
    (toList children)

zipList :: forall a b. ((Expr -> Expr) -> Expr -> Div) -> (List Expr -> Expr) -> List Expr -> List Div
zipList zipp hole Nil = Nil
zipList zipp hole (Cons x xs) = Cons (zipp (\x -> hole $ Cons x xs) x) (zipList zipp (hole <<< Cons x) xs)

exprToDiv:: Expr -> Div
exprToDiv expr = go id expr
  where
    go :: (Expr -> Expr) -> Expr -> Div
    go hole expr@(Atom _ a)            = atom a
    go hole expr@(List _ ls)           = list (zipList go (hole <<< List unit) ls) expr hole
    go hole expr@(NTuple _ ls)         = ntuple (zipList go (hole <<< NTuple unit) ls) expr hole
    go hole expr@(Binary _ op e1 e2)   = binary op
                                           (go (\e1 -> hole $ Binary unit op e1 e2) e1)
                                           (go (\e2 -> hole $ Binary unit op e1 e2) e2)
                                           expr hole
    go hole (Unary _ op e)        = unary op (go hole e)
    go hole (SectL _ e op)        = sectl (go hole e) op
    go hole (SectR _ op e)        = sectr op (go hole e)
    go hole (PrefixOp _ op)       = prefixOp op
    go hole (IfExpr _ ce te ee)   = ifexpr (go hole ce) (go hole te) (go hole ee)
    go hole (LetExpr _ b v e)     = letexpr (binding b) (go hole v) (go hole e)
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

listify :: forall a. String -> String -> String -> List Div -> List Div
listify b s e ls = (Cons begin (snoc (interleave sep ls) end))
  where
    begin = node b ["brace"] []
    sep = node s ["brace"] []
    end = node e ["comma"] []

list :: List Div -> DivHole
list ls = node' "" ["list"] $ listify "[" "," "]" ls

ntuple :: List Div -> DivHole
ntuple ls = node' "" ["tuple"] $ listify "(" "," ")" ls

binary :: Op -> Div -> Div -> DivHole
binary op d1 d2 = node' "" ["binary"] [d1, opDiv, d2]
  where
    opDiv = node (pPrintOp op) ["op"] []

unary :: Op -> Div -> Div
unary _ _ = node "" [] []

sectl :: Div -> Op -> Div
sectl _ _ = node "" [] []

sectr :: Op -> Div -> Div
sectr _ _ = node "" [] []

prefixOp :: Op -> Div
prefixOp _ = node "" [] []

ifexpr :: Div -> Div -> Div -> Div
ifexpr _ _ _ = node "" [] []

letexpr :: Div -> Div -> Div -> Div
letexpr _ _ _ = node "" [] []

lambda :: List Div -> Div -> DivHole
lambda params body = node' "" ["lambda"] (Cons open (Cons bslash (params ++ (Cons arrow (Cons body (Cons close Nil))))))
  where
    open = node "(" ["brace"] []
    bslash = node "\\" ["backslash"] []
    arrow = node "->" ["arrow"] []
    close = node ")" ["brace"] []

app :: Div -> List Div -> DivHole
app func args = node' "" ["app"] (Cons func args)

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
      return unit
  return div

makeDiv :: forall eff. String -> List String -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for classes (flip J.addClass d)
  return d







-- unary:: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- unary jop jexpr t i = do
--   jtypExp <- makeDiv "" (singleton "unary typExpContainer")
--   jExpand <-  buildExpandDiv t
--   J.append jExpand jtypExp
--   jUnary <- makeDiv "" (singleton "unary expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   J.append jop jUnary
--   J.append jexpr jUnary
--   J.append jUnary jtypExp
--   return jtypExp


-- section :: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- section j1 j2 t i = do
--   jtypExp <- makeDiv "" (singleton "section typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   jSect <- makeDiv "" (singleton "section expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   open <- makeDiv "(" (singleton "brace")
--   J.append open jSect
--   J.append j1 jSect
--   J.append j2 jSect
--   close <- makeDiv ")" (singleton "brace")
--   J.append close jSect
--   J.append jSect jtypExp
--   return jtypExp

-- ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- ifexpr cond thenExpr elseExpr t i = do
--   jtypExp <- makeDiv "" (singleton "if typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dIf <- makeDiv "" (singleton "if expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   makeDiv "if" (singleton "keyword") >>= flip J.append dIf
--   J.append cond dIf
--   makeDiv "then" (singleton "keyword") >>= flip J.append dIf
--   J.append thenExpr dIf
--   makeDiv "else" (singleton "keyword") >>= flip J.append dIf
--   J.append elseExpr dIf
--   J.append dIf jtypExp
--   return jtypExp
