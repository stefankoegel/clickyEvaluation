module Web where

import Prelude
import Data.Foldable (class Foldable, intercalate)
import Data.Unfoldable (fromMaybe)
import Data.List (List(Nil, Cons), snoc, fromFoldable)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..))
import Data.Traversable (for, for_)
import Data.Array as Arr
import Data.String as Str

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import DOM (DOM)

import AST (Expr, Tree(..), Binding(..), Atom(..), Op, pPrintOp, ExprQualTree, QualTree(..))

data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple Expr (Expr -> Expr)) }

type DivHole = Expr -> (Expr -> Expr) -> Div

nodeHole :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Expr -> (Expr -> Expr) -> Div
nodeHole content classes children expr hole =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: (Just (Tuple expr hole))
    }
    (fromFoldable children)


node :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Div
node content classes children =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: Nothing
    }
    (fromFoldable children)

zipList :: forall a b z. ((a -> z) -> a -> b) -> (List a -> z) -> List a -> List b
zipList zipp hole Nil = Nil
zipList zipp hole (Cons a as) = Cons (zipp (\x -> hole $ Cons x as) a) (zipList zipp (hole <<< Cons a) as)

exprToDiv:: Expr -> Div
exprToDiv = go id
  where
    go :: (Expr -> Expr) -> Expr -> Div
    go hole      (Atom _ a)            = atom a
    go hole expr@(List _ ls)           = case toString ls of
                                           Nothing  -> list (zipList go (hole <<< List unit) ls) expr hole
                                           Just str -> node ("\"" <> str <> "\"") ["list", "string"] []
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
    go hole expr@(LetExpr _ bes body)  = letexpr
                                           (zipList
                                              (\listHole (Tuple b e) -> Tuple (binding b) (go (\x -> listHole $ Tuple b x) e))
                                              (\xs -> hole $ LetExpr unit xs body)
                                              bes)
                                           (go (\x -> hole $ LetExpr unit bes x) body)
                                           expr hole
    go hole expr@(Lambda _ binds body) = lambda (binding <$> binds) (go (hole <<< Lambda unit binds) body) expr hole

    go hole expr@(ArithmSeq _ start next end)
                                       = arithmseq
                                           (go (\x -> hole $ ArithmSeq unit x next end) start)
                                           (go (\x -> hole $ ArithmSeq unit start (Just x) end) <$> next)
                                           (go (\x -> hole $ ArithmSeq unit start next (Just x)) <$> end)
                                           expr hole

    go hole expr@(ListComp _ e qs)     = listcomp
                                           (go (\x -> hole $ ListComp unit x qs) e)
                                           (zipList qualToDiv (\xs -> hole $ ListComp unit e xs) qs)
                                           expr hole
      where
        qualToDiv :: (ExprQualTree -> Expr) -> ExprQualTree -> Div
        qualToDiv hole (Guard _ e) = guardQual           (go (\x -> hole $ Guard unit x) e)
        qualToDiv hole (Let _ b e) = letQual (binding b) (go (\x -> hole $ Let unit b x) e)
        qualToDiv hole (Gen _ b e) = genQual (binding b) (go (\x -> hole $ Gen unit b x) e)

    go hole expr@(App _ func args)     = app (go funcHole func) argsDivs expr hole
      where
        funcHole func = hole $ App unit func args
        argsDivs = zipList go (hole <<< App unit func) args

guardQual :: Div -> Div
guardQual guard = node "" ["guard"] [guard]

letQual :: Div -> Div -> Div
letQual bind expr = node "" ["let"] [letDiv, bind, eqDiv, expr]
  where
    letDiv = node "let" ["keyword"] []
    eqDiv  = node "=" ["comma"] []

genQual :: Div -> Div -> Div
genQual bind expr = node "" ["gen"] [bind, arrow, expr]
  where
    arrow = node "<-" ["comma"] []

atom :: Atom -> Div
atom (AInt n) = node (show n) ["atom", "num"] []
atom (Bool b) = node (if b then "True" else "False") ["atom", "bool"] []
atom (Char c) = node ("'" <> c <> "'") ["atom", "char"] []
atom (Name n) = node n ["atom", "name"] []

interleave :: forall a. a -> List a -> List a
interleave _ Nil          = Nil
interleave _ (Cons x Nil) = Cons x Nil
interleave a (Cons x xs)  = Cons x $ Cons a $ interleave a xs

listify :: String -> String -> String -> List Div -> List Div
listify b s e ls = (Cons begin (snoc (interleave sep ls) end))
  where
    begin = node b ["brace", "left"] []
    sep = node s ["separator", "comma"] []
    end = node e ["brace", "right"] []

list :: List Div -> DivHole
list Nil = nodeHole "[]" ["list empty"] []
list ls  = nodeHole "" ["list"] $ listify "[" "," "]" ls

ntuple :: List Div -> DivHole
ntuple ls = nodeHole "" ["tuple"] $ listify "(" "," ")" ls

opToDiv :: Op -> Div
opToDiv op = node (pPrintOp op) ["op"] []

binary :: Op -> Div -> Div -> DivHole
binary op d1 d2 = nodeHole "" ["binary"] [d1, opToDiv op, d2]

openBrace :: Div
openBrace = node "(" ["brace", "left"] []

closeBrace :: Div
closeBrace = node ")" ["brace", "right"] []

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

intersperse :: forall a. a -> List a -> List a
intersperse _ Nil          = Nil
intersperse _ (Cons a Nil) = Cons a Nil
intersperse s (Cons a as)  = Cons a $ Cons s $ intersperse s as

letexpr :: List (Tuple Div Div) -> Div -> DivHole
letexpr binds expr = nodeHole "" ["letexpr"] $ [letDiv] <> (intercalate [semi] (bind <$> binds)) <> [inDiv, expr]
  where
    letDiv = node "let" ["keyword"] []
    inDiv  = node "in" ["keyword"] []
    semi   = node ";" ["comma"] []
    equal  = node "=" ["comma"] []
    bind :: Tuple Div Div -> Array Div
    bind (Tuple b e) = [node "" [] [b, equal, e]]

listcomp :: Div -> List Div -> DivHole
listcomp expr quals = nodeHole "" ["listcomp", "list"] $ [open, expr, pipe] <> Arr.fromFoldable (intersperse comma quals) <> [close]
  where
    open  = node "[" ["brace"] []
    close = node "]" ["brace"] []
    pipe  = node "|" ["brace"] []
    comma = node "," ["comma"] []

lambda :: List Div -> Div -> DivHole
lambda params body = nodeHole "" ["lambda"] (Cons open (Cons bslash (params <> (Cons arrow (Cons body (Cons close Nil))))))
  where
    open = node "(" ["brace", "left"] []
    bslash = node "\\" ["backslash", "separator"] []
    arrow = node "->" ["arrow", "separator"] []
    close = node ")" ["brace", "right"] []

app :: Div -> List Div -> DivHole
app func args = nodeHole "" ["app"] (Cons func args)

arithmseq :: Div -> Maybe Div -> Maybe Div -> DivHole
arithmseq start mnext mend = nodeHole "" ["arithmseq", "list"] $ [open, start] <> commaNext <> [dots] <> end <> [close]
 where
    open      = node "[" ["brace"] []
    comma     = node "," ["comma"] []
    commaNext = maybe [] (\next -> [comma, next]) mnext
    dots      = node ".." ["dots"] []
    end       = fromMaybe mend
    close     = node "]" ["brace"] []

binding :: forall a. Binding a -> Div
binding (Lit _ a)         = node "" ["binding", "lit"] [atom a]
binding (ConsLit _ b1 b2) = node "" ["binding", "conslit"] $ listify "(" ":" ")" (Cons (binding b1) (Cons (binding b2) Nil))
binding (ListLit _ ls)    = node "" ["binding", "listlit"] $ listify "[" "," "]" (binding <$> ls)
binding (NTupleLit _ ls)   = node "" ["binding", "tuplelit"] $ listify "(" "," ")" (binding <$> ls)

type Callback = forall eff. Expr -> (Expr -> Expr) -> (J.JQueryEvent -> J.JQuery -> Eff (dom :: DOM | eff) Unit)

divToJQuery :: forall eff. Callback -> Div -> Eff (dom :: DOM | eff) J.JQuery
divToJQuery callback (Node { content: content, classes: classes, zipper: zipper } children) = do
  div <- makeDiv content classes
  for children (divToJQuery callback >=> flip J.append div)
  case zipper of
    Nothing                -> pure unit
    Just (Tuple expr hole) -> do
      J.on "click" (callback expr hole) div
      J.on "mouseover" (callback expr hole) div
      J.on "mouseout" (callback expr hole) div
      pure unit
  pure div

toString :: List Expr -> Maybe String
toString ls = Str.fromCharArray <$> go [] ls
  where
    go :: Array Char -> List Expr -> Maybe (Array Char)
    go acc (Cons (Atom _ (Char c)) rs) = case Str.toChar c of
                                           Just char -> go (Arr.snoc acc char) rs
                                           Nothing   -> Nothing
    go []  Nil                         = Nothing
    go acc Nil                         = Just acc
    go _   _                           = Nothing

type Class = String

makeDiv :: forall eff. String -> List Class -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for_ classes (flip J.addClass d)
  pure d
