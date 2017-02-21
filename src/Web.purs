module Web where

import Prelude
import Data.Foldable (class Foldable, intercalate)
import Data.Unfoldable (fromMaybe)
import Data.List (List(Nil, Cons), snoc, fromFoldable, (:))
import Data.Set (intersection, size)
import Data.Set as Set
import Data.Maybe (Maybe(..), maybe, isJust)
import Data.Tuple (Tuple(..))
import Data.Traversable (for, for_)
import Data.Array as Arr
import Data.String as Str

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import DOM (DOM)

import AST (Atom(..), Binding(..), MType, Op, QualTree(..), Tree(..), TypeTree, TypedBinding,
            Type(..), TypeQual, pPrintOp, prettyPrintType, prettyPrintTypeError)

data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple TypeTree (TypeTree -> TypeTree)), exprType :: MType }

type DivHole = TypeTree -> (TypeTree -> TypeTree) -> Div

type OpTuple = Tuple Op MType

nodeHole :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> TypeTree -> (TypeTree -> TypeTree) -> Div
nodeHole content classes children expr hole =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: (Just (Tuple expr hole))
    , exprType: Nothing
    }
    (fromFoldable children)

typedNodeHole :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> MType -> TypeTree -> (TypeTree -> TypeTree) -> Div
typedNodeHole content classes children exprType expr hole =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: (Just (Tuple expr hole))
    , exprType: exprType
    }
    (fromFoldable children)

node :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Div
node content classes children =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: Nothing
    , exprType: Nothing
    }
    (fromFoldable children)

typedNode :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> MType -> Div
typedNode content classes children exprType =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: Nothing
    , exprType: exprType
    }
    (fromFoldable children)

zipList :: forall a b z. ((a -> z) -> a -> b) -> (List a -> z) -> List a -> List b
zipList zipp hole Nil = Nil
zipList zipp hole (Cons a as) = Cons (zipp (\x -> hole $ Cons x as) a) (zipList zipp (hole <<< Cons a) as)

exprToDiv:: TypeTree -> Div
exprToDiv = go id
  where
    go :: (TypeTree -> TypeTree) -> TypeTree -> Div
    go hole      (Atom t a)            = atom t a
    go hole expr@(List t ls)           = case toString ls of
                                           Nothing  -> list t (zipList go (hole <<< List Nothing) ls) expr hole
                                           Just str -> typedNode ("\"" <> str <> "\"") ["list", "string"] [] t
    go hole expr@(NTuple t ls)         = ntuple t (zipList go (hole <<< NTuple Nothing) ls) expr hole
    go hole expr@(Binary binType opTuple e1 e2) = binary binType opTuple
                                           (go (\e1 -> hole $ Binary Nothing opTuple e1 e2) e1)
                                           (go (\e2 -> hole $ Binary Nothing opTuple e1 e2) e2)
                                           expr hole
    go hole expr@(Unary t opTuple e)   = unary t opTuple (go (hole <<< Unary Nothing opTuple) e) expr hole
    go hole expr@(SectL t e opTuple)   = sectl t (go (\e -> hole $ SectL Nothing e opTuple) e) opTuple expr hole
    go hole expr@(SectR t opTuple e)   = sectr t opTuple (go (hole <<< SectR Nothing opTuple) e) expr hole
    go hole      (PrefixOp t opTuple)  = prefixOp t opTuple
    go hole expr@(IfExpr t ce te ee)   = ifexpr t
                                           (go (\ce -> hole $ IfExpr Nothing ce te ee) ce)
                                           (go (\te -> hole $ IfExpr Nothing ce te ee) te)
                                           (go (\ee -> hole $ IfExpr Nothing ce te ee) ee)
                                           expr hole
    go hole expr@(LetExpr t bes body)  = letexpr t
                                           (zipList
                                              (\listHole (Tuple b e) -> Tuple (binding b) (go (\x -> listHole $ Tuple b x) e))
                                              (\xs -> hole $ LetExpr Nothing xs body)
                                              bes)
                                           (go (\x -> hole $ LetExpr Nothing bes x) body)
                                           expr hole
    go hole expr@(Lambda t binds body) = lambda t (binding <$> binds) (go (hole <<< Lambda Nothing binds) body) expr hole

    go hole expr@(ArithmSeq t start next end)
                                       = arithmseq t
                                           (go (\x -> hole $ ArithmSeq Nothing x next end) start)
                                           (go (\x -> hole $ ArithmSeq Nothing start (Just x) end) <$> next)
                                           (go (\x -> hole $ ArithmSeq Nothing start next (Just x)) <$> end)
                                           expr hole

    go hole expr@(ListComp t e qs)     = listcomp t
                                           (go (\x -> hole $ ListComp Nothing x qs) e)
                                           (zipList qualToDiv (\xs -> hole $ ListComp Nothing e xs) qs)
                                           expr hole
      where
        qualToDiv :: (TypeQual -> TypeTree) -> TypeQual -> Div
        qualToDiv hole (Guard t e) = guardQual t           (go (\x -> hole $ Guard Nothing x) e)
        qualToDiv hole (Let t b e) = letQual t (binding b) (go (\x -> hole $ Let Nothing b x) e)
        qualToDiv hole (Gen t b e) = genQual t (binding b) (go (\x -> hole $ Gen Nothing b x) e)

    go hole expr@(App t func args) = app t (go funcHole func) argsDivs expr hole
      where
        funcHole func = hole $ App Nothing func args
        argsDivs = zipList go (hole <<< App Nothing func) args

guardQual :: MType -> Div -> Div
guardQual t guard = typedNode "" ["guard"] [guard] t

letQual :: MType -> Div -> Div -> Div
letQual t bind expr = typedNode "" ["let"] [letDiv, bind, eqDiv, expr] t
  where
    letDiv = node "let" ["keyword"] []
    eqDiv  = node "=" ["comma"] []

genQual :: MType -> Div -> Div -> Div
genQual t bind expr = typedNode "" ["gen"] [bind, arrow, expr] t
  where
    arrow = node "<-" ["comma"] []

atom :: MType -> Atom -> Div
atom t (AInt n) = typedNode (show n) ["atom", "num"] [] t
atom t (Bool b) = typedNode (if b then "True" else "False") ["atom", "bool"] [] t
atom t (Char c) = typedNode ("'" <> c <> "'") ["atom", "char"] [] t
atom t (Name n) = typedNode n ["atom", "name"] [] t

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

list :: MType -> List Div -> DivHole
list t Nil = typedNodeHole "[]" ["list empty"] [] t
list t ls  = typedNodeHole "" ["list"] (listify "[" "," "]" ls) t

ntuple :: MType -> List Div -> DivHole
ntuple t ls = typedNodeHole "" ["tuple"] (listify "(" "," ")" ls) t

unpackOp :: OpTuple -> Op
unpackOp (Tuple op _) = op

opToDiv :: OpTuple -> Div
opToDiv (Tuple op t) = typedNode (pPrintOp op) ["op"] [] t

binary :: MType -> OpTuple -> Div -> Div -> DivHole
binary binType op d1 d2 = typedNodeHole "" ["binary"] [d1, opToDiv op, d2] binType

openBrace :: Div
openBrace = node "(" ["brace", "left"] []

closeBrace :: Div
closeBrace = node ")" ["brace", "right"] []

unary :: MType -> OpTuple -> Div -> DivHole
unary t op div = typedNodeHole "" ["unary"] [openBrace, opToDiv op, div, closeBrace] t

sectl :: MType -> Div -> OpTuple -> DivHole
sectl t div op = typedNodeHole "" ["section"] [openBrace, div, opToDiv op, closeBrace] t

sectr :: MType -> OpTuple -> Div -> DivHole
sectr t op div = typedNodeHole "" ["section"] [openBrace, opToDiv op, div, closeBrace] t

prefixOp :: MType -> OpTuple -> Div
prefixOp binType op = typedNode "" ["prefixOp"] [openBrace, opToDiv op, closeBrace] binType

ifexpr :: MType -> Div -> Div -> Div -> DivHole
ifexpr t cd td ed = typedNodeHole "" ["if"] [ifDiv, cd, thenDiv, td, elseDiv, ed] t
  where
    ifDiv = node "if" ["keyword"] []
    thenDiv = node "then" ["keyword"] []
    elseDiv = node "else" ["keyword"] []

intersperse :: forall a. a -> List a -> List a
intersperse _ Nil          = Nil
intersperse _ (Cons a Nil) = Cons a Nil
intersperse s (Cons a as)  = Cons a $ Cons s $ intersperse s as

letexpr :: MType -> List (Tuple Div Div) -> Div -> DivHole
letexpr t binds expr = typedNodeHole "" ["letexpr"] ([letDiv] <> (intercalate [semi] (bind <$> binds)) <> [inDiv, expr]) t
  where
    letDiv = node "let" ["keyword"] []
    inDiv  = node "in" ["keyword"] []
    semi   = node ";" ["comma"] []
    equal  = node "=" ["comma"] []
    bind :: Tuple Div Div -> Array Div
    bind (Tuple b e) = [node "" [] [b, equal, e]]

listcomp :: MType -> Div -> List Div -> DivHole
listcomp t expr quals = typedNodeHole "" ["listcomp", "list"] ([open, expr, pipe] <> Arr.fromFoldable (intersperse comma quals) <> [close]) t
  where
    open  = node "[" ["brace"] []
    close = node "]" ["brace"] []
    pipe  = node "|" ["brace"] []
    comma = node "," ["comma"] []

lambda :: MType -> List Div -> Div -> DivHole
lambda t params body = typedNodeHole "" ["lambda"] (open : bslash : params <> (arrow : body : close : Nil)) t
  where
    open = node "(" ["brace", "left"] []
    bslash = node "\\" ["backslash", "separator"] []
    arrow = node "->" ["arrow", "separator"] []
    close = node ")" ["brace", "right"] []

app :: MType -> Div -> List Div -> DivHole
app t func args = typedNodeHole "" ["app"] (Cons func args) t

arithmseq :: MType -> Div -> Maybe Div -> Maybe Div -> DivHole
arithmseq t start mnext mend = typedNodeHole "" ["arithmseq", "list"] ([open, start] <> commaNext <> [dots] <> end <> [close]) t
 where
    open      = node "[" ["brace"] []
    comma     = node "," ["comma"] []
    commaNext = maybe [] (\next -> [comma, next]) mnext
    dots      = node ".." ["dots"] []
    end       = fromMaybe mend
    close     = node "]" ["brace"] []

binding :: TypedBinding -> Div
binding (Lit t a)         = typedNode "" ["binding", "lit"] [atom t a] t
binding (ConsLit t b1 b2) = typedNode "" ["binding", "conslit"] (listify "(" ":" ")" (binding b1 : binding b2 : Nil)) t
binding (ListLit t ls)    = typedNode "" ["binding", "listlit"] (listify "[" "," "]" (binding <$> ls)) t
binding (NTupleLit t ls)   = typedNode "" ["binding", "tuplelit"] (listify "(" "," ")" (binding <$> ls)) t

type Callback = forall eff. TypeTree -> (TypeTree -> TypeTree) -> (J.JQueryEvent -> J.JQuery -> Eff (dom :: DOM | eff) Unit)

-- | Create a type div with the pretty printed type as content.
createTypeDiv :: forall eff. MType -> Eff (dom :: DOM | eff) J.JQuery
createTypeDiv (Just (TypeError typeError)) = makeDiv (prettyPrintTypeError typeError) ["typeContainer", "hasTypeError"]
createTypeDiv mType = makeDiv (" :: " <> maybe "" prettyPrintType mType) ["typeContainer"]

-- | Add a type tooltip to the given div.
addTypeTooltip :: forall eff. MType -> J.JQuery -> Eff (dom :: DOM | eff) Unit
addTypeTooltip (Just (TypeError typeError)) div = J.setAttr "title" (prettyPrintTypeError typeError) div
addTypeTooltip mType div = J.setAttr "title" (" :: " <> maybe "" prettyPrintType mType) div

-- | Return true, if the first list of classes contains a class from the second list.
oneOfClasses :: forall f1 f2. (Foldable f1, Foldable f2) => f1 String -> f2 String -> Boolean
oneOfClasses cs1 cs2 = size (set1 `intersection` set2) > 0
  where
  set1 = Set.fromFoldable cs1
  set2 = Set.fromFoldable cs2

-- | Given a list of classes as well as the expression type determine if the expression should have
-- | a type div.
needsTypeContainer :: forall f. Foldable f => f String -> MType -> Boolean
needsTypeContainer _ Nothing = false
needsTypeContainer classes (Just t) = decideByClass classes && decideByType t
    where
    decideByType _ = true
    decideByClass classes = if oneOfClasses ["op", "binding", "num", "char", "bool", "gen", "guard", "let"] classes then false else true

divToJQuery :: forall eff. Boolean -> Callback -> Div -> Eff (dom :: DOM | eff) J.JQuery
divToJQuery isTopLevelDiv callback (Node { content: content, classes: classes, zipper: zipper, exprType: exprType } children) = do
  let needsContainer = needsTypeContainer classes exprType || isTopLevelDiv
  let isTyped = isJust exprType

  container <- makeDiv "" ["container"]
  div <- makeDiv content classes

  if needsContainer
    then do
      typeDiv <- createTypeDiv exprType
      J.append typeDiv container
      J.append div container
      J.addClass "hasTypeContainer" div
    else pure unit

  if isTyped
    then addTypeTooltip exprType div
    else pure unit

  for children (divToJQuery false callback >=> flip J.append div)
  case zipper of
    Nothing                -> pure unit
    Just (Tuple expr hole) -> do
      J.on "click" (callback expr hole) div
      J.on "mouseover" (callback expr hole) div
      J.on "mouseout" (callback expr hole) div
      pure unit

  if needsContainer
    then pure container
    else pure div

toString :: List TypeTree -> Maybe String
toString ls = Str.fromCharArray <$> go [] ls
  where
    go :: Array Char -> List TypeTree -> Maybe (Array Char)
    go acc (Cons (Atom _ (Char c)) rs) = case Str.toChar c of
                                           Just char -> go (Arr.snoc acc char) rs
                                           Nothing   -> Nothing
    go []  Nil                         = Nothing
    go acc Nil                         = Just acc
    go _   _                           = Nothing

type Class = String

makeDiv :: forall f eff. Foldable f => String -> f Class -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for_ classes (flip J.addClass d)
  pure d
