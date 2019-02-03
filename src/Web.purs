module Web where

import Prelude
import Data.Foldable (class Foldable, intercalate, foldr)
import Data.Unfoldable (fromMaybe)
import Data.List (List(Nil, Cons), snoc, fromFoldable, (:), singleton)
import Data.Set (intersection, size)
import Data.Set as Set
import Data.Maybe (Maybe(..), maybe, isJust)
import Data.Tuple (Tuple(..))
import Data.Traversable (for, for_)
import Data.Array as Arr
import Data.String.CodeUnits as Str

import Effect (Effect)
import JQuery as J

import AST (Atom(..), Binding(..), MType, Op, QualTree(..), Tree(..), TypeTree, TypedBinding, Meta(..), Index,
            Type(..), TypeQual, DataConstr(..), pPrintOp, prettyPrintType, prettyPrintTypeError, getMetaMType)

import AST as AST


data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple TypeTree (TypeTree -> TypeTree)), exprType :: MType }

type DivHole = TypeTree -> (TypeTree -> TypeTree) -> Div

type OpTuple = Tuple Op Meta

-- Tells, which nodes are to be marked as clicked or evaluated, if any.
type Highlight = List (Tuple String Index)


-- Given a Highlight value and the Meta information of a node, generated additional classes to highlight the node

highlight' :: Highlight -> Meta -> List String
highlight' hl (Meta m) = foldr f Nil hl
  where
    f (Tuple c i) acc | i == m.index = Cons c acc
    f _           acc                = acc

highlight :: Highlight -> Meta -> Div -> Div
highlight hl meta (Node a chs) = Node (a { classes = a.classes <> highlight' hl meta }) chs


nodeHole :: forall f1 f2. Foldable f1 => Foldable f2 => String -> f1 String -> f2 Div -> TypeTree -> (TypeTree -> TypeTree) -> Div
nodeHole content classes children expr hole =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: (Just (Tuple expr hole))
    , exprType: Nothing
    }
    (fromFoldable children)

typedNodeHole :: forall f1 f2. Foldable f1 => Foldable f2 => String -> f1 String -> f2 Div -> MType -> TypeTree -> (TypeTree -> TypeTree) -> Div
typedNodeHole content classes children exprType expr hole =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: (Just (Tuple expr hole))
    , exprType: exprType
    }
    (fromFoldable children)

node :: forall f1 f2. Foldable f1 => Foldable f2 => String -> f1 String -> f2 Div -> Div
node content classes children =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: Nothing
    , exprType: Nothing
    }
    (fromFoldable children)

typedNode :: forall f1 f2. Foldable f1 => Foldable f2 => String -> f1 String -> f2 Div -> MType -> Div
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

exprToDiv :: Highlight -> TypeTree -> Div
exprToDiv hl = go identity
  where
    h :: Meta -> Div -> Div
    h = highlight hl

    go :: (TypeTree -> TypeTree) -> TypeTree -> Div
    go hole      (Atom meta a)            = h meta $ atom (getMetaMType meta) a
    go hole expr@(List meta ls)           = case toString ls of
                                           Nothing  -> h meta $ list (getMetaMType meta) (zipList go (hole <<< List meta) ls) expr hole
                                           Just str -> h meta $ typedNode ("\"" <> str <> "\"") ["list", "string"] [] (getMetaMType meta)
    go hole expr@(NTuple meta ls)         = h meta $ ntuple (getMetaMType meta) (zipList go (hole <<< NTuple meta) ls) expr hole
    go hole expr@(Binary meta opTuple e1 e2) = h meta $ binary (getMetaMType meta) opTuple
                                           (go (\e1 -> hole $ Binary meta opTuple e1 e2) e1)
                                           (go (\e2 -> hole $ Binary meta opTuple e1 e2) e2)
                                           expr hole
    go hole expr@(Unary meta opTuple e)   = h meta $ unary (getMetaMType meta) opTuple (go (hole <<< Unary meta opTuple) e) expr hole
    go hole expr@(SectL meta e opTuple)   = h meta $ sectl (getMetaMType meta) (go (\e -> hole $ SectL meta e opTuple) e) opTuple expr hole
    go hole expr@(SectR meta opTuple e)   = h meta $ sectr (getMetaMType meta) opTuple (go (hole <<< SectR meta opTuple) e) expr hole
    go hole      (PrefixOp meta opTuple)  = h meta $ prefixOp (getMetaMType meta) opTuple
    go hole expr@(IfExpr meta ce te ee)   = h meta $ ifexpr (getMetaMType meta)
                                           (go (\ce -> hole $ IfExpr meta ce te ee) ce)
                                           (go (\te -> hole $ IfExpr meta ce te ee) te)
                                           (go (\ee -> hole $ IfExpr meta ce te ee) ee)
                                           expr hole
    go hole expr@(LetExpr meta bes body)  = h meta $ letexpr (getMetaMType meta)
                                           (zipList
                                              (\listHole (Tuple b e) -> Tuple (binding b) (go (\x -> listHole $ Tuple b x) e))
                                              (\xs -> hole $ LetExpr meta xs body)
                                              bes)
                                           (go (\x -> hole $ LetExpr meta bes x) body)
                                           expr hole
    go hole expr@(Lambda meta binds body) = h meta $ lambda (getMetaMType meta) (binding <$> binds) (go (hole <<< Lambda meta binds) body) expr hole

    go hole expr@(ArithmSeq meta start next end)
                                       = h meta $ arithmseq (getMetaMType meta)
                                           (go (\x -> hole $ ArithmSeq meta x next end) start)
                                           (go (\x -> hole $ ArithmSeq meta start (Just x) end) <$> next)
                                           (go (\x -> hole $ ArithmSeq meta start next (Just x)) <$> end)
                                           expr hole

    go hole expr@(ListComp meta e qs)     = h meta $ listcomp (getMetaMType meta)
                                           (go (\x -> hole $ ListComp meta x qs) e)
                                           (zipList qualToDiv (\xs -> hole $ ListComp meta e xs) qs)
                                           expr hole
      where
        qualToDiv :: (TypeQual -> TypeTree) -> TypeQual -> Div
        qualToDiv hole (Guard meta e) = h meta $ guardQual (getMetaMType meta)           (go (\x -> hole $ Guard meta x) e)
        qualToDiv hole (Let meta b e) = h meta $ letQual (getMetaMType meta) (binding b) (go (\x -> hole $ Let meta b x) e)
        qualToDiv hole (Gen meta b e) = h meta $ genQual (getMetaMType meta) (binding b) (go (\x -> hole $ Gen meta b x) e)

    go hole expr@(App meta func args) = h meta $ app (getMetaMType meta) (go funcHole func) argsDivs expr hole
      where
        funcHole func = hole $ App meta func args
        argsDivs = zipList go (hole <<< App meta func) args

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
    arrow = node "<-" ["separator"] []

atom :: MType -> Atom -> Div
atom t (AInt n) = typedNode (show n) ["atom", "num"] [] t
atom t (Bool b) = typedNode (if b then "True" else "False") ["atom", "bool"] [] t
atom t (Char c) = typedNode ("'" <> c <> "'") ["atom", "char"] [] t
atom t (Name n) = typedNode n ["atom", "name"] [] t
atom t (Constr n) = typedNode n ["constr", "name"] [] t

constr :: MType -> String -> Div
constr t n = typedNode n ["constr", "name"] [] t

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
opToDiv (Tuple op (Meta meta)) = typedNode (pPrintOp op) ["op"] [] meta.mtype

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
    open  = node "[" ["brace", "left"] []
    close = node "]" ["brace", "right"] []
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
    open      = node "[" ["brace", "left"] []
    comma     = node "," ["comma"] []
    commaNext = maybe [] (\next -> [comma, next]) mnext
    dots      = node ".." ["dots", "comma"] []
    end       = fromMaybe mend
    close     = node "]" ["brace", "right"] []

binding :: TypedBinding -> Div
binding (Lit t a)         = typedNode "" ["binding", "lit"] [atom (getMetaMType t) a] (getMetaMType t)
binding (ConsLit t b1 b2) = typedNode "" ["binding", "conslit"] (listify "(" ":" ")" (binding b1 : binding b2 : Nil)) (getMetaMType t)
binding (ListLit t ls)    = typedNode "" ["binding", "listlit"] (listify "[" "," "]" (binding <$> ls)) (getMetaMType t)
binding (NTupleLit t ls)   = typedNode "" ["binding", "tuplelit"] (listify "(" "," ")" (binding <$> ls)) (getMetaMType t)
binding (ConstrLit t c) = case c of
  PrefixDataConstr name _ ls -> typedNode ""
                                  ["binding", "constrlit"]
                                  (node "(" ["brace","left"] [] : constr (getMetaMType t) name : (binding <$> ls) <> singleton (node ")" ["brace", "right"] []))
                                  (getMetaMType t)
  InfixDataConstr name _ _ b1 b2 -> typedNode ""
                                      ["binding", "constrlit"]
                                      [binding b1, constr (getMetaMType t) name, binding b2]
                                      (getMetaMType t)

type Callback = TypeTree -> (TypeTree -> TypeTree) -> (J.JQueryEvent -> J.JQuery -> Effect Unit)

-- | Create a type div with the pretty printed type as content.
createTypeDiv :: MType -> Effect J.JQuery
createTypeDiv (Just (TypeError typeError)) = makeDiv (prettyPrintTypeError typeError) ["typeContainer", "hasTypeError"]
createTypeDiv mType = makeDiv (" :: " <> maybe "" prettyPrintType mType) ["typeContainer"]

-- | Add a type tooltip to the given div.
addTypeTooltip :: MType -> J.JQuery -> Effect Unit
addTypeTooltip (Just (TypeError typeError)) div = J.setAttr "title" (prettyPrintTypeError typeError) div
addTypeTooltip mType div = J.setAttr "title" (" :: " <> maybe "" prettyPrintType mType) div

-- | Return true, if the first list of classes contains a class from the second list.
oneOfClasses :: forall f1 f2.  Foldable f1 => Foldable f2 => f1 String -> f2 String -> Boolean
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

-- | Return true if the given `MType` represents a type error.
isTypeError :: MType -> Boolean
isTypeError (Just (TypeError _)) = true
isTypeError _ = false

divToJQuery :: Boolean -> Callback -> Div -> Effect J.JQuery
divToJQuery isTopLevelDiv callback (Node { content: content, classes: classes, zipper: zipper, exprType: exprType } children) = do
  let needsContainer = needsTypeContainer classes exprType || isTopLevelDiv || isTypeError exprType
  let isTyped = isJust exprType

  container <- makeDiv "" ["container"]
  div <- makeDiv content classes

  -- if needsContainer
  --   then do
  --     typeDiv <- createTypeDiv exprType
  --     J.append typeDiv container
  --     J.append div container
  --     J.addClass "hasTypeContainer" div
  --   else pure unit

  J.append div container

  -- if isTyped
  --   then addTypeTooltip exprType div
  --   else pure unit

  _ <- for children (divToJQuery false callback >=> flip J.append div)
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

makeDiv :: forall f. Foldable f => String -> f Class -> Effect J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for_ classes (flip J.addClass d)
  pure d
