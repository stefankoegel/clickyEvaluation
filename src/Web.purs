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
import Control.Monad.Eff.Console (CONSOLE)
import Control.Monad.Eff.JQuery as J
import DOM (DOM)

import AST (Atom(..), Binding(..), MType, Op, QualTree(..), Tree(..), TypeTree, TypedBinding, Meta(..), Index,
            Type(..), TypeQual, DataConstr(..), pPrintOp, prettyPrintType, prettyPrintTypeError, getMetaMType)

import AST as AST


data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple TypeTree (TypeTree -> TypeTree)), exprType :: MType }

type DivHole = TypeTree -> (TypeTree -> TypeTree) -> Div

type OpTuple = Tuple Op Meta

-- Tells, which nodes are to be marked as clicked or evaluated, if any.
type Highlight = { clicked: Maybe Index, evaluated: Maybe Index }

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
    go hole      (Atom meta a)            = atom (getMetaMType meta) a
    go hole expr@(List meta ls)           = case toString ls of
                                           Nothing  -> list (getMetaMType meta) (zipList go (hole <<< List AST.emptyMeta) ls) expr hole
                                           Just str -> typedNode ("\"" <> str <> "\"") ["list", "string"] [] (getMetaMType meta)
    go hole expr@(NTuple meta ls)         = ntuple (getMetaMType meta) (zipList go (hole <<< NTuple AST.emptyMeta) ls) expr hole
    go hole expr@(Binary meta opTuple e1 e2) = binary (getMetaMType meta) opTuple
                                           (go (\e1 -> hole $ Binary AST.emptyMeta opTuple e1 e2) e1)
                                           (go (\e2 -> hole $ Binary AST.emptyMeta opTuple e1 e2) e2)
                                           expr hole
    go hole expr@(Unary meta opTuple e)   = unary (getMetaMType meta) opTuple (go (hole <<< Unary AST.emptyMeta opTuple) e) expr hole
    go hole expr@(SectL meta e opTuple)   = sectl (getMetaMType meta) (go (\e -> hole $ SectL AST.emptyMeta e opTuple) e) opTuple expr hole
    go hole expr@(SectR meta opTuple e)   = sectr (getMetaMType meta) opTuple (go (hole <<< SectR AST.emptyMeta opTuple) e) expr hole
    go hole      (PrefixOp meta opTuple)  = prefixOp (getMetaMType meta) opTuple
    go hole expr@(IfExpr meta ce te ee)   = ifexpr (getMetaMType meta)
                                           (go (\ce -> hole $ IfExpr AST.emptyMeta ce te ee) ce)
                                           (go (\te -> hole $ IfExpr AST.emptyMeta ce te ee) te)
                                           (go (\ee -> hole $ IfExpr AST.emptyMeta ce te ee) ee)
                                           expr hole
    go hole expr@(LetExpr meta bes body)  = letexpr (getMetaMType meta)
                                           (zipList
                                              (\listHole (Tuple b e) -> Tuple (binding b) (go (\x -> listHole $ Tuple b x) e))
                                              (\xs -> hole $ LetExpr AST.emptyMeta xs body)
                                              bes)
                                           (go (\x -> hole $ LetExpr AST.emptyMeta bes x) body)
                                           expr hole
    go hole expr@(Lambda meta binds body) = lambda (getMetaMType meta) (binding <$> binds) (go (hole <<< Lambda AST.emptyMeta binds) body) expr hole

    go hole expr@(ArithmSeq meta start next end)
                                       = arithmseq (getMetaMType meta)
                                           (go (\x -> hole $ ArithmSeq AST.emptyMeta x next end) start)
                                           (go (\x -> hole $ ArithmSeq AST.emptyMeta start (Just x) end) <$> next)
                                           (go (\x -> hole $ ArithmSeq AST.emptyMeta start next (Just x)) <$> end)
                                           expr hole

    go hole expr@(ListComp meta e qs)     = listcomp (getMetaMType meta)
                                           (go (\x -> hole $ ListComp AST.emptyMeta x qs) e)
                                           (zipList qualToDiv (\xs -> hole $ ListComp AST.emptyMeta e xs) qs)
                                           expr hole
      where
        qualToDiv :: (TypeQual -> TypeTree) -> TypeQual -> Div
        qualToDiv hole (Guard meta e) = guardQual (getMetaMType meta)           (go (\x -> hole $ Guard AST.emptyMeta x) e)
        qualToDiv hole (Let meta b e) = letQual (getMetaMType meta) (binding b) (go (\x -> hole $ Let AST.emptyMeta b x) e)
        qualToDiv hole (Gen meta b e) = genQual (getMetaMType meta) (binding b) (go (\x -> hole $ Gen AST.emptyMeta b x) e)

    go hole expr@(App meta func args) = app (getMetaMType meta) (go funcHole func) argsDivs expr hole
      where
        funcHole func = hole $ App AST.emptyMeta func args
        argsDivs = zipList go (hole <<< App AST.emptyMeta func) args

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
atom t (Constr n) = typedNode n ["atom", "name", "dataConstructor"] [] t

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
binding (ConstrLit t constr) = case constr of
  PrefixDataConstr name _ ls -> typedNode ""
                                  ["binding", "constrlit"]
                                  (atom (getMetaMType t) (Name name) : (binding <$> ls))
                                  (getMetaMType t)
  InfixDataConstr name _ _ b1 b2 -> typedNode ""
                                      ["binding", "constrlit"]
                                      [binding b1, atom (getMetaMType t) (Name name), binding b2]
                                      (getMetaMType t)

type Callback = forall eff. TypeTree -> (TypeTree -> TypeTree) -> (J.JQueryEvent -> J.JQuery -> Eff (dom :: DOM, console :: CONSOLE | eff) Unit)

-- | Create a type div with the pretty printed type as content.
createTypeDiv :: forall eff. MType -> Eff (dom :: DOM , console :: CONSOLE| eff) J.JQuery
createTypeDiv (Just (TypeError typeError)) = makeDiv (prettyPrintTypeError typeError) ["typeContainer", "hasTypeError"]
createTypeDiv mType = makeDiv (" :: " <> maybe "" prettyPrintType mType) ["typeContainer"]

-- | Add a type tooltip to the given div.
addTypeTooltip :: forall eff. MType -> J.JQuery -> Eff (dom :: DOM , console :: CONSOLE| eff) Unit
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

-- | Return true if the given `MType` represents a type error.
isTypeError :: MType -> Boolean
isTypeError (Just (TypeError _)) = true
isTypeError _ = false

divToJQuery :: forall eff. Boolean -> Callback -> Div -> Eff (dom :: DOM, console :: CONSOLE | eff) J.JQuery
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

makeDiv :: forall f eff. Foldable f => String -> f Class -> Eff (dom :: DOM , console :: CONSOLE| eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for_ classes (flip J.addClass d)
  pure d
