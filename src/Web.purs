module Web
  ( exprToDiv
  , divToJQuery
  , getPath
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

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) (Maybe Path)
getPath j = do
  fpath <- J.getProp pathPropName j
  if isUndefined fpath
    then return Nothing
    else return $ Just $ unsafeFromForeign fpath

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
    go hole (Lambda _ binds body) = lambda (binding <$> binds) (go hole body)
    go hole (App _ func args)     = app (go hole func) (go hole <$> args)

atom :: Atom -> Div
atom (AInt n) = node (show n) ["atom", "num"] [] 
atom (Bool b) = node (if b then "True" else "False") ["atom", "bool"] [] 
atom (Char c) = node ("'" ++ c ++ "'") ["atom", "char"] [] 
atom (Name n) = node n ["atom", "name"] [] 

-- tuple :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- tuple js t i = do
--   jtypExp <- makeDiv "" (singleton "tuple  typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dtuple <- makeDiv "" (singleton "tuple  expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   open <- makeDiv "(" (singleton "brace")
--   J.append open dtuple
--   interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js
--   close <- makeDiv ")" (singleton "brace")
--   J.append close dtuple
--   J.append dtuple jtypExp
--   return jtypExp

-- list :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- list js t   i  = do
--   jtypExp <- makeDiv "" (singleton "list typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dls <- makeDiv "" (singleton "list expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   open <- makeDiv "[" (singleton "brace")
--   J.append open dls
--   interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js
--   close <- makeDiv "]" (singleton "brace")
--   J.append close dls
--   J.append dls jtypExp
--   return jtypExp

interleave :: forall a. a -> List a -> List a
interleave _ Nil          = Nil
interleave _ (Cons x Nil) = Cons x Nil
interleave a (Cons x xs)  = Cons x $ Cons a $ interleave a xs

list :: List Div -> DivHole
list ls = node' "" ["list"] (snoc (Cons open (interleave comma ls)) close)
  where
    open = node "[" ["brace"] []
    close = node "]" ["brace"] []
    comma = node "," ["comma"] []

ntuple :: List Div -> DivHole
ntuple ls = node' "" ["tuple"] (snoc (Cons open (interleave comma ls)) close)
  where
    open = node "(" ["brace"] []
    close = node ")" ["brace"] []
    comma = node "," ["comma"] []

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

lambda :: List Div -> Div -> Div
lambda _ _ = node "" [] [] 

app :: Div -> List Div -> Div
app _ _ = node "" [] [] 

binding :: Binding -> Div
binding _ = node "" [] [] 

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

-- binding :: forall eff. Tuple IBinding (Tuple Binding  TypeBinding) -> Eff (dom :: DOM | eff) J.JQuery
-- binding b = case b of
--   Tuple (ILit i) (Tuple (Lit a) (TLit t))       -> atom a t i
--   cl@(Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))) -> do
--     jCons <- makeDiv ""  [] >>= addTypetoDiv t >>= addIdtoDiv i
--     makeDiv "(" (singleton "brace") >>= flip J.append jCons
--     consBinding cl jCons
--     makeDiv ")" (singleton "brace") >>= flip J.append jCons
--   Tuple (IListLit is i)(Tuple (ListLit bs) (TListLit tbs t)) -> do
--     jList <- makeDiv "" Nil >>= addTypetoDiv t >>= addIdtoDiv i
--     makeDiv "[" (singleton "brace") >>= flip J.append jList
--     interleaveM_
--       (\b -> binding b >>= flip J.append jList)
--       (makeDiv "," (singleton "comma") >>= flip J.append jList)
--       (zip is (zip bs tbs))
--     makeDiv "]" (singleton "brace") >>= flip J.append jList
--   Tuple (INTupleLit is i)(Tuple (NTupleLit bs) (TNTupleLit tbs t))-> do
--     jTuple <- makeDiv "" Nil >>= addTypetoDiv t >>= addIdtoDiv i
--     makeDiv "(" (singleton "brace") >>= flip J.append jTuple
--     let b = (zip is (zip bs tbs))
--     interleaveM_ (binding >=> flip J.append jTuple) (makeDiv "," (singleton "comma") >>= flip J.append jTuple) b
--     makeDiv ")" (singleton "brace") >>= flip J.append jTuple
--     return jTuple

--   _ -> makeDiv ("congrats you found a bug in Web.binding") Nil
--   where
--     consBinding :: Tuple IBinding (Tuple Binding  TypeBinding) -> J.JQuery-> Eff (dom :: DOM | eff) Unit
--     consBinding (Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))) jCons = do
--       binding (Tuple i1 (Tuple b tb)) >>= flip J.append jCons
--       makeDiv ":" (singleton "colon") >>= flip J.append jCons
--       consBinding (Tuple i2 (Tuple bs tbs)) jCons
--     consBinding b jCons = void $ binding b >>= flip J.append jCons

-- lambda :: forall eff. List J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- lambda jBinds jBody t i = do
--   jtypExp <- makeDiv "" (singleton "lambda typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   jLam <- makeDiv "" (singleton "lambda expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   open <- makeDiv "(\\" (Cons "brace" (Cons "backslash" Nil))
--   J.append open jLam
--   for jBinds (flip J.append jLam)
--   arrow <- makeDiv "->" (singleton "arrow")
--   J.append arrow jLam
--   J.append jBody jLam
--   close <- makeDiv ")" (singleton "brace")
--   J.append close jLam
--   J.append jLam jtypExp
--   return jtypExp



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



-- isString :: List Expr -> Boolean
-- isString es = length es > 0 && all isChar es
--   where
--   isChar (Atom (Char _)) = true
--   isChar _               = false

-- string :: forall eff. String -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- string str t i = do
--   jtypExp <- makeDiv "" (singleton "list string typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   jString <- makeDiv ("\"" ++ str ++ "\"") (toList ["list", "string", "expr"]) >>= addTypetoDiv t >>= addIdtoDiv i
--   J.append jString  jtypExp

-- toStr :: List Expr -> Maybe String
-- toStr Nil = Nothing
-- toStr ls  = (joinWith "" <<< fromList) <$> for ls extract
--   where
--    extract:: Expr -> Maybe String
--    extract (Atom (Char s)) = Just s
--    extract _               = Nothing

-- app :: forall eff. J.JQuery -> List J.JQuery -> Type -> Type -> Int  -> Eff (dom :: DOM | eff) J.JQuery
-- app jFunc jArgs tFunc t i = do
--   jtypExp <- makeDiv "" (singleton "app typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dApp <- makeDiv "" (singleton "app expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   J.addClass "func" jFunc
--   J.addClass "funcContainer" jFunc
--   innerExpr <- children ".expr" jFunc
--   jExpand2 <- children ".expand" jFunc
--   innerTyp <- children ".type" jExpand2
--   typeArr <- children ".type-arr" jExpand2
--   J.css {transform: "rotate(180deg)"} typeArr
--   case tFunc of
--     TypeError _ -> J.setVisible true innerTyp
--     _ -> J.setVisible false innerTyp
--   J.addClass "func" innerExpr
--   J.append jFunc dApp
--   for jArgs (flip J.append dApp)
--   J.append dApp jtypExp
--   return jtypExp

-- type Class = String



-- emptyJQuery:: forall eff . Eff (dom :: DOM | eff) J.JQuery
-- emptyJQuery = J.create ""

