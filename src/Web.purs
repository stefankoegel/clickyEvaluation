module Web
  ( exprToDiv
  , divToJQuery
  , getPath
  , Prsenter
  ) where

import Prelude
import Data.Foldable (all)
import Data.Traversable (for, traverse)
import Data.String (joinWith)
import Data.List (List(Nil, Cons), singleton, fromList, toList, length, zip, (..), zipWithA)
import Data.Foreign (unsafeFromForeign, isUndefined)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import Control.Monad.State (State, put, get, runState)
import DOM (DOM)


import AST (Expr, Tree(..), Binding(..), Expr(..), Atom(..), Op(..), pPrintOp, Path(..))
import JSHelpers (showTooltip, children)

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) (Maybe Path)
getPath j = do
  fpath <- J.getProp pathPropName j
  if isUndefined fpath
    then return Nothing
    else return $ Just $ unsafeFromForeign fpath

data Prsenter a b = Node a b (List (Prsenter a b))

type Div = Prsenter String (List String)

exprToDiv:: Expr -> Div
exprToDiv expr = go expr
  where
    go (Atom _ a) = atom a 
    go (List _ ls) = list (go <$> ls)
    go (NTuple _ ls) = ntuple (go <$> ls)
    go (Binary _ op e1 e2) = binary op (go e1) (go e2)
    go (Unary _ op e) = unary op (go e)
    go (SectL _ e op) = sectl (go e) op
    go (SectR _ op e) = sectr op (go e)
    go (PrefixOp _ op) = prefixOp op
    go (IfExpr _ ce te ee) = ifexpr (go ce) (go te) (go ee)
    go (LetExpr _ b v e) = letexpr (binding b) (go v) (go e)
    go (Lambda _ binds body) = lambda (binding <$> binds) (go body)
    go (App _ func args) = app (go func) (go <$> args)

atom :: Atom -> Div
atom (AInt n) = Node (show n) (toList ["atom", "num"]) Nil
atom (Bool b) = Node (if b then "True" else "False") (toList ["atom", "bool"]) Nil
atom (Char c) = Node ("'" ++ c ++ "'") (toList ["atom", "char"]) Nil

list :: List Div -> Div
list _ = Node "" (toList []) Nil

ntuple :: List Div -> Div
ntuple _ = Node "" (toList []) Nil

binary :: Op -> Div -> Div -> Div
binary op d1 d2 = Node "" (toList ["binary"]) (toList [d1, opDiv, d2])
  where
    opDiv = Node (pPrintOp op) (toList ["op"]) Nil

unary :: Op -> Div -> Div
unary _ _ = Node "" (toList []) Nil

sectl :: Div -> Op -> Div
sectl _ _ = Node "" (toList []) Nil

sectr :: Op -> Div -> Div
sectr _ _ = Node "" (toList []) Nil

prefixOp :: Op -> Div
prefixOp _ = Node "" (toList []) Nil

ifexpr :: Div -> Div -> Div -> Div
ifexpr _ _ _ = Node "" (toList []) Nil

letexpr :: Div -> Div -> Div -> Div
letexpr _ _ _ = Node "" (toList []) Nil

lambda :: List Div -> Div -> Div
lambda _ _ = Node "" (toList []) Nil

app :: Div -> List Div -> Div
app _ _ = Node "" (toList []) Nil

binding :: Binding -> Div
binding _ = Node "" (toList []) Nil

divToJQuery :: forall eff. Div -> Eff (dom :: DOM | eff) J.JQuery
divToJQuery (Node content classes children) = do
  div <- makeDiv content classes
  for children (divToJQuery >=> flip J.append div)
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
--     jCons <- makeDiv "" Nil >>= addTypetoDiv t >>= addIdtoDiv i
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

-- interleaveM_ :: forall a b m. (Monad m) => (a -> m b) -> m b -> List a -> m Unit
-- interleaveM_ f sep = go
--   where
--   go Nil     = return unit
--   go (Cons x Nil)    = void $ f x
--   go (Cons x xs) = f x *> sep *> go xs

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

