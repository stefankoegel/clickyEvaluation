module Web
  ( exprToJQuery
  , getPath
  ) where

import Control.Monad.Eff
import Control.Monad.Eff.JQuery as J
import DOM
import Prelude

import Data.Foldable (all)
import Data.Traversable (for)
import Data.List
import Data.Tuple
import Data.String (joinWith)
import Data.Foreign (unsafeFromForeign)
import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))

import AST
import Evaluator (Path(..))
import TypeChecker (prettyPrintType,extractType)

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) Path
getPath j = unsafeFromForeign <$> J.getProp pathPropName j

-- TODO rename to fit new Type
exprToJQuery :: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery output = go id output
  where
  go :: (Path -> Path) -> Output -> Eff (dom :: DOM | eff) J.JQuery
  go p o = J.setProp pathPropName (p End) =<< case o of
    {expr:(Atom a), typ:(TAtom t)} -> atom a t
    {expr:(Binary op e1 e2), typ:(TBinary opt tt1 tt2 t)} -> do
      j1 <- go (p <<< Fst) {expr:e1, typ:tt1}
      j2 <- go (p <<< Snd) {expr:e2, typ:tt2}
      binary op opt t j1 j2 

    {expr:(List es), typ:(TListTree ts t)} -> case isString es of
                  true  -> string es t
                  false -> do js <- zipWithA (\i (Tuple e t) -> go (p <<< Nth i) {expr:e, typ:t}) (0 .. (length es - 1)) (zip es ts)
                              list js (map extractType ts) t
    {expr:NTuple es, typ:TNTuple ts t} -> do
      js <- zipWithA (\i (Tuple e t) -> go (p <<< Nth i) {expr:e, typ:t}) (0 .. (length es - 1)) (zip es ts)
      tuple js (map extractType ts) t
    {expr:SectL e op, typ:TSectL tt opt t} -> do
      j <- go (p <<< Fst) {expr:e, typ:tt}
      jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt
      section j jop t
    {expr:SectR op e, typ:TSectR opt tt t} -> do
      jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt
      j <- go (p <<< Snd) {expr:e, typ:tt}
      section jop j t
    {expr:PrefixOp op, typ:TPrefixOp t} -> makeDiv ("(" ++ pPrintOp op ++ ")") (toList ["prefix", "op"]) >>= addTypetoDiv t
    {expr:IfExpr cond thenExpr elseExpr, typ:TIfExpr tt1 tt2  tt3 t} -> do
      jc <- go (p <<< Fst) {expr:cond, typ:tt1}
      jt <- go (p <<< Snd) {expr:thenExpr, typ:tt2}
      je <- go (p <<< Thrd) {expr:elseExpr, typ:tt3}
      ifexpr jc jt je t
    {expr:Lambda binds body, typ:TLambda lb tt t} -> do
      jBinds <- for (zip binds lb) binding
      jBody <- go (p <<< Fst) {expr:body, typ:tt}
      lambda jBinds jBody t
    {expr:App func args, typ:TApp tt ts t} -> do
      jFunc <- go (p <<< Fst) {expr:func, typ:tt}
      jArgs <- zipWithA (\i (Tuple e t) -> go (p <<< Nth i) {expr:e, typ:t}) (0 .. (length args - 1)) (zip args ts)
      app jFunc jArgs t


atom :: forall eff. Atom -> Type -> Eff (dom :: DOM | eff) J.JQuery
atom (AInt n) t     = makeDiv (show n) (toList ["atom", "num"]) >>= addTypetoDiv (TypCon "HALLO") >>= addTypetoDiv t
atom (Bool true) t  = makeDiv "True"  (toList ["atom", "bool"]) >>= addTypetoDiv t
atom (Bool false) t = makeDiv "False" (toList ["atom", "bool"]) >>= addTypetoDiv t
atom (Char c) t    = (makeDiv ("'" ++ c ++ "'") (toList ["atom", "char"])) >>= addTypetoDiv t
atom (Name name) t = makeDiv name (toList ["atom", "name"]) >>= addTypetoDiv t

binding :: forall eff. Tuple Binding  TypeBinding -> Eff (dom :: DOM | eff) J.JQuery
binding b = case b of
  Tuple (Lit a) (TLit t)       -> atom a t
  Tuple (ConsLit b bs) (TConsLit tb tbs t)-> do
    jCons <- makeDiv "" Nil >>= addTypetoDiv t
    makeDiv "(" (singleton "brace") >>= flip J.append jCons
    binding (Tuple b tb)            >>= flip J.append jCons
    makeDiv ":" (singleton "colon") >>= flip J.append jCons
    binding (Tuple bs tbs)           >>= flip J.append jCons
    makeDiv ")" (singleton "brace") >>= flip J.append jCons
  Tuple (ListLit bs) (TListLit tbs t) -> do
    jList <- makeDiv "" Nil >>= addTypetoDiv t
    makeDiv "[" (singleton "brace") >>= flip J.append jList
    let bx = zip bs tbs
    for bx $ \b -> do
      binding b >>= flip J.append jList
      makeDiv "," (singleton "comma") >>= flip J.append jList
    makeDiv "]" (singleton "brace") >>= flip J.append jList
  Tuple (NTupleLit bs) (TNTupleLit tbs t)-> do
    jTuple <- makeDiv "" Nil >>= addTypetoDiv t
    makeDiv "(" (singleton "brace") >>= flip J.append jTuple
    let b = (zip bs tbs)
    interleaveM_ (binding >=> flip J.append jTuple) (makeDiv "," (singleton "comma") >>= flip J.append jTuple) b
    makeDiv ")" (singleton "brace") >>= flip J.append jTuple
    return jTuple

lambda :: forall eff. List J.JQuery -> J.JQuery -> Type -> Eff (dom :: DOM | eff) J.JQuery
lambda jBinds jBody t = do
  jLam <- makeDiv "" (singleton "lambda") >>= addTypetoDiv t
  open <- makeDiv "(" (singleton "brace")
  J.append open jLam
  bs <- makeDiv "\\" (singleton "backslash")
  J.append bs jLam
  for jBinds (flip J.append jLam)
  arrow <- makeDiv "->" (singleton "arrow")
  J.append arrow jLam
  J.append jBody jLam
  close <- makeDiv ")" (singleton "brace")
  J.append close jLam
  return jLam

binary :: forall eff. Op -> Type -> Type -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
binary op opt t j1 j2 = do
  dBin <- makeDiv "" (singleton "binary") >>= addTypetoDiv t
  J.append j1 dBin
  dOp <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt
  J.append dOp dBin
  J.append j2 dBin
  return dBin

section :: forall eff. J.JQuery -> J.JQuery -> Type -> Eff (dom :: DOM | eff) J.JQuery
section j1 j2 t = do
  jSect <- makeDiv "" (singleton "section") >>= addTypetoDiv t
  open <- makeDiv "(" (singleton "brace")
  J.append open jSect
  J.append j1 jSect
  J.append j2 jSect
  close <- makeDiv ")" (singleton "brace")
  J.append close jSect
  return jSect

ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Type -> Eff (dom :: DOM | eff) J.JQuery
ifexpr cond thenExpr elseExpr t = do
  dIf <- makeDiv "" (singleton "if") >>= addTypetoDiv t
  makeDiv "if" (singleton "keyword") >>= flip J.append dIf
  J.append cond dIf
  makeDiv "then" (singleton "keyword") >>= flip J.append dIf
  J.append thenExpr dIf
  makeDiv "else" (singleton "keyword") >>= flip J.append dIf
  J.append elseExpr dIf
  return dIf

interleaveM_ :: forall a b m. (Monad m) => (a -> m b) -> m b -> List a -> m Unit
interleaveM_ f sep = go
  where
  go Nil     = return unit
  go (Cons x Nil)    = void $ f x
  go (Cons x xs) = f x *> sep *> go xs

tuple :: forall eff. List J.JQuery -> List Type -> Type -> Eff (dom :: DOM | eff) J.JQuery
tuple js ts t = do
  dtuple <- makeDiv "" (singleton "tuple") >>= addTypetoDiv t
  open <- makeDiv "(" (singleton "brace")
  js' <- zipWithA (\j t -> addTypetoDiv t j) js ts
  J.append open dtuple
  interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js'
  close <- makeDiv ")" (singleton "brace")
  J.append close dtuple
  return dtuple

list :: forall eff. List J.JQuery -> List Type -> Type -> Eff (dom :: DOM | eff) J.JQuery
list js ts t = do
  dls <- makeDiv "" (singleton "list") >>= addTypetoDiv t
  open <- makeDiv "[" (singleton "brace")
  js' <- zipWithA (\j t -> addTypetoDiv t j) js ts
  J.append open dls
  interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js'
  close <- makeDiv "]" (singleton "brace")
  J.append close dls
  return dls

isString :: List Expr -> Boolean
isString es = length es > 0 && all isChar es
  where
  isChar (Atom (Char _)) = true
  isChar _               = false

string :: forall eff. List Expr -> Type -> Eff (dom :: DOM | eff) J.JQuery
string es t = do
  let str = "\"" ++ joinWith "" (fromList ((\(Atom (Char s)) -> s) <$> es)) ++ "\""
  dstring <- makeDiv str (toList ["list", "string"]) >>= addTypetoDiv t
  return dstring

app :: forall eff. J.JQuery -> List J.JQuery -> Type -> Eff (dom :: DOM | eff) J.JQuery
app jFunc jArgs t = do
  dApp <- makeDiv "" (singleton "app") >>= addTypetoDiv t
  J.addClass "func" jFunc
  J.append jFunc dApp
  for jArgs (flip J.append dApp)
  return dApp

type Class = String

makeDiv :: forall eff. String -> List Class -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for classes (flip J.addClass d)
  return d


addTypetoDiv:: forall eff. Type -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addTypetoDiv typ = J.setAttr "title" (prettyPrintType typ)
