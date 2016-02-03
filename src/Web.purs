module Web
  ( exprToJQuery
  , getPath
  ) where

import Prelude (class Monad, Unit, return, flip, bind, (<<<), (<$>), (++), (&&), (>), (>>=), void, ($), unit, show, id, (-))
import Data.Foldable (all)
import Data.Traversable (for)
import Data.List (List(Nil, Cons), singleton, fromList, toList, length, (..), zipWithA)
import Data.String (joinWith)
import Data.Foreign (unsafeFromForeign)
import Data.Maybe (Maybe(..))

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import DOM (DOM)

import AST (Atom(..), Binding(..), Expr(..), Op(), pPrintOp)
import Evaluator (Path(..))

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) Path
getPath j = unsafeFromForeign <$> J.getProp pathPropName j

exprToJQuery :: forall eff. Expr -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery expr = go id expr
  where
  go :: (Path -> Path) -> Expr -> Eff (dom :: DOM | eff) J.JQuery
  go p e = J.setProp pathPropName (p End) =<< case e of
    Atom a -> atom a
    Binary op e1 e2 -> do
      j1 <- go (p <<< Fst) e1
      j2 <- go (p <<< Snd) e2
      binary op j1 j2
    List es -> case toStr es of
      Just str -> string str
      Nothing  -> do
        js <- zipWithA (\i e -> go (p <<< Nth i) e) (0 .. (length es - 1)) es
        list js
    NTuple es -> do
      js <- zipWithA (\i e -> go (p <<< Nth i) e) (0 .. (length es - 1)) es
      tuple js
    SectL e op -> do
      j <- go (p <<< Fst) e
      jop <- makeDiv (pPrintOp op) (singleton "op")
      section j jop
    SectR op e -> do
      jop <- makeDiv (pPrintOp op) (singleton "op")
      j <- go (p <<< Snd) e
      section jop j
    PrefixOp op -> makeDiv ("(" ++ pPrintOp op ++ ")") (toList ["prefix", "op"])
    IfExpr cond thenExpr elseExpr -> do
      jc <- go (p <<< Fst) cond
      jt <- go (p <<< Snd) thenExpr
      je <- go (p <<< Thrd) elseExpr
      ifexpr jc jt je
    Lambda binds body -> do
      jBinds <- for binds binding
      jBody <- go (p <<< Fst) body
      lambda jBinds jBody
    App func args -> do
      jFunc <- go (p <<< Fst) func
      jArgs <- zipWithA (\i e -> go (p <<< Nth i) e) (0 .. (length args - 1)) args
      app jFunc jArgs
    e -> makeDiv ("Not yet supported: " ++ show e) Nil

atom :: forall eff. Atom -> Eff (dom :: DOM | eff) J.JQuery
atom (AInt n)      = makeDiv (show n) (toList ["atom", "num"])
atom (Bool true)  = makeDiv "True"  (toList ["atom", "bool"])
atom (Bool false) = makeDiv "False" (toList ["atom", "bool"])
atom (Char c)     = makeDiv ("'" ++ c ++ "'") (toList ["atom", "char"])
atom (Name name)  = makeDiv name (toList ["atom", "name"])

binding :: forall eff. Binding -> Eff (dom :: DOM | eff) J.JQuery
binding b = case b of
  Lit a        -> atom a
  ConsLit b bs -> do
    jCons <- makeDiv "" Nil
    makeDiv "(" (singleton "brace") >>= flip J.append jCons
    binding b             >>= flip J.append jCons
    makeDiv ":" (singleton "colon") >>= flip J.append jCons
    binding bs            >>= flip J.append jCons
    makeDiv ")" (singleton "brace") >>= flip J.append jCons
  ListLit bs -> do
    jList <- makeDiv "" Nil
    makeDiv "[" (singleton "brace") >>= flip J.append jList
    for bs $ \b -> do
      binding b >>= flip J.append jList
      makeDiv "," (singleton "comma") >>= flip J.append jList
    makeDiv "]" (singleton "brace") >>= flip J.append jList
  NTupleLit bs -> do
    jTuple <- makeDiv "" Nil
    makeDiv "(" (singleton "brace") >>= flip J.append jTuple
    interleaveM_ (binding >=> flip J.append jTuple) (makeDiv "," (singleton "comma") >>= flip J.append jTuple) bs
    makeDiv ")" (singleton "brace") >>= flip J.append jTuple
    return jTuple

lambda :: forall eff. List J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
lambda jBinds jBody = do
  jLam <- makeDiv "" (singleton "lambda")
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

binary :: forall eff. Op -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
binary op j1 j2 = do
  dBin <- makeDiv "" (singleton "binary")
  J.append j1 dBin
  dOp <- makeDiv (pPrintOp op) (singleton "op")
  J.append dOp dBin
  J.append j2 dBin
  return dBin

section :: forall eff. J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
section j1 j2 = do
  jSect <- makeDiv "" (singleton "section")
  open <- makeDiv "(" (singleton "brace")
  J.append open jSect
  J.append j1 jSect
  J.append j2 jSect
  close <- makeDiv ")" (singleton "brace")
  J.append close jSect
  return jSect

ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
ifexpr cond thenExpr elseExpr = do
  dIf <- makeDiv "" (singleton "if")
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

tuple :: forall eff. List J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
tuple js = do
  dtuple <- makeDiv "" (singleton "tuple")
  open <- makeDiv "(" (singleton "brace")
  J.append open dtuple
  interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js
  close <- makeDiv ")" (singleton "brace")
  J.append close dtuple
  return dtuple

list :: forall eff. List J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
list js = do
  dls <- makeDiv "" (singleton "list")
  open <- makeDiv "[" (singleton "brace")
  J.append open dls
  interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js
  close <- makeDiv "]" (singleton "brace")
  J.append close dls
  return dls

isString :: List Expr -> Boolean
isString es = length es > 0 && all isChar es
  where
  isChar (Atom (Char _)) = true
  isChar _               = false

string :: forall eff. String -> Eff (dom :: DOM | eff) J.JQuery
string str = makeDiv ("\"" ++ str ++ "\"") (toList ["list", "string"])

toStr :: List Expr -> Maybe String
toStr Nil = Nothing
toStr ls  = (joinWith "" <<< fromList) <$> for ls extract
  where
   extract:: Expr -> Maybe String
   extract (Atom (Char s)) = Just s
   extract _               = Nothing

app :: forall eff. J.JQuery -> List J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
app jFunc jArgs = do
  dApp <- makeDiv "" (singleton "app")
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
