module Evaluator
  ( Path(..)
  , Env()
  , evalPath1
  , defsToEnv
  ) where

import Data.Array    (head, mapMaybe, (!!), updateAt, elemIndex)
import Data.StrMap   (StrMap(), empty, lookup, insert)
import Data.Tuple
import Data.Maybe
import Data.Foldable (foldl, foldMap, any)

import Math (pow)

import Control.Apply ((*>))
import Control.Monad.State
import Control.Monad.State.Trans
import Control.Monad.State.Class
import Control.Monad.Trans

import AST

data Path = Nth Number Path
          | Fst Path
          | Snd Path
          | End

instance showPath :: Show Path where
  show p = case p of
    Nth i p -> "(Nth " ++ show i ++ " " ++ show p ++")"
    Fst   p -> "(Fst " ++ show p ++")"
    Snd   p -> "(Snd " ++ show p ++")"
    End     -> "End"

mapWithPath :: Path -> (Expr -> Maybe Expr) -> Expr -> Maybe Expr
mapWithPath p f = go p
  where
  go End e     = f e
  go (Fst p) e = case e of
    Binary op e1 e2 -> Binary op <$> go p e1 <*> Just e2
    Unary op e      -> Unary op  <$> go p e
    SectL e op      -> SectL     <$> go p e <*> Just op
    Lambda bs body  -> Lambda bs <$> go p body
    App e es        -> App       <$> go p e <*> Just es
    _               -> Nothing
  go (Snd p) e = case e of
    Binary op e1 e2 -> Binary op e1 <$> go p e2
    SectR op e      -> SectR op     <$> go p e
    _               -> Nothing
  go (Nth n p) e = case e of
    List es  -> List  <$> mapMaybeIndex n (go p) es
    NTuple es -> NTuple <$> mapMaybeIndex n (go p) es
    App e es -> App e <$> mapMaybeIndex n (go p) es
    _        -> Nothing

mapMaybeIndex :: forall m a. Number -> (a -> Maybe a) -> [a] -> Maybe [a]
mapMaybeIndex i f as = do
  a <- (as !! i) >>= f
  return $ updateAt i a as

evalPath1 :: Env -> Path -> Expr -> Maybe Expr
evalPath1 env path expr = mapWithPath path (eval1 env) expr

type Env = StrMap [Tuple [Binding] Expr]

defsToEnv :: [Definition] -> Env
defsToEnv = foldl insertDef empty

insertDef :: Env -> Definition -> Env
insertDef env (Def name bindings body) = case lookup name env of
  Nothing   -> insert name [Tuple bindings body] env
  Just defs -> insert name (defs ++ [Tuple bindings body]) env

eval1 :: Env -> Expr -> Maybe Expr
eval1 env expr = case expr of
  (Binary op e1 e2)             -> binary op e1 e2
  (Unary op e)                  -> unary op e
  (Atom (Name name))            -> apply env name []
  (List (e:es))                 -> Just $ Binary Cons e (List es)
  (App (Binary Composition f g) [e]) -> Just $ App f [App g [e]]
  (App (Lambda binds body) args) -> matchls binds args body
  (App (SectL e1 op) [e2])      -> Just $ Binary op e1 e2
  (App (SectR op e2) [e1])      -> Just $ Binary op e1 e2
  (App (Prefix op) [e1, e2])    -> Just $ Binary op e1 e2
  (App (Atom (Name name)) args) -> apply env name args
  (App (App func es) es')       -> Just $ App func (es ++ es')
  _                 -> Nothing

binary :: Op -> Expr -> Expr -> Maybe Expr
binary = go
  where
  go Power (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ pow i j

  go Mul (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i * j
  go Div (Atom (Num i)) (Atom (Num 0)) = Nothing
  go Div (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ Math.floor (i / j)
  go Mod (Atom (Num i)) (Atom (Num 0)) = Nothing
  go Mod (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i % j

  go Add (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i + j
  go Sub (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Num $ i - j

  go Cons   e          (List es)  = Just $ List $ e:es
  go Append (List es1) (List es2) = Just $ List $ es1 ++ es2

  go Eq  (Atom a1) (Atom a2) = Just $ Atom $ Bool $ a1 == a2
  go Neq (Atom a1) (Atom a2) = Just $ Atom $ Bool $ a1 /= a2
  go Leq (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Bool $ i <= j
  go Lt  (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Bool $ i < j
  go Geq (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Bool $ i >= j
  go Gt  (Atom (Num i)) (Atom (Num j)) = Just $ Atom $ Bool $ i > j

  go And (Atom (Bool true))  b = Just b
  go And (Atom (Bool false)) _ = Just $ Atom $ Bool $ false

  go Or  (Atom (Bool true))  _ = Just $ Atom $ Bool $ true
  go Or  (Atom (Bool false)) b = Just b

  go Dollar f e = Just $ App f [e]

  go _       _               _               = Nothing

unary :: Op -> Expr -> Maybe Expr
unary Sub (Atom (Num i)) = Just $ Atom $ Num (-i)
unary _   _              = Nothing

apply :: Env -> String -> [Expr] -> Maybe Expr
apply env name args = case lookup name env of
  Nothing    -> Nothing
  Just cases -> head $ mapMaybe app cases
    where
    app :: Tuple [Binding] Expr -> Maybe Expr
    app (Tuple binds body) = matchls binds args body

matchls :: [Binding] -> [Expr] -> Expr -> Maybe Expr
matchls []     []     expr = Just expr
matchls (b:bs) (e:es) expr = do
  expr' <- execStateT (match b e) expr
  matchls bs es expr'
matchls []     es     expr = Just $ App expr es
matchls _ _ _ = Nothing

match :: Binding -> Expr -> StateT Expr Maybe Unit
match (Lit (Name x))   e                = modify (replace x e)
match (Lit l)          (Atom a)         | a == l  = return unit
match (ConsLit b bs)   (List (e:es))    = match b e *> match bs (List es)
match (ConsLit b bs)   (Binary Cons e es) = match b e *> match bs es
match (ListLit [])     (List [])        = return unit
match (ListLit (b:bs)) (List (e:es))    = match b e *> match (ListLit bs) (List es)
match (ListLit (b:bs)) (Binary Cons e es) = match b e *> match (ListLit bs) es
match (NTupleLit bs)   (NTuple es)      = match (ListLit bs) (List es)
match _                _                = lift Nothing

boundNames :: Binding -> [String]
boundNames = go
  where
  go (Lit (Name name)) = [name]
  go (ConsLit b1 b2)   = go b1 ++ go b2
  go (ListLit bs)      = foldMap go bs
  go (NTupleLit bs)    = foldMap go bs

isNameBound :: String -> Binding -> Boolean
isNameBound name binding = (elemIndex name $ boundNames binding) >= 0

replace :: String -> Expr -> Expr -> Expr
replace name value = go
  where
  go expr = case expr of
    a@(Atom (Name str)) -> if str == name then value else a
    (List exprs)        -> List (go <$> exprs)
    (NTuple exprs)      -> NTuple (go <$> exprs)
    (Binary op e1 e2)   -> Binary op (go e1) (go e2)
    (Unary op e)        -> Unary op (go e)
    (SectL e op)        -> SectL (go e) op
    (SectR op e)        -> SectR op (go e)
    l@(Lambda binds body) -> if any (isNameBound name) binds
                               then l
                               else Lambda binds (go body)
    (App func exprs)    -> App (go func) (go <$> exprs)
    e                   -> e
