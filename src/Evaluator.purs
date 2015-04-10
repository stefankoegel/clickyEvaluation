module Evaluator
  ( Path(..)
  , Env()
  , evalPath1
  , defsToEnv
  ) where

import Data.Array    (head, mapMaybe, (!!), updateAt, elemIndex, length)
import Data.StrMap   (StrMap(), empty, lookup, insert)
import Data.Tuple    (Tuple(Tuple), fst, snd)
import Data.Maybe
import Data.Foldable (foldl, foldMap, any)
import Data.Identity
import Data.Either

import Math (pow)

import Control.Apply ((*>))
import Control.Alt ((<|>))
import qualified Control.Plus as P
import Control.Monad.State
import Control.Monad.State.Trans
import Control.Monad.State.Class

import Control.Monad.Writer
import Control.Monad.Writer.Trans
import Control.Monad.Writer.Class

import Control.Monad.Error
import Control.Monad.Error.Trans
import Control.Monad.Error.Class

import Control.Monad.Trans

import AST

type Matching = Tuple Atom Expr

type Evaluator = WriterT [Matching] (ErrorT String Identity)

runEvalM :: forall a. Evaluator a -> Either String (Tuple a [Matching])
runEvalM = runIdentity <<< runErrorT <<< runWriterT

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

mapWithPath :: Path -> (Expr -> Evaluator Expr) -> Expr -> Evaluator Expr
mapWithPath p f = go p
  where
  go End e     = f e
  go (Fst p) e = case e of
    Binary op e1 e2 -> Binary op <$> go p e1 <*> pure e2
    Unary op e      -> Unary op  <$> go p e
    SectL e op      -> SectL     <$> go p e <*> pure op
    Lambda bs body  -> Lambda bs <$> go p body
    App e es        -> App       <$> go p e <*> pure es
    _               -> throwError $ "Cannot match " ++ show (Fst p) ++ " with " ++ show e
  go (Snd p) e = case e of
    Binary op e1 e2 -> Binary op e1 <$> go p e2
    SectR op e      -> SectR op     <$> go p e
    _               -> throwError $ "Cannot match " ++ show (Snd p) ++ " with " ++ show e
  go (Nth n p) e = case e of
    List es  -> List  <$> mapMaybeIndex n (go p) es
    NTuple es -> NTuple <$> mapMaybeIndex n (go p) es
    App e es -> App e <$> mapMaybeIndex n (go p) es
    _        -> throwError $ "Cannot match " ++ show (Nth n p) ++ " with " ++ show e

mapMaybeIndex :: forall m a. Number -> (a -> Evaluator a) -> [a] -> Evaluator [a]
mapMaybeIndex i f as = do
  case as !! i of
    Nothing -> throwError $ "Nothing at index " ++ show i ++ "! (length = " ++ show (length as) ++ ")"
    Just a  -> do
      a' <- f a
      return $ updateAt i a' as

evalPath1 :: Env -> Path -> Expr -> Either String (Tuple Expr [Tuple Atom Expr])
evalPath1 env path expr = runEvalM $ mapWithPath path (eval1 env) expr

type Env = StrMap [Tuple [Binding] Expr]

defsToEnv :: [Definition] -> Env
defsToEnv = foldl insertDef empty

insertDef :: Env -> Definition -> Env
insertDef env (Def name bindings body) = case lookup name env of
  Nothing   -> insert name [Tuple bindings body] env
  Just defs -> insert name (defs ++ [Tuple bindings body]) env

eval1 :: Env -> Expr -> Evaluator Expr
eval1 env expr = case expr of
  (Binary op e1 e2)                  -> binary op e1 e2
  (Unary op e)                       -> unary op e
  (Atom (Name name))                 -> apply env name []
  (List (e:es))                      -> return $ Binary Cons e (List es)
  (App (Binary Composition f g) [e]) -> return $ App f [App g [e]]
  (App (Lambda binds body) args)     -> execMatcher (matchls binds args) body
  (App (SectL e1 op) [e2])           -> return $ Binary op e1 e2
  (App (SectR op e2) [e1])           -> return $ Binary op e1 e2
  (App (Prefix op) [e1, e2])         -> return $ Binary op e1 e2
  (App (Atom (Name name)) args)      -> apply env name args
  (App (App func es) es')            -> return $ App func (es ++ es')
  _ -> throwError $ "Cannot evaluate " ++ show expr

binary :: Op -> Expr -> Expr -> Evaluator Expr
binary = go
  where
  retA = return <<< Atom
  go Power (Atom (Num i)) (Atom (Num j)) = retA $ Num $ pow i j

  go Mul (Atom (Num i)) (Atom (Num j)) = retA $ Num $ i * j
  go Div (Atom (Num i)) (Atom (Num 0)) = throwError "Division by zero!"
  go Div (Atom (Num i)) (Atom (Num j)) = retA $ Num $ Math.floor (i / j)
  go Mod (Atom (Num i)) (Atom (Num 0)) = throwError "Mod by zero!"
  go Mod (Atom (Num i)) (Atom (Num j)) = retA $ Num $ i % j

  go Add (Atom (Num i)) (Atom (Num j)) = retA $ Num $ i + j
  go Sub (Atom (Num i)) (Atom (Num j)) = retA $ Num $ i - j

  go Cons   e          (List es)  = return $ List $ e:es
  go Append (List es1) (List es2) = return $ List $ es1 ++ es2

  go Eq  (Atom a1) (Atom a2) = retA $ Bool $ a1 == a2
  go Neq (Atom a1) (Atom a2) = retA $ Bool $ a1 /= a2
  go Leq (Atom (Num i)) (Atom (Num j)) = retA $ Bool $ i <= j
  go Lt  (Atom (Num i)) (Atom (Num j)) = retA $ Bool $ i < j
  go Geq (Atom (Num i)) (Atom (Num j)) = retA $ Bool $ i >= j
  go Gt  (Atom (Num i)) (Atom (Num j)) = retA $ Bool $ i > j

  go And (Atom (Bool true))  b = return b
  go And (Atom (Bool false)) _ = retA $ Bool $ false

  go Or  (Atom (Bool true))  _ = retA $ Bool $ true
  go Or  (Atom (Bool false)) b = return b

  go Dollar f e = return $ App f [e]

  go op e1 e2 = throwError $ "Cannot apply operator " ++ show op ++  " to " ++ show e1 ++ " and " ++ show e2

unary :: Op -> Expr -> Evaluator Expr
unary Sub (Atom (Num i)) = return $ Atom $ Num (-i)
unary op e = throwError $ "Cannot apply unary operator " ++ show op ++ " to " ++ show e

apply :: Env -> String -> [Expr] -> Evaluator Expr
apply env name args = case lookup name env of
  Nothing    -> throwError $ "Unknown function: " ++ name
  Just cases -> case runEvalM $ foldl (<|>) P.empty (app <$> cases) of
    Right (Tuple expr _) -> return expr
    Left msg   -> throwError $ "No matching funnction found for " ++ name ++ "(last reason: " ++ msg ++ ")"
  where
  app :: Tuple [Binding] Expr -> Evaluator Expr
  app (Tuple binds body) = execMatcher (matchls binds args) body

type Matcher = StateT Expr Evaluator

matchls :: [Binding] -> [Expr] -> Matcher Unit
matchls []     []     = return unit
matchls (b:bs) (e:es) = match b e *> matchls bs es
matchls []     es     = modify (\expr -> App expr es)
matchls bs     es     = throwError $ "Cannot match " ++ show bs ++ " with " ++ show es

execMatcher :: forall a. Matcher a -> Expr -> Evaluator Expr
execMatcher = execStateT

match :: Binding -> Expr -> Matcher Unit
match (Lit (Name x))   e                = modify (replace x e)
match (Lit l)          (Atom a)         | a == l  = return unit
--match (ConsLit b bs)   (List (e:es))    = match b e *> match bs (List es)
match (ConsLit b bs)   (Binary Cons e es) = match b e *> match bs es
match (ListLit [])     (List [])        = return unit
match (ListLit (b:bs)) (List (e:es))    = match b e *> match (ListLit bs) (List es)
--match (ListLit (b:bs)) (Binary Cons e es) = match b e *> match (ListLit bs) es
match (NTupleLit bs)   (NTuple es)      = match (ListLit bs) (List es)
match b                e                = throwError $ "Cannot match " ++ show b ++ " with " ++ show e

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
