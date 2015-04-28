module Evaluator
  ( Path(..)
  , Env()
  , evalPath1
  , defsToEnv
  ) where

import Data.Array    (head, mapMaybe, (!!), updateAt, elemIndex, length, concat, concatMap, nub, (\\), intersect, drop)
import Data.StrMap   (StrMap(), empty, lookup, insert, delete, values)
import Data.Tuple    (Tuple(Tuple), fst, snd)
import Data.Maybe
import Data.Foldable (foldl, foldr, foldMap, any)
import Data.Traversable (zipWithA, traverse)
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

type Evaluator = ErrorT String Identity

runEvalM :: forall a. Evaluator a -> Either String a
runEvalM = runIdentity <<< runErrorT

data Path = Nth Number Path
          | Fst Path
          | Snd Path
          | Thrd Path
          | End

instance showPath :: Show Path where
  show p = case p of
    Nth i p -> "(Nth " ++ show i ++ " " ++ show p ++")"
    Fst   p -> "(Fst " ++ show p ++")"
    Snd   p -> "(Snd " ++ show p ++")"
    Thrd   p -> "(Thrd " ++ show p ++")"
    End     -> "End"

mapWithPath :: Path -> (Expr -> Evaluator Expr) -> Expr -> Evaluator Expr
mapWithPath p f = go p
  where
  go End e     = f e
  go (Fst p) e = case e of
    Binary op e1 e2 -> Binary op <$> go p e1 <*> pure e2
    Unary op e      -> Unary op  <$> go p e
    SectL e op      -> SectL     <$> go p e <*> pure op
    IfExpr ce te ee -> IfExpr <$> go p ce <*> pure te <*> pure ee
    Lambda bs body  -> Lambda bs <$> go p body
    App e es        -> App       <$> go p e <*> pure es
    _               -> throwError $ "Cannot match " ++ show (Fst p) ++ " with " ++ show e
  go (Snd p) e = case e of
    Binary op e1 e2 -> Binary op e1 <$> go p e2
    SectR op e      -> SectR op     <$> go p e
    IfExpr ce te ee -> IfExpr <$> pure ce <*> go p te <*> pure ee
    _               -> throwError $ "Cannot match " ++ show (Snd p) ++ " with " ++ show e
  go (Thrd p) e = case e of
    IfExpr ce te ee -> IfExpr <$> pure ce <*> pure te <*> go p ee
    _               -> throwError $ "Cannot match " ++ show (Thrd p) ++ " with " ++ show e
  go (Nth n p) e = case e of
    List es  -> List  <$> mapIndex n (go p) es
    NTuple es -> NTuple <$> mapIndex n (go p) es
    App e es -> App e <$> mapIndex n (go p) es
    _        -> throwError $ "Cannot match " ++ show (Nth n p) ++ " with " ++ show e

mapIndex :: forall m a. Number -> (a -> Evaluator a) -> [a] -> Evaluator [a]
mapIndex i f as = do
  case as !! i of
    Nothing -> throwError $ "Nothing at index " ++ show i ++ "! (length = " ++ show (length as) ++ ")"
    Just a  -> do
      a' <- f a
      return $ updateAt i a' as

evalPath1 :: Env -> Path -> Expr -> Either String Expr
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
  (IfExpr (Atom (Bool true)) te _)   -> return te
  (IfExpr (Atom (Bool false)) _ ee)  -> return ee
--  (List (e:es))                      -> return $ Binary Cons e (List es)
  (App (Binary Composition f g) [e]) -> return $ App f [App g [e]]
  (App (Lambda binds body) args)     -> matchls' binds args >>= flip replace' body >>= wrapLambda binds args
  (App (SectL e1 op) [e2])           -> binary op e1 e2 <|> (return $ Binary op e1 e2)
  (App (SectR op e2) [e1])           -> binary op e1 e2 <|> (return $ Binary op e1 e2)
  (App (Prefix op) [e1, e2])         -> binary op e1 e2 <|> (return $ Binary op e1 e2)
  (App (Atom (Name name)) args)      -> apply env name args
  (App (App func es) es')            -> return $ App func (es ++ es')
  _ -> throwError $ "Cannot evaluate " ++ show expr

wrapLambda :: [Binding] -> [Expr] -> Expr -> Evaluator Expr
wrapLambda binds args body =
  case compare (length binds) (length args) of
    EQ -> return body
    GT -> return $ Lambda (drop (length args) binds) body
    LT -> return $ App body (drop (length binds) args)


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
    Right expr -> return expr
    Left msg   -> throwError $ "No matching funnction found for " ++ name ++ "(last reason: " ++ msg ++ ")"
  where
  app :: Tuple [Binding] Expr -> Evaluator Expr
  app (Tuple binds body) | length binds == length args = matchls' binds args >>= flip replace' body
                         | otherwise                   = throwError $ "Wrong number of arguments!"

matchls' :: [Binding] -> [Expr] -> Evaluator (StrMap Expr)
matchls' bs es = execStateT (zipWithA match' bs es) empty

match' :: Binding -> Expr -> StateT (StrMap Expr) Evaluator Unit
match' (Lit (Name name)) e                             = modify (insert name e)
match' (Lit ba)          (Atom ea)          | ba == ea = return unit
match' (ConsLit b bs)    (Binary Cons e es)            = match' b e *> match' bs es
match' (ConsLit b bs)    (List (e:es))                 = match' (ConsLit b bs) (Binary Cons e (List es))
match' (ListLit bs)      (List es)          | length bs == length es = void $ zipWithA match' bs es
match' (ListLit bs)      (Binary Cons e (List es))     = match' (ListLit bs) (List (e:es))
match' (NTupleLit bs)    (NTuple es)        | length bs == length es = void $ zipWithA match' bs es
match' b                 e                             = throwError $ "Cannot match " ++ show b ++ " with " ++ show e

replace' :: StrMap Expr -> Expr -> Evaluator Expr
replace' subs = go
  where
  go expr = case expr of
    a@(Atom (Name name)) -> case lookup name subs of
      Just subExpr -> return subExpr
      Nothing      -> return a
    (List exprs)         -> List <$> (traverse go exprs)
    (NTuple exprs)       -> NTuple <$> (traverse go exprs)
    (Binary op e1 e2)    -> Binary <$> pure op <*> go e1 <*> go e2
    (Unary op e)         -> Unary <$> pure op <*> go e
    (SectL e op)         -> SectL <$> go e <*> pure op
    (SectR op e)         -> SectR <$> pure op <*> go e
    (IfExpr ce te ee)    -> IfExpr <$> go ce <*> go te <*> go ee
    (Lambda binds body)  -> (avoidCapture subs binds) *> (Lambda <$> pure binds <*> replace' (foldr delete subs (boundNames' binds)) body)
    (App func exprs)     -> App <$> go func <*> traverse go exprs
    e                    -> return e

avoidCapture :: StrMap Expr -> [Binding] -> Evaluator Unit
avoidCapture subs binds = case intersect (concatMap freeVariables $ values subs) (boundNames' binds) of
  []       -> return unit
  captures -> throwError $ "Some variables have been captured: " ++ show captures

freeVariables :: Expr -> [String]
freeVariables = nub <<< foldExpr
  (\a -> case a of
    Name name -> [name]
    _         -> [])
  concat
  concat
  (\_ f1 f2 -> f1 ++ f2)
  (\_ f -> f)
  (\f _ -> f)
  (\_ f -> f)
  (\_ -> [])
  (\f1 f2 f3 -> f1 ++ f2 ++ f3)
  (\bs f -> nub f \\ boundNames' bs)
  (\f fs -> f ++ concat fs)

boundNames' :: [Binding] -> [String]
boundNames' = concatMap boundNames

boundNames :: Binding -> [String]
boundNames = go
  where
  go (Lit (Name name)) = [name]
  go (ConsLit b1 b2)   = go b1 ++ go b2
  go (ListLit bs)      = foldMap go bs
  go (NTupleLit bs)    = foldMap go bs
