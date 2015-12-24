module TypeChecker where

import Prelude hiding (apply,compose)
import Control.Monad.Eff
import Control.Monad.Eff.Console

import Control.Monad.Except
import Control.Monad.RWS.Trans
import Control.Monad.Except.Trans
import Control.Monad.State

import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.Writer.Class
import Control.Monad.Error.Class
import Control.Monad.Except.Trans

import Data.Either
import Data.List
import Data.Map as Map
import Data.Tuple
import Data.Set as Set
import Data.Foldable
import Data.Maybe
import Data.String as String
import Data.Array as Array

import AST

data TVar = TVar String

data Type
    = TypVar TVar -- Typ Variables e.x. a
    | TypCon String -- Typ Constants e.x Int
    | TypArr Type Type -- e.x Int -> Int
    | AD AD

data AD
    = TList Type
    | TTuple (List Type)

instance showType :: Show Type where
  show (TypVar a) = show a
  show (TypCon a) = show a
  show (TypArr a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (AD a) = show a

instance eqType :: Eq Type where
  eq (TypVar a) (TypVar b) = a == b
  eq (TypCon a) (TypCon b) = a == b
  eq (TypArr a b) (TypArr a' b') = (a == a') && (b == b')
  eq (AD a) (AD b) = eq a b
  eq _ _ = false

instance ordTVar :: Ord TVar where
  compare (TVar a) (TVar b) = compare a b

instance eqTVar :: Eq TVar where
  eq (TVar a) (TVar b) = a == b

instance showTVar :: Show TVar where
  show (TVar a) = show a

instance showAD :: Show AD where
  show (TList a) = "[" ++ show a ++ "]"
  show (TTuple a) = "TTuple " ++ show a

instance eqAD :: Eq AD where
  eq (TList a) (TList b) = eq a b
  eq (TTuple a) (TTuple b) = eq a b

data Scheme = Forall (List TVar) Type

instance showScheme :: Show Scheme where
  show (Forall a b) = "forall " ++ show a ++ "." ++ show b

data TypeEnv = TypeEnv (Map.Map Atom Scheme)

data Unique = Unique { count :: Int }

type Infer a = ExceptT TypeError (State Unique) a

data InferState = InferState { count  :: Int }

data Env = TypEnv {types:: Map.Map Atom Scheme}

type Constraint = Tuple Type Type
type Subst = Map.Map TVar Type

data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  | Ambigious (List Constraint)
  | UnificationMismatch (List Type) (List Type)
  | UnknownError String

instance showTypeError :: Show TypeError where
  show (UnificationFail a b) = "Cant unify " ++ show a ++ " with " ++  show b
  show (InfiniteType a b ) = "Cant construct Infinite type" ++  show a ++ " ~ " ++ show b
  show (UnboundVariable a) = show a ++ " not in scope"
  show (Ambigious _) = "Ambigious TODO error msg"
  show (UnificationMismatch a b) = "Cant unify " ++ show a ++ " with " ++ show b
  show (UnknownError a) = "UnknownError " ++ show a


class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance subScheme :: Substitutable Scheme where
    apply s (Forall as t)   = Forall as $ apply s' t
                              where s' = foldr Map.delete s as
    ftv (Forall as t) = (ftv t) `Set.difference` Set.fromList as

instance subType :: Substitutable Type where
   apply _ (TypCon a) = TypCon a
   apply s t@(TypVar a) = fromMaybe t $ Map.lookup a s
   apply s (TypArr t1 t2) =  TypArr (apply s t1) (apply s t2)
   apply s (AD a) = AD (apply s a)

   ftv (TypCon  _)         = Set.empty
   ftv (TypVar a)       = Set.singleton a
   ftv (TypArr t1 t2) =  Set.union (ftv t1) (ftv t2)
   ftv (AD a) = ftv a


instance listSub :: (Substitutable a) => Substitutable (List a) where
  apply s xs = map (apply s) xs
  ftv   = foldr (\a b -> Set.union (ftv a) b) Set.empty

instance subTypeEnv :: Substitutable TypeEnv where
  apply s (TypeEnv env) =  TypeEnv $ map (apply s) env
  ftv (TypeEnv env) = ftv $ snd $ unzip $ Map.toList env

instance subAD :: Substitutable AD where
  apply s (TList t) = TList (apply s t)
  apply s(TTuple t) = TTuple (apply s t)

  ftv (TList t) = ftv t
  ftv (TTuple t) = ftv t


initInfer :: InferState
initInfer = InferState { count : 0}

initUnique :: Unique
initUnique = Unique { count : 0 }

extend :: TypeEnv -> Tuple Atom Scheme -> TypeEnv
extend (TypeEnv env) (Tuple x s) = TypeEnv $ Map.insert x s env

nullSubst:: Subst
nullSubst = Map.empty

letters:: List String
letters = map String.fromCharArray letters'
  where
    letters' = inf 1 >>= flip Array.replicateM (toList $ String.toCharArray "abcdefghijklmnopqrstuvwxyz")
    inf 2 = 2:Nil --TODO remove limit somehow -- nessary because of strict evaluation
    inf x = x:inf(x+1)

fresh :: Infer Type
fresh = do
  (Unique s) <- get
  put (Unique {count:(s.count+1)})
  case (letters !! s.count) of
    Nothing -> throwError $ UnknownError "out of letters" --TODO make sure this never ever happens
    Just l -> return $ TypVar $ TVar l



unify ::  Type -> Type -> Infer Subst
unify (TypArr l r) (TypArr l' r')  = do
    s1 <- unify l l'
    s2 <- unify (apply s1 r) (apply s1 r')
    return (s2 `compose` s1)

unify (TypVar a) t = bindVar a t
unify t (TypVar a) = bindVar a t
unify (TypCon a) (TypCon b) | a == b = return nullSubst
unify (AD a) (AD b) | a == b = return nullSubst
unify (AD a) (AD b) = unifyAD a b
unify t1 t2 = throwError $ UnificationFail t1 t2

unifyAD :: AD -> AD -> Infer Subst
unifyAD (TList a) (TList b) = unify a b
unifyAD (TTuple (Cons a as)) (TTuple (Cons b bs)) = do
  s1 <- unifyAD (TTuple as) (TTuple bs)
  s2 <- unify a b
  return (s1 `compose` s2)

unifyAD a b = throwError $ UnificationFail (AD a) (AD b)


bindVar ::  TVar -> Type -> Infer Subst
bindVar a t | t == (TypVar a)     = return nullSubst
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return $ Map.singleton a t

occursCheck :: forall a.  (Substitutable a) => TVar -> a -> Boolean
occursCheck a t = a `Set.member` ftv t

compose :: Subst -> Subst -> Subst
compose s1 s2 = map (apply s1) s2 `Map.union` s1


instantiate ::  Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  return $ apply s t

generalize :: TypeEnv -> Type -> Scheme
generalize env t  = Forall as t
    where as = Set.toList $ ftv t `Set.difference` ftv env

runInfer :: Infer (Tuple Subst Type) -> Either TypeError Scheme
runInfer m = case evalState (runExceptT m) initUnique of
  Left err -> Left err
  Right res -> Right $ closeOver res

closeOver :: (Tuple (Map.Map TVar Type) Type) -> Scheme
closeOver (Tuple sub ty) = sc --TODO add normalize back in
  where sc = generalize emptyTyenv (apply sub ty)

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

-- TODO find Purescript equivalent
mapM :: forall a b m. (Monad m) => (a -> m b) -> List a -> m (List b)
mapM f as = foldr k (return Nil) as
            where
              k a r = do
                x <- f a
                xs <- r
                return (x:xs)


lookupEnv :: TypeEnv -> Atom -> Infer (Tuple Subst Type)
lookupEnv (TypeEnv env) x = do
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just s  -> do t <- instantiate s
                  return (Tuple nullSubst t)


    -- TODO remove
    -- just here so that i can look at it ;-)

    -- data Expr =

    --           Atom Atom

    --              kind :: * -> *
    --           | List (List Expr)           -> find out common type (infer and generalize)

    --              kind ::  * -> * -> * bei n = 2 ~~ allgemein (*->)^n -> *
    --           | NTuple (List Expr)         -> type every Expr in Tuple

    --           | Binary Op Expr Expr        -> Application
    --           | Unary Op Expr              -> Application
    --           | SectL Expr Op              -> Application
    --           | SectR Op Expr              -> Application
    --           | PrefixOp Op                -> Lookup (simple Function)
    --           | IfExpr Expr Expr Expr      -> Application
    --           | LetExpr Binding Expr Expr  -> Let
    --           | Lambda (List Binding) Expr -> Abstraktion
    --           | App Expr (List Expr)       -> Application


    -- data Atom = AInt Int     -> Prim Type
    --           | Bool Boolean -> Prim Type
    --           | Char String  -> Prim Type
    --           | Name String  -> Variable

    -- data Binding = Lit Atom
    --              | ConsLit Binding Binding
    --              | ListLit (List Binding)
    --              | NTupleLit (List Binding)

-- Tuple and List not supported yet
infer :: TypeEnv -> Expr -> Infer (Tuple Subst Type)
infer env ex = case ex of

  (Atom x@(Name _)) -> lookupEnv env x
  (Atom (Bool _)) -> return (Tuple nullSubst (TypCon "Bool"))
  (Atom (Char _)) -> return (Tuple nullSubst (TypCon "Char"))
  (Atom (AInt _)) -> return (Tuple nullSubst (TypCon "Int"))

  Lambda (Cons (Lit x@(Name _)) Nil) e -> do
    tv <- fresh
    let env' = env `extend` (Tuple x (Forall Nil tv))
    (Tuple s1 t1) <- infer env' e
    return (Tuple s1 (apply s1 tv `TypArr` t1))

  Lambda (Cons (Lit x@(Name _)) xs) e -> do
    tv <- fresh
    let env' = env `extend` (Tuple x (Forall Nil tv))
    (Tuple s1 t1) <- infer env' (Lambda xs e)
    return (Tuple s1 (apply s1 tv `TypArr` t1))

    -- one element list
  App e1 (Cons e2 Nil) -> do
    tv <- fresh
    (Tuple s1 t1) <- infer env e1
    (Tuple s2 t2) <- infer (apply s1 env) e2
    s3       <- unify (apply s2 t1) (TypArr t2 tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 tv))

  App e1 (Cons e2 xs) -> infer env  (App (App e1 (Cons e2 Nil)) xs)

-- TODO  support just atom let expr for now
  LetExpr (Lit x@(Name _)) e1 e2 -> do
    (Tuple s1 t1) <- infer env e1
    let env' = apply s1 env
        t'   = generalize env' t1
    (Tuple s2 t2) <- infer (env' `extend` (Tuple x t')) e2
    return (Tuple (s1 `compose` s2) t2)


  IfExpr cond tr fl -> do
    (Tuple s1 t1) <- infer env cond
    (Tuple s2 t2) <- infer env tr
    (Tuple s3 t3) <- infer env fl
    s4 <- unify t1 (TypCon "Bool")
    s5 <- unify t2 t3
    return (Tuple (s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1) (apply s5 t2))

  PrefixOp op -> inferOp op

  SectL e op -> do
    tv <- fresh
    (Tuple s1 t1) <- inferOp op
    (Tuple s2 t2) <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr t2 tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 tv))

  SectR op e -> do
    (Tuple s1 t1@(TypArr a (TypArr b c))) <- inferOp op
    (Tuple s2 t2) <- infer env e
    s3       <- unify (apply s2 b) t2
    let s4 = (s3 `compose` s2 `compose` s1)
    return (Tuple s4 (apply s4 (TypArr a c)))

  Unary op e -> do
    tv <- fresh
    (Tuple s1 t1) <- inferOp op
    (Tuple s2 t2) <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr t2 tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 tv))

  Binary op e1 e2 ->  infer env (App (PrefixOp op) (Cons e1 (Cons e2 Nil)))

  List (Cons e1 xs) -> do
    (Tuple s1 (AD (TList t1))) <- infer env (List xs)
    (Tuple s2 t2) <- infer (apply s1 env) e1
    s3 <- unify (apply s2 t1) t2
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (AD $ TList t2)))

  List Nil -> do
    tv <- fresh
    return (Tuple nullSubst (AD $ TList tv))


  NTuple (Cons e Nil) -> do
    (Tuple s t) <- infer env e
    return $ Tuple s (AD $ TTuple $ Cons t Nil)

  NTuple (Cons e1 xs) -> do
    (Tuple s1 (AD (TTuple t1))) <- infer env (NTuple xs)
    (Tuple s2 t2) <- infer (apply s1 env) e1
    return (Tuple (s2 `compose` s1) (AD $ TTuple (Cons t2 t1)))

inferOp :: Op -> Infer (Tuple Subst Type)
inferOp op = do
  a <- fresh
  b <- fresh
  c <- fresh
  case op of
    Composition ->
      f ((b `TypArr` c) `TypArr` ((a `TypArr` b) `TypArr` (a `TypArr` c)))
    Power -> int3
    Mul ->  int3
    Div -> int3
    Mod -> int3
    Add -> int3
    Sub -> int3
    Colon -> f (a `TypArr` ((AD $ TList a) `TypArr` (AD $ TList a)))
    Append -> f ((AD $ TList a) `TypArr` ((AD $ TList a) `TypArr` (AD $ TList a)))
    Equ -> aBool a
    Neq -> aBool a
    Lt -> aBool a
    Leq -> aBool a
    Gt -> aBool a
    Geq -> aBool a
    And -> f (TypCon "Bool" `TypArr` (TypCon "Bool" `TypArr` TypCon "Bool"))
    Or -> f (TypCon "Bool" `TypArr` (TypCon "Bool" `TypArr` TypCon "Bool"))
    Dollar -> f ((a `TypArr` b) `TypArr` (a `TypArr` b))
 where
  f typ = return (Tuple nullSubst typ)
  int3 = f (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int"))
  aBool a = f (a `TypArr` (a `TypArr` TypCon "Bool"))
