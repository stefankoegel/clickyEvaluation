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
  show (TypVar var) = "(TypVar  " ++ show var ++ ")"
  show (TypCon con) = "(TypCon " ++ show con ++ ")"
  show (TypArr t1 t2) = "(TypArr "++ show t1 ++" " ++ show t2 ++ ")"
  show (AD ad) = "(AD "++ show ad ++ ")"

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
  show (TVar a) = "(TVar " ++ show a ++ ")"

instance showAD :: Show AD where
  show (TList t) = "(TList "++ show t ++")"
  show (TTuple tl) = "(TTuple ("++ show tl ++ "))"

instance eqAD :: Eq AD where
  eq (TList a) (TList b) = eq a b
  eq (TTuple a) (TTuple b) = eq a b

data Scheme = Forall (List TVar) Type

instance showScheme :: Show Scheme where
  show (Forall a b) = "Forall (" ++ show a ++ ") " ++ show b

data TypeEnv = TypeEnv (Map.Map Atom Scheme)

instance showTypeEnv :: Show TypeEnv where
  show (TypeEnv a) = show a

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
  | UnificationMismatch (List Type) (List Type)
  | UnknownError String

instance showTypeError :: Show TypeError where
  show (UnificationFail a b) = "(UnificationFail "++ show a ++ " " ++ show b ++")"
  show (InfiniteType a b ) = "(InfiniteType " ++ show a ++ " " ++ show b ++ ")"
  show (UnboundVariable a) = "(UnboundVariable " ++ show a ++ ")"
  show (UnificationMismatch a b) = "(UnificationMismatch " ++ show a ++ " " ++ show b ++ ")"
  show (UnknownError a) = "(UnknownError " ++ show a ++ ")"

instance eqTypeError :: Eq TypeError where
  eq (UnificationFail a b) (UnificationFail a' b') = (a == a') && (b == b')
  eq (InfiniteType a b) (InfiniteType a' b') = (a == a') && (b == b')
  eq (UnboundVariable a) (UnboundVariable a') = (a == a')
  eq (UnificationMismatch a b) (UnificationMismatch a' b') = (a == a') && (b == b')
  eq (UnknownError a) (UnknownError a') = (a == a')


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

instance subTupAtomScheme :: Substitutable (Tuple Atom Scheme) where
  apply s (Tuple a b) = Tuple a (apply s b)

  ftv (Tuple _ b) = ftv b

initInfer :: InferState
initInfer = InferState { count : 0}

initUnique :: Unique
initUnique = Unique { count : 0 }

extend :: TypeEnv -> Tuple Atom Scheme -> TypeEnv
extend (TypeEnv env) (Tuple x s) = TypeEnv $ Map.insert x s env

nullSubst:: Subst
nullSubst = Map.empty

-- not used right now
-- use later to replace t_xx with letters on output
letters:: List String
letters = map String.fromCharArray letters'
  where
    letters' = inf 1 >>= flip Array.replicateM
      (toList $ String.toCharArray "abcdefghijklmnopqrstuvwxyz")
    inf 2 = 2:Nil --TODO remove limit somehow -- nessary because of strict evaluation
    inf x = x:inf(x+1)

fresh :: Infer Type
fresh = do
  (Unique s) <- get
  put (Unique {count:(s.count+1)})
  return $ TypVar $ TVar $ "t_" ++ show s.count


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
unifyAD (TTuple Nil) (TTuple Nil) = return nullSubst

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
    Nothing -> throwError $ UnboundVariable (f x)
    Just s  -> do t <- instantiate s
                  return (Tuple nullSubst t)
  where
    f (Name x) = x



infer :: TypeEnv -> Expr -> Infer (Tuple Subst Type)
infer env ex = case ex of

  (Atom x@(Name _)) -> lookupEnv env x
  (Atom (Bool _)) -> return (Tuple nullSubst (TypCon "Bool"))
  (Atom (Char _)) -> return (Tuple nullSubst (TypCon "Char"))
  (Atom (AInt _)) -> return (Tuple nullSubst (TypCon "Int"))

  Lambda (Cons bin Nil) e -> do
    tv <- fresh
    Tuple envL tvB <- extractBinding bin
    let env' = foldr (\a b -> extend b a) env envL
    s0 <- unify tv tvB
    (Tuple s1 t1) <- infer env' e
    return (Tuple s1 (apply (s0 `compose` s1) tv `TypArr` t1))

  Lambda (Cons bin xs) e -> do
    tv <- fresh
    Tuple envL tvB <- extractBinding bin
    let env' = foldr (\a b -> extend b a) env envL
    s0 <- unify tv tvB
    (Tuple s1 t1) <- infer env' (Lambda xs e)
    return (Tuple s1 (apply (s0 `compose` s1) tv `TypArr` t1))

  Lambda Nil e -> infer env e

    -- one element list
  App e1 (Cons e2 Nil) -> do
    tv <- fresh
    (Tuple s1 t1) <- infer env e1
    (Tuple s2 t2) <- infer (apply s1 env) e2
    s3       <- unify (apply s2 t1) (TypArr t2 tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 tv))

  App e1 (Cons e2 xs) -> infer env  (App (App e1 (Cons e2 Nil)) xs)

  LetExpr bin e1 e2 -> do
    (Tuple s1 t1) <- infer env e1
    (Tuple list typ) <- extractBinding bin
    s2 <- unify typ t1
    let env' = apply (s1 `compose` s2) env
        t'   = generalize env' (apply (s1 `compose` s2) t1)
        env'' = apply s2 (foldr (\a b -> extend b a) env' list)
    (Tuple s3 t2) <- infer env'' e2
    return (Tuple (s1 `compose` s2 `compose` s3) t2)


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

-- recursive functions are typed wrong
inferDef :: TypeEnv -> Definition -> Infer (Tuple Subst Type)
inferDef env (Def str bin exp) = do
    tv <- fresh
    let env' = env `extend` (Tuple (Name str) (Forall Nil tv))
    let exp' = Lambda bin exp
    Tuple s1 t1 <- infer env' exp'
    return $ Tuple s1 (apply s1 t1)
    -- Tuple s1 t1 <- infer env' exp'
    -- let env'' = (apply s1 env')
    -- -- throwError $ UnknownError $ show env''
    -- infer env'' exp'
    --infer env' (LetExpr (Lit $ Name str) exp' exp')
  -- Tuple s1 t1 <- infer env' $ Lambda bin exp
  -- return (Tuple s1 (apply s1 tv))


extractConsLit:: Type -> Binding -> Infer (Tuple (List (Tuple Atom Scheme)) Type)
extractConsLit tv (ConsLit a b@(ConsLit _ _)) = do
  Tuple list1 typ1 <- extractBinding a
  s1 <- unify typ1  tv
  let list1' = apply s1 list1
  Tuple listB (AD ( TList typB)) <- extractConsLit tv b
  s2 <- unify typB (apply s1 tv)
  return $ Tuple (apply s2 (list1' ++ listB)) (AD $ TList (apply s2 typB))

extractConsLit tv (ConsLit a (Lit b)) = do
  Tuple list typ <- extractBinding a
  s1 <- unify tv typ
  let list' = apply s1 list
  let ltyp = AD $ TList (apply s1 tv)
  return $ Tuple (Cons (Tuple b $ Forall Nil ltyp) list') ltyp


extractConsLit tv (ConsLit a b) = do
  Tuple list typ <- extractBinding a
  Tuple list2 typ2 <- extractBinding b
  s1 <- unify typ2 typ
  s2 <- unify (apply s1 typ) tv
  let sC =  s2 `compose` s1
  let list' = map (\(Tuple a b) -> Tuple a $ apply sC b) list
  let list2' = map (\ (Tuple a b) -> Tuple a $  apply sC b) list2
  return $ Tuple (list' ++ list2') $ AD $ TList tv


extractListLit :: List Binding -> Infer (List (Tuple (List (Tuple Atom Scheme)) Type))
extractListLit (Cons a Nil) = do
  b1 <- extractBinding a
  return (Cons b1 Nil)

extractListLit (Cons a b) = do
  b1 <- extractBinding a
  bs <- extractListLit b
  return (Cons b1 bs)

extractListLit Nil = return Nil

extractBinding:: Binding -> Infer (Tuple (List (Tuple Atom Scheme)) Type)
extractBinding (Lit a) = do
  tv <- fresh
  return $ Tuple (toList [(Tuple a (Forall Nil tv))]) tv

extractBinding a@(ConsLit _ _) = do
  tv <- fresh
  extractConsLit tv a

extractBinding (ListLit a) = do
  bs <- extractListLit a
  tv <- fresh
  let ini = Tuple Nil tv
  Tuple list typ <- foldM f ini bs
  return $ Tuple list (AD $ TList typ)
  where
-- :: Tuple (List (Tuple Atom Scheme)) Type -> Tuple (List (Tuple Atom Scheme)) Type
--           -> Infer (Tuple (List (Tuple Atom Scheme)) Type)
    f (Tuple l1 t1) (Tuple l2 t2) = do
      let ls = l1 ++ l2
      s1 <- unify t1 t2
      return $ Tuple (apply s1 ls) (apply s1 t1)


extractBinding (NTupleLit a) = do
  bs <- extractListLit a
  let tup = unzip bs
  return $ Tuple (concat $ fst tup) (AD $ TTuple $ snd tup)


inferGroup:: TypeEnv -> List Definition -> Infer (Tuple Subst Type)
inferGroup _ Nil = throwError $ UnknownError "Cant type empty Group"
inferGroup env (Cons def1 Nil) = inferDef env def1
inferGroup env (Cons def1 defs) = do
  Tuple s1 t1 <- inferDef env def1
  Tuple s2 t2 <- inferGroup env defs
  s3 <- unify t1 t2
  return $ Tuple s3 (apply s3 t1)


buildTypeEnv:: List Definition -> Either TypeError TypeEnv
buildTypeEnv Nil = Right emptyTyenv
buildTypeEnv defs = buildTypeEnvFromGroups emptyTyenv groupMap keys
  where
    groupMap = buildGroups defs
    keys = Map.keys groupMap

buildGroups:: List Definition -> Map.Map String (List Definition)
buildGroups Nil = Map.empty
buildGroups (Cons def@(Def str bin exp) Nil) =
  Map.singleton str (Cons def Nil)

buildGroups (Cons def@(Def str bin exp) defs) =
  case binList of
    Just list -> Map.insert str (Cons def list) defMap
    Nothing -> Map.insert str (Cons def Nil) defMap
  where
    defMap = buildGroups defs
    binList = Map.lookup str defMap
--                         old -> grouped Definitions -> keys -> new
buildTypeEnvFromGroups:: TypeEnv -> Map.Map String (List Definition)
  -> List String -> Either TypeError TypeEnv
buildTypeEnvFromGroups env _ Nil = Right env
buildTypeEnvFromGroups env groupMap k@(Cons key keys) =
  case mayDefs of
    Nothing -> Left $ UnboundVariable key
    Just defs -> case runInfer $ inferGroup env defs of
      Right scheme -> buildTypeEnvFromGroups
        (env `extend` (Tuple (Name key) scheme)) (Map.delete key groupMap) keys
      Left (UnboundVariable var) -> buildTypeEnvFromGroups
        env groupMap (Cons var (delete var k))
      Left err -> Left err
  where
    mayDefs = Map.lookup key groupMap


typeProgramn:: List Definition -> Expr -> Either TypeError Scheme
typeProgramn defs exp = case runInfer <$>
    (infer <$> (buildTypeEnv defs) <*> pure exp) of
  Left err -> Left err
  Right a -> a
