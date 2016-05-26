module TypeChecker where

import Prelude (class Monad, class Eq, class Show, (&&), (==), (>>=), map, (++), ($), pure, (<*>), (<$>), return, bind, const, otherwise, show, (+), div, mod, flip)

import Control.Monad.Except.Trans (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, evalState, put, get)

import Data.Either (Either(Left, Right))
import Data.List (List(..), length, delete, concat, unzip, foldM, toList, (:), zip)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple), snd, fst)
import Data.Set as Set
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..), fromMaybe, maybe)

import Data.Tuple (Tuple(..),fst,snd)
import Data.Map (Map(..), insert, lookup, empty)
import Data.List.WordsLines (fromCharList)
import Data.List (List(Nil, Cons), singleton, fromList, toList, length, (..), zipWithA,concat,zip, (!!))
import Data.String (joinWith, toCharArray)

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.State

import AST (AD(..), Atom(..), Binding(..), Definition(..), Expr(..), Op(..), TVar(..), Type(..), TypeBinding(..), TypeTree(..),TypeError(..),Path(..))

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
   apply _ (TypeError err) = TypeError err  --TODO make typeError Substitutable

   ftv (TypCon  _)         = Set.empty
   ftv (TypVar a)       = Set.singleton a
   ftv (TypArr t1 t2) =  Set.union (ftv t1) (ftv t2)
   ftv (AD a) = ftv a
   ftv (TypeError err) = Set.empty


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

instance subTypeTree :: Substitutable TypeTree where
  apply s (TAtom t) = TAtom $ apply s t
  apply s (TListTree l t) = TListTree (apply s l) (apply s t)
  apply s (TNTuple l t) = TNTuple (apply s l) (apply s t)
  apply s (TBinary op tt1 tt2 t) =  TBinary (apply s op) (apply s tt1) (apply s tt2) (apply s t)
  apply s (TUnary op tt t) = TUnary (apply s op) (apply s tt) (apply s t)
  apply s (TSectL tt op t) = TSectL (apply s tt) (apply s op) (apply s t)
  apply s (TSectR op tt t) = TSectR (apply s op) (apply s tt) (apply s t)
  apply s (TPrefixOp t) = TPrefixOp $ apply s t
  apply s (TIfExpr tt1 tt2 tt3 t) = TIfExpr (apply s tt1) (apply s tt2) (apply s tt3) (apply s t)
  apply s (TArithmSeq st by end t) = TArithmSeq (apply s st) ((apply s) <$> by) ((apply s) <$> end) (apply s t) 
  apply s (TLetExpr b tt1 tt2 t) = TLetExpr (apply s b) (apply s tt1) (apply s tt2) (apply s t)
  apply s (TLambda lb tt t) = TLambda (apply s lb) (apply s tt) (apply s t)
  apply s (TApp tt1 l t) = TApp (apply s tt1) (apply s l) (apply s t)

  ftv (TAtom t)  = ftv t
  ftv (TListTree _ t)  = ftv t
  ftv (TNTuple _ t)  = ftv t
  ftv (TBinary _ _ _ t)  = ftv t
  ftv (TUnary _ _ t)  = ftv t
  ftv (TSectL _ _ t)  = ftv t
  ftv (TSectR _ _ t)  = ftv t
  ftv (TPrefixOp t)  = ftv t
  ftv (TIfExpr _ _ _ t)  = ftv t
  ftv (TArithmSeq _ _ _ t) = ftv t
  ftv (TLetExpr _ _ _ t)  = ftv t
  ftv (TLambda _ _ t)  = ftv t
  ftv (TApp _ _ t)  = ftv t

instance subTypeBinding :: Substitutable TypeBinding where
  apply s (TLit t) = TLit $ apply s t
  apply s (TConsLit b1 b2 t) = TConsLit (apply s b1) (apply s b2) (apply s t)
  apply s (TListLit lb t) = TListLit (apply s lb) (apply s t)
  apply s (TNTupleLit lb t) = TNTupleLit (apply s lb) (apply s t)

  ftv (TLit t) = ftv t
  ftv (TConsLit _ _ t) = ftv t
  ftv (TListLit _ t) = ftv t
  ftv (TNTupleLit _ t) = ftv t

initInfer :: InferState
initInfer = InferState { count : 0}

initUnique :: Unique
initUnique = Unique { count : 0 }

extend :: TypeEnv -> Tuple Atom Scheme -> TypeEnv
extend (TypeEnv env) (Tuple x s) = TypeEnv $ Map.insert x s env

nullSubst:: Subst
nullSubst = Map.empty



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

mapM' :: forall a b m. (Monad m) => (a -> m b) -> Maybe a -> m (Maybe b)
mapM' f Nothing  = pure Nothing
mapM' f (Just x) = Just <$> (f x)


lookupEnv :: TypeEnv -> Atom -> Infer (Tuple Subst Type)
lookupEnv (TypeEnv env) x = do
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (f x)
    Just s  -> do t <- instantiate s
                  return (Tuple nullSubst t)
  where
    f (Name x) = x
    f x = show x


extractType:: TypeTree -> Type
extractType (TAtom t)  =  t
extractType (TListTree _ t)  =  t
extractType (TNTuple _ t)  =  t
extractType (TBinary _ _ _ t)  =  t
extractType (TUnary _ _ t)  =  t
extractType (TSectL _ _ t)  =  t
extractType (TSectR _ _ t)  =  t
extractType (TPrefixOp t)  =  t
extractType (TIfExpr _ _ _ t)  =  t
extractType (TArithmSeq _ _ _ t) = t
extractType (TLetExpr _ _ _ t)  =  t
extractType (TLambda _ _ t)  =  t
extractType (TApp tt1 _ t)  =  t

extractBindingType:: TypeBinding -> Type
extractBindingType (TLit t) = t
extractBindingType (TConsLit _ _ t) = t
extractBindingType (TListLit _ t) = t
extractBindingType (TNTupleLit _ t) = t


inferType :: TypeEnv -> Expr -> Infer (Tuple Subst Type)
inferType env exp = do
  Tuple s t <- infer env exp
  let t' = extractType t
  return $ Tuple s t'

infer :: TypeEnv -> Expr -> Infer (Tuple Subst TypeTree)
infer env ex = case ex of

  (Atom x@(Name n)) -> case n of
    "mod" -> return $ Tuple nullSubst (TAtom (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int")))
    "div" -> return $ Tuple nullSubst (TAtom (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int")))
    _     -> do
      Tuple s t <- lookupEnv env x
      return (Tuple s $ TAtom t)
  (Atom (Bool _)) -> return (Tuple nullSubst $ TAtom (TypCon "Bool"))
  (Atom (Char _)) -> return (Tuple nullSubst $ TAtom (TypCon "Char"))
  (Atom (AInt _)) -> return (Tuple nullSubst $ TAtom (TypCon "Int"))

  Lambda (Cons bin Nil) e -> do
    Tuple envL tvB <- extractBinding bin
    let env' = foldr (\a b -> extend b a) env envL
    (Tuple s1 t1) <- infer env' e
    return (Tuple s1 $ apply s1 (TLambda (Cons tvB Nil) t1 $ (extractBindingType tvB) `TypArr` (extractType t1)))

  Lambda (Cons bin xs) e -> do
    Tuple envL tvB <- extractBinding bin
    let env' = foldr (\a b -> extend b a) env envL
    (Tuple s1 (TLambda tb tt t1)) <- infer env' (Lambda xs e)
    return (Tuple s1 $ apply s1 (TLambda (Cons tvB tb) tt ((extractBindingType tvB) `TypArr` t1)))

  Lambda Nil e -> infer env e

    -- one element list
  App e1 (Cons e2 Nil) -> do
    tv <- fresh
    (Tuple s1 t1) <- infer env e1
    (Tuple s2 t2) <- infer (apply s1 env) e2
    s3       <- unify (apply (s1  `compose` s2) (extractType t1)) (TypArr (extractType t2) tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 $ TApp t1 (Cons t2 Nil) tv))

  App e1 (Cons e2 xs) -> do
    Tuple s (TApp (TApp tt lt _) lt' t') <- infer env  (App (App e1 (Cons e2 Nil)) xs)
    return $ Tuple s (TApp tt (lt++lt') t')

  App _ Nil -> throwError $ UnknownError "congrats you found a bug TypeChecker.infer (App Nil)"

  LetExpr bin e1 e2 -> do
    (Tuple s1 t1) <- infer env e1
    (Tuple list typ) <- extractBinding bin
    s2 <- unify (extractBindingType typ) (extractType t1)
    let env' = apply (s1 `compose` s2) env
        t'   = generalize env' (apply (s1 `compose` s2) (extractType t1))
        env'' = apply s2 (foldr (\a b -> extend b a) env' list)
    (Tuple s3 t2) <- infer env'' e2
    let sC = (s1 `compose` s2 `compose` s3)
    return (Tuple sC $ apply sC (TLetExpr typ t1 t2 (extractType t2)))


  IfExpr cond tr fl -> do
    tv <- fresh
    t@(TypVar t') <- fresh
    let name = Name $ "if"
    let env' = env `extend` (Tuple name (Forall (Cons t' Nil) (TypArr (TypCon "Bool") (TypArr t (TypArr t  t)))))
    Tuple s (TApp tt (Cons tcond (Cons ttr (Cons tfl Nil))) ift) <- infer env' (App (Atom  name) (toList [cond, tr, fl]))
    return (Tuple s $ apply s (TIfExpr tcond ttr tfl ift))

  ArithmSeq begin jstep jend -> do
    Tuple s1 t1 <- infer env begin
    tup2 <- mapM' (infer env) jstep
    tup3 <- mapM' (infer env) jend
    let t2 = snd <$> tup2
    let t3 = snd <$> tup3
    let s2 = maybe nullSubst fst tup2
    let s3 = maybe nullSubst fst tup3
    let s  = s1 `compose` s2 `compose` s3                 
    return $ Tuple s $ apply s $ TArithmSeq t1 t2 t3 (AD (TList (extractType t1)))

  PrefixOp op -> do
    Tuple s t <- inferOp env op
    return (Tuple s $ TPrefixOp t)

  SectL e op -> do
    tv <- fresh
    (Tuple s1 t1) <- inferOp env op
    (Tuple s2 t2) <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr (extractType t2) tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TSectL t2 t1 tv)))

  SectR op e -> do
    (Tuple s1 t1@(TypArr a (TypArr b c))) <- inferOp env op
    (Tuple s2 t2) <- infer env e
    s3       <- unify (apply s2 b) (extractType t2)
    let s4 = (s3 `compose` s2 `compose` s1)
    return (Tuple s4 (apply s4 (TSectR t1 t2 (TypArr a c))))

  Unary (Sub) e -> do
      tv <- fresh
      let t1 = (TypCon "Int" `TypArr` TypCon "Int")
      (Tuple s2 t2) <- infer env e
      s3       <- unify (apply s2 t1) (TypArr (extractType t2) tv)
      return (Tuple (s3 `compose` s2) (apply s3 (TUnary t1 t2 tv)))

  Unary op e -> do
    tv <- fresh
    (Tuple s1 t1) <- inferOp env op
    (Tuple s2 t2) <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr (extractType t2) tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TUnary t1 t2 tv)))

  Binary op e1 e2 -> do
    (Tuple s (TApp tt (Cons tt1 (Cons tt2 Nil)) t)) <- infer env (App (PrefixOp op) (Cons e1 (Cons e2 Nil)))
    return $ Tuple s (TBinary (extractType tt) tt1 tt2 t)


  List (Cons e1 xs) -> do
    (Tuple s1 (TListTree ltt (AD (TList t1)))) <- infer env (List xs)
    (Tuple s2 t2) <- infer (apply s1 env) e1
    s3 <- unify (apply s2 t1) (extractType t2)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TListTree (Cons t2 ltt) (AD $ TList (extractType t2)))))

  List Nil -> do
    tv <- fresh
    return (Tuple nullSubst $ TListTree Nil (AD $ TList tv))


  NTuple (Cons e Nil) -> do
    (Tuple s t) <- infer env e
    return $ Tuple s $ TNTuple (Cons t Nil) (AD $ TTuple $ Cons (extractType t) Nil)

  NTuple (Cons e1 xs) -> do
    (Tuple s1 (TNTuple lt (AD (TTuple t1)))) <- infer env (NTuple xs)
    (Tuple s2 t2) <- infer (apply s1 env) e1
    return (Tuple (s2 `compose` s1) $ TNTuple (Cons t2 lt) (AD $ TTuple (Cons (extractType t2) t1)))

  NTuple Nil -> throwError $ UnknownError "congrats you found a bug in TypeChecker.infer (NTuple Nil)"

inferOp :: TypeEnv -> Op -> Infer (Tuple Subst Type)
inferOp env op = do
  a <- fresh
  b <- fresh
  c <- fresh
  case op of
    Composition ->
      f ((b `TypArr` c) `TypArr` ((a `TypArr` b) `TypArr` (a `TypArr` c)))
    Power -> int3
    Mul ->  int3
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
    InfixFunc name -> inferType env (Atom (Name name))
 where
  f typ = return (Tuple nullSubst typ)
  int3 = f (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int"))
  aBool a = f (a `TypArr` (a `TypArr` TypCon "Bool"))

inferDef :: TypeEnv -> Definition -> Infer (Tuple Subst Type)
inferDef env (Def str bin exp) = do
    tv <- fresh
    let env' = env `extend` (Tuple (Name str) (Forall Nil tv))
    let exp' = Lambda bin exp
    Tuple s1 t1' <- infer env' exp'
    let t1 = extractType t1'
    let env'' = env `extend` (Tuple (Name str) (Forall Nil (apply s1 t1)))
    Tuple s2 t2 <- infer env'' exp'
    s3 <- unify (apply s1 t1) (apply s2 (extractType t2))
    return $ Tuple (s3 `compose` s1) (apply s3 (apply s1 t1))


extractConsLit:: Type -> Binding -> Infer (Tuple (List (Tuple Atom Scheme)) TypeBinding)
extractConsLit tv (ConsLit a b@(ConsLit _ _)) = do
  Tuple list1 typ1 <- extractBinding a
  Tuple list2 t2@(TConsLit b1 b2 (AD (TList typ2))) <- extractBinding b
  s1 <- unify tv (extractBindingType typ1)
  s2 <- unify (apply s1 tv) (typ2)
  return $ Tuple (apply s2 (apply s1 (list1 ++ list2))) (apply s2 (apply s1 (TConsLit typ1 t2 (AD $ TList typ2))))

extractConsLit tv (ConsLit a (Lit b)) = do
  Tuple list typ <- extractBinding a
  s1 <- unify tv (extractBindingType typ)
  let list' = apply s1 list
  let ltyp = AD $ TList (apply s1 tv)
  return $ Tuple (Cons (Tuple b $ Forall Nil ltyp) list') $ (apply s1 (TConsLit typ (TLit ltyp) ltyp))

extractConsLit tv (ConsLit a b@(ListLit _)) = do
  Tuple list1 typ1 <- extractBinding a
  Tuple list2 t2@(TListLit b1 (AD (TList typ2))) <- extractBinding b
  s1 <- unify tv (extractBindingType typ1)
  s2 <- unify (apply s1 tv) (typ2)
  return $ Tuple (apply s2 (apply s1 (list1 ++ list2))) (apply s2 (apply s1 (TConsLit typ1 t2 (AD $ TList typ2))))

extractConsLit _ _ = throwError $ UnknownError "congrats you found a bug in TypeChecker.extractConsLit"


extractListLit :: List Binding -> Infer (List (Tuple (List (Tuple Atom Scheme)) TypeBinding))
extractListLit (Cons a Nil) = do
  b1 <- extractBinding a
  return (Cons b1 Nil)

extractListLit (Cons a b) = do
  b1 <- extractBinding a
  bs <- extractListLit b
  return (Cons b1 bs)

extractListLit Nil = return Nil

extractBinding:: Binding -> Infer (Tuple (List (Tuple Atom Scheme)) TypeBinding)
extractBinding (Lit a@(Name _)) = do
  tv <- fresh
  return $ Tuple (toList [(Tuple a (Forall Nil tv))]) (TLit tv)
extractBinding (Lit (Bool _)) = return $ Tuple Nil $ TLit (TypCon "Bool")
extractBinding (Lit (Char _)) = return $ Tuple Nil $ TLit (TypCon "Char")
extractBinding (Lit (AInt _)) = return $ Tuple Nil $ TLit (TypCon "Int")

extractBinding a@(ConsLit _ _) = do
  tv <- fresh
  extractConsLit tv a

extractBinding (ListLit a) = do -- Tuple TypEnv  (TListLit (List TypeBinding) Type)
  bs <- extractListLit a
  tv <- fresh
  let ini = Tuple Nil (TListLit Nil tv)
  Tuple list (TListLit lb typ) <- foldM f ini bs
  return $ Tuple list (TListLit lb (AD $ TList typ))
  where
-- :: Tuple (List (Tuple Atom Scheme)) BindingType -> Tuple (List (Tuple Atom Scheme)) BindingType
--           -> Infer (Tuple (List (Tuple Atom Scheme)) BindingType)
    f (Tuple l1 (TListLit lb1 t1)) (Tuple l2 b) = do
      let ls = l1 ++ l2
      s1 <- unify t1 (extractBindingType b)
      return $ Tuple (apply s1 ls) (apply s1 (TListLit (Cons b lb1) t1))
    f _ _ = throwError $ UnknownError "congrats you found a bug in TypeChecker.extractBinding"


extractBinding (NTupleLit a) = do
  bs <- extractListLit a
  let tup = unzip bs
  return $ Tuple (concat $ fst tup) (TNTupleLit (snd tup) (AD $ TTuple $ (map extractBindingType (snd tup))))


getTypEnv:: Binding -> TypeEnv -> Maybe TypeEnv
getTypEnv b  env= case evalState (runExceptT (extractBinding b)) initUnique of
    Left _ -> Nothing
    Right (Tuple bs _) -> Just $ foldr (\a b -> extend b a) env bs

getTypEnvFromList::  List Binding -> TypeEnv-> Maybe TypeEnv
getTypEnvFromList bs env = do
                  mTypList <-  mapM (flip getTypEnv emptyTyenv) bs
                  return $ foldr (\a b -> unionTypeEnv a b) env mTypList

unionTypeEnv :: TypeEnv -> TypeEnv -> TypeEnv
unionTypeEnv (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

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
    (inferType <$> (buildTypeEnv defs) <*> pure exp) of
  Left err -> Left err
  Right a -> a

typeTreeProgramn:: List Definition -> Expr -> Either TypeError TypeTree
typeTreeProgramn defs exp = case m of
  Left e -> Left e
  Right m' -> case evalState (runExceptT m') initUnique of
    Left err -> Left err
    Right res -> Right $ closeOver' res
  where
    m = (infer <$> (buildTypeEnv defs) <*> pure exp)

typeTreeProgramnEnv:: TypeEnv -> Expr -> Either TypeError TypeTree
typeTreeProgramnEnv env expr = case evalState (runExceptT (infer env expr)) initUnique of
      Left err -> Left err
      Right res -> Right $ closeOver' res


closeOver' :: (Tuple (Map.Map TVar Type) TypeTree) -> TypeTree
closeOver' (Tuple s tt) = apply s tt


prettyPrintType:: Type -> String
prettyPrintType (TypVar (TVar a)) = a
prettyPrintType (TypCon a) =  a
prettyPrintType (TypArr t1@(TypArr _ _) t2) = "(" ++ prettyPrintType t1 ++ ")" ++ " -> " ++ prettyPrintType t2
prettyPrintType (TypArr t1 t2) = prettyPrintType t1 ++ " -> " ++ prettyPrintType t2
prettyPrintType (AD a) = prettyPrintAD a
prettyPrintType (TypeError a) = prettyPrintTypeError a


prettyPrintAD:: AD -> String
prettyPrintAD (TList a) = "[" ++ prettyPrintType a ++ "]"
prettyPrintAD (TTuple (Cons t1 a)) = foldl (\s t -> s ++ "," ++ prettyPrintType t) ("(" ++ prettyPrintType t1 ) a  ++ ")"
prettyPrintAD (TTuple Nil) = "()"

emptyType:: Type
emptyType = TypCon ""


-- typeTreeProgramnEnv env expr
-- types subtree if typ correct
buildPartiallyTypedTree:: TypeEnv -> Expr  -> TypeTree
buildPartiallyTypedTree env e = case typeTreeProgramnEnv env e of
  Right tt -> tt
  Left err -> f err e
  where
  f err (Atom _) = TAtom (TypeError err)
  f err (List ls) = TListTree (map (buildPartiallyTypedTree env) ls) (TypeError err)
  f err (NTuple ls) = TNTuple (map (buildPartiallyTypedTree env) ls) (TypeError err)
  f err (Binary op e1 e2) = TBinary (typeOP op) (buildPartiallyTypedTree env e1) (buildPartiallyTypedTree env e2) (TypeError err)
  f err (SectL e op) = TSectL (buildPartiallyTypedTree env e) (typeOP op) (TypeError err)
  f err (SectR op e) = TSectR (typeOP op) (buildPartiallyTypedTree env e) (TypeError err)
  f err (PrefixOp _) = TPrefixOp (TypeError err)
  f err (IfExpr e1 e2 e3) = TIfExpr (buildPartiallyTypedTree env e1) (buildPartiallyTypedTree env e2) (buildPartiallyTypedTree env e3) (TypeError err)
  f err (ArithmSeq e1 e2 e3) = TArithmSeq (buildPartiallyTypedTree env e1) ((buildPartiallyTypedTree env) <$> e2) ((buildPartiallyTypedTree env) <$> e3) (TypeError err)
  f err (LetExpr b1 e1 e2) =let f env' =  TLetExpr (g b1) (buildPartiallyTypedTree env' e1) (buildPartiallyTypedTree env' e2) (TypeError err) in
                        case getTypEnv b1 env of
                          Nothing -> f env
                          Just env' -> f env'
  f err (Lambda bs e) = let f env' = TLambda (map g bs) (buildPartiallyTypedTree env' e) (TypeError err) in
                    case getTypEnvFromList bs env of
                          Nothing -> f env
                          Just env' -> f env'
  f err (App e es) = TApp (buildPartiallyTypedTree env e) (map (buildPartiallyTypedTree env) es) (TypeError err)
  f err (Unary op e) = TUnary (typeOP op) (buildPartiallyTypedTree env e) (TypeError err)

-- Binding to BindingType
  g (Lit _) = TLit emptyType
  g (ConsLit b1 b2) = TConsLit (g b1) (g b2) emptyType
  g (ListLit bs) = TListLit (map g bs) emptyType
  g (NTupleLit bs) = TNTupleLit (map g bs) emptyType

  typeOP op = case typeTreeProgramnEnv env (PrefixOp op) of
    Left err -> TypeError err
    Right (TPrefixOp typ) -> typ


eqScheme :: Scheme -> Scheme -> Boolean
eqScheme (Forall l1 t1) (Forall l2 t2)
  = ((length l1) == (length l2)) && (fst (eqType Map.empty t1 t2))

eqType:: Map.Map TVar TVar -> Type -> Type ->Tuple Boolean (Map.Map TVar TVar)
eqType map (TypVar a) (TypVar b) = case  Map.lookup a map of
  (Just b') -> Tuple (b' == b) (map)
  Nothing -> Tuple true (Map.insert a b map)
eqType map (TypCon a) (TypCon b) = Tuple (a == b) map
eqType map (TypArr a b) (TypArr a' b') = Tuple (fst tup1 && fst tup2) (snd tup2)
  where
  tup1 = eqType map a a'
  tup2 = eqType (snd tup1) b b'
eqType map (AD (TList a)) (AD (TList b)) = eqType map a b
eqType map (AD (TTuple a)) (AD (TTuple b)) = eqTypeList map a b
eqType map _ _ = Tuple false map

eqTypeList:: Map.Map TVar TVar -> List Type -> List Type -> Tuple Boolean (Map.Map TVar TVar)
eqTypeList map (Cons a as) (Cons b bs) = let tup1 = eqType map a b in if (fst tup1)
  then eqTypeList (snd tup1) as bs
  else Tuple false (snd tup1)
eqTypeList map Nil Nil = Tuple true map
eqTypeList map _ _ = Tuple false map


txToABC:: TypeTree -> TypeTree
txToABC tt = fst $ runState (helptxToABC tt) {count : 0, env : empty}

helptxToABC:: TypeTree -> State {count:: Int, env:: Map String String} TypeTree
helptxToABC tt = go tt
  where
    go (TAtom t) = helpTypeToABC t >>= \t -> return $ TAtom t
    go (TListTree tts t) = do
      tts' <- mapM helptxToABC tts
      t' <- helpTypeToABC t
      return $ TListTree tts' t'
    go (TNTuple tts t) = do
      tts' <- mapM helptxToABC tts
      t' <- helpTypeToABC t
      return $ TNTuple tts' t'
    go (TBinary t1 tt1 tt2 t) = do
      t1' <- helpTypeToABC t1
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      t' <- helpTypeToABC t
      return $ TBinary t1' tt1' tt2' t'
    go (TUnary t1 tt t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ (TUnary t1' tt' t')
    go (TSectL tt t1 t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ TSectL tt' t1' t'
    go (TSectR t1 tt t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ TSectR t1' tt' t'
    go (TPrefixOp t) = helpTypeToABC t >>= \t -> return $ TPrefixOp t
    go (TIfExpr tt1 tt2 tt3 t) = do
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      tt3' <- helptxToABC tt3
      t' <- helpTypeToABC t
      return $ TIfExpr tt1' tt2' tt3' t'
    go (TArithmSeq tt1 tt2 tt3 t) = do
      tt1' <- helptxToABC tt1
      tt2' <- mapM' helptxToABC tt2
      tt3' <- mapM' helptxToABC tt3
      t'   <- helpTypeToABC t
      return $ TArithmSeq tt1' tt2' tt3' t'        
    go (TLetExpr tb tt1 tt2 t) = do
      tb' <- helpBindingToABC tb
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      t' <- helpTypeToABC t
      return $ TLetExpr tb' tt1' tt2' t'
    go (TLambda tbs tt t) = do
      tbs' <- mapM helpBindingToABC tbs
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ TLambda tbs' tt' t'
    go (TApp tt tts t) = do
      tt' <- helptxToABC tt
      tts' <- mapM helptxToABC tts
      t' <- helpTypeToABC t
      return $ TApp tt' tts' t'

typeToABC:: Type -> Type
typeToABC t = fst $ runState (helpTypeToABC t) {count: 0, env: empty}


helpTypeToABC:: Type  -> State {count :: Int, env:: (Map String String)} Type
helpTypeToABC t = go t
  where
   go (TypVar (TVar var)) = do
      {env = env :: Map String String} <- get
      case lookup var env of
        Just var' -> return $ TypVar (TVar var')
        Nothing -> do
          var' <- freshLetter
          let env' = (insert var var' env)
          {count=count:: Int} <- get
          put {count:count, env:env'}
          return $ TypVar (TVar var')
   go (TypArr t1 t2) = do
        t1' <- helpTypeToABC t1
        t2' <- helpTypeToABC t2
        return $ TypArr t1' t2'
   go (AD a) = helpADTypeToABC a >>= \a -> return $ AD a
   go a = return a

helpADTypeToABC:: AD -> State {count :: Int, env:: (Map String String)} AD
helpADTypeToABC (TList t) = helpTypeToABC t >>= \t -> return $ TList t
helpADTypeToABC (TTuple ts) = mapM helpTypeToABC ts >>= \ts -> return $ TTuple ts

helpBindingToABC:: TypeBinding -> State {count :: Int, env:: (Map String String)} TypeBinding
helpBindingToABC bin = go bin
  where
    go (TLit t) = helpTypeToABC t >>= \t ->return $ TLit t
    go (TConsLit tb1 tb2 t) = do
      tb1' <- helpBindingToABC tb1
      tb2' <- helpBindingToABC tb2
      t' <- helpTypeToABC t
      return $ TConsLit tb1' tb2' t'
    go (TListLit tbs t) = do
      tbs' <- mapM helpBindingToABC tbs
      t' <- helpTypeToABC t
      return $ TListLit tbs' t'
    go (TNTupleLit tbs t) = do
      tbs' <- mapM helpBindingToABC tbs
      t' <- helpTypeToABC t
      return $ TNTupleLit tbs' t'

freshLetter:: State {count:: Int, env:: Map String String} String
freshLetter = do
    {count = count, env = env :: Map String String} <- get
    put {count:count+1, env:env}
    return $ fromCharList $ newTypVar count


letters:: List Char
letters = (toList $ toCharArray "abcdefghijklmnopqrstuvwxyz")

letters1:: List Char
letters1 = (toList $ toCharArray " abcdefghijklmnopqrstuvwxyz")

newTypVar:: Int -> List Char
newTypVar i = case (letters !! i) of
  Just c ->  Cons c Nil
  Nothing -> let i1 = (i `div` 26) in let i2 = (i `mod` 26) in (newTypVar1 i1) ++ (newTypVar i2)

-- workaround
-- if i  subtract one from i => stack overflow at ~50
newTypVar1:: Int -> List Char
newTypVar1 i = case (letters1 !! (i)) of
  Just c ->  Cons c Nil
  Nothing -> let i1 = (i `div` 26) in let i2 = (i `mod` 26) in (newTypVar1 i1) ++ (newTypVar i2)



prettyPrintTypeError:: TypeError -> String
prettyPrintTypeError (UnificationFail t1 t2) = let t1t2 = twoTypesToABC t1 t2  in
                                                "UnificationFail: Can't unify "
                                                ++ prettyPrintType (fst t1t2) ++ " with "
                                                ++ prettyPrintType (snd t1t2)
prettyPrintTypeError (InfiniteType a b) = let ab = twoTypesToABC (TypVar a) b in
                                              "InfiniteType: cannot construct the infinite type: "
                                              ++ prettyPrintType (fst ab)++ " ~ "
                                              ++ prettyPrintType (snd ab)
prettyPrintTypeError (UnboundVariable var) = "UnboundVariable: Not in scope "
                                              ++ var
prettyPrintTypeError (UnificationMismatch ts1 ts2) = let ts1ts2 = twoTypeListsToABC ts1 ts2 in
    "UnificationMismatch: " ++ toStr (fst ts1ts2) ++ " " ++ toStr (snd ts1ts2)
  where
    toStr ts = "[" ++ (foldr (\t s -> t ++ "," ++ s) "]" (map (\a -> prettyPrintType (typeToABC a)) ts))
prettyPrintTypeError (UnknownError str) = "UnknownError: " ++ str


twoTypesToABC t1 t2 = (\(TypArr t1' t2') -> Tuple t1' t2') (typeToABC (TypArr t1 t2))
twoTypeListsToABC t1 t2 = (\(TypArr (AD (TTuple t1')) (AD (TTuple t2'))) -> Tuple t1' t2') (typeToABC (TypArr (AD (TTuple t1)) (AD (TTuple t2)) ))


checkForError:: Path -> TypeTree -> Boolean
checkForError p' tt = case p' of
  (End) -> isTypeError $ extractType tt
  (Fst p) -> case tt of
      TBinary op e1 e2 _-> checkForError p e1
      TUnary op e      _-> checkForError p e
      TSectL e op      _-> checkForError p e
      TIfExpr ce te ee _-> checkForError p ce
      TArithmSeq ce te ee _ -> checkForError p ce
      TLambda bs body  _-> checkForError p body
      TApp e es        _-> checkForError p e
      _               -> true
  (Snd p) -> case tt of
      TBinary op e1 e2 _-> checkForError p e2
      TSectR op e      _-> checkForError p e
      TIfExpr ce te ee _-> checkForError p te
      TArithmSeq ce (Just te) ee _-> checkForError p te
      _               -> true
  (Thrd p) -> case tt of
      TIfExpr ce te ee _-> checkForError p ee
      TArithmSeq ce te (Just ee) _-> checkForError p ee
      _ -> true
  (Nth n p) -> case tt of
      TListTree es  _-> nth n es p
      TNTuple es _-> nth n es p
      TApp e' es _-> nth n es p
      _        -> true
  where
    nth n es p = case (!!) es n of
                  Nothing -> true
                  Just e -> checkForError p e

isTypeError:: Type -> Boolean
isTypeError t = case t of
  (TypeError _) -> true
  _ -> false
