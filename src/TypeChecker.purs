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

instance subTypeTree :: Substitutable TypeTree where
  apply s (TAtom t) = TAtom $ apply s t
  apply s (TListTree l t) = TListTree (apply s l) (apply s t)
  apply s (TNTuple l t) = TNTuple (apply s l) (apply s t)
  apply s (TBinary op tt1 tt2 t) =  TBinary (apply s op) (apply s tt1) (apply s tt2) (apply s t)
  apply s (TUnary op tt t) = TUnary (apply s op) (apply s tt) (apply s t)
  apply s (TSectL tt op t) = TSectL (apply s tt) (apply s op) (apply s t)
  apply s (TSectR op tt t) = TSectR (apply s op) (apply s tt) (apply s t)
  apply s (TPrefixOp t) = TPrefixOp $ apply s t
  apply s (TIfExpr tt1 tt2 tt3 t) = TIfExpr (apply s tt1) (apply s tt2) (apply s tt2) (apply s t)
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
  ftv (TLetExpr _ _ _ t)  = ftv t
  ftv (TLambda _ _ t)  = ftv t
  ftv (TApp _ _ t)  = ftv t

instance subTypeBinding :: Substitutable TypeBinding where
  apply s (TLit t) = TLit $ apply s t
  apply s (TConsLit b1 b2 t) = TConsLit (apply s b1) (apply s b2) (apply s t)
  apply s (TListLit lb t) = TListLit (apply s lb) (apply s t)
  apply s (TNTupleLit lb t) = TListLit (apply s lb) (apply s t)

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

  (Atom x@(Name _)) -> do
    Tuple s t <- lookupEnv env x
    return (Tuple s $ TAtom t)
  (Atom (Bool _)) -> return (Tuple nullSubst $ TAtom (TypCon "Bool"))
  (Atom (Char _)) -> return (Tuple nullSubst $ TAtom (TypCon "Char"))
  (Atom (AInt _)) -> return (Tuple nullSubst $ TAtom (TypCon "Int"))

  Lambda (Cons bin Nil) e -> do
    tv <- fresh
    Tuple envL tvB <- extractBinding bin
    let env' = foldr (\a b -> extend b a) env envL
    s0 <- unify tv (extractBindingType tvB)
    (Tuple s1 t1) <- infer env' e
    return (Tuple s1 $ apply (s0 `compose` s1) (TLambda (Cons tvB Nil) t1 $ tv `TypArr` (extractType t1)))

  Lambda (Cons bin xs) e -> do
    tv <- fresh
    Tuple envL tvB <- extractBinding bin
    let env' = foldr (\a b -> extend b a) env envL
    s0 <- unify tv (extractBindingType tvB)
    (Tuple s1 (TLambda tb tt t1)) <- infer env' (Lambda xs e)
    return (Tuple s1 $ apply (s0 `compose` s1) (TLambda (Cons tvB tb) tt (tv `TypArr` t1)))

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
    (Tuple s1 t1) <- infer env cond
    (Tuple s2 t2) <- infer env tr
    (Tuple s3 t3) <- infer env fl
    s4 <- unify (extractType t1) (TypCon "Bool")
    s5 <- unify (extractType t2) (extractType t3)
    let sC = (s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1)
    return $ Tuple sC (apply sC $ TIfExpr t1 t2 t3 (extractType t2))

  PrefixOp op -> do
    Tuple s t <- inferOp op
    return (Tuple s $ TPrefixOp t)

  SectL e op -> do
    tv <- fresh
    (Tuple s1 t1) <- inferOp op
    (Tuple s2 t2) <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr (extractType t2) tv)
    return (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TSectL t2 t1 tv)))

  SectR op e -> do
    (Tuple s1 t1@(TypArr a (TypArr b c))) <- inferOp op
    (Tuple s2 t2) <- infer env e
    s3       <- unify (apply s2 b) (extractType t2)
    let s4 = (s3 `compose` s2 `compose` s1)
    return (Tuple s4 (apply s4 (TSectR t1 t2 (TypArr a c))))

  Unary op e -> do
    tv <- fresh
    (Tuple s1 t1) <- inferOp op
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
  s1 <- unify (extractBindingType typ1) tv
  let list1' = apply s1 list1
  Tuple listB b@(TConsLit b1 b2 (AD ( TList typB))) <- extractConsLit tv b
  s2 <- unify typB (apply s1 tv)
  return $ Tuple (apply s2 (list1' ++ listB)) $ apply s2 (TConsLit typ1 b (AD $ TList (apply s2 typB)))

extractConsLit tv (ConsLit a (Lit b)) = do
  Tuple list typ <- extractBinding a
  s1 <- unify tv (extractBindingType typ)
  let list' = apply s1 list
  let ltyp = AD $ TList (apply s1 tv)
  return $ Tuple (Cons (Tuple b $ Forall Nil ltyp) list') $ (apply s1 (TConsLit typ (TLit ltyp) ltyp))


extractConsLit tv (ConsLit a b) = do
  Tuple list typ <- extractBinding a
  Tuple list2 typ2 <- extractBinding b
  s1 <- unify (extractBindingType typ2) (extractBindingType typ)
  s2 <- unify (apply s1 (extractBindingType typ)) tv
  let sC =  s2 `compose` s1
  let list' = map (\(Tuple a b) -> Tuple a $ apply sC b) list
  let list2' = map (\ (Tuple a b) -> Tuple a $  apply sC b) list2
  return $ Tuple (list' ++ list2') $ apply sC $ TConsLit typ typ2 $ AD $ TList tv


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
extractBinding (Lit a) = do
  tv <- fresh
  return $ Tuple (toList [(Tuple a (Forall Nil tv))]) (TLit tv)

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


extractBinding (NTupleLit a) = do
  bs <- extractListLit a
  let tup = unzip bs
  return $ Tuple (concat $ fst tup) (TNTupleLit (snd tup) (AD $ TTuple $ (map extractBindingType (snd tup))))


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
  Right m -> case evalState (runExceptT m) initUnique of
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


prettyPrintType:: Type -> String -- TODO
prettyPrintType = f
  where
  f (TypVar (TVar a)) = show a
  f (TypCon a) = show a
  f (TypArr t1 t2) = "(" ++ f t1 ++ " -> " ++ f t2 ++ ")"
  f (AD a) = prettyPrintAD a


prettyPrintAD:: AD -> String
prettyPrintAD (TList a) = "[" ++ prettyPrintType a ++ "]"
prettyPrintAD (TTuple a) = "(" ++ foldr (\t s -> prettyPrintType t ++","++s) ")" a
