module TypeChecker where

import Prelude (class Show, (&&), (==), (/=), (>>=), map, ($), pure, (<*>), (<$>), bind, const, otherwise, show, (+), div, mod, flip, (<>), (>), (-), (<<<))

import Control.Monad.Except.Trans (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, evalState, runState, put, get)
import Control.Apply (lift2)
import Control.Bind (ifM)
import Data.Either (Either(Left, Right))
import Data.List (List(..), filter, delete, concatMap, reverse, unzip, foldM, (:), zip, singleton, length, concat, (!!))
import Data.Array as Array
import Data.Map as Map
import Data.Map (Map, insert, lookup, empty)
import Data.Tuple (Tuple(Tuple), snd, fst)
import Data.Traversable (traverse)
import Data.Set as Set
import Data.Foldable (foldl, foldr, foldMap, elem)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (toCharArray, fromCharArray)
import Data.Char as Char

import AST (AD(..), Atom(..), Binding(..), Definition(..), Expr(..), Qual(..), ExprQual, QualTree(..), TypeQual, Op(..), TVar, Type(..), TypeBinding(..), TypeTree(..),TypeError(..),Path(..), extractType, extractBindingType, prettyPrintType)

data Scheme = Forall (List TVar) Type

instance showScheme :: Show Scheme where
  show (Forall a b) = "Forall (" <> show a <> ") " <> show b

data TypeEnv = TypeEnv (Map.Map TVar Scheme)

instance showTypeEnv :: Show TypeEnv where
  show (TypeEnv a) = show a

data Unique = Unique { count :: Int }

type Infer a = ExceptT TypeError (State Unique) a

type Subst = Map.Map TVar Type

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance subScheme :: Substitutable Scheme where
    apply s (Forall as t)   = Forall as $ apply s' t
                              where s' = foldr Map.delete s as
    ftv (Forall as t) = (ftv t) `Set.difference` Set.fromFoldable as

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

instance subTupTVarScheme :: Substitutable (Tuple String Scheme) where
  apply s (Tuple a b) = Tuple a (apply s b)

  ftv (Tuple _ b) = ftv b

instance subQual :: (Substitutable b, Substitutable e) => Substitutable (Qual b e) where
  apply s (Gen b e) = Gen (apply s b) (apply s e)
  apply s (Let b e) = Let (apply s b) (apply s e)
  apply s (Guard e) = Guard (apply s e)

  ftv (Gen _ t) = ftv t
  ftv (Let _ t) = ftv t
  ftv (Guard t) = ftv t

instance subQualTree :: (Substitutable a, Substitutable b, Substitutable c) => Substitutable (QualTree a b c) where
  apply s (TGen a b c) = TGen (apply s a) (apply s b) (apply s c)
  apply s (TLet a b c) = TLet (apply s a) (apply s b) (apply s c)
  apply s (TGuard a c) = TGuard (apply s a) (apply s c)

  ftv (TGen a b c) = ftv c
  ftv (TLet a b c) = ftv c
  ftv (TGuard a c) = ftv c

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
  apply s (TLetExpr bin tt t) = TLetExpr ((\(Tuple x y) -> (Tuple (apply s x) (apply s y))) <$> bin) (apply s tt) (apply s t)
  apply s (TLambda lb tt t) = TLambda (apply s lb) (apply s tt) (apply s t)
  apply s (TApp tt1 l t) = TApp (apply s tt1) (apply s l) (apply s t)
  apply s (TListComp tt tts t) = TListComp (apply s tt) (apply s tts) (apply s t)

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
  ftv (TLetExpr _ _ t)  = ftv t
  ftv (TLambda _ _ t)  = ftv t
  ftv (TApp _ _ t)  = ftv t
  ftv (TListComp _ _ t) = ftv t

instance subTypeBinding :: Substitutable TypeBinding where
  apply s (TLit t) = TLit $ apply s t
  apply s (TConsLit b1 b2 t) = TConsLit (apply s b1) (apply s b2) (apply s t)
  apply s (TListLit lb t) = TListLit (apply s lb) (apply s t)
  apply s (TNTupleLit lb t) = TNTupleLit (apply s lb) (apply s t)

  ftv (TLit t) = ftv t
  ftv (TConsLit _ _ t) = ftv t
  ftv (TListLit _ t) = ftv t
  ftv (TNTupleLit _ t) = ftv t

initUnique :: Unique
initUnique = Unique { count : 0 }

extend :: TypeEnv -> Tuple TVar Scheme -> TypeEnv
extend (TypeEnv env) (Tuple x s) = TypeEnv $ Map.insert x s env

extendMultiple :: TypeEnv -> List (Tuple TVar Scheme) -> TypeEnv
extendMultiple = foldr (flip extend)

nullSubst :: Subst
nullSubst = Map.empty

fresh :: Infer Type
fresh = do
  Unique s <- get
  put (Unique {count:(s.count+1)})
  pure $ TypVar $ "t_" <> show s.count

unify :: Type -> Type -> Infer Subst
unify (TypArr l r) (TypArr l' r')  = do
    s1 <- unify l l'
    s2 <- unify (apply s1 r) (apply s1 r')
    pure (s2 `compose` s1)

unify (TypVar a) t = bindVar a t
unify t (TypVar a) = bindVar a t
unify (TypCon a) (TypCon b) | a == b = pure nullSubst
unify (AD a) (AD b) | a == b = pure nullSubst
unify (AD a) (AD b) = unifyAD a b
unify t1 t2 = throwError $ normalizeTypeError $ UnificationFail t1 t2

unifyAD :: AD -> AD -> Infer Subst
unifyAD (TList a) (TList b) = unify a b
unifyAD (TTuple (Cons a as)) (TTuple (Cons b bs)) = do
  s1 <- unifyAD (TTuple as) (TTuple bs)
  s2 <- unify a b
  pure (s1 `compose` s2)
unifyAD (TTuple Nil) (TTuple Nil) = pure nullSubst

unifyAD a b = throwError $ normalizeTypeError $ UnificationFail (AD a) (AD b)

bindVar ::  TVar -> Type -> Infer Subst
bindVar a t
  | t == (TypVar a) = pure nullSubst
  | occursCheck a t = throwError $ normalizeTypeError $ InfiniteType a t
  | otherwise       = pure $ Map.singleton a t

occursCheck :: forall a.  (Substitutable a) => TVar -> a -> Boolean
occursCheck a t = a `Set.member` ftv t

compose :: Subst -> Subst -> Subst
compose s1 s2 = map (apply s1) s2 `Map.union` s1

envUnion :: TypeEnv -> TypeEnv -> TypeEnv
envUnion (TypeEnv a) (TypeEnv b) = TypeEnv $ a `Map.union` b

instantiate ::  Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- traverse (const fresh) as
  let s = Map.fromFoldable $ zip as as'
  pure $ apply s t

generalize :: TypeEnv -> Type -> Scheme
generalize env t  = Forall as t
  where as = Set.toUnfoldable $ ftv t `Set.difference` ftv env

runInfer :: Infer (Tuple Subst Type) -> Either TypeError Scheme
runInfer m = case evalState (runExceptT m) initUnique of
  Left err -> Left err
  Right res -> Right $ closeOverType res

closeOverType :: (Tuple Subst Type) -> Scheme
closeOverType (Tuple sub ty) = generalize emptyTyenv (apply sub ty)

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

overlappingBindings :: List Binding -> List String
overlappingBindings Nil = Nil
overlappingBindings (Cons x Nil) = Nil
overlappingBindings (Cons x xs) = (filter (\y -> elem y (concatMap boundNames xs)) (boundNames x)) <> overlappingBindings xs
  where
    boundNames :: Binding -> (List String)
    boundNames = go
      where
      go (Lit (Name name)) = singleton name
      go (ConsLit b1 b2)   = go b1 <> go b2
      go (ListLit bs)      = foldMap go bs
      go (NTupleLit bs)    = foldMap go bs
      go _                 = Nil

lookupEnv :: TypeEnv -> TVar -> Infer (Tuple Subst Type)
lookupEnv (TypeEnv env) tvar = do
  case Map.lookup tvar env of
    Nothing -> throwError $ UnboundVariable tvar
    Just s  -> do t <- instantiate s
                  pure (Tuple nullSubst t)

inferType :: TypeEnv -> Expr -> Infer (Tuple Subst Type)
inferType env exp = do
  Tuple s t <- infer env exp
  let t' = extractType t
  pure $ Tuple s t'

data InferResult a = InferResult {subst :: Subst, envi :: TypeEnv, result :: a}

inferBinding :: TypeEnv -> Binding -> Expr -> Infer (InferResult (Tuple TypeBinding TypeTree))
inferBinding env bin e1 = do
  Tuple s1 t1 <- infer env e1
  Tuple list typ <- extractBinding bin
  s2 <- unify (extractBindingType typ) (extractType t1)
  let env' = apply (s1 `compose` s2) env
      t'   = generalize env' (apply (s1 `compose` s2) (extractType t1))
      env'' = apply s2 (foldr (\a b -> extend b a) env' list)
  pure $ InferResult {subst: s2, envi: env'', result: (Tuple typ t1)}

inferBindings :: TypeEnv -> List (Tuple Binding Expr) -> Infer (InferResult (List (Tuple TypeBinding TypeTree)))
inferBindings _ Nil = throwError $ UnknownError "congrats you found a bug TypeChecker.inferBindings"
inferBindings env (Cons (Tuple bin expr) Nil) = do
  InferResult {subst: s, envi: e, result: r} <- inferBinding env bin expr
  pure $ InferResult {subst: s, envi: e, result: (pure r)}
inferBindings env (Cons (Tuple bin expr) rest) = do
  InferResult {subst: s, envi: e, result: res}    <- inferBinding env bin expr
  InferResult {subst: sr, envi: er, result: resr} <- inferBindings e rest
  let sRes = s `compose` sr
  pure $ InferResult {subst: sRes, envi: er, result: (Cons res resr)}

infer :: TypeEnv -> Expr -> Infer (Tuple Subst TypeTree)
infer env ex = case ex of
  Atom (Name name) -> case name of
    "mod" -> pure $ Tuple nullSubst (TAtom (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int")))
    "div" -> pure $ Tuple nullSubst (TAtom (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int")))
    _     -> do
      Tuple s t <- lookupEnv env name
      pure (Tuple s $ TAtom t)
  Atom (Bool _) -> pure (Tuple nullSubst $ TAtom (TypCon "Bool"))
  Atom (Char _) -> pure (Tuple nullSubst $ TAtom (TypCon "Char"))
  Atom (AInt _) -> pure (Tuple nullSubst $ TAtom (TypCon "Int"))

  Lambda (Cons bin Nil) e -> do
    Tuple envL tvB <- extractBinding bin
    let env' = env `extendMultiple` envL
    Tuple s1 t1 <- infer env' e
    pure (Tuple s1 $ apply s1 (TLambda (Cons tvB Nil) t1 $ (extractBindingType tvB) `TypArr` (extractType t1)))

  Lambda (Cons bin xs) e -> do
    Tuple envL tvB <- extractBinding bin
    let env' = env `extendMultiple` envL
    inferred <- infer env' (Lambda xs e)
    case inferred of
      (Tuple s1 (TLambda tb tt t1)) ->
        pure (Tuple s1 $ apply s1 (TLambda (Cons tvB tb) tt ((extractBindingType tvB) `TypArr` t1)))
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  Lambda Nil e -> infer env e

    -- one element list
  App e1 (Cons e2 Nil) -> do
    tv <- fresh
    Tuple s1 t1 <- infer env e1
    Tuple s2 t2 <- infer (apply s1 env) e2
    s3       <- unify (apply (s1  `compose` s2) (extractType t1)) (TypArr (extractType t2) tv)
    pure (Tuple (s3 `compose` s2 `compose` s1) (apply s3 $ TApp t1 (Cons t2 Nil) tv))

  App e1 (Cons e2 xs) -> do
    inferred <- infer env  (App (App e1 (Cons e2 Nil)) xs)
    case inferred of
      Tuple s (TApp (TApp tt lt _) lt' t') -> pure $ Tuple s (TApp tt (lt<>lt') t')
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  App _ Nil -> throwError $ UnknownError "congrats you found a bug TypeChecker.infer (App Nil)"

  ListComp expr quals -> do
    Tuple sq (Tuple tq env') <- inferQuals env quals
    --let env' = apply sq env
    Tuple s t <- infer env' expr
    let s' = sq `compose` s
    pure $ Tuple s' $ apply s' $ TListComp t tq (AD (TList (extractType t)))

  LetExpr bindings expr -> case overlappingBindings (fst <$> bindings) of
    Cons x _ -> throwError $ UnknownError $ "Conflicting definitions for \'" <> x <> "\'"
    Nil      -> do
      InferResult {subst: sb, envi: envb, result: resb} <- inferBindings env bindings
      Tuple se te <- infer envb expr
      let s = sb `compose` se
      pure $ Tuple s $ apply s $ TLetExpr resb te (extractType te)

  IfExpr cond tr fl -> do
    tv <- fresh
    freshVar <- fresh
    case freshVar of
      t@(TypVar t') -> do
        let env' = env `extend` (Tuple "if" (Forall (Cons t' Nil) (TypArr (TypCon "Bool") (TypArr t (TypArr t  t)))))
        inferred <- infer env' (App (Atom $ Name "if") (Array.toUnfoldable [cond, tr, fl]))
        case inferred of
          Tuple s (TApp tt (Cons tcond (Cons ttr (Cons tfl Nil))) ift) -> pure (Tuple s $ apply s (TIfExpr tcond ttr tfl ift))
          _ -> throwError $ UnknownError "TODO: Fix uncovered cases."
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  ArithmSeq begin jstep jend -> do
    Tuple s1 t1 <- infer env begin
    tup2 <- traverse (infer env) jstep
    tup3 <- traverse (infer env) jend
    let t2 = snd <$> tup2
    let t3 = snd <$> tup3
    let s2 = maybe nullSubst fst tup2
    let s3 = maybe nullSubst fst tup3
    let s  = s1 `compose` s2 `compose` s3
    let tt = extractType t1
    let typeMissMatch m1 m2 = fromMaybe (UnknownError "congrats you found a bug TypeChecker.infer (ArithmSeq begin jstep jend)") (normalizeTypeError <$> lift2 UnificationFail m1 m2)
    ifM (pure (fromMaybe false (lift2 (/=) (Just tt) (extractType <$> t2))))
      (throwError (typeMissMatch (Just tt) (extractType <$> t2)))
      (ifM (pure (fromMaybe false (lift2 (/=) (Just tt) (extractType <$> t3))))
        (throwError (typeMissMatch (Just tt) (extractType <$> t3)))
        (ifM (pure (fromMaybe false (lift2 (/=) (extractType <$> t2) (extractType <$> t3))))
          (throwError (typeMissMatch (extractType <$> t2) (extractType <$> t3)))
          (case tt of
            TypCon "Int"  -> pure $ Tuple s $ apply s $ TArithmSeq t1 t2 t3 (AD (TList tt))
            TypCon "Bool" -> pure $ Tuple s $ apply s $ TArithmSeq t1 t2 t3 (AD (TList tt))
            TypCon "Char" -> pure $ Tuple s $ apply s $ TArithmSeq t1 t2 t3 (AD (TList tt))
            _             -> throwError $ NoInstanceOfEnum tt)))

  PrefixOp op -> do
    Tuple s t <- inferOp env op
    pure (Tuple s $ TPrefixOp t)

  SectL e op -> do
    tv <- fresh
    Tuple s1 t1 <- inferOp env op
    Tuple s2 t2 <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr (extractType t2) tv)
    pure (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TSectL t2 t1 tv)))

  SectR op e -> do
    inferredOp <- inferOp env op
    case inferredOp of
      Tuple s1 t1@(TypArr a (TypArr b c)) -> do
        Tuple s2 t2 <- infer env e
        s3       <- unify (apply s2 b) (extractType t2)
        let s4 = (s3 `compose` s2 `compose` s1)
        pure (Tuple s4 (apply s4 (TSectR t1 t2 (TypArr a c))))
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  Unary (Sub) e -> do
      tv <- fresh
      let t1 = (TypCon "Int" `TypArr` TypCon "Int")
      Tuple s2 t2 <- infer env e
      s3 <- unify (apply s2 t1) (TypArr (extractType t2) tv)
      pure (Tuple (s3 `compose` s2) (apply s3 (TUnary t1 t2 tv)))

  Unary op e -> do
    tv <- fresh
    Tuple s1 t1 <- inferOp env op
    Tuple s2 t2 <- infer (apply s1 env) e
    s3       <- unify (apply s2 t1) (TypArr (extractType t2) tv)
    pure (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TUnary t1 t2 tv)))

  Binary op e1 e2 -> do
    inferred <- infer env (App (PrefixOp op) (Cons e1 (Cons e2 Nil)))
    case inferred of
      (Tuple s (TApp tt (Cons tt1 (Cons tt2 Nil)) t)) -> pure $ Tuple s (TBinary (extractType tt) tt1 tt2 t)
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  List (Cons e1 xs) -> do
    inferred1 <- infer env (List xs)
    case inferred1 of
      Tuple s1 (TListTree ltt (AD (TList t1))) -> do
        Tuple s2 t2 <- infer (apply s1 env) e1
        s3 <- unify (apply s2 t1) (extractType t2)
        pure (Tuple (s3 `compose` s2 `compose` s1) (apply s3 (TListTree (Cons t2 ltt) (AD $ TList (extractType t2)))))
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  List Nil -> do
    tv <- fresh
    pure (Tuple nullSubst $ TListTree Nil (AD $ TList tv))

  NTuple (Cons e Nil) -> do
    Tuple s t <- infer env e
    pure $ Tuple s $ TNTuple (Cons t Nil) (AD $ TTuple $ Cons (extractType t) Nil)

  NTuple (Cons e1 xs) -> do
    inferred1 <- infer env (NTuple xs)
    case inferred1 of
      Tuple s1 (TNTuple lt (AD (TTuple t1))) -> do
          Tuple s2 t2 <- infer (apply s1 env) e1
          pure (Tuple (s2 `compose` s1) $ TNTuple (Cons t2 lt) (AD $ TTuple (Cons (extractType t2) t1)))
      _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

  NTuple Nil -> throwError $ UnknownError "congrats you found a bug in TypeChecker.infer (NTuple Nil)"

inferQual :: TypeEnv -> ExprQual -> Infer (Tuple Subst (Tuple TypeQual TypeEnv))
inferQual env (Let bin e1) = do
  Tuple s1 t1    <- infer env e1
  Tuple binding bindingType <- extractBinding bin
  s2 <- unify (extractBindingType bindingType) (extractType t1)
  let env' = apply s2 $ env `extendMultiple` binding
  let subst = s1 `compose` s2
  pure $ Tuple subst $ Tuple (apply subst (TLet bindingType t1 (extractType t1))) env'
inferQual env (Gen bin expr) = do
  Tuple s1 exprType <- infer env expr
  -- Think: [ bin | x <- expr], where x is found in bin
  case extractType exprType of
    -- Type is: [T]
    AD (TList t) -> do
      (Tuple binding bindingType) <- extractBinding bin
      s2 <- unify (extractBindingType bindingType) t
      let env' = apply s2 $ env `extendMultiple` binding
      let subst = s1 `compose` s2
      pure $ Tuple subst $ Tuple (apply subst (TGen bindingType exprType t)) env'

    -- Type is: T (a hopefully bound type variable)
    TypVar tvar -> do
      -- First extract the binding and the corresponding type t0.
      -- Then unify [t0] with the type variable tvar ([t0] ~ tvar).
      -- Apply the resulting substitution to the environment extended by the binding.
      Tuple binding bindingType <- extractBinding bin
      s2 <- unify (AD $ TList $ extractBindingType bindingType) (TypVar tvar)
      let env' = apply s2 $ env `extendMultiple` binding
      let typeTree = TGen bindingType exprType (TypVar tvar)
      let subst = s1 `compose` s2
      pure $ Tuple subst (Tuple (apply subst typeTree) env')

    _ -> fresh >>= (\t -> throwError $ normalizeTypeError $ UnificationFail (extractType exprType) (AD (TList t)))
inferQual env (Guard expr) = do
  Tuple s t <- infer env expr
  case extractType t of
    TypCon "Bool" -> pure $ Tuple s $ Tuple (apply s (TGuard t (extractType t))) env
    _             -> throwError $ normalizeTypeError $ UnificationFail (extractType t) (TypCon "Bool")

inferQuals :: TypeEnv -> List ExprQual -> Infer (Tuple Subst (Tuple (List TypeQual) TypeEnv))
inferQuals env Nil = pure $ Tuple nullSubst $ Tuple Nil emptyTyenv
inferQuals env (Cons x rest) = do
  Tuple s  (Tuple t  env1) <- inferQual env x
  Tuple sr (Tuple tr env2) <- inferQuals (apply s env1) rest
  let s' = s `compose` sr
  pure $ Tuple s' $ Tuple (t `Cons` tr) (envUnion env2 env1)

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
  f typ = pure (Tuple nullSubst typ)
  int3 = f (TypCon "Int" `TypArr` (TypCon "Int" `TypArr` TypCon "Int"))
  aBool a = f (a `TypArr` (a `TypArr` TypCon "Bool"))

inferDef :: TypeEnv -> Definition -> Infer (Tuple Subst Type)
inferDef env (Def str bin exp) = do
    tv <- fresh
    let env' = env `extend` (Tuple str (Forall Nil tv))
    let exp' = Lambda bin exp
    Tuple s1 t1' <- infer env' exp'
    let t1 = extractType t1'
    let env'' = env `extend` (Tuple str (Forall Nil (apply s1 t1)))
    Tuple s2 t2 <- infer env'' exp'
    s3 <- unify (apply s1 t1) (apply s2 (extractType t2))
    pure $ Tuple (s3 `compose` s1) (apply s3 (apply s1 t1))

extractConsLit :: Type -> Binding -> Infer (Tuple (List (Tuple TVar Scheme)) TypeBinding)
extractConsLit tv (ConsLit a b@(ConsLit _ _)) = do
  Tuple list1 typ1 <- extractBinding a
  secondBinding <- extractBinding b
  case secondBinding of
    Tuple list2 t2@(TConsLit b1 b2 (AD (TList typ2))) -> do
      s1 <- unify tv (extractBindingType typ1)
      s2 <- unify (apply s1 tv) (typ2)
      pure $ Tuple (apply s2 (apply s1 (list1 <> list2))) (apply s2 (apply s1 (TConsLit typ1 t2 (AD $ TList typ2))))
    _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

extractConsLit tv (ConsLit a (Lit (Name name))) = do
  Tuple list typ <- extractBinding a
  s1 <- unify tv (extractBindingType typ)
  let list' = apply s1 list
  let ltyp = AD $ TList (apply s1 tv)
  pure $ Tuple (Cons (Tuple name $ Forall Nil ltyp) list') $ (apply s1 (TConsLit typ (TLit ltyp) ltyp))

extractConsLit tv (ConsLit a b@(ListLit _)) = do
  Tuple list1 typ1 <- extractBinding a
  secondBinding <- extractBinding b
  case secondBinding of
    Tuple list2 t2@(TListLit b1 (AD (TList typ2))) -> do
      s1 <- unify tv (extractBindingType typ1)
      s2 <- unify (apply s1 tv) (typ2)
      pure $ Tuple (apply s2 (apply s1 (list1 <> list2))) (apply s2 (apply s1 (TConsLit typ1 t2 (AD $ TList typ2))))
    _ -> throwError $ UnknownError "TODO: Fix uncovered cases."

extractConsLit _ _ = throwError $ UnknownError "congrats you found a bug in TypeChecker.extractConsLit"

extractListLit :: List Binding -> Infer (List (Tuple (List (Tuple TVar Scheme)) TypeBinding))
extractListLit (Cons a Nil) = do
  b1 <- extractBinding a
  pure (Cons b1 Nil)

extractListLit (Cons a b) = do
  b1 <- extractBinding a
  bs <- extractListLit b
  pure (Cons b1 bs)

extractListLit Nil = pure Nil

extractBinding :: Binding -> Infer (Tuple (List (Tuple TVar Scheme)) TypeBinding)
extractBinding (Lit (Name name)) = do
  tv <- fresh
  pure $ Tuple (Array.toUnfoldable [(Tuple name (Forall Nil tv))]) (TLit tv)
extractBinding (Lit (Bool _)) = pure $ Tuple Nil $ TLit (TypCon "Bool")
extractBinding (Lit (Char _)) = pure $ Tuple Nil $ TLit (TypCon "Char")
extractBinding (Lit (AInt _)) = pure $ Tuple Nil $ TLit (TypCon "Int")

extractBinding a@(ConsLit _ _) = do
  tv <- fresh
  extractConsLit tv a

extractBinding (ListLit a) = do -- Tuple TypEnv  (TListLit (List TypeBinding) Type)
  bs <- extractListLit a
  tv <- fresh
  let ini = Tuple Nil (TListLit Nil tv)

  binding <- foldM f ini bs
  case binding of
    Tuple list (TListLit lb typ) -> pure $ Tuple list (TListLit lb (AD $ TList typ))
    _ -> throwError $ UnknownError "TODO: Fix uncovered cases."
  where
-- :: Tuple (List (Tuple Atom Scheme)) BindingType -> Tuple (List (Tuple Atom Scheme)) BindingType
--           -> Infer (Tuple (List (Tuple Atom Scheme)) BindingType)
    f (Tuple l1 (TListLit lb1 t1)) (Tuple l2 b) = do
      let ls = l1 <> l2
      s1 <- unify t1 (extractBindingType b)
      pure $ Tuple (apply s1 ls) (apply s1 (TListLit (Cons b lb1) t1))
    f _ _ = throwError $ UnknownError "congrats you found a bug in TypeChecker.extractBinding"

extractBinding (NTupleLit a) = do
  bs <- extractListLit a
  let tup = unzip bs
  pure $ Tuple (concat $ fst tup) (TNTupleLit (snd tup) (AD $ TTuple $ (map extractBindingType (snd tup))))

getTypEnv :: Binding -> TypeEnv -> Maybe TypeEnv
getTypEnv b env = case evalState (runExceptT (extractBinding b)) initUnique of
    Left _ -> Nothing
    Right (Tuple bs _) -> Just $ env `extendMultiple` bs

getTypEnvFromList :: List Binding -> TypeEnv -> Maybe TypeEnv
getTypEnvFromList bs env = do
                  mTypList <- traverse (flip getTypEnv emptyTyenv) bs
                  pure $ foldr (\a b -> unionTypeEnv a b) env mTypList

unionTypeEnv :: TypeEnv -> TypeEnv -> TypeEnv
unionTypeEnv (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

inferGroup :: TypeEnv -> List Definition -> Infer (Tuple Subst Type)
inferGroup _ Nil = throwError $ UnknownError "Cant type empty Group"
inferGroup env (Cons def1 Nil) = inferDef env def1
inferGroup env (Cons def1 defs) = do
  Tuple s1 t1 <- inferDef env def1
  Tuple s2 t2 <- inferGroup env defs
  s3 <- unify t1 t2
  pure $ Tuple s3 (apply s3 t1)

buildTypeEnv :: List Definition -> Either TypeError TypeEnv
buildTypeEnv Nil = Right emptyTyenv
buildTypeEnv defs = buildTypeEnvFromGroups emptyTyenv groupMap keys
  where
    groupMap = buildGroups defs
    keys = Map.keys groupMap

buildGroups :: List Definition -> Map.Map String (List Definition)
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
buildTypeEnvFromGroups :: TypeEnv -> Map.Map String (List Definition)
  -> List String -> Either TypeError TypeEnv
buildTypeEnvFromGroups env _ Nil = Right env
buildTypeEnvFromGroups env groupMap k@(Cons key keys) =
  case mayDefs of
    Nothing -> Left $ UnboundVariable key
    Just defs -> case runInfer $ inferGroup env defs of
      Right scheme -> buildTypeEnvFromGroups
        (env `extend` (Tuple key scheme)) (Map.delete key groupMap) keys
      Left (UnboundVariable var) -> buildTypeEnvFromGroups
        env groupMap (Cons var (delete var k))
      Left err -> Left err
  where
    mayDefs = Map.lookup key groupMap

typeProgramn :: List Definition -> Expr -> Either TypeError Scheme
typeProgramn defs exp = case runInfer <$>
    (inferType <$> (buildTypeEnv defs) <*> pure exp) of
  Left err -> Left err
  Right a -> a

typeTreeProgramn :: List Definition -> Expr -> Either TypeError TypeTree
typeTreeProgramn defs exp = case m of
  Left e -> Left e
  Right m' -> case evalState (runExceptT m') initUnique of
    Left err -> Left err
    Right res -> Right $ closeOverTypeTree res
  where
    m = (infer <$> (buildTypeEnv defs) <*> pure exp)

typeTreeProgramnEnv :: TypeEnv -> Expr -> Either TypeError TypeTree
typeTreeProgramnEnv env expr = case evalState (runExceptT (infer env expr)) initUnique of
      Left err -> Left err
      Right res -> Right $ closeOverTypeTree res

closeOverTypeTree :: (Tuple Subst TypeTree) -> TypeTree
closeOverTypeTree (Tuple s tt) = normalizeTypeTree (apply s tt)

emptyType :: Type
emptyType = TypCon ""

-- typeTreeProgramnEnv env expr
-- types subtree if typ correct
buildPartiallyTypedTree :: TypeEnv -> Expr -> TypeTree
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
  f err (LetExpr bin expr) = let
    tup   = buildPartiallyTypedTreeBindings env bin
    env'  = fst tup
    binds = snd tup in TLetExpr binds (buildPartiallyTypedTree env' expr) (TypeError err)

  f err (Lambda bs e) = let f' env' = TLambda (map g bs) (buildPartiallyTypedTree env' e) (TypeError err) in
                    case getTypEnvFromList bs env of
                          Nothing -> f' env
                          Just env' -> f' env'
  f err (App e es) = TApp (buildPartiallyTypedTree env e) (map (buildPartiallyTypedTree env) es) (TypeError err)

  f err (ListComp e es) = TListComp (buildPartiallyTypedTree env e) (map (buildPartiallyTypedTreeQual err env) es) (TypeError err)
  f err (Unary op e) = TUnary (typeOP op) (buildPartiallyTypedTree env e) (TypeError err)

-- Binding to BindingType
  g (Lit _) = TLit emptyType
  g (ConsLit b1 b2) = TConsLit (g b1) (g b2) emptyType
  g (ListLit bs) = TListLit (map g bs) emptyType
  g (NTupleLit bs) = TNTupleLit (map g bs) emptyType

  -- typeOp :: Op -> Type
  typeOP op = case typeTreeProgramnEnv env (PrefixOp op) of
    Left err -> TypeError err
    Right (TPrefixOp typ) -> typ
    Right _ -> TypeError $ UnknownError "TODO: stupid error"

  buildPartiallyTypedTreeQual :: TypeError -> TypeEnv -> ExprQual -> TypeQual
  buildPartiallyTypedTreeQual err env qual = case qual of
    Let bin expr -> let env' = fromMaybe env (getTypEnvFromList (singleton bin) env) in
      TLet (g bin) (buildPartiallyTypedTree env' expr) (TypeError err)
    Gen bin expr -> let env' = fromMaybe env (getTypEnvFromList (singleton bin) env) in
      TGen (g bin) (buildPartiallyTypedTree env' expr) (TypeError err)
    Guard expr   -> TGuard (buildPartiallyTypedTree env expr) (TypeError err)

  buildPartiallyTypedTreeBindings :: TypeEnv -> List (Tuple Binding Expr) -> Tuple TypeEnv (List (Tuple TypeBinding TypeTree))
  buildPartiallyTypedTreeBindings env binds = case binds of
    Nil                   -> Tuple env Nil
    Cons (Tuple b e) bs -> let
      t     = buildPartiallyTypedTree env e
      env'  = fromMaybe env (getTypEnv b env)
      env'' = envUnion env env' in
        case buildPartiallyTypedTreeBindings env'' bs of
          Tuple envR rest -> Tuple envR $ (Tuple (g b) t) : rest

eqScheme :: Scheme -> Scheme -> Boolean
eqScheme (Forall l1 t1) (Forall l2 t2)
  = ((length l1) == (length l2)) && (fst (eqType Map.empty t1 t2))

eqType :: Map.Map TVar TVar -> Type -> Type -> Tuple Boolean (Map.Map TVar TVar)
eqType map (TypVar a) (TypVar b) = case  Map.lookup a map of
  Just b' -> Tuple (b' == b) (map)
  Nothing -> Tuple true (Map.insert a b map)
eqType map (TypCon a) (TypCon b) = Tuple (a == b) map
eqType map (TypArr a b) (TypArr a' b') = Tuple (fst tup1 && fst tup2) (snd tup2)
  where
  tup1 = eqType map a a'
  tup2 = eqType (snd tup1) b b'
eqType map (AD (TList a)) (AD (TList b)) = eqType map a b
eqType map (AD (TTuple a)) (AD (TTuple b)) = eqTypeList map a b
eqType map _ _ = Tuple false map

eqTypeList :: Map.Map TVar TVar -> List Type -> List Type -> Tuple Boolean (Map.Map TVar TVar)
eqTypeList map (Cons a as) (Cons b bs) = let tup1 = eqType map a b in if (fst tup1)
  then eqTypeList (snd tup1) as bs
  else Tuple false (snd tup1)
eqTypeList map Nil Nil = Tuple true map
eqTypeList map _ _ = Tuple false map

normalizeTypeTree :: TypeTree -> TypeTree
normalizeTypeTree tt = fst $ runState (helptxToABC tt) {count : 0, env : empty}

helptxToABC :: TypeTree -> State {count :: Int, env :: Map String String} TypeTree
helptxToABC tt = go tt
  where
    go (TAtom t) = helpTypeToABC t >>= \t -> pure $ TAtom t
    go (TListTree tts t) = do
      tts' <- traverse helptxToABC tts
      t' <- helpTypeToABC t
      pure $ TListTree tts' t'
    go (TNTuple tts t) = do
      tts' <- traverse helptxToABC tts
      t' <- helpTypeToABC t
      pure $ TNTuple tts' t'
    go (TBinary t1 tt1 tt2 t) = do
      t1' <- helpTypeToABC t1
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      t' <- helpTypeToABC t
      pure $ TBinary t1' tt1' tt2' t'
    go (TUnary t1 tt t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      pure $ (TUnary t1' tt' t')
    go (TSectL tt t1 t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      pure $ TSectL tt' t1' t'
    go (TSectR t1 tt t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      pure $ TSectR t1' tt' t'
    go (TPrefixOp t) = helpTypeToABC t >>= \t -> pure $ TPrefixOp t
    go (TIfExpr tt1 tt2 tt3 t) = do
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      tt3' <- helptxToABC tt3
      t' <- helpTypeToABC t
      pure $ TIfExpr tt1' tt2' tt3' t'
    go (TArithmSeq tt1 tt2 tt3 t) = do
      tt1' <- helptxToABC tt1
      tt2' <- traverse helptxToABC tt2
      tt3' <- traverse helptxToABC tt3
      t'   <- helpTypeToABC t
      pure $ TArithmSeq tt1' tt2' tt3' t'
    go (TLetExpr bin tt t) = do
      bin' <- traverse (\(Tuple x y) -> lift2 Tuple (helpBindingToABC x) (helptxToABC y)) bin
      tt'  <- helptxToABC tt
      t'   <- helpTypeToABC t
      pure $ TLetExpr bin' tt' t'
    go (TLambda tbs tt t) = do
      tbs' <- traverse helpBindingToABC tbs
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      pure $ TLambda tbs' tt' t'
    go (TApp tt tts t) = do
      tt' <- helptxToABC tt
      tts' <- traverse helptxToABC tts
      t' <- helpTypeToABC t
      pure $ TApp tt' tts' t'
    go (TListComp tt tts t) = do
      tt'  <- helptxToABC tt
      tts' <- traverse helptxToABCQual tts
      t'   <- helpTypeToABC t
      pure $ TListComp tt' tts' t'

normalizeType :: Type -> Type
normalizeType t = fst $ runState (helpTypeToABC t) {count: 0, env: empty}

normalizeTypeError :: TypeError -> TypeError
normalizeTypeError (UnificationFail t1 t2) = UnificationFail (normalizeType t1) (normalizeType t2)
normalizeTypeError (InfiniteType tvar t) = InfiniteType (prettyPrintType $ normalizeType $ TypVar tvar) (normalizeType t)
normalizeTypeError error = error

helptxToABCQual :: TypeQual -> State {count :: Int, env :: Map String String} TypeQual
helptxToABCQual q = case q of
  TGen b e t -> do
    b' <- helpBindingToABC b
    e' <- helptxToABC e
    t' <- helpTypeToABC t
    pure $ TGen b' e' t'
  TLet b e t -> do
    b' <- helpBindingToABC b
    e' <- helptxToABC e
    t' <- helpTypeToABC t
    pure $ TLet b' e' t'
  TGuard e t -> do
    e' <- helptxToABC e
    t' <- helpTypeToABC t
    pure $ TGuard e' t'

helpTypeToABC :: Type  -> State {count :: Int, env :: (Map String String)} Type
helpTypeToABC t = go t
  where
   go (TypVar var) = do
      {env: env} :: {count :: Int, env :: Map String String} <- get
      case lookup var env of
        Just var' -> pure $ TypVar var'
        Nothing -> do
          {count: count} <- get
          let newVarName = getNthName count
          let env' = insert var newVarName env
          put {count: count + 1, env: env'}
          pure $ TypVar newVarName
   go (TypArr t1 t2) = do
        t1' <- helpTypeToABC t1
        t2' <- helpTypeToABC t2
        pure $ TypArr t1' t2'
   go (AD a) = helpADTypeToABC a >>= \a -> pure $ AD a
   go a = pure a

helpADTypeToABC :: AD -> State {count :: Int, env :: (Map String String)} AD
helpADTypeToABC (TList t) = helpTypeToABC t >>= \t -> pure $ TList t
helpADTypeToABC (TTuple ts) = traverse helpTypeToABC ts >>= \ts -> pure $ TTuple ts

helpBindingToABC :: TypeBinding -> State {count :: Int, env :: (Map String String)} TypeBinding
helpBindingToABC bin = go bin
  where
    go (TLit t) = helpTypeToABC t >>= \t -> pure $ TLit t
    go (TConsLit tb1 tb2 t) = do
      tb1' <- helpBindingToABC tb1
      tb2' <- helpBindingToABC tb2
      t' <- helpTypeToABC t
      pure $ TConsLit tb1' tb2' t'
    go (TListLit tbs t) = do
      tbs' <- traverse helpBindingToABC tbs
      t' <- helpTypeToABC t
      pure $ TListLit tbs' t'
    go (TNTupleLit tbs t) = do
      tbs' <- traverse helpBindingToABC tbs
      t' <- helpTypeToABC t
      pure $ TNTupleLit tbs' t'

-- Given an int generate an array of integers used as indices into the alphabet in `getNthName`.
-- Example: map indexList (700..703) => [[24,25],[25,25],[0,0,0],[1,0,0]]
indexList :: Int -> Array Int
indexList n | n `div` 26 > 0 = n `mod` 26 `Array.cons` indexList (n `div` 26 - 1)
indexList n = [n `mod` 26]

-- Given an int choose a new name. We choose names simply by indexing into the alphabet. As soon
-- "z" is reached, begin with "aa" and so on.
-- Example: map getNthName (700..703) => ["zy","zz","aaa","aab"]
getNthName :: Int -> String
getNthName = fromCharArray <<< toCharArray <<< Array.reverse <<< indexList
  where toCharArray = map (Char.fromCharCode <<< ((+) 97))

checkForError :: Path -> TypeTree -> Boolean
checkForError p' tt = case p' of
  End -> isTypeError $ extractType tt
  Fst p -> case tt of
      TBinary op e1 e2 _ -> checkForError p e1
      TUnary op e      _ -> checkForError p e
      TSectL e op      _ -> checkForError p e
      TIfExpr ce te ee _ -> checkForError p ce
      TArithmSeq ce te ee _ -> checkForError p ce
      TLambda bs body  _ -> checkForError p body
      TApp e es        _ -> checkForError p e
      TListComp e _    _ -> checkForError p e
      TLetExpr (Cons (Tuple _ e) _) _ _ -> checkForError p e
      _               -> true
  Snd p -> case tt of
      TBinary op e1 e2 _ -> checkForError p e2
      TSectR op e      _ -> checkForError p e
      TIfExpr ce te ee _ -> checkForError p te
      TArithmSeq ce (Just te) ee _ -> checkForError p te
      _               -> true
  Thrd p -> case tt of
      TIfExpr ce te ee _ -> checkForError p ee
      TArithmSeq ce te (Just ee) _ -> checkForError p ee
      _ -> true
  Nth n p -> case tt of
      TListTree es  _ -> nth n es p
      TNTuple es _ -> nth n es p
      TApp e' es _ -> nth n es p
      TListComp e' es _ -> nth' n es p
      _        -> true
  where
    nth n es p = case (!!) es n of
      Nothing -> true
      Just e -> checkForError p e

    nth' n es p = case (!!) es n of
      Nothing -> true
      Just e -> checkForError' p e

checkForError' :: Path -> TypeQual -> Boolean
checkForError' p' q = case p' of
  (End)   -> isTypeError $ extractedType q
  (Fst p) -> case q of
      TLet bin expr t -> checkForError p expr
      TGen bin expr t -> checkForError p expr
      TGuard expr t   -> checkForError p expr
  _ -> true
  where
    extractedType qu = case qu of
      TLet _ _ t -> t
      TGen _ _ t -> t
      TGuard _ t -> t

isTypeError :: Type -> Boolean
isTypeError t = case t of
  (TypeError _) -> true
  _ -> false
