module Evaluator where

import Prelude hiding (apply)
import Data.List (List(Nil, Cons), null, singleton, concatMap, intersect, zipWith, zipWithA, length, (:), drop, concat)
import Data.List.Lazy (replicate)
import Data.StrMap (StrMap, delete)
import Data.StrMap as Map
import Data.Tuple (Tuple(Tuple), fst, snd)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Foldable (foldl, foldr, foldMap, product)
import Data.Traversable (traverse)
import Data.Identity (Identity)
import Data.Either (Either(..), either)
import Data.Monoid (class Monoid)
import Data.String (toChar)
import Data.String (singleton) as String
import Data.Char (fromCharCode)
import Data.Enum (fromEnum)
import Control.Comonad (extract)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (State, runState)
import Control.Monad.State.Trans (StateT, get, modify, put, runStateT, execStateT)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.Except.Trans (ExceptT, throwError, runExceptT)

-- import JSHelpers (unsafeUndef)

import AST (TypeTree, Tree(..), Atom(..), Binding(..), Definition(Def), Op(..), QualTree(..), TypeQual, MType, DataConstr (..), Meta (..))
import AST as AST

--------------------------------------------------------------------------------
-- Utils -----------------------------------------------------------------------
--------------------------------------------------------------------------------

zipWithM :: forall m a b c. (Monad m) => (a -> b -> m c) -> List a -> List b -> m (List c)
zipWithM _ Nil _                   = pure Nil
zipWithM _ _   Nil                 = pure Nil
zipWithM f (Cons a as) (Cons b bs) = Cons <$> f a b <*> zipWithM f as bs

mapM' :: forall a b m. (Monad m) => (a -> m b) -> Maybe a -> m (Maybe b)
mapM' f Nothing  = pure Nothing
mapM' f (Just x) = Just <$> (f x)
--------------------------------------------------------------------------------

data EvalError =
    IndexError Int Int
  | DivByZero
  | EvalError TypeTree
  | BinaryOpError Op TypeTree TypeTree
  | UnaryOpError Op TypeTree
  | NameCaptureError (List String)
  | UnknownFunction String
  | NoMatchingFunction String (List MatchingError)
  | BindingError MatchingError
  | CannotEvaluate TypeTree
  | NoError
  | MoreErrors EvalError EvalError

instance semigroupEvalError :: Semigroup EvalError where
  append e1 e2 = MoreErrors e1 e2

instance monoidEvalError :: Monoid EvalError where
  mempty = NoError

instance showEvalError :: Show EvalError where
  show (IndexError i l)           = "IndexError " <> show i <> " " <> show l
  show DivByZero                  = "DivByZero"
  show (EvalError e)              = "EvalError " <> show e
  show (BinaryOpError o e1 e2)    = "BinaryOpError " <> show o <> " (" <> show e1 <> ") (" <> show e2 <> ")"
  show (UnaryOpError o e)         = "UnaryOpError " <> show o <> " " <> show e
  show (NameCaptureError ns)      = "NameCaptureError " <> show ns
  show (UnknownFunction n)        = "UnknownFunction " <> show n
  show (NoMatchingFunction n mes) = "NoMatchingFunction " <> show n <> " " <> show mes
  show (BindingError me)          = "BindingError " <> show me
  show (CannotEvaluate e)         = "CannotEvaluate " <> show e
  show NoError                    = "NoError"
  show (MoreErrors e1 e2)         = "(MoreErrors " <> show e1 <> " " <> show e2 <> ")"

data MatchingError =
    MatchingError (Binding Meta) TypeTree
  | StrictnessError (Binding Meta) TypeTree
  | TooFewArguments (List (Binding Meta)) (List TypeTree)

instance showMatchingError :: Show MatchingError where
  show (MatchingError b e)     = "MatchingError " <> show b <> " " <> show e
  show (StrictnessError b e)   = "StrictnessError " <> show b <> " " <> show e
  show (TooFewArguments bs es) = "TooFewArguments " <> show bs <> " " <> show es

type Evaluator = StateT Int (ExceptT EvalError Identity)

runEvalM :: forall a. Int -> Evaluator a -> Either EvalError (Tuple a Int)
runEvalM idx = extract <<< runExceptT <<< flip runStateT idx

type Matcher = StateT Int (ExceptT MatchingError Identity)

runMatcherM :: forall a. Int -> Matcher a -> Either MatchingError (Tuple a Int)
runMatcherM idx = extract <<< runExceptT <<< flip runStateT idx

type Env = StrMap (List (Tuple (List (Binding Meta)) TypeTree))

defsToEnv :: (List Definition) -> Env
defsToEnv = foldl insertDef Map.empty

envToDefs :: Env -> (List Definition)
envToDefs env = concat $ map tupleToDef $ Map.toList env
  where
    tupleToDef (Tuple name defs) = map
                                    (\(Tuple bin expr) -> Def name bin expr)
                                    defs

insertDef :: Env -> Definition -> Env
insertDef env (Def name bindings body) = case Map.lookup name env of
  Nothing   -> Map.insert name (singleton $ Tuple bindings body) env
  Just defs -> Map.insert name (defs <> (singleton $ Tuple bindings body)) env

-- | Evaluates an expression by one step in a given environment.
eval1 :: Env -> TypeTree -> Evaluator TypeTree
eval1 env expr = case expr of
  (Binary _ op e1 e2)                  -> binary env op e1 e2
  (Unary _ op e)                       -> unary env op e
  (Atom _ (Name name))                 -> apply env name Nil
  (IfExpr _ (Atom _ (Bool true)) te _)   -> pure te
  (IfExpr _ (Atom _ (Bool false)) _ ee)  -> pure ee
  (ArithmSeq _ start step end)         -> evalArithmSeq start step end
  -- (List _ (Cons e es))                      -> pure $ Binary Nothing Colon e (List Nothing es)
  (App _ (Binary _ (Tuple Composition _) f g) (Cons e Nil)) -> pure $ App AST.emptyMeta f (singleton $ App AST.emptyMeta g (Cons e Nil))
  (App _ (Lambda _ binds body) args)     -> tryAll env (singleton $ Tuple binds body) args "lambda" Nil
  (App _ (SectL _ e1 op) (Cons e2 Nil))           -> {-binary env op e1 e2 <|>-} (pure $ Binary AST.emptyMeta op e1 e2)
  (App _ (SectR _ op e2) (Cons e1 Nil))           -> {-binary env op e1 e2 <|>-} (pure $ Binary AST.emptyMeta op e1 e2)
  (App _ (PrefixOp _ op) (Cons e1 (Cons e2 Nil)))         -> {-binary env op e1 e2 <|>-} (pure $ Binary AST.emptyMeta op e1 e2)
  (App _ (Atom _ (Name name)) args)      -> apply env name args
  (App _ (App _ func es) es')            -> pure $ App AST.emptyMeta func (es <> es')
--  (App _ (Atom _ (Constr _)) _)      -> pure expr
  (ListComp _ e qs)                    -> evalListComp env e qs
  (LetExpr _ binds exp)                -> evalLetTypeTree binds exp
--  (Atom _ (Constr x))                -> pure expr
  _                                  -> throwError $ CannotEvaluate expr

eval :: Int -> Env -> TypeTree -> Tuple TypeTree Int
eval nextIdx env expr = runState (evalToBinding env expr (Lit AST.emptyMeta (Name "_|_"))) nextIdx

freshMeta :: forall m. (MonadState Int m) => m Meta
freshMeta = do
  i <- get
  modify (\i -> i + 1)
  pure $ AST.idxMeta i

-- | Evaluates an expression until it matches a given binding in a given environment.
evalToBinding :: Env -> TypeTree -> Binding Meta -> State Int TypeTree
evalToBinding env expr bind = case bind of
  (Lit _ (Name "_|_")) -> recurse env expr bind
  (Lit _ (Name _))     -> pure expr
  (Lit _ _)            -> case expr of
    (Atom _ _) -> pure expr
    _          -> recurse env expr bind

  (ConsLit _ b bs)     -> case expr of
    (Binary meta (Tuple Colon meta') e es) -> Binary meta (Tuple Colon meta') <$> evalToBinding env e b <*> evalToBinding env es bs
    (List _ (Cons e es))  -> do
      meta   <- freshMeta
      meta'  <- freshMeta
      meta'' <- freshMeta
      evalToBinding env (Binary meta (Tuple Colon meta') e (List meta'' es)) bind
    _                     -> recurse env expr bind

  (ListLit _ bs) -> case expr of
    (List meta es)
      | (length es == length bs) -> List meta <$> zipWithM (evalToBinding env) es bs -- TODO Define zipWithM
      | otherwise                -> pure expr
    _           -> recurse env expr bind

  (NTupleLit _ bs) -> case expr of
    (NTuple meta es) -> NTuple meta <$> zipWithM (evalToBinding env) es bs
    _                -> recurse env expr bind
  (ConstrLit _ (PrefixDataConstr n _ ps)) ->
    case expr of
      (App meta (Atom meta' (Constr n')) ps') ->
        case n == n' && length ps == length ps' of
          true -> App meta (Atom meta' (Constr n')) <$> zipWithM (evalToBinding env) ps' ps
          false -> pure expr
      _ -> recurse env expr bind
  (ConstrLit _ (InfixDataConstr n _ _ l r)) ->
    case expr of
      (App meta (PrefixOp meta' (Tuple (InfixConstr n') meta'')) (Cons l' (Cons r' Nil))) ->
        case n == n' && meta'' == AST.emptyMeta of
             true -> do
               el <- evalToBinding env l' l
               er <- evalToBinding env r' r
               pure $ App meta (PrefixOp meta' (Tuple (InfixConstr n') meta'')) (Cons el (Cons er Nil))
             false -> pure expr
      (Binary meta (Tuple (InfixConstr n') meta') l' r') ->
        case n == n' of
             true -> Binary meta (Tuple (InfixConstr n') meta') <$> evalToBinding env l' l <*> evalToBinding env r' r
             false -> pure expr
      _ -> recurse env expr bind



recurse :: Env -> TypeTree -> Binding Meta -> State Int TypeTree
recurse env expr bnd = do
  e' <- expr'
  idx <- get
  eval1d <- case runEvalM idx (eval1 env e') of
       Left _                 -> pure e'
       Right (Tuple e'' idx') -> do
         put idx'
         pure e''
  if expr == eval1d
     then pure expr
     else evalToBinding env eval1d bnd
 where
    expr' :: State Int TypeTree
    expr' = case expr of
      (Binary meta op e1 e2)  ->
        Binary meta <$> pure op <*> evalToBinding env e1 bnd <*> evalToBinding env e2 bnd
      (Unary meta op e)       ->
        Unary meta <$> pure op <*> evalToBinding env e bnd
      (List meta es)          ->
        List meta <$> mapM (\e -> evalToBinding env e bnd) es
      (NTuple meta es)        ->
        NTuple meta <$> mapM (\e -> evalToBinding env e bnd) es
      (IfExpr meta c t e)     ->
        IfExpr meta <$> evalToBinding env c bnd <*> pure t <*> pure e
      (App meta c@(Atom _ (Constr _)) args) ->
        App meta <$> pure c <*> mapM (\e -> evalToBinding env e bnd) args
      (App meta f args)       ->
        App meta <$> evalToBinding env f bnd <*> pure args
      (ArithmSeq meta c t e)     ->
        ArithmSeq meta
        <$> evalToBinding env c bnd
        <*> mapM' (\x -> evalToBinding env x bnd) t
        <*> mapM' (\x -> evalToBinding env x bnd) e
      (ListComp meta e qs)    ->
        ListComp meta <$> evalToBinding env e bnd <*> mapM (\x -> evalToBindingQual env x bnd) qs
      _                  -> pure expr

    evalToBindingQual :: Env -> TypeQual -> Binding Meta -> State Int TypeQual
    evalToBindingQual environment qual bnding = case qual of
      Let meta b e -> Let meta b <$> evalToBinding environment e bnd
      Gen meta b e -> Gen meta b <$> evalToBinding environment e bnd
      Guard meta e -> Guard meta <$> evalToBinding environment e bnd



wrapLambda :: (List (Binding Meta)) -> (List TypeTree) -> TypeTree -> Evaluator TypeTree
wrapLambda binds args body =
  case compare (length binds) (length args) of
    EQ -> pure body
    GT -> pure $ Lambda AST.emptyMeta (drop (length args) binds) body
    LT -> pure $ App AST.emptyMeta body (drop (length binds) args)

------------------------------------------------------------------------------------------
-- Arithmetic Sequences
------------------------------------------------------------------------------------------

--  packs the evaluation result for arithmetic sequences (AS)

--  example:
--  Quat (Just x) (Just y) (Just z) (Just a) will be displayed as x : [y, z .. a]

data Quat a = Quat a a a a

instance functorQuat :: Functor Quat where
  map f (Quat a b c d) = Quat (f a) (f b) (f c) (f d)

intFromStepTo :: Int -> Maybe Int -> Maybe Int -> Quat (Maybe Int)
intFromStepTo start Nothing Nothing     = Quat (Just start) (clampSucc start) Nothing Nothing

intFromStepTo start (Just step) Nothing = case clampStep start step of
  Just nstep -> Quat (Just start) (Just step) (Just nstep) Nothing
  Nothing    -> Quat (Just start) (Just step) Nothing (Just step)

intFromStepTo start Nothing (Just end) = case start > end of
  true  -> Quat Nothing Nothing Nothing Nothing
  false -> case start == end of
    true  -> Quat (Just end) Nothing Nothing Nothing
    false -> case clampSucc start of
      Just nstart -> Quat (Just start) (Just nstart) Nothing (Just end)
      Nothing     -> Quat (Just start) Nothing Nothing Nothing

intFromStepTo start (Just step) (Just end) = case (start <= step && start > end) || (start > step && start < end) of
  true  -> Quat Nothing Nothing Nothing Nothing
  false -> if start == end || (abs step) > (abs end)
    then Quat (Just start) Nothing Nothing Nothing
    else case clampStep start step of
      Nothing    -> Quat (Just start) (Just step) Nothing (Just step)
      Just nstep -> Quat (Just start) (Just step) (Just nstep) (Just end)

abs :: Int -> Int
abs x = if x < 0 then -x else x

clampSucc :: Int -> Maybe Int
clampSucc i = if i < top then Just (i + 1) else Nothing

clampStep :: Int -> Int -> Maybe Int
clampStep istart istep = if istep >= istart
  then if (top - istep)    >= (istep - istart) then Just (istep + (istep - istart)) else Nothing
  else if (bottom - istep) <= (istep - istart) then Just (istep + (istep - istart)) else Nothing

exprFromStepTo :: TypeTree -> Maybe TypeTree -> Maybe TypeTree -> Quat (Maybe TypeTree)
exprFromStepTo start step end = case start of
  Atom _ (AInt i) -> (\x -> (Atom AST.emptyMeta <<< AInt) <$> x) <$> intQuat
  Atom _ (Bool b) -> (\x -> (Atom AST.emptyMeta <<< Bool) <$> x) <$> (intToABool intQuat)
  Atom _ (Char c) -> (\x -> (Atom AST.emptyMeta <<< Char <<< String.singleton) <$> x) <$> (intToAChar intQuat)
  _             -> Quat Nothing Nothing Nothing Nothing
    where
      intQuat = intFromStepTo (unsafeTypeTreeToInt start) (unsafeTypeTreeToInt <$> step) (unsafeTypeTreeToInt <$> end)

--detects whether 'top' or 'bottom' for Boolean was reached
intToABool :: Quat (Maybe Int) -> Quat (Maybe Boolean)
intToABool quat = case temp of
  Quat (Just x) (Just y) z a -> if x == y then Quat (Just x) Nothing Nothing Nothing else temp
  _ -> temp
  where 
    temp :: Quat (Maybe Boolean)
    temp = (\x -> intToBool' <$> x) <$> quat

    intToBool' :: Int -> Boolean
    intToBool' i = if i <= 0 then false else true

--detects whether 'top' or 'bottom' for Char was reached
intToAChar :: Quat (Maybe Int) -> Quat (Maybe Char)
intToAChar quat = case temp of
  Quat (Just x) (Just y) z a -> if x == y then Quat (Just x) Nothing Nothing Nothing else temp
  _ -> temp
  where
    temp :: Quat (Maybe Char)
    temp = (\x -> intToChar' <$> x) <$> quat

    intToChar' :: Int -> Char
    intToChar' i = if c >= (top :: Char) then top else if c <= (bottom :: Char) then bottom else c
      where c = fromCharCode i

unsafeTypeTreeToInt :: TypeTree -> Int
unsafeTypeTreeToInt (Atom _ (AInt i))   = i
unsafeTypeTreeToInt (Atom _ (Bool b))   = fromEnum b
unsafeTypeTreeToInt (Atom _ (Char str)) = fromEnum $ fromMaybe 'E' (toChar str)
unsafeTypeTreeToInt _ = top

evalArithmSeq :: TypeTree -> Maybe TypeTree -> Maybe TypeTree -> Evaluator TypeTree
evalArithmSeq start step end = case foldr (&&) true (isValid <$> [Just start, step, end]) of
  false -> throwError $ CannotEvaluate $ ArithmSeq AST.emptyMeta start step end
  true  -> evalArithmSeq'
  where
    isValid :: Maybe TypeTree -> Boolean
    isValid Nothing = true
    isValid (Just (Atom _ (Name _))) = false
    isValid (Just (Atom _ _)) = true
    isValid _ = false

    evalArithmSeq' :: Evaluator TypeTree
    evalArithmSeq' = case (exprFromStepTo start step end) of
      Quat Nothing _ _ _          -> pure $ List AST.emptyMeta Nil
      Quat (Just a) Nothing _ _   -> pure $ AST.binary Colon a (List AST.emptyMeta Nil)
      Quat (Just a) (Just na) b c -> pure $ AST.binary Colon a (ArithmSeq AST.emptyMeta na b c)

------------------------------------------------------------------------------------------
-- List Comprehensions
------------------------------------------------------------------------------------------

evalListComp :: Env -> TypeTree -> List TypeQual -> Evaluator TypeTree
evalListComp _   expr Nil         = pure $ List AST.emptyMeta $ singleton expr
evalListComp env expr (Cons q qs) = case q of
  Guard _ (Atom _ (Bool false)) -> pure $ List AST.emptyMeta Nil
  Guard _ (Atom _ (Bool true))  -> if null qs then pure (List AST.emptyMeta (singleton expr)) else pure (ListComp AST.emptyMeta expr qs)
  Gen _ _ (List _ Nil)          -> pure $ List AST.emptyMeta Nil
  -- Gen _ b (List (Cons e Nil)) -> evalListComp env expr (Cons (Let AST.emptyMeta b e) qs)
  Gen _ b (List _ (Cons e es))  -> do
    listcomp1 <- evalListComp env expr (Cons (Let AST.emptyMeta b e) qs)
    listcomp2 <- pure $ ListComp AST.emptyMeta expr (Cons (Gen AST.emptyMeta b (List AST.emptyMeta es)) qs)
    case listcomp1 of
      List _ (Cons x Nil) -> pure $ Binary AST.emptyMeta (Tuple Colon AST.emptyMeta) x listcomp2
      _ -> pure $ AST.binary Append listcomp1 listcomp2
  -- Gen _ b (Binary Colon e (List Nil)) -> evalListComp env expr (Cons (Let AST.emptyMeta b e) qs)
  Gen _ b (Binary _ (Tuple Colon _) e es)  -> do
    listcomp1 <- evalListComp env expr (Cons (Let AST.emptyMeta b e) qs)
    listcomp2 <- pure $ ListComp AST.emptyMeta expr (Cons (Gen AST.emptyMeta b es) qs)
    case listcomp1 of
      List _ (Cons x Nil) -> pure $ AST.binary Colon x listcomp2
      _ -> pure $ AST.binary Append listcomp1 listcomp2
  Gen _ b e -> pure $ ListComp AST.emptyMeta expr
    (Cons (Gen AST.emptyMeta b (evalToBinding env e (ConsLit AST.emptyMeta b (Lit AST.emptyMeta (Name "_"))))) qs)
  Let _ b e -> case runMatcherM $ matchls' Map.empty (singleton b) (singleton e) of
    Right r -> do
      Tuple qs' r' <- runStateT (replaceQualifiers qs) r
      expr'        <- replace' r' expr
      case qs' of 
          Nil -> pure $ List AST.emptyMeta $ singleton expr'
          _   -> pure $ ListComp AST.emptyMeta expr' qs'
    Left l  -> throwError $ BindingError $ MatchingError b e
  _ -> throwError $ CannotEvaluate (ListComp AST.emptyMeta expr (Cons q qs))

-- replaces expressions in List-Comprehension-Qualifiers and considers overlapping bindings
replaceQualifiers :: List TypeQual -> StateT (StrMap TypeTree) Evaluator (List TypeQual)
replaceQualifiers = traverse replaceQual
  where
    replaceQual :: TypeQual -> StateT (StrMap TypeTree) Evaluator TypeQual
    replaceQual qual = case qual of
      Gen _ b e -> scope b e >>= \e' -> pure $ Gen AST.emptyMeta b e'
      Let _ b e -> scope b e >>= \e' -> pure $ Let AST.emptyMeta b e'
      Guard _ e -> do
        sub <- get
        e'  <- lift $ replace' sub e
        pure $ Guard AST.emptyMeta e'

scope :: Binding Meta -> TypeTree -> StateT (StrMap TypeTree) Evaluator TypeTree
scope b e = do
  sub <- get
  e'  <- lift $ replace' sub e
  modify (removeOverlapping b)
  pure e'

------------------------------------------------------------------------------------------
-- Let TypeTreeessions
------------------------------------------------------------------------------------------

type Bindings = List (Tuple (Binding Meta) TypeTree)

evalLetTypeTree :: Bindings -> TypeTree -> Evaluator TypeTree
evalLetTypeTree Nil e = pure e
evalLetTypeTree (Cons (Tuple b e) rest) expr = case runMatcherM $ matchls' Map.empty (singleton b) (singleton e) of
  Left l  -> throwError $ BindingError $ MatchingError b e
  Right r -> do
    case rest of
      Nil -> replace' r expr
      _   -> do
        Tuple rest' r' <- runStateT (replaceBindings rest) r
        expr' <- replace' r' expr
        pure $ LetExpr AST.emptyMeta rest' expr'

replaceBindings :: Bindings -> StateT (StrMap TypeTree) Evaluator Bindings
replaceBindings = traverse $ \(Tuple bin expr) -> do
  expr' <- scope bin expr
  pure $ Tuple bin expr'

------------------------------------------------------------------------------------------

binary :: Env -> (Tuple Op Meta) -> TypeTree -> TypeTree -> Evaluator TypeTree
binary env (Tuple operator meta) = case operator of
  Power  -> aint Power (\i j -> product $ replicate j i)
  Mul    -> aint Mul (*)
  Add    -> aint Add (+)
  Sub    -> aint Sub (-)
  Colon  -> \e es -> case es of
    (List _ ls) -> pure $ List AST.emptyMeta $ e:ls
    _         -> throwError $ BinaryOpError Colon e es
  Append -> \es1 es2 -> case (Tuple es1 es2) of
    (Tuple (List _ ls1) (List _ ls2)) -> pure $ List AST.emptyMeta $ ls1 <> ls2
    _                                 -> throwError $ BinaryOpError Append es1 es2
  Equ    -> ord Equ (==) (==) (==)
  Neq    -> ord Neq (/=) (/=) (/=)
  Leq    -> ord Leq (<=) (<=) (<=)
  Lt     -> ord Lt  (<)  (<)  (<)
  Geq    -> ord Geq (>=) (>=) (>=)
  Gt     -> ord Gt  (>)  (>)  (>)
  And    -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom _ (Bool false)) _                  )   -> pure $ Atom AST.emptyMeta $ Bool false
    (Tuple _                     (Atom _ (Bool false))) -> pure $ Atom AST.emptyMeta $ Bool false
    (Tuple (Atom _ (Bool true))  (Atom _ (Bool true)))  -> pure $ Atom AST.emptyMeta $ Bool true
    (Tuple _                   _                     )  -> throwError $ BinaryOpError And e1 e2
  Or     -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom _ (Bool true))  _                   )  -> pure $ Atom AST.emptyMeta $ Bool true
    (Tuple _                     (Atom _ (Bool true)))  -> pure $ Atom AST.emptyMeta $ Bool true
    (Tuple (Atom _ (Bool false)) (Atom _ (Bool false))) -> pure $ Atom AST.emptyMeta $ Bool false
    (Tuple _                     _                   )  -> throwError $ BinaryOpError And e1 e2
  Dollar -> (\f e -> pure $ App AST.emptyMeta f (singleton e))
  Composition -> \e1 e2 -> throwError $ BinaryOpError And e1 e2
  InfixFunc name -> \e1 e2 -> apply env name (e1 : e2 : Nil)
  InfixConstr name -> \e1 e2 -> pure $ Binary AST.emptyMeta (Tuple operator meta) e1 e2
  where
    aint :: Op -> (Int -> Int -> Int) -> TypeTree -> TypeTree -> Evaluator TypeTree
    aint _   f (Atom _ (AInt i)) (Atom _ (AInt j)) = pure $ Atom AST.emptyMeta $ AInt $ f i j
    aint op  _ e1                e2                = throwError $ BinaryOpError op e1 e2

    ord :: Op -> (Int -> Int -> Boolean) -> (String -> String -> Boolean) -> (Boolean -> Boolean -> Boolean)-> TypeTree -> TypeTree -> Evaluator TypeTree
    ord _  fi _  _  (Atom _ (AInt i))  (Atom _ (AInt j))  = pure $ Atom AST.emptyMeta $ Bool $ fi i j
    ord _  _  fs _  (Atom _ (Char s1)) (Atom _ (Char s2)) = pure $ Atom AST.emptyMeta $ Bool $ fs s1 s2
    ord _  _  _  fb (Atom _ (Bool b1)) (Atom _ (Bool b2)) = pure $ Atom AST.emptyMeta $ Bool $ fb b1 b2
    ord op _  _  _  e1               e2               = throwError $ BinaryOpError op e1 e2


unary :: Env -> Tuple Op Meta -> TypeTree -> Evaluator TypeTree
unary env (Tuple Sub _) (Atom _ (AInt i)) = pure $ Atom AST.emptyMeta $ AInt (-i)
unary env (Tuple op _) e = throwError $ UnaryOpError op e

apply :: Env -> String -> (List TypeTree) -> Evaluator TypeTree
apply env "div" (Cons e1 (Cons e2 _)) = division e1 e2 
apply env "mod" (Cons e1 (Cons e2 _)) = modulo e1 e2
apply env name args = case Map.lookup name env of
  Nothing    -> throwError $ UnknownFunction name
  Just cases -> tryAll env cases args name Nil

-- built-in div
division :: TypeTree -> TypeTree -> Evaluator TypeTree 
division (Atom _ (AInt i)) (Atom _ (AInt 0)) = throwError DivByZero
division (Atom _ (AInt i)) (Atom _ (AInt j)) = pure $ Atom AST.emptyMeta $ AInt $ div i j
division e1 e2 = throwError $ BinaryOpError (InfixFunc "div") e1 e2

-- built-in mod
modulo :: TypeTree -> TypeTree -> Evaluator TypeTree  
modulo (Atom _ (AInt i)) (Atom _ (AInt 0)) = throwError DivByZero
modulo (Atom _ (AInt i)) (Atom _ (AInt j)) = pure $ Atom AST.emptyMeta $ AInt $ mod i j
modulo e1 e2 = throwError $ BinaryOpError (InfixFunc "mod") e1 e2


tryAll :: Env -> (List (Tuple (List (Binding Meta)) TypeTree)) -> (List TypeTree) -> String -> (List MatchingError) -> Evaluator TypeTree
tryAll _   Nil                        _    name errs = throwError $ NoMatchingFunction name errs
tryAll env (Cons (Tuple binds body) cases) args name errs | (length args) < (length binds) = tryAll env cases args name (errs <> (singleton $ TooFewArguments binds args))
tryAll env (Cons (Tuple binds body) cases) args name errs = case runMatcherM $ matchls' env binds args of
  Right replMap                 -> replace' replMap body >>= wrapLambda binds args
  Left se@(StrictnessError _ _) -> throwError $ NoMatchingFunction name (errs <> singleton se)
  Left err                      -> tryAll env cases args name (errs <> singleton err)

whnf :: TypeTree -> Boolean
whnf (Atom _ (Name _)) = false
whnf (Atom _ _)        = true
whnf (List _ _)        = true
whnf (NTuple _ _)      = true
whnf (Binary _ (Tuple (InfixConstr _) _) _ _) = true
whnf (App _ (Atom _ (Constr _)) _) = true
whnf _                 = false

checkStrictness :: Binding Meta -> TypeTree -> MatchingError
checkStrictness bs es | whnf es   = MatchingError bs es
                      | otherwise = StrictnessError bs es


matchls' :: Env -> (List (Binding Meta)) -> (List TypeTree) -> Matcher (StrMap TypeTree)
matchls' env bs es = execStateT (zipWithA m bs es) Map.empty
 where
   m :: Binding Meta -> TypeTree -> StateT (StrMap TypeTree) Matcher Unit
   m b t = do
     i <- get
     let bndAndIdx = runState (evalToBinding env t b) i
         i' = snd bndAndIdx
         t' = fst bndAndIdx
     put i'
     match' b t'


match' :: Binding Meta -> TypeTree -> StateT (StrMap TypeTree) Matcher Unit
match' (Lit _ (Name name)) e                   = modify (Map.insert name e)
match' (Lit meta ba)       (Atom meta' ea)     = case ba == ea of
                                                 true  -> pure unit
                                                 false -> throwError $ MatchingError (Lit meta ba) (Atom meta' ea)
match' (Lit meta b)        e                   = throwError $ checkStrictness (Lit meta b) e

match' (ConsLit _ b bs)    (Binary _ (Tuple Colon _) e es) = match' b e *> match' bs es
match' (ConsLit meta b bs) (List _ (Cons e es))  = do
  meta' <- lift freshMeta
  match' (ConsLit meta b bs) (AST.binary Colon e (List meta' es))
match' (ConsLit meta b bs)   (List meta' Nil)    = throwError $ MatchingError (ConsLit meta b bs) (List meta' Nil)
match' (ConsLit meta b bs)   e                   = throwError $ checkStrictness (ConsLit meta b bs) e

match' (ListLit meta (Cons b bs)) (Binary _ (Tuple Colon _) e es) = match' b e *> match' (ListLit meta bs) es
match' (ListLit meta bs)      (List meta' es)               = case length bs == length es of
                                                       true  -> void $ zipWithA match' bs es
                                                       false -> throwError $ MatchingError (ListLit meta bs) (List meta' es)
match' (ListLit meta bs)      e                         = throwError $ checkStrictness (ListLit meta bs) e

match' (NTupleLit meta bs)    (NTuple meta' es) = case length bs == length es of
                                           true  -> void $ zipWithA match' bs es
                                           false -> throwError $ MatchingError (NTupleLit meta bs) (NTuple meta' es)
match' (NTupleLit meta bs)    e             = throwError $ checkStrictness (NTupleLit meta bs) e
match' b@(ConstrLit _ (PrefixDataConstr n a ps)) e@(App _ (Atom _ (Constr n')) ps')
  = case  n == n' && length ps == length ps' of
         true -> void $ zipWithA match' ps ps'
         false -> throwError $ MatchingError b e

match' b@(ConstrLit _ (InfixDataConstr n _ _ l r)) e@(Binary _ (Tuple (InfixConstr n') _) l' r')
  = case n == n' of
         true -> match' l l' *> match' r r'
         false -> throwError $ MatchingError b e

match' b@(ConstrLit _ (InfixDataConstr n _ _ l r)) e@(App _ (PrefixOp _ (Tuple (InfixConstr n') _)) (Cons l' (Cons r' Nil)))
  = case n == n' of
         true -> match' l l' *> match' r r'
         false -> throwError $ MatchingError b e
match' b@(ConstrLit _ _) e = throwError $ checkStrictness b e


--TODO: replace with purescript mapM
mapM :: forall a b m. (Monad m) => (a -> m b) -> List a -> m (List b)
mapM f Nil = pure Nil
mapM f (Cons x xs) = do
  y  <- f x
  ys <- mapM f xs
  pure $ Cons y ys

-- removes every entry in StrMap that is inside the binding
removeOverlapping :: Binding Meta -> StrMap TypeTree -> StrMap TypeTree
removeOverlapping bind = removeOverlapping' (boundNames bind)
  where
    removeOverlapping' :: List String -> StrMap TypeTree -> StrMap TypeTree
    removeOverlapping' Nil         = id
    removeOverlapping' (Cons s ss) = removeOverlapping' ss <<< delete s

replace' :: StrMap TypeTree -> TypeTree -> Evaluator TypeTree
replace' subs = go
  where
  go tt = case tt of
    a@(Atom _ (Name name)) -> case Map.lookup name subs of
      Just subTypeTree -> pure subTypeTree
      Nothing      -> pure a
    (List _ exprs)         -> List AST.emptyMeta <$> (traverse go exprs)
    (NTuple _ exprs)       -> NTuple AST.emptyMeta <$> (traverse go exprs)
    (Binary _ op e1 e2)    -> Binary AST.emptyMeta <$> pure op <*> go e1 <*> go e2
    (Unary _ op e)         -> Unary AST.emptyMeta <$> pure op <*> go e
    (SectL _ e op)         -> SectL AST.emptyMeta <$> go e <*> pure op
    (SectR _ op e)         -> SectR AST.emptyMeta <$> pure op <*> go e
    (IfExpr _ ce te ee)    -> IfExpr AST.emptyMeta <$> go ce <*> go te <*> go ee
    (ArithmSeq _ ce te ee) -> ArithmSeq AST.emptyMeta <$> go ce <*> (mapM' go te) <*> (mapM' go ee)
    (Lambda _ binds body)  -> (avoidCapture subs binds)
      *> (Lambda AST.emptyMeta <$> pure binds <*> replace' (foldr Map.delete subs (boundNames' binds)) body)
    (App _ func exprs)     -> App AST.emptyMeta <$> go func <*> traverse go exprs
    (ListComp _ expr quals) -> do
      Tuple quals' subs' <- runStateT (replaceQualifiers quals) subs
      expr'              <- replace' subs' expr
      pure $ ListComp AST.emptyMeta expr' quals'
    (LetExpr _ binds expr)  -> do
      Tuple binds' subs' <- runStateT (replaceBindings binds) subs
      expr'              <- replace' subs' expr
      pure $ LetExpr AST.emptyMeta binds' expr'
    e                     -> pure e

avoidCapture :: StrMap TypeTree -> (List (Binding Meta)) -> Evaluator Unit
avoidCapture subs binds = case intersect (concatMap freeVariables $ Map.values subs) (boundNames' binds) of
  Nil      -> pure unit
  captures -> throwError $ NameCaptureError captures

freeVariables :: TypeTree -> (List String)
freeVariables _ = Nil
-- freeVariables = nub <<< foldTypeTree
--   (\a -> case a of
--     Name name -> singleton $ name
--     _         -> Nil)
--   concat
--   concat
--   (\_ f1 f2 -> f1 <> f2)
--   (\_ f -> f)
--   (\f _ -> f)
--   (\_ f -> f)
--   (\_ -> Nil)
--   (\f1 f2 f3 -> f1 <> f2 <> f3)
--   (\bs f -> nub f \\ boundNames' bs)
--   (\f fs -> f <> concat fs)

boundNames' :: (List (Binding Meta)) -> (List String)
boundNames' = concatMap boundNames

boundNames :: Binding Meta -> (List String)
boundNames = go
  where
  go (Lit _  (Name name)) = singleton name
  go (ConsLit _ b1 b2)   = go b1 <> go b2
  go (ListLit _ bs)      = foldMap go bs
  go (NTupleLit _ bs)    = foldMap go bs
  go _                 = Nil
