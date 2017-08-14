module Evaluator where

import Prelude hiding (apply)
import Data.List (List(Nil, Cons), null, singleton, concatMap, intersect, zipWith, zipWithA, length, (:), drop, concat)
import Data.List.Lazy (replicate)
import Data.StrMap (StrMap, delete)
import Data.StrMap as Map
import Data.Tuple (Tuple(Tuple))
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
import Control.Monad.State.Trans (StateT, get, modify, runStateT, execStateT)
import Control.Monad.Except.Trans (ExceptT, throwError, runExceptT)

import JSHelpers (unsafeUndef)

import AST (TypeTree, Tree(..), Atom(..), Binding(..), Definition(Def), Op(..), QualTree(..), TypeQual, MType)
import AST as AST

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
    MatchingError (Binding MType) TypeTree
  | StrictnessError (Binding MType) TypeTree
  | TooFewArguments (List (Binding MType)) (List TypeTree)

instance showMatchingError :: Show MatchingError where
  show (MatchingError b e)     = "MatchingError " <> show b <> " " <> show e
  show (StrictnessError b e)   = "StrictnessError " <> show b <> " " <> show e
  show (TooFewArguments bs es) = "TooFewArguments " <> show bs <> " " <> show es

type Evaluator = ExceptT EvalError Identity

runEvalM :: forall a. Evaluator a -> Either EvalError a
runEvalM = extract <<< runExceptT

type Matcher = ExceptT MatchingError Identity

runMatcherM :: forall a. Matcher a -> Either MatchingError a
runMatcherM = extract <<< runExceptT

type Env = StrMap (List (Tuple (List (Binding MType)) TypeTree))

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

eval1 :: Env -> TypeTree -> Evaluator TypeTree
eval1 env expr = case expr of
  (Binary _ op e1 e2)                  -> binary env op e1 e2
  (Unary _ op e)                       -> unary env op e
  (Atom _ (Name name))                 -> apply env name Nil
  (IfExpr _ (Atom _ (Bool true)) te _)   -> pure te
  (IfExpr _ (Atom _ (Bool false)) _ ee)  -> pure ee
  (ArithmSeq _ start step end)         -> evalArithmSeq start step end
  -- (List _ (Cons e es))                      -> pure $ Binary Nothing Colon e (List Nothing es)
  (App _ (Binary _ (Tuple Composition _) f g) (Cons e Nil)) -> pure $ App Nothing f (singleton $ App Nothing g (Cons e Nil))
  (App _ (Lambda _ binds body) args)     -> tryAll env (singleton $ Tuple binds body) args "lambda" Nil
  (App _ (SectL _ e1 op) (Cons e2 Nil))           -> {-binary env op e1 e2 <|>-} (pure $ Binary Nothing op e1 e2)
  (App _ (SectR _ op e2) (Cons e1 Nil))           -> {-binary env op e1 e2 <|>-} (pure $ Binary Nothing op e1 e2)
  (App _ (PrefixOp _ op) (Cons e1 (Cons e2 Nil)))         -> {-binary env op e1 e2 <|>-} (pure $ Binary Nothing op e1 e2)
  (App _ (Atom _ (Name name)) args)      -> apply env name args
  (App _ (App _ func es) es')            -> pure $ App Nothing func (es <> es')
  (ListComp _ e qs)                    -> evalListComp env e qs
  (LetExpr _ binds exp)                -> evalLetTypeTree binds exp
  _                                  -> throwError $ CannotEvaluate expr

eval :: Env -> TypeTree -> TypeTree
eval env expr = evalToBinding env expr (Lit Nothing (Name "_|_"))

evalToBinding :: Env -> TypeTree -> Binding MType -> TypeTree
evalToBinding env expr bind = case bind of
  (Lit _ (Name "_|_")) -> recurse env expr bind
  (Lit _ (Name _))     -> expr
  (Lit _ _)            -> case expr of
    (Atom _ _) -> expr
    _          -> recurse env expr bind

  (ConsLit _ b bs)     -> case expr of
    (Binary _ (Tuple Colon _) e es) -> Binary Nothing (Tuple Colon Nothing) (evalToBinding env e b) (evalToBinding env es bs)
    (List _ (Cons e es))  -> evalToBinding env (Binary Nothing (Tuple Colon Nothing) e (List Nothing es)) bind
    _                     -> recurse env expr bind

  (ListLit _ bs)       -> case expr of
    (List _ es) -> if (length es == length bs) then List Nothing (zipWith (evalToBinding env) es bs) else expr
    _           -> recurse env expr bind

  (NTupleLit _ bs)     -> case expr of
    (NTuple _ es)  -> NTuple Nothing (zipWith (evalToBinding env) es bs)
    _              -> recurse env expr bind
-- TODO
  (ConstrLit _ _) -> unsafeUndef "evalToBinding ... (ConstrLit _ _) -> "


recurse :: Env -> TypeTree -> Binding MType -> TypeTree
recurse env expr bind = if expr == eval1d then expr else evalToBinding env eval1d bind
  where
    eval1d :: TypeTree
    eval1d = either (const expr') id $ runEvalM $ eval1 env expr'
    expr' :: TypeTree
    expr' = case expr of
      (Binary _ op e1 e2)  ->
        Binary Nothing op (evalToBinding env e1 bind) (evalToBinding env e2 bind)
      (Unary _ op e)       ->
        Unary Nothing op (evalToBinding env e bind)
      (List _ es)          ->
        List Nothing ((\e -> evalToBinding env e bind) <$> es)
      (NTuple _ es)        ->
        NTuple Nothing ((\e -> evalToBinding env e bind) <$> es)
      (IfExpr _ c t e)     ->
        IfExpr Nothing (evalToBinding env c bind) t e
      (App _ f args)       -> do
        App Nothing (evalToBinding env f bind) args
      (ArithmSeq _ c t e)     ->
        ArithmSeq Nothing (evalToBinding env c bind) ((\x -> evalToBinding env x bind) <$> t) ((\x -> evalToBinding env x bind) <$> e)
      (ListComp _ e qs)    -> do
        ListComp Nothing (evalToBinding env e bind) ((\x -> evalToBindingQual env x bind) <$> qs)
      _                  ->
        expr

    evalToBindingQual :: Env -> TypeQual -> Binding MType ->TypeQual
    evalToBindingQual environment qual binding = case qual of
      Let _ b e -> Let Nothing b (evalToBinding environment e bind)
      Gen _ b e -> Gen Nothing b (evalToBinding environment e bind)
      Guard _ e -> Guard Nothing (evalToBinding environment e bind)


wrapLambda :: (List (Binding MType)) -> (List TypeTree) -> TypeTree -> Evaluator TypeTree
wrapLambda binds args body =
  case compare (length binds) (length args) of
    EQ -> pure body
    GT -> pure $ Lambda Nothing (drop (length args) binds) body
    LT -> pure $ App Nothing body (drop (length binds) args)

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
  Atom _ (AInt i) -> (\x -> (Atom Nothing <<< AInt) <$> x) <$> intQuat
  Atom _ (Bool b) -> (\x -> (Atom Nothing <<< Bool) <$> x) <$> (intToABool intQuat)
  Atom _ (Char c) -> (\x -> (Atom Nothing <<< Char <<< String.singleton) <$> x) <$> (intToAChar intQuat)
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
  false -> throwError $ CannotEvaluate $ ArithmSeq Nothing start step end
  true  -> evalArithmSeq'
  where
    isValid :: Maybe TypeTree -> Boolean
    isValid Nothing = true
    isValid (Just (Atom _ (Name _))) = false
    isValid (Just (Atom _ _)) = true
    isValid _ = false

    evalArithmSeq' :: Evaluator TypeTree
    evalArithmSeq' = case (exprFromStepTo start step end) of
      Quat Nothing _ _ _          -> pure $ List Nothing Nil
      Quat (Just a) Nothing _ _   -> pure $ AST.binary Colon a (List Nothing Nil)
      Quat (Just a) (Just na) b c -> pure $ AST.binary Colon a (ArithmSeq Nothing na b c)

------------------------------------------------------------------------------------------
-- List Comprehensions
------------------------------------------------------------------------------------------

evalListComp :: Env -> TypeTree -> List TypeQual -> Evaluator TypeTree
evalListComp _   expr Nil         = pure $ List Nothing $ singleton expr
evalListComp env expr (Cons q qs) = case q of
  Guard _ (Atom _ (Bool false)) -> pure $ List Nothing Nil
  Guard _ (Atom _ (Bool true))  -> if null qs then pure (List Nothing (singleton expr)) else pure (ListComp Nothing expr qs)
  Gen _ _ (List _ Nil)          -> pure $ List Nothing Nil
  -- Gen _ b (List (Cons e Nil)) -> evalListComp env expr (Cons (Let Nothing b e) qs)
  Gen _ b (List _ (Cons e es))  -> do
    listcomp1 <- evalListComp env expr (Cons (Let Nothing b e) qs)
    listcomp2 <- pure $ ListComp Nothing expr (Cons (Gen Nothing b (List Nothing es)) qs)
    case listcomp1 of
      List _ (Cons x Nil) -> pure $ Binary Nothing (Tuple Colon Nothing) x listcomp2
      _ -> pure $ AST.binary Append listcomp1 listcomp2
  -- Gen _ b (Binary Colon e (List Nil)) -> evalListComp env expr (Cons (Let Nothing b e) qs)
  Gen _ b (Binary Nothing (Tuple Colon _) e es)  -> do
    listcomp1 <- evalListComp env expr (Cons (Let Nothing b e) qs)
    listcomp2 <- pure $ ListComp Nothing expr (Cons (Gen Nothing b es) qs)
    case listcomp1 of
      List _ (Cons x Nil) -> pure $ AST.binary Colon x listcomp2
      _ -> pure $ AST.binary Append listcomp1 listcomp2
  Gen _ b e -> pure $ ListComp Nothing expr (Cons (Gen Nothing b (evalToBinding env e (ConsLit Nothing b (Lit Nothing (Name "_"))))) qs)
  Let _ b e -> case runMatcherM $ matchls' Map.empty (singleton b) (singleton e) of
    Right r -> do
      Tuple qs' r' <- runStateT (replaceQualifiers qs) r
      expr'        <- replace' r' expr
      case qs' of 
          Nil -> pure $ List Nothing $ singleton expr'
          _   -> pure $ ListComp Nothing expr' qs'
    Left l  -> throwError $ BindingError $ MatchingError b e
  _ -> throwError $ CannotEvaluate (ListComp Nothing expr (Cons q qs))

-- replaces expressions in List-Comprehension-Qualifiers and considers overlapping bindings
replaceQualifiers :: List TypeQual -> StateT (StrMap TypeTree) Evaluator (List TypeQual)
replaceQualifiers = traverse replaceQual
  where
    replaceQual :: TypeQual -> StateT (StrMap TypeTree) Evaluator TypeQual
    replaceQual qual = case qual of
      Gen _ b e -> scope b e >>= \e' -> pure $ Gen Nothing b e'
      Let _ b e -> scope b e >>= \e' -> pure $ Let Nothing b e'
      Guard _ e -> do
        sub <- get
        e'  <- lift $ replace' sub e
        pure $ Guard Nothing e'

scope :: Binding MType -> TypeTree -> StateT (StrMap TypeTree) Evaluator TypeTree
scope b e = do
  sub <- get
  e'  <- lift $ replace' sub e
  modify (removeOverlapping b)
  pure e'

------------------------------------------------------------------------------------------
-- Let TypeTreeessions
------------------------------------------------------------------------------------------

type Bindings = List (Tuple (Binding MType) TypeTree)

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
        pure $ LetExpr Nothing rest' expr'

replaceBindings :: Bindings -> StateT (StrMap TypeTree) Evaluator Bindings
replaceBindings = traverse $ \(Tuple bin expr) -> scope bin expr >>= \expr' -> pure $ Tuple bin expr'

------------------------------------------------------------------------------------------

binary :: Env -> (Tuple Op MType) -> TypeTree -> TypeTree -> Evaluator TypeTree
binary env (Tuple operator mtype) = case operator of
  Power  -> aint Power (\i j -> product $ replicate j i)
  Mul    -> aint Mul (*)
  Add    -> aint Add (+)
  Sub    -> aint Sub (-)
  Colon  -> \e es -> case es of
    (List _ ls) -> pure $ List Nothing $ e:ls
    _         -> throwError $ BinaryOpError Colon e es
  Append -> \es1 es2 -> case (Tuple es1 es2) of
    (Tuple (List _ ls1) (List _ ls2)) -> pure $ List Nothing $ ls1 <> ls2
    _                                 -> throwError $ BinaryOpError Append es1 es2
  Equ    -> ord Equ (==) (==) (==)
  Neq    -> ord Neq (/=) (/=) (/=)
  Leq    -> ord Leq (<=) (<=) (<=)
  Lt     -> ord Lt  (<)  (<)  (<)
  Geq    -> ord Geq (>=) (>=) (>=)
  Gt     -> ord Gt  (>)  (>)  (>)
  And    -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom _ (Bool false)) _                  )   -> pure $ Atom Nothing $ Bool false
    (Tuple _                     (Atom _ (Bool false))) -> pure $ Atom Nothing $ Bool false
    (Tuple (Atom _ (Bool true))  (Atom _ (Bool true)))  -> pure $ Atom Nothing $ Bool true
    (Tuple _                   _                     )  -> throwError $ BinaryOpError And e1 e2
  Or     -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom _ (Bool true))  _                   )  -> pure $ Atom Nothing $ Bool true
    (Tuple _                     (Atom _ (Bool true)))  -> pure $ Atom Nothing $ Bool true
    (Tuple (Atom _ (Bool false)) (Atom _ (Bool false))) -> pure $ Atom Nothing $ Bool false
    (Tuple _                     _                   )  -> throwError $ BinaryOpError And e1 e2
  Dollar -> (\f e -> pure $ App Nothing f (singleton e))
  Composition -> \e1 e2 -> throwError $ BinaryOpError And e1 e2
  InfixFunc name -> \e1 e2 -> apply env name (e1 : e2 : Nil)
  where
    aint :: Op -> (Int -> Int -> Int) -> TypeTree -> TypeTree -> Evaluator TypeTree
    aint _   f (Atom _ (AInt i)) (Atom _ (AInt j)) = pure $ Atom Nothing $ AInt $ f i j
    aint op  _ e1                e2                = throwError $ BinaryOpError op e1 e2

    ord :: Op -> (Int -> Int -> Boolean) -> (String -> String -> Boolean) -> (Boolean -> Boolean -> Boolean)-> TypeTree -> TypeTree -> Evaluator TypeTree
    ord _  fi _  _  (Atom _ (AInt i))  (Atom _ (AInt j))  = pure $ Atom Nothing $ Bool $ fi i j
    ord _  _  fs _  (Atom _ (Char s1)) (Atom _ (Char s2)) = pure $ Atom Nothing $ Bool $ fs s1 s2
    ord _  _  _  fb (Atom _ (Bool b1)) (Atom _ (Bool b2)) = pure $ Atom Nothing $ Bool $ fb b1 b2
    ord op _  _  _  e1               e2               = throwError $ BinaryOpError op e1 e2


unary :: Env -> Tuple Op MType -> TypeTree -> Evaluator TypeTree
unary env (Tuple Sub _) (Atom _ (AInt i)) = pure $ Atom Nothing $ AInt (-i)
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
division (Atom _ (AInt i)) (Atom _ (AInt j)) = pure $ Atom Nothing $ AInt $ div i j
division e1 e2 = throwError $ BinaryOpError (InfixFunc "div") e1 e2

-- built-in mod
modulo :: TypeTree -> TypeTree -> Evaluator TypeTree  
modulo (Atom _ (AInt i)) (Atom _ (AInt 0)) = throwError DivByZero
modulo (Atom _ (AInt i)) (Atom _ (AInt j)) = pure $ Atom Nothing $ AInt $ mod i j
modulo e1 e2 = throwError $ BinaryOpError (InfixFunc "mod") e1 e2


tryAll :: Env -> (List (Tuple (List (Binding MType)) TypeTree)) -> (List TypeTree) -> String -> (List MatchingError) -> Evaluator TypeTree
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
whnf _                 = false

checkStrictness :: Binding MType -> TypeTree -> MatchingError
checkStrictness bs es | whnf es   = MatchingError bs es
                      | otherwise = StrictnessError bs es


matchls' :: Env -> (List (Binding MType)) -> (List TypeTree) -> Matcher (StrMap TypeTree)
matchls' env bs es = execStateT (zipWithA (\b e -> match' b (evalToBinding env e b)) bs es) Map.empty

match' :: Binding MType -> TypeTree -> StateT (StrMap TypeTree) Matcher Unit
match' (Lit _ (Name name)) e                   = modify (Map.insert name e)
match' (Lit _ ba)          (Atom _ ea)         = case ba == ea of
                                                 true  -> pure unit
                                                 false -> throwError $ MatchingError (Lit Nothing ba) (Atom Nothing ea)
match' (Lit _ b)           e                   = throwError $ checkStrictness (Lit Nothing b) e

match' (ConsLit _ b bs)    (Binary _ (Tuple Colon _) e es) = match' b e *> match' bs es
match' (ConsLit _ b bs)    (List _ (Cons e es))  = match' (ConsLit Nothing b bs) (AST.binary Colon e (List Nothing es))
match' (ConsLit _ b bs)    (List _ Nil)          = throwError $ MatchingError (ConsLit Nothing b bs) (List Nothing Nil)
match' (ConsLit _ b bs)    e                     = throwError $ checkStrictness (ConsLit Nothing b bs) e

match' (ListLit _ (Cons b bs)) (Binary _ (Tuple Colon _) e es) = match' b e *> match' (ListLit Nothing bs) es
match' (ListLit _ bs)      (List _ es)               = case length bs == length es of
                                                       true  -> void $ zipWithA match' bs es
                                                       false -> throwError $ MatchingError (ListLit Nothing bs) (List Nothing es)
match' (ListLit _ bs)      e                         = throwError $ checkStrictness (ListLit Nothing bs) e

match' (NTupleLit _ bs)    (NTuple _ es) = case length bs == length es of
                                           true  -> void $ zipWithA match' bs es
                                           false -> throwError $ MatchingError (NTupleLit Nothing bs) (NTuple Nothing es)
match' (NTupleLit _ bs)    e             = throwError $ checkStrictness (NTupleLit Nothing bs) e
-- TODO
match' (ConstrLit _ _) _ = unsafeUndef "match' (ConstrLit _ _)"

--TODO: replace with purescript mapM
mapM' :: forall a b m. (Monad m) => (a -> m b) -> Maybe a -> m (Maybe b)
mapM' f Nothing  = pure Nothing
mapM' f (Just x) = Just <$> (f x)

mapM :: forall a b m. (Monad m) => (a -> m b) -> List a -> m (List b)
mapM f Nil = pure Nil
mapM f (Cons x xs) = do
  y  <- f x
  ys <- mapM f xs
  pure $ Cons y ys

-- removes every entry in StrMap that is inside the binding
removeOverlapping :: Binding MType -> StrMap TypeTree -> StrMap TypeTree
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
    (List _ exprs)         -> List Nothing <$> (traverse go exprs)
    (NTuple _ exprs)       -> NTuple Nothing <$> (traverse go exprs)
    (Binary _ op e1 e2)    -> Binary Nothing <$> pure op <*> go e1 <*> go e2
    (Unary _ op e)         -> Unary Nothing <$> pure op <*> go e
    (SectL _ e op)         -> SectL Nothing <$> go e <*> pure op
    (SectR _ op e)         -> SectR Nothing <$> pure op <*> go e
    (IfExpr _ ce te ee)    -> IfExpr Nothing <$> go ce <*> go te <*> go ee
    (ArithmSeq _ ce te ee) -> ArithmSeq Nothing <$> go ce <*> (mapM' go te) <*> (mapM' go ee)
    (Lambda _ binds body)  -> (avoidCapture subs binds) *> (Lambda Nothing <$> pure binds <*> replace' (foldr Map.delete subs (boundNames' binds)) body)
    (App _ func exprs)     -> App Nothing <$> go func <*> traverse go exprs
    (ListComp _ expr quals) -> do
      Tuple quals' subs' <- runStateT (replaceQualifiers quals) subs
      expr'              <- replace' subs' expr
      pure $ ListComp Nothing expr' quals'
    (LetExpr _ binds expr)  -> do
      Tuple binds' subs' <- runStateT (replaceBindings binds) subs
      expr'              <- replace' subs' expr
      pure $ LetExpr Nothing binds' expr'
    e                     -> pure e

avoidCapture :: StrMap TypeTree -> (List (Binding MType)) -> Evaluator Unit
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

boundNames' :: (List (Binding MType)) -> (List String)
boundNames' = concatMap boundNames

boundNames :: Binding MType -> (List String)
boundNames = go
  where
  go (Lit _  (Name name)) = singleton name
  go (ConsLit _ b1 b2)   = go b1 <> go b2
  go (ListLit _ bs)      = foldMap go bs
  go (NTupleLit _ bs)    = foldMap go bs
  go _                 = Nil
