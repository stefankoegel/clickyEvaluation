module Evaluator where

import Prelude (class Show, top, class Semigroup, class Functor, class Monad, Unit, Ordering(..), (++), ($), (||), (&&), unit, return, (<*>), (<$>), pure, void, (==), otherwise, (>>=), (<), negate, (>), (>=), (<=), (/=), (-), (+), mod, div, (*), (<<<), compare, id, const, bind, show, map)
import Data.List (List(Nil, Cons), singleton, concatMap, intersect, zipWith, zipWithA, length, (:), replicate, drop, updateAt, (!!),concat)
import Data.StrMap (StrMap)
import Data.StrMap as Map
import Data.Tuple (Tuple(Tuple))
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Foldable (foldl, foldr, foldMap, product)
import Data.Traversable (traverse)
import Data.Identity (Identity, runIdentity)
import Data.Either (Either(..), either)
import Data.Monoid (class Monoid)
import Data.String (fromChar, toChar)
import Data.Enum (fromEnum, toEnum)
import Control.Bind (join)
import Control.Apply ((*>))
import Control.Alt ((<|>))
import Control.Monad.State.Trans (StateT, modify, execStateT)
import Control.Monad.Except.Trans (ExceptT, throwError, runExceptT)

import AST (Atom(..), Binding(..), Definition(Def), Expr(..), Qual(..), ExprQual, Op(..),Path(..))

data EvalError =
    PathError Path Expr
  | IndexError Int Int
  | DivByZero
  | EvalError Expr
  | BinaryOpError Op Expr Expr
  | UnaryOpError Op Expr
  | NameCaptureError (List String)
  | UnknownFunction String
  | NoMatchingFunction String (List MatchingError)
  | CannotEvaluate Expr
  | NoError
  | MoreErrors EvalError EvalError

instance semigroupEvalError :: Semigroup EvalError where
  append e1 e2 = MoreErrors e1 e2

instance monoidEvalError :: Monoid EvalError where
  mempty = NoError

instance showEvalError :: Show EvalError where
  show (PathError p e)            = "PathError " ++ show p ++ " " ++ show e
  show (IndexError i l)           = "IndexError " ++ show i ++ " " ++ show l
  show DivByZero                  = "DivByZero"
  show (EvalError e)              = "EvalError " ++ show e
  show (BinaryOpError o e1 e2)    = "BinaryOpError " ++ show o ++ " (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (UnaryOpError o e)         = "UnaryOpError " ++ show o ++ " " ++ show e
  show (NameCaptureError ns)      = "NameCaptureError " ++ show ns
  show (UnknownFunction n)        = "UnknownFunction " ++ show n
  show (NoMatchingFunction n mes) = "NoMatchingFunction " ++ show n ++ " " ++ show mes
  show (CannotEvaluate e)         = "CannotEvaluate " ++ show e
  show NoError                    = "NoError"
  show (MoreErrors e1 e2)         = "(MoreErrors " ++ show e1 ++ " " ++ show e2 ++ ")"

data MatchingError =
    MatchingError Binding Expr
  | StrictnessError Binding Expr
  | TooFewArguments (List Binding) (List Expr)

instance showMatchingError :: Show MatchingError where
  show (MatchingError b e)     = "MatchingError " ++ show b ++ " " ++ show e
  show (StrictnessError b e)   = "StrictnessError " ++ show b ++ " " ++ show e
  show (TooFewArguments bs es) = "TooFewArguments " ++ show bs ++ " " ++ show es

type Evaluator = ExceptT EvalError Identity

runEvalM :: forall a. Evaluator a -> Either EvalError a
runEvalM = runIdentity <<< runExceptT

type Matcher = ExceptT MatchingError Identity

runMatcherM :: forall a. Matcher a -> Either MatchingError a
runMatcherM = runIdentity <<< runExceptT

mapWithPath :: Path -> (Expr -> Evaluator Expr) -> Expr -> Evaluator Expr
mapWithPath p f = go p
  where
  go End e     = f e
  go (Fst p) e = case e of
    Binary op e1 e2 -> Binary op <$> go p e1 <*> pure e2
    Unary op e      -> Unary op  <$> go p e
    SectL e op      -> SectL     <$> go p e <*> pure op
    IfExpr ce te ee -> IfExpr    <$> go p ce <*> pure te <*> pure ee
    ArithmSeq s b e -> ArithmSeq <$> go p s <*> pure b <*> pure e
    Lambda bs body  -> Lambda bs <$> go p body
    App e es        -> App       <$> go p e <*> pure es
    ListComp e qs   -> ListComp  <$> go p e <*> pure qs
    _               -> throwError $ PathError (Fst p) e
  go (Snd p) e = case e of
    Binary op e1 e2 -> Binary op e1 <$> go p e2
    SectR op e      -> SectR op     <$> go p e
    IfExpr ce te ee -> IfExpr <$> pure ce <*> go p te <*> pure ee
    ArithmSeq s b e -> ArithmSeq <$> pure s <*> (mapM' (go p) b) <*> pure e
    _               -> throwError $ PathError (Snd p) e
  go (Thrd p) e = case e of
    IfExpr ce te ee -> IfExpr <$> pure ce <*> pure te <*> go p ee
    ArithmSeq s b (Just e) -> ArithmSeq <$> pure s <*> pure b <*> (Just <$> (go p e))
    _               -> throwError $ PathError (Thrd p) e
  go (Nth n p) e = case e of
    List es  -> List  <$> mapIndex n (go p) es
    NTuple es -> NTuple <$> mapIndex n (go p) es
    App e es -> App e <$> mapIndex n (go p) es
    ListComp e qs -> ListComp e <$> mapIndexQual n (go p) qs
    _        -> throwError $ PathError (Nth n p) e

  evalQual :: (Expr -> Evaluator Expr) -> Qual Binding Expr -> Evaluator (Qual Binding Expr)
  evalQual f q = case q of
    Gen bin expr -> Gen bin <$> f expr 
    Let bin expr -> Let bin <$> f expr
    Guard expr   -> Guard <$> f expr

  mapIndexQual :: Int -> (Expr -> Evaluator Expr) -> (List (Qual Binding Expr)) -> Evaluator (List (Qual Binding Expr))
  mapIndexQual i f qs = do
    case qs !! i of
      Nothing -> throwError $ IndexError i (length qs)
      Just q  -> do
        q' <- evalQual f q
        case updateAt i q' qs of
          Nothing  -> throwError $ IndexError i (length qs)
          Just qs' -> return qs'    

mapIndex :: forall a. Int -> (a -> Evaluator a) -> (List a) -> Evaluator (List a)
mapIndex i f as = do
  case as !! i of
    Nothing -> throwError $ IndexError i (length as)
    Just a  -> do
      a' <- f a
      case updateAt i a' as of
        Nothing  -> throwError $ IndexError i (length as)
        Just as' -> return as'

evalPath1 :: Env -> Path -> Expr -> Either EvalError Expr
evalPath1 env path expr = runEvalM $ mapWithPath path (eval1 env) expr

evalPathAll :: Env -> Path -> Expr -> Either EvalError Expr
evalPathAll env path expr = runEvalM $ mapWithPath path (return <<< eval env) expr

type Env = StrMap (List (Tuple (List Binding) Expr))

defsToEnv :: (List Definition) -> Env
defsToEnv = foldl insertDef Map.empty

envToDefs :: Env -> (List Definition)
envToDefs env = concat $ map tupleToDef $ Data.StrMap.toList env
  where
    tupleToDef (Tuple name defs) = map
                                    (\(Tuple bin expr) -> Def name bin expr)
                                    defs

insertDef :: Env -> Definition -> Env
insertDef env (Def name bindings body) = case Map.lookup name env of
  Nothing   -> Map.insert name (singleton $ Tuple bindings body) env
  Just defs -> Map.insert name (defs ++ (singleton $ Tuple bindings body)) env

eval1 :: Env -> Expr -> Evaluator Expr
eval1 env expr = case expr of
  (Binary op e1 e2)                  -> binary env op e1 e2
  (Unary op e)                       -> unary env op e
  (Atom (Name name))                 -> apply env name Nil
  (IfExpr (Atom (Bool true)) te _)   -> return te
  (IfExpr (Atom (Bool false)) _ ee)  -> return ee
  (ArithmSeq start step end)         -> evalArithmSeq start step end  
--  (List (e:es))                      -> return $ Binary Cons e (List es)
  (App (Binary Composition f g) (Cons e Nil)) -> return $ App f (singleton $ App g (Cons e Nil))
  (App (Lambda binds body) args)     -> tryAll env (singleton $ Tuple binds body) args "lambda" Nil
  (App (SectL e1 op) (Cons e2 Nil))           -> binary env op e1 e2 <|> (return $ Binary op e1 e2)
  (App (SectR op e2) (Cons e1 Nil))           -> binary env op e1 e2 <|> (return $ Binary op e1 e2)
  (App (PrefixOp op) (Cons e1 (Cons e2 Nil)))         -> binary env op e1 e2 <|> (return $ Binary op e1 e2)
  (App (Atom (Name name)) args)      -> apply env name args
  (App (App func es) es')            -> return $ App func (es ++ es')
  (ListComp e qs)                    -> evalListComp env e qs
  _                                  -> throwError $ CannotEvaluate expr

eval :: Env -> Expr -> Expr
eval env expr = evalToBinding env expr (Lit (Name "_|_"))

evalToBinding :: Env -> Expr -> Binding -> Expr
evalToBinding env expr bind = case bind of
  (Lit (Name "_|_")) -> recurse env expr bind
  (Lit (Name _))     -> expr
  (Lit _)            -> case expr of
    (Atom _) -> expr
    _        -> recurse env expr bind

  (ConsLit b bs)     -> case expr of
    (Binary Colon e es) -> Binary Colon (evalToBinding env e b) (evalToBinding env es bs)
    (List (Cons e es))  -> evalToBinding env (Binary Colon e (List es)) bind
    _                   -> recurse env expr bind

  (ListLit bs)       -> case expr of
    (List es) -> if (length es == length bs) then List (zipWith (evalToBinding env) es bs) else expr
    _         -> recurse env expr bind

  (NTupleLit bs)     -> case expr of
    (NTuple es)  -> NTuple (zipWith (evalToBinding env) es bs)
    _            -> recurse env expr bind


recurse :: Env -> Expr -> Binding -> Expr
recurse env expr bind = if expr == eval1d then expr else evalToBinding env eval1d bind
  where
    eval1d :: Expr
    eval1d = either (const expr') id $ runEvalM $ eval1 env expr'
    expr' :: Expr
    expr' = case expr of
      (Binary op e1 e2)  ->
        Binary op (evalToBinding env e1 bind) (evalToBinding env e2 bind)
      (Unary op e)       ->
        Unary op (evalToBinding env e bind)
      (List es)          ->
        List ((\e -> evalToBinding env e bind) <$> es)
      (NTuple es)        ->
        NTuple ((\e -> evalToBinding env e bind) <$> es)
      (IfExpr c t e)     ->
        IfExpr (evalToBinding env c bind) t e
      (ArithmSeq c t e)     ->
        ArithmSeq (evalToBinding env c bind) ((\x -> evalToBinding env x bind) <$> t) ((\x -> evalToBinding env x bind) <$> e)
      (App f args)       -> do
        App (evalToBinding env f bind) args
      --TODO: check
      --(ListComp e qs)    -> do
      --  ListComp (evalToBinding env e bind) ((\x -> evalToBindingQual env x bind) <$> qs)
      _                  ->
        expr

    --TODO: make correct
    evalToBindingQual :: Env -> Qual Binding Expr -> Binding -> Qual Binding Expr
    evalToBindingQual env qual binding = case qual of
      Let bin expr -> Let bin (evalToBinding env expr bind)      
      Gen bin expr -> Gen bin (evalToBinding env expr bind)
      Guard expr   -> Guard (evalToBinding env expr bind)

wrapLambda :: (List Binding) -> (List Expr) -> Expr -> Evaluator Expr
wrapLambda binds args body =
  case compare (length binds) (length args) of
    EQ -> return body
    GT -> return $ Lambda (drop (length args) binds) body
    LT -> return $ App body (drop (length binds) args)

------------------------------------------------------------------------------------------
-- Arithmetic Sequences
------------------------------------------------------------------------------------------

{-
packs the evaluation result for arithmetic sequences (AS)
example: 
Trip (Just x) (Just y) (Just z) will be displayed as x : [y, z ..] 
if no end of (AS) was given or x : [y, z .. end] if end was given
-}
data Trip a = Trip a a a

instance functorTrip :: Functor Trip where
  map f (Trip x y z) = Trip (f x) (f y) (f z)

intFromStepTo :: Int -> Maybe Int -> Maybe Int -> Trip (Maybe Int)
intFromStepTo start Nothing Nothing     = Trip (Just start) (Just (start + 1)) Nothing
intFromStepTo start (Just step) Nothing = Trip (Just start) (Just step) (Just (step + step - start))
intFromStepTo start Nothing (Just end)  = case start > end of
  true  -> Trip Nothing Nothing Nothing 
  false -> case start == end of
    true  -> Trip (Just end) Nothing Nothing
    false -> Trip (Just start) (Just (start + 1)) Nothing
intFromStepTo start (Just step) (Just end) = case (start <= step && start > end) || (start > step && start < end) of
  true  -> Trip Nothing Nothing Nothing
  false -> case start == end of
    true  -> Trip (Just end) Nothing Nothing
    false -> Trip (Just (start)) (Just (step)) (Just (step + step - start))

--detect whether top or bottom for Boolean was reached
intToBool :: Trip (Maybe Int) -> Trip (Maybe Boolean) 
intToBool trip = case temp of
  Trip (Just x) (Just y) z -> if x == y then Trip (Just x) Nothing Nothing else temp
  _ -> temp
  where 
    temp :: Trip (Maybe Boolean)
    temp = (\x -> intToBool' <$> x) <$> trip

    intToBool' :: Int -> Boolean
    intToBool' i = if i <= 0 then false else true

exprFromStepTo :: Expr -> Maybe Expr -> Maybe Expr -> Trip (Maybe Expr)
exprFromStepTo start step end = case start of 
  Atom (AInt i) -> (\x -> (Atom <<< AInt) <$> x) <$> intTrip
  Atom (Bool b) -> (\x -> (Atom <<< Bool) <$> x) <$> (intToBool intTrip)
  Atom (Char c) -> (\x -> (Atom <<< Char <<< fromChar) <$> x) <$> (\x -> join (toEnum <$> x)) <$> intTrip
  _             -> Trip Nothing Nothing Nothing
    where 
      intTrip = intFromStepTo (unsafeExprToInt start) (unsafeExprToInt <$> step) (unsafeExprToInt <$> end)

unsafeExprToInt :: Expr -> Int
unsafeExprToInt (Atom (AInt i))   = i
unsafeExprToInt (Atom (Bool b))   = fromEnum b
unsafeExprToInt (Atom (Char str)) = fromEnum $ fromMaybe 'E' (toChar str)
unsafeExprToInt _ = top

evalArithmSeq :: Expr -> Maybe Expr -> Maybe Expr -> Evaluator Expr
evalArithmSeq start step end = case foldr (&&) true (isValid <$> [Just start, step, end]) of
  false -> throwError $ CannotEvaluate $ ArithmSeq start step end
  true  -> evalArithmSeq'
  where
    isValid :: Maybe Expr -> Boolean
    isValid Nothing = true
    isValid (Just (Atom (Name _))) = false
    isValid (Just (Atom _)) = true
    isValid _ = false

    evalArithmSeq' :: Evaluator Expr
    evalArithmSeq' = case (exprFromStepTo start step end) of
      Trip (Just a) (Just b) nextStep -> return $ Binary Colon a (ArithmSeq b nextStep end)
      Trip (Just a) Nothing _         -> return $ List (singleton a)
      Trip Nothing _ _                -> return $ List Nil

------------------------------------------------------------------------------------------
-- List Comprehensions
------------------------------------------------------------------------------------------

--TODO: let
evalListComp :: Env -> Expr -> List ExprQual -> Evaluator Expr
evalListComp _ expr Nil           = return $ List $ singleton expr
evalListComp env expr (Cons q qs) = case q of
  Guard (Atom (Bool false)) -> return $ List Nil
  Guard (Atom (Bool true))  -> return $ ListComp expr qs
  Gen _ (List Nil)          -> return $ List Nil
  Gen b (List (Cons e Nil)) -> return $ ListComp expr (Cons (Let b e) qs)
  Gen b (List (Cons e es))  -> do
    listcomp1 <- return $ ListComp expr (Cons (Let b e) qs)
    listcomp2 <- return $ ListComp expr (Cons (Gen b (List es)) qs)
    return $ Binary Append listcomp1 listcomp2
  --TODO: fix overlapping bindings
  Let b e -> case runMatcherM $ matchls' env (singleton b) (singleton e) of 
    Right r -> do
      qs' <- traverse (replaceInQual r) qs
      expr' <- replace' r expr
      case qs' of 
        Nil -> return $ List $ singleton expr'
        _   -> return $ ListComp expr' qs'
    Left  l -> throwError $ UnknownFunction "something went wrong in binding of let guard"
  _ -> throwError $ CannotEvaluate (ListComp expr (Cons q qs))
  where
    replaceInQual :: StrMap Expr -> ExprQual -> Evaluator ExprQual
    replaceInQual str qual = case qual of
      Gen b e -> replace' str e >>= \x -> return $ Gen b x
      Let b e -> replace' str e >>= \x -> return $ Let b x
      Guard e -> replace' str e >>= \x -> return $ Guard x

------------------------------------------------------------------------------------------

binary :: Env -> Op -> Expr -> Expr -> Evaluator Expr
binary env op = case op of
  Power  -> aint Power (\i j -> product $ replicate j i)
  Mul    -> aint Mul (*)
  Add    -> aint Add (+)
  Sub    -> aint Sub (-)
  Colon  -> \e es -> case es of
    (List ls) -> return $ List $ e:ls
    _         -> throwError $ BinaryOpError Colon e es
  Append -> \es1 es2 -> case (Tuple es1 es2) of
    (Tuple (List ls1) (List ls2)) -> return $ List $ ls1 ++ ls2
    _                             -> throwError $ BinaryOpError Append es1 es2
  Equ    -> ord Equ (==) (==) (==)
  Neq    -> ord Neq (/=) (/=) (/=)
  Leq    -> ord Leq (<=) (<=) (<=)
  Lt     -> ord Lt  (<)  (<)  (<)
  Geq    -> ord Geq (>=) (>=) (>=)
  Gt     -> ord Gt  (>)  (>)  (>)
  And    -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom (Bool false)) _                  ) -> return $ Atom $ Bool false
    (Tuple _                   (Atom (Bool false))) -> return $ Atom $ Bool false
    (Tuple (Atom (Bool true))  (Atom (Bool true)) ) -> return $ Atom $ Bool true
    (Tuple _                   _                  ) -> throwError $ BinaryOpError And e1 e2
  Or     -> \e1 e2 -> case (Tuple e1 e2) of
    (Tuple (Atom (Bool true))  _                   ) -> return $ Atom $ Bool true
    (Tuple _                   (Atom (Bool true))  ) -> return $ Atom $ Bool true
    (Tuple (Atom (Bool false))  (Atom (Bool false))) -> return $ Atom $ Bool false
    (Tuple _                   _                   ) -> throwError $ BinaryOpError And e1 e2
  Dollar -> (\f e -> return $ App f (singleton e))
  Composition -> \e1 e2 -> throwError $ BinaryOpError And e1 e2
  InfixFunc name -> \e1 e2 -> apply env name (e1 : e2 : Nil)
  where
    aint :: Op -> (Int -> Int -> Int) -> Expr -> Expr -> Evaluator Expr
    aint _   f (Atom (AInt i)) (Atom (AInt j)) = return $ Atom $ AInt $ f i j
    aint op  _ e1              e2              = throwError $ BinaryOpError op e1 e2

    ord :: Op -> (Int -> Int -> Boolean) -> (String -> String -> Boolean) -> (Boolean -> Boolean -> Boolean)-> Expr -> Expr -> Evaluator Expr
    ord _  fi _  _  (Atom (AInt i))  (Atom (AInt j))  = return $ Atom $ Bool $ fi i j
    ord _  _  fs _  (Atom (Char s1)) (Atom (Char s2)) = return $ Atom $ Bool $ fs s1 s2
    ord _  _  _  fb (Atom (Bool b1)) (Atom (Bool b2)) = return $ Atom $ Bool $ fb b1 b2
    ord op _  _  _  e1               e2               = throwError $ BinaryOpError op e1 e2


unary :: Env -> Op -> Expr -> Evaluator Expr
unary env Sub (Atom (AInt i)) = return $ Atom $ AInt (-i)
unary env op e = throwError $ UnaryOpError op e

apply :: Env -> String -> (List Expr) -> Evaluator Expr
apply env "div" (Cons e1 (Cons e2 _)) = division e1 e2 
apply env "mod" (Cons e1 (Cons e2 _)) = modulo e1 e2
apply env name args = case Map.lookup name env of
  Nothing    -> throwError $ UnknownFunction name
  Just cases -> tryAll env cases args name Nil

-- built-in div
division :: Expr -> Expr -> Evaluator Expr 
division (Atom (AInt i)) (Atom (AInt 0)) = throwError DivByZero
division (Atom (AInt i)) (Atom (AInt j)) = return $ Atom $ AInt $ div i j
division e1 e2 = throwError $ BinaryOpError (InfixFunc "div") e1 e2

-- built-in mod
modulo :: Expr -> Expr -> Evaluator Expr  
modulo (Atom (AInt i)) (Atom (AInt 0)) = throwError DivByZero
modulo (Atom (AInt i)) (Atom (AInt j)) = return $ Atom $ AInt $ mod i j
modulo e1 e2 = throwError $ BinaryOpError (InfixFunc "mod") e1 e2


tryAll :: Env -> (List (Tuple (List Binding) Expr)) -> (List Expr) -> String -> (List MatchingError) -> Evaluator Expr
tryAll _   Nil                        _    name errs = throwError $ NoMatchingFunction name errs
tryAll env (Cons (Tuple binds body) cases) args name errs | (length args) < (length binds) = tryAll env cases args name (errs ++ (singleton $ TooFewArguments binds args))
tryAll env (Cons (Tuple binds body) cases) args name errs = case runMatcherM $ matchls' env binds args of
  Right replMap                 -> replace' replMap body >>= wrapLambda binds args
  Left se@(StrictnessError _ _) -> throwError $ NoMatchingFunction name (errs ++ singleton se)
  Left err                      -> tryAll env cases args name (errs ++ singleton err)

whnf :: Expr -> Boolean
whnf (Atom (Name _)) = false
whnf (Atom _)        = true
whnf (List _)        = true
whnf (NTuple _)      = true
whnf _               = false

checkStrictness :: Binding -> Expr -> MatchingError
checkStrictness bs es | whnf es   = MatchingError bs es
                      | otherwise = StrictnessError bs es


matchls' :: Env -> (List Binding) -> (List Expr) -> Matcher (StrMap Expr)
matchls' env bs es = execStateT (zipWithA (\b e -> match' b (evalToBinding env e b)) bs es) Map.empty

match' :: Binding -> Expr -> StateT (StrMap Expr) Matcher Unit
match' (Lit (Name name)) e                   = modify (Map.insert name e)
match' (Lit ba)          (Atom ea)           = case ba == ea of
                                                 true  -> return unit
                                                 false -> throwError $ MatchingError (Lit ba) (Atom ea)
match' (Lit b)           e                   = throwError $ checkStrictness (Lit b) e

match' (ConsLit b bs)    (Binary Colon e es)  = match' b e *> match' bs es
match' (ConsLit b bs)    (List (Cons e es))  = match' (ConsLit b bs) (Binary Colon e (List es))
match' (ConsLit b bs)    (List Nil)           = throwError $ MatchingError (ConsLit b bs) (List Nil)
match' (ConsLit b bs)    e                   = throwError $ checkStrictness (ConsLit b bs) e

match' (ListLit (Cons b bs))  (Binary Colon e es)  = match' b e *> match' (ListLit bs) es
match' (ListLit bs)      (List es)           = case length bs == length es of
                                                 true  -> void $ zipWithA match' bs es
                                                 false -> throwError $ MatchingError (ListLit bs) (List es)
match' (ListLit bs)      e                   = throwError $ checkStrictness (ListLit bs) e

match' (NTupleLit bs)    (NTuple es)         = case length bs == length es of
                                                 true  -> void $ zipWithA match' bs es
                                                 false -> throwError $ MatchingError (NTupleLit bs) (NTuple es)
match' (NTupleLit bs)    e                   = throwError $ checkStrictness (NTupleLit bs) e


mapM' :: forall a b m. (Monad m) => (a -> m b) -> Maybe a -> m (Maybe b)
mapM' f Nothing  = pure Nothing
mapM' f (Just x) = Just <$> (f x)

replace' :: StrMap Expr -> Expr -> Evaluator Expr
replace' subs = go
  where
  go expr = case expr of
    a@(Atom (Name name)) -> case Map.lookup name subs of
      Just subExpr -> return subExpr
      Nothing      -> return a
    (List exprs)         -> List <$> (traverse go exprs)
    (NTuple exprs)       -> NTuple <$> (traverse go exprs)
    (Binary op e1 e2)    -> Binary <$> pure op <*> go e1 <*> go e2
    (Unary op e)         -> Unary <$> pure op <*> go e
    (SectL e op)         -> SectL <$> go e <*> pure op
    (SectR op e)         -> SectR <$> pure op <*> go e
    (IfExpr ce te ee)    -> IfExpr <$> go ce <*> go te <*> go ee
    (ArithmSeq ce te ee) -> ArithmSeq <$> go ce <*> (mapM' go te) <*> (mapM' go ee)
    (Lambda binds body)  -> (avoidCapture subs binds) *> (Lambda <$> pure binds <*> replace' (foldr Map.delete subs (boundNames' binds)) body)
    (App func exprs)     -> App <$> go func <*> traverse go exprs
    --TODO: Add ListComp
    e                    -> return e

avoidCapture :: StrMap Expr -> (List Binding) -> Evaluator Unit
avoidCapture subs binds = case intersect (concatMap freeVariables $ Map.values subs) (boundNames' binds) of
  Nil       -> return unit
  captures -> throwError $ NameCaptureError captures

freeVariables :: Expr -> (List String)
freeVariables _ = Nil
-- freeVariables = nub <<< foldExpr
--   (\a -> case a of
--     Name name -> singleton $ name
--     _         -> Nil)
--   concat
--   concat
--   (\_ f1 f2 -> f1 ++ f2)
--   (\_ f -> f)
--   (\f _ -> f)
--   (\_ f -> f)
--   (\_ -> Nil)
--   (\f1 f2 f3 -> f1 ++ f2 ++ f3)
--   (\bs f -> nub f \\ boundNames' bs)
--   (\f fs -> f ++ concat fs)

boundNames' :: (List Binding) -> (List String)
boundNames' = concatMap boundNames

boundNames :: Binding -> (List String)
boundNames = go
  where
  go (Lit (Name name)) = singleton name
  go (ConsLit b1 b2)   = go b1 ++ go b2
  go (ListLit bs)      = foldMap go bs
  go (NTupleLit bs)    = foldMap go bs
  go _                 = Nil
