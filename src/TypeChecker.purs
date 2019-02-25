module TypeChecker where

import Control.Monad.Except as Ex
import Control.Monad.RWS (ask, evalRWST, local)
import Control.Monad.RWS.Trans (RWST)
import Control.Monad.State (State, evalState, put, get)
import Data.Array as Array
import Data.Char as Char
import Data.Either (Either(..))
import Data.Foldable (intercalate, fold, foldl, foldr)
import Data.List (List(..), (:), concat, unzip, zip, last)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, fromJust, isJust, maybe)
import Data.Set as Set
import Data.String.CodeUnits as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(Tuple), snd, fst)
import Partial.Unsafe (unsafeCrashWith)
import Prelude (
  class Eq, class Show, Unit,
  ($), (+), (-), (<$>), (<<<), (<>), (==), (>), (>>=), (>>>), (&&),
  bind, const, discard, div, flip, identity, map, mod, negate, not, otherwise, pure, show, unit)

import AST
import AST as AST



---------------------------------------------------------------------------------------------------
-- | Data Types and Helper Functions                                                             --
---------------------------------------------------------------------------------------------------

-- | A triple type.
data Triple a b c = Triple a b c

-- | Similar to `unzip` on tuples.
unzip3 :: forall a b c. List (Triple a b c) -> Triple (List a) (List b) (List c)
unzip3 = foldr
         (\(Triple a b c) (Triple as bs cs) ->
            Triple (a : as) (b : bs) (c : cs))
         (Triple Nil Nil Nil)

uncurry3 :: forall a b c d. (a -> b -> c -> d) -> (Triple a b c -> d)
uncurry3 f (Triple x y z) = f x y z

zip3 :: forall a b c. List a -> List b -> List c -> List (Triple a b c)
zip3 Nil _ _ = Nil
zip3 _ Nil _ = Nil
zip3 _ _ Nil = Nil
zip3 (Cons x xs) (Cons y ys) (Cons z zs) = Cons (Triple x y z) (zip3 xs ys zs)

last' :: forall a. List a -> a
last' Nil = unsafeCrashWith "last': empty list"
last' (x:Nil) = x
last' (_:xs) = last' xs
-- +--------------+
-- | Type Schemes |
-- +--------------+

-- | A type scheme represents a polytype. It contains a list of type variables, which may occur in
-- | the type.
data Scheme = Forall (List TVar) Type

derive instance eqScheme :: Eq Scheme

-- TODO: Remove, and use `ppScheme`?
instance showScheme :: Show Scheme where
  show (Forall a b) = "Forall (" <> show a <> ") " <> show b

-- | Pretty print a type scheme.
ppScheme :: Scheme -> String
ppScheme (Forall Nil t) = prettyPrintType t
ppScheme (Forall tvars t) = "forall " <> intercalate " " tvars <> ". " <> prettyPrintType t

-- +---------------+
-- | Substitutions |
-- +---------------+

-- | Substitions map type variables to monotypes and can be applied to data structures containing
-- | types.
type Subst = Map.Map TVar Type

-- | Pretty print a substitution.
-- | Example output:
-- | ```
-- | Substitution:
-- |   t0 ~ Int,
-- |   t1 ~ Int -> Int
-- | ```
ppSubst :: Subst -> String
ppSubst subst = "Substitutions:\n" <>
  ((map ppTVAndType :: Array (Tuple TVar Type) -> Array String) >>> intercalate ",\n")
  (Map.toUnfoldable subst)
  where ppTVAndType (Tuple tv t) = "\t" <> tv <> " ~ " <> prettyPrintType t

-- | The empty substition.
nullSubst :: Subst
nullSubst = Map.empty

-- | Compose the two given substitiutions into a single one.
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.unionWith f (map (apply s1) s2) s1
    where
    f UnknownType _ = UnknownType
    f _ UnknownType = UnknownType
    f t1 t2 = t1

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance subScheme :: Substitutable Scheme where
    apply s (Forall as t)   = Forall as $ apply s' t
                              where s' = foldr Map.delete s as
    ftv (Forall as t) = (ftv t) `Set.difference` Set.fromFoldable as

instance subType :: Substitutable Type where
   apply _ UnknownType = UnknownType
   apply _ (TypCon a) = TypCon a
   apply s t@(TypVar a) = fromMaybe t $ Map.lookup a s
   apply s (TypArr t1 t2) =  TypArr (apply s t1) (apply s t2)
   apply s (TList t) = TList (apply s t)
   apply s (TTuple t) = TTuple (apply s t)
   apply s (TTypeCons n ps) = TTypeCons n (apply s ps)
   apply _ (TypeError err) = TypeError err

   ftv UnknownType = Set.empty
   ftv (TypCon  _)         = Set.empty
   ftv (TypVar a)       = Set.singleton a
   ftv (TypArr t1 t2) =  Set.union (ftv t1) (ftv t2)
   ftv (TList t) = ftv t
   ftv (TTuple t) = ftv t
   ftv (TTypeCons n ps) = ftv ps
   ftv (TypeError err) = Set.empty

instance subMaybeType :: Substitutable (Maybe Type) where
  apply s t = apply s <$> t
  ftv (Just t) = ftv t
  ftv Nothing = Set.empty

instance listSub :: (Substitutable a) => Substitutable (List a) where
  apply s xs = map (apply s) xs
  ftv   = foldr (\a b -> Set.union (ftv a) b) Set.empty

instance subTypeEnv :: Substitutable TypeEnv where
  apply s (TypeEnv env) =  TypeEnv $ map (apply s) env
  ftv (TypeEnv env) = ftv $ snd $ unzip $ Map.toUnfoldable env

instance subQualTree :: (Substitutable a, Substitutable b, Substitutable c) => Substitutable (QualTree a b c) where
  apply s (Gen a b c) = Gen (apply s a) (apply s b) (apply s c)
  apply s (Let a b c) = Let (apply s a) (apply s b) (apply s c)
  apply s (Guard a c) = Guard (apply s a) (apply s c)

  ftv (Gen a b c) = ftv c
  ftv (Let a b c) = ftv c
  ftv (Guard a c) = ftv c

-- | Substitutable instance for the type tree.
instance subTypeTree :: Substitutable (Tree Atom (Binding Meta) (Tuple Op Meta) Meta) where
  apply s (Atom t a) = Atom (apply s t) a
  apply s (List t es) = List (apply s t) (apply s es)
  apply s (NTuple t es) = NTuple (apply s t) (apply s es)
  apply s (Binary t op l r) = Binary (apply s t) (apply s op) (apply s l) (apply s r)
  apply s (Unary t op e) = Unary (apply s t) (apply s op) (apply s e)
  apply s (SectL t e op) = SectL (apply s t) (apply s e) (apply s op)
  apply s (SectR t op e) = SectR (apply s t) (apply s op) (apply s e)
  apply s (PrefixOp t op) = PrefixOp (apply s t) (apply s op)
  apply s (IfExpr t c l r) = IfExpr (apply s t) (apply s c) (apply s l) (apply s r)
  apply s (ArithmSeq t begin step end) = ArithmSeq (apply s t) (apply s begin) (apply s <$> step) (apply s <$> end)
  apply s (LetExpr t bs e) = LetExpr (apply s t) ((\(Tuple x y) -> Tuple (apply s x) (apply s y)) <$> bs) (apply s e)
  apply s (Lambda t bs body) = Lambda (apply s t) (apply s bs) (apply s body)
  apply s (App t e es) = App (apply s t) (apply s e) (apply s es)
  apply s (ListComp t e qs) = ListComp (apply s t) (apply s e) (apply s qs)
  ftv typeTree = ftv (extractFromTree typeTree)

-- | Substitutable instance for operator tuples used in the type tree.
instance subOpTuple :: Substitutable (Tuple Op Meta) where
  apply s (Tuple op t) = Tuple op (apply s t)
  ftv (Tuple op t) = ftv t

instance subTypedBinding :: Substitutable a => Substitutable (Binding a) where
  apply s (Lit t atom) = Lit (apply s t) atom
  apply s (ConsLit t b1 b2) = ConsLit (apply s t) (apply s b1) (apply s b2)
  apply s (ListLit t lb) = ListLit (apply s t) (apply s lb)
  apply s (NTupleLit t lb) = NTupleLit (apply s t) (apply s lb)
  apply s (ConstrLit t c) = ConstrLit (apply s t) (map (apply s) c)

  ftv = extractFromBinding >>> ftv

instance subMeta :: Substitutable Meta where
  apply s (Meta meta) = Meta (meta {mtype = apply s meta.mtype})
  ftv (Meta meta) = ftv meta.mtype

-- +------------------------+
-- | Type Variable Mappings |
-- +------------------------+

-- | Mappings from type variable to type schemes. These mappings are used for bindings in lambda
-- | and let expressions and list comprehensions. Here for every binding the type variable and the
-- | corresponding scheme is stored.
-- TODO: Rename to `BindingEnvironment`?
type TVarMapping = Tuple TVar Scheme
type TVarMappings = List TVarMapping

ppTVarMappings :: TVarMappings -> String
ppTVarMappings mappings = "Type Variable Mappings:\n" <>
  (map ppTVarMapping >>> intercalate ",\n") mappings
  where ppTVarMapping (Tuple tv scheme) = "\t" <> tv <> " :: " <> ppScheme scheme

-- +------------------+
-- | Type Environment |
-- +------------------+

-- | The type environment is a mapping from type variables to polytypes.
data TypeEnv = TypeEnv (Map.Map TVar Scheme)

-- TODO: Remove in favor of `ppTypeEnv`?
instance showTypeEnv :: Show TypeEnv where
  show (TypeEnv a) = show a

-- | Pretty print a type environment.
-- | Example output:
-- | ```
-- | Type environment:
-- |   not : Bool -> Bool,
-- |   id : forall t_2. t_2 -> t_2
-- | ```
ppTypeEnv :: TypeEnv -> String
ppTypeEnv (TypeEnv env) = "Type environment:\n" <>
  ((map ppTVAndScheme :: Array (Tuple TVar Scheme) -> Array String) >>> intercalate ",\n")
  (Map.toUnfoldable env)
  where ppTVAndScheme (Tuple tv scheme) = "\t" <> tv <> " :: " <> ppScheme scheme

-- | Create an empty type environment.
emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv Map.empty

-- | Given a list of type variable names, remove the corresponding schemes from the type
-- | environment.
removeMultiple :: TypeEnv -> List TVar -> TypeEnv
removeMultiple (TypeEnv env) tvars = TypeEnv $ foldr Map.delete env tvars

-- | Remove an entry from the type environment given a type variable name.
remove :: TypeEnv -> TVar -> TypeEnv
remove (TypeEnv env) tvar = TypeEnv $ Map.delete tvar env

-- | Fold a list of type environments into a single type environment.
combine :: List TypeEnv -> TypeEnv
combine = foldl combine' emptyTypeEnv
  where
  combine' (TypeEnv env1) (TypeEnv env2) = TypeEnv $ Map.union env1 env2

-- | Extend the given type environment by the given type variable to scheme mapping.
extend :: TypeEnv -> TVarMapping -> TypeEnv
extend (TypeEnv env) (Tuple x s) = TypeEnv $ Map.insert x s env

-- | Extend the given type environment by the given mappings.
extendMultiple :: TypeEnv -> TVarMappings -> TypeEnv
extendMultiple = foldr (flip extend)

-- +--------------------------------+
-- | Type Specific Helper Functions |
-- +--------------------------------+

-- | The type `Bool`.
boolType :: Type
boolType = TypCon "Bool"

-- | The type `Char`.
charType :: Type
charType = TypCon "Char"

-- | The type `Int`.
intType :: Type
intType = TypCon "Int"

-- | The type `Int -> Int`.
intToIntType :: Type
intToIntType = intType `TypArr` intType

-- | The type `Int -> Int -> Int`.
intToIntToIntType :: Type
intToIntToIntType = intType `TypArr` intToIntType

-- | Given a list of types create the corresponding arrow type. Conceptually:
-- | [t0, t1, t2] => t0 -> (t1 -> t2)
toArrowType :: List Type -> Type
toArrowType Nil = unsafeCrashWith "Function `toArrowType` must not be called with an empty list."
toArrowType (t : Nil) = t
toArrowType (t:ts) = t `TypArr` (toArrowType ts)

fromArrowType :: Type -> List Type
fromArrowType (TypArr t t') = t : fromArrowType t'
fromArrowType t = t : Nil

-- +------------------+
-- | Type Constraints |
-- +------------------+

-- | Type constraints.
data Constraint = Constraint Type Type
                | ConstraintError Type

-- TODO: Simplify:
-- Map.Map Index TVar: (Remember which node index corresponds to which type variable)
-- List (Tuple Index Constraint): holds *all* the constraints

-- | A collection of constraints.
type Constraints = {
    -- Mapped constraints associate a node index with a constraint, which determines the type
    -- of the node.
    mapped :: Map.Map Index Constraint
    -- Unmapped constraints are a list of constraints together with index of the corresponding
    -- expression node. The index is needed here, because we need to associate occurring
    -- unification errors with expression nodes.
  , unmapped :: List (Tuple Index Constraint)
  }

-- | Convert the given set of constraints into a list of constraints.
toConstraintList :: Constraints -> List Constraint
toConstraintList constraints =
  (Map.toUnfoldable >>> map snd) constraints.mapped <>
  map snd constraints.unmapped

toConstraintAndIndexLists :: Constraints -> Tuple (List Index) (List Constraint)
toConstraintAndIndexLists constraints =
  unzip constraints.unmapped <>
  unzip (Map.toUnfoldable constraints.mapped)

-- | Construct an empty constraint map.
emptyConstraints :: Constraints
emptyConstraints =
  { unmapped: Nil
  , mapped: Map.empty
  }

-- | Append the given constraints.
appendConstraints :: Constraints -> Constraints -> Constraints
appendConstraints cs1 cs2 =
  { unmapped: cs1.unmapped <> cs2.unmapped
  , mapped: cs1.mapped <> cs2.mapped
  }

-- | Create a constraint structure representing an error of a tree node.
constraintError :: Index -> Type -> TypeError -> Constraints
constraintError idx tv error =
  { unmapped: Tuple idx (Constraint tv UnknownType) : Nil
  , mapped: Map.singleton idx (ConstraintError $ TypeError error)
  }

constraintSingleUnmapped :: Index -> Type -> Type -> Constraints
-- The unknown type should always stand on the right.
constraintSingleUnmapped idx UnknownType t =
  { unmapped: (Tuple idx (Constraint t UnknownType)) : Nil
  , mapped: Map.empty
  }
constraintSingleUnmapped idx t1 t2 =
  { unmapped: (Tuple idx (Constraint t1 t2)) : Nil
  , mapped: Map.empty
  }

constraintSingleMapped :: Index -> Type -> Type -> Constraints
constraintSingleMapped idx UnknownType t =
  { unmapped: Nil
  , mapped: Map.singleton idx (Constraint t UnknownType)
  }
constraintSingleMapped idx t1 t2 =
  { unmapped: Nil
  , mapped: Map.singleton idx (Constraint t1 t2)
  }

-- | Fold the given list of constraints down to a single constraint set.
foldConstraints :: List Constraints -> Constraints
foldConstraints = foldr (<+>) emptyConstraints

infixr 5 appendConstraints as <+>

-- | Constraints are substitutable.
instance substitutableConstraint :: Substitutable Constraint where
  apply s (Constraint t1 t2) = Constraint (apply s t1) (apply s t2)
  apply s (ConstraintError typeError) = ConstraintError (apply s typeError)
  ftv (Constraint t1 t2) = ftv t1 `Set.union` ftv t2
  ftv (ConstraintError typeError) = Set.empty

-- | Pretty print the given constraint.
ppConstraint :: Constraint -> String
ppConstraint (Constraint t1 t2) = prettyPrintType t1 <> " is " <> prettyPrintType t2
ppConstraint (ConstraintError typeError) = prettyPrintType typeError

-- | Pretty print the given constraints.
ppConstraints :: Constraints -> String
ppConstraints constraints = "Constraints:\n" <>
  "  determining the type:\n" <>
    ((map ppTuple :: Array (Tuple Index Constraint) -> Array String) >>> intercalate ",\n")
    (Map.toUnfoldable constraints.mapped) <> "\n" <>
  "  other:\n" <>
    (map ppTuple >>> intercalate ",\n")
    constraints.unmapped
  where
  ppTuple (Tuple idx constraint) = "\tnode " <> show idx <> ": " <> ppConstraint constraint

-- | Pretty print the given constraint list.
ppConstraintList :: List Constraint -> String
ppConstraintList constraints = "Constraints:\n" <>
  (map ppConstraint >>> intercalate ",\n") constraints

---------------------------------------------------------------------------------------------------
-- | Type Inference                                                                              --
---------------------------------------------------------------------------------------------------

data Unique = Unique { count :: Int }

initUnique :: Unique
initUnique = Unique { count : 0 }

type InferEnv = { env :: TypeEnv, stopOnError :: Boolean }

type Infer a = (RWST
  InferEnv              -- ^ Read from the type environment.
  Unit
  Unique                -- ^ The infer state.
  (Ex.Except TypeError) -- ^ Catch type errors.
  a)

-- | Run the type inference with a given typed environment and catch type errors. Note that the
-- | only possible errors are:
-- |   * `UnboundVariable`
-- |   * `NoInstanceOfEnum`
-- |   * `UnknownError`
-- | All other errors can only be encountered during the constraint solving phase.
runInferWith :: forall a. TypeEnv -> Boolean -> Infer a -> Either TypeError a
runInferWith env stopOnError m = Ex.runExcept (fst <$> evalRWST m inferEnv initUnique)
  where inferEnv = { env: env, stopOnError: stopOnError }

-- | Run the type inference with the empty environment.
runInfer :: forall a. Boolean -> Infer a -> Either TypeError a
runInfer = runInferWith emptyTypeEnv

-- | Check, if a type variable occurs in a substitutable instance.
occursCheck :: forall a. Substitutable a => TVar -> a -> Boolean
occursCheck a t = a `Set.member` ftv t

-- | Generalize a monotype to a polytype in the context of a given type environment.
generalize :: TypeEnv -> Type -> Scheme
generalize env t  = Forall as t
  where as = Set.toUnfoldable $ ftv t `Set.difference` ftv env

-- | Choose a fresh type variable name.
freshTVar :: Infer TVar
freshTVar = do
  Unique s <- get
  put (Unique { count: (s.count + 1) })
  pure $ "t_" <> show s.count

-- | Choose a fresh type variable.
fresh :: Infer Type
fresh = TypVar <$> freshTVar

-- | Create a monotype from the given type scheme.
instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- traverse (const fresh) as
  let s = Map.fromFoldable $ zip as as'
  pure $ apply s t

-- | Return canonical, polymorphic type.
closeOverType :: Type -> Scheme
closeOverType t = generalize emptyTypeEnv t

-- | Lookup a type in the type environment.
lookupEnv :: TVar -> Infer MType
lookupEnv tvar = do
  { env: (TypeEnv env) } <- ask
  case Map.lookup tvar env of
    Nothing -> pure Nothing
    Just scheme -> instantiate scheme >>= (pure <<< Just)

-- | Given an indexed expression, add a type constraint using the given type and expression index.
returnWithConstraint :: TypeTree -> Type -> Infer (Tuple Type Constraints)
returnWithConstraint expr t = do
  tv <- fresh
  pure $ Tuple tv (constraintSingleMapped (index expr) tv t)

-- TODO: Where can this be used instead of `returnWithConstraint`?
returnDirect :: TypeTree -> Type -> Infer (Tuple Type Constraints)
returnDirect expr t = pure $ Tuple t (constraintSingleMapped (index expr) t t)

returnWithTypeError :: TypeTree -> TypeError -> Infer (Tuple Type Constraints)
returnWithTypeError expr typeError = do
  { stopOnError: stopOnError } <- ask
  if stopOnError
    then Ex.throwError typeError
    else do
      tv <- fresh
      pure $ Tuple tv (constraintError (index expr) tv typeError)

setTypeConstraintFor' :: Index -> Type -> Type -> Constraints
setTypeConstraintFor' idx t1 t2 = constraintSingleMapped idx t1 t2

-- | Setup a new type constraint for a given expression node.
setTypeConstraintFor :: TypeTree -> Type -> Type -> Constraints
setTypeConstraintFor expr t1 t2 = constraintSingleMapped (index expr) t1 t2

-- | Setup a new type constraint mapping a type to itself.
setSingleTypeConstraintFor :: TypeTree -> Type -> Constraints
setSingleTypeConstraintFor expr t = constraintSingleMapped (index expr) t t

setSingleTypeConstraintFor' :: Index -> Type -> Constraints
setSingleTypeConstraintFor' idx t = constraintSingleMapped idx t t

-- | Set a constraint not referring to a node.
setConstraintFor :: TypeTree -> Type -> Type -> Constraints
setConstraintFor expr t1 t2 = constraintSingleUnmapped (index expr) t1 t2

setConstraintFor' :: Index -> Type -> Type -> Constraints
setConstraintFor' idx t1 t2 = constraintSingleUnmapped idx t1 t2

-- | Determine the type of the given operator.
getOpType :: Op -> Infer Type
getOpType op = case op of
    Composition -> do
      a <- fresh
      b <- fresh
      c <- fresh
      pure $ (b `TypArr` c) `TypArr` ((a `TypArr` b) `TypArr` (a `TypArr` c))
    Power -> pure intToIntToIntType
    Mul -> pure intToIntToIntType
    Add -> pure intToIntToIntType
    Sub -> pure intToIntToIntType
    Colon -> do
      a <- fresh
      pure $ a `TypArr` (TList a `TypArr` TList a)
    Append -> do
      a <- fresh
      pure $ TList a `TypArr` (TList a `TypArr` TList a)
    Equ -> toBoolType
    Neq -> toBoolType
    Lt -> toBoolType
    Leq -> toBoolType
    Gt -> toBoolType
    Geq -> toBoolType
    And -> pure $ boolType `TypArr` (boolType `TypArr` boolType)
    Or -> pure $ boolType `TypArr` (boolType `TypArr` boolType)
    Dollar -> do
      a <- fresh
      b <- fresh
      pure $ (a `TypArr` b) `TypArr` (a `TypArr` b)
    InfixConstr name -> do
      mt <- lookupEnv name
      case mt of
        Nothing -> Ex.throwError $ UnknownDataConstructor name
        Just t  -> pure t
    _ -> pure UnknownType
  where
  -- The type `a -> a -> Bool`.
  toBoolType = do
    a <- fresh
    pure $ a `TypArr` (a `TypArr` boolType)

-- | Given an operator tuple, determine the operator type and put a type constraint on the
-- | corresponding expression node.
inferOp :: Tuple Op Meta -> Infer (Tuple Type Constraints)
inferOp (Tuple (InfixFunc name) (Meta meta)) = do
  Tuple t c <- infer (Atom (Meta $ meta {index = meta.index}) (Name name))
  pure $ Tuple t c
inferOp opTuple@(Tuple op _) = do
  t <- getOpType op
  let c = setSingleTypeConstraintFor' (opIndex opTuple) t
  pure $ Tuple t c

-- | Return true, if the top-level node of the given expression has a type.
isTypedExpr :: TypeTree -> Boolean
isTypedExpr = extractFromTree >>> getMetaMType >>> isJust

-- | Traverse the given (partially typed) expression and collect type constraints. For expression
-- | nodes which are already typed, corresponding constraints are emitted.
infer :: TypeTree -> Infer (Tuple Type Constraints)
infer expr
  | isTypedExpr expr = do
      -- Perform type inference on the expression as usual.
      Tuple inferredType cs <- infer' expr
      let t = getType expr
          idx = index expr
      -- Add already known type as well as the inferred type as constraints.
      tv1 <- fresh
      tv2 <- fresh
      let newConstraints = Tuple idx (Constraint tv1 t)
                         : Tuple idx (Constraint tv2 inferredType)
                         : Tuple idx (Constraint tv1 tv2)
                         : Nil
      pure $ Tuple t { mapped: cs.mapped, unmapped: newConstraints <> cs.unmapped }
    where
    getType = extractFromTree >>> getMetaMType >>> fromMaybe UnknownType
  | otherwise = infer' expr

-- | Traverse the given untyped expression and collect type constraints. This function is only
-- | called by `infer`, which checks for already present type information.
infer' :: TypeTree -> Infer (Tuple Type Constraints)
infer' ex = case ex of
  Atom _ atom@(Bool _) -> returnWithConstraint ex boolType
  Atom _ atom@(Char _) -> returnWithConstraint ex charType
  Atom _ atom@(AInt _) -> returnWithConstraint ex intType
  Atom _ atom@(Constr name) -> do
    mt <- lookupEnv name
    case mt of
         Nothing -> returnWithTypeError ex (UnknownDataConstructor name)
         Just t  -> returnWithConstraint ex t
  Atom _ atom@(Name name) -> case name of
    -- Built-in functions.
    "mod" -> returnWithConstraint ex intToIntToIntType
    "div" -> returnWithConstraint ex intToIntToIntType
    -- Try to find the variable name in the type environment.
    _     -> do
      mt <- lookupEnv name
      case mt of
        -- The name is not in the environment, report an error.
        Nothing -> returnWithTypeError ex (UnboundVariable name)
        -- The current expression should have type `t`.
        Just t -> returnWithConstraint ex t

  Lambda _ bs e -> do
    -- Infer the binding types, accumulate type variable/scheme mappings and setup type information
    -- for every binding node in the expression tree.
    Triple t1 bindingEnv c1 <- makeBindingEnvLambda bs
    -- Infer the type of the body expression.
    Tuple t2 c2 <- withEnv bindingEnv (infer e)
    -- Given a list of binding types, construct the corresponding type. Conceptually:
    -- `(\a b c -> ...) => typeof a -> typeof b -> typeof c -> t2`
    let lambdaType = toArrowType (t1 <> (t2 : Nil))
    -- Set the type for the current expression.
    let c3 = setSingleTypeConstraintFor ex lambdaType
    pure $ Tuple lambdaType (c1 <+> c2 <+> c3)

  -- Example expression: `mod 2 3`:
  -- The subexpression `e` refers to `mod`, the expression list `es` refers to `2` and `3`.
  App _ e es -> do
    Tuple t1 c1 <- infer e
    -- Collect the constraints and type information of the given parameters.
    Tuple ts cs <- unzip <$> traverse infer es
    let c2 = foldConstraints cs
    tv <- fresh
    -- The function type has to match up with the given parameter types.
    let c3 = setConstraintFor ex t1 (toArrowType (ts <> (tv : Nil)))
    -- The application expression has the type referred to by type variable `tv`.
    let c4 = setSingleTypeConstraintFor ex tv
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4)

  LetExpr _ defs e -> do
    -- Construct the binding environment and use it for the type inference of the body
    Tuple bindingEnv c1 <- makeBindingEnvLet defs
    Tuple t2 c2 <- withEnv bindingEnv (infer e)
    -- Set the type for the current expression.
    let c3 = setSingleTypeConstraintFor ex t2
    pure $ Tuple t2 (c1 <+> c2 <+> c3)

  IfExpr _ cond l r -> do
    Tuple t1 c1 <- infer cond
    Tuple t2 c2 <- infer l
    Tuple t3 c3 <- infer r
    -- In the condition node: t1 has to be a `Bool`.
    -- Because the `cond` expression has already been given a mapped constraint, we have to use
    -- `setConstraintFor` and not `setTypeConstraintFor`.
    let c4 = setConstraintFor cond t1 boolType
    -- In the node of the if expression: t2 and t3 have to be equal.
    let c5 = setTypeConstraintFor ex t2 t3
    pure $ Tuple t2 (c1 <+> c2 <+> c3 <+> c4 <+> c5)

  Binary _ op e1 e2 -> do
    Tuple t1 c1 <- inferOp op
    Tuple t2 c2 <- infer e1
    Tuple t3 c3 <- infer e2
    tv <- fresh
    let c4 = setConstraintFor ex t1 (t2 `TypArr` (t3 `TypArr` tv))
    let c5 = setSingleTypeConstraintFor ex tv
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4 <+> c5)

  Unary _ op e -> do
    Tuple t1 c1 <- inferOp op
    Tuple t2 c2 <- infer e
    tv <- fresh
    let c3 = setConstraintFor ex t1 (t2 `TypArr` tv)
    let c4 = setSingleTypeConstraintFor ex tv
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4)

  -- Expressions of the form `(4+)`.
  SectL _ e op -> do
    Tuple t1 c1 <- inferOp op
    Tuple left c2 <- infer e
    right <- fresh
    tv <- fresh
    let c3 = setConstraintFor ex t1 (left `TypArr` (right `TypArr` tv))
    let c4 = setSingleTypeConstraintFor ex (right `TypArr` tv)
    pure $ Tuple (right `TypArr` tv) (c1 <+> c2 <+> c3 <+> c4)

  -- Expressions of the form `(^2)`.
  SectR _ op e -> do
    Tuple t1 c1 <- inferOp op
    Tuple right c2 <- infer e
    left <- fresh
    tv <- fresh
    let c3 = setSingleTypeConstraintFor ex (left `TypArr` tv)
    let c4 = setConstraintFor ex t1 (left `TypArr` (right `TypArr` tv))
    pure $ Tuple (left `TypArr` tv) (c1 <+> c2 <+> c3 <+> c4)

  -- Expressions of the form `(:)`.
  PrefixOp _ op -> do
    Tuple t1 c1 <- inferOp op
    tv <- fresh
    let c2 = setSingleTypeConstraintFor ex t1
    pure $ Tuple t1 (c1 <+> c2)

  -- Empty lists.
  List _ Nil -> do
    -- We use `tv` as type variable for the list expression and `tv2` for type of the list
    -- elements.
    tv <- fresh
    tv2 <- fresh
    -- tv ~ [tv2]
    let listType = TList tv2
    let c = setTypeConstraintFor ex tv listType
    pure $ Tuple listType c

  -- Single element lists.
  List _ (e : Nil) -> do
    -- Get the constraints and type of the first list element.
    Tuple t c1 <- infer e
    -- The list expression has the type `[t1]` where `t1` denotes the type of the first list
    -- element.
    tv <- fresh
    let listType = TList t
    let c2 = setTypeConstraintFor ex tv listType
    pure $ Tuple listType (c1 <+> c2)

  -- List with multiple elements.
  List _ (e : es) -> do
    Tuple t1 c1  <- infer e
    Tuple ts cs  <- unzip <$> traverse infer es
    -- Also add constraints for the rest of the list elements. All elements should have the same
    -- type as the first list element.
    let c2 = foldConstraints (map (setConstraintFor ex t1) ts)
    let c3 = foldConstraints cs
    -- The list expression has the type `[t1]` where `t1` denotes the type of the first list
    -- element.
    tv <- fresh
    let listType = TList t1
    let c4 = setTypeConstraintFor ex tv listType
    pure $ Tuple listType (c1 <+> c2 <+> c3 <+> c4)

  NTuple _ es -> do
    Tuple ts cs <- unzip <$> traverse infer es
    tv <- fresh
    let tupleType = TTuple ts
    let c = setTypeConstraintFor ex tv tupleType
    pure $ Tuple tupleType (foldConstraints cs <+> c)

  ArithmSeq _ first step last -> do
    -- Infer the type of the beginning expression, which always exists.
    Tuple t1 c1 <- inferRequireEnumType first
    -- Try to infer the types of the `step` and `last` expression if existing and set the
    -- constraints accordingly.
    c2 <- tryInferRequireEnumType step t1
    c3 <- tryInferRequireEnumType last t1
    tv <- fresh
    let c4 = setTypeConstraintFor ex tv (TList t1)
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4)

  ListComp  _ body quals -> do
    -- Infer the types of the qual expressions, gather the constraints and the binding environment.
    Tuple bindingEnv c1 <- makeBindingEnvListComp quals
    Tuple t1 c2 <- withEnv bindingEnv (infer body)
    tv <- fresh
    let c4 = setTypeConstraintFor ex tv (TList t1)
    pure $ Tuple tv (c1 <+> c2 <+> c4)

-- +-----------------------------------+
-- | Bindings and Binding Environments |
-- +-----------------------------------+

-- | Return true, if the given top-level binding has a type.
isTypedBinding :: TypedBinding -> Boolean
isTypedBinding = extractFromBinding >>> (\(Meta meta) -> meta.mtype) >>> isJust

-- | Proxy for `makeBindingEnv`. Checks, if the given binding is typed. Whenever the binding is
-- | typed, call `makeBindingEnv` and overwrite the constraints with a type constraint for the
-- | current binding node.
makeBindingEnvPartial :: TypedBinding -> Infer (Triple Type TVarMappings Constraints)
makeBindingEnvPartial binding
  | isTypedBinding binding = case binding of

    -- In this case, the mapping also has to be updated to contain the type already set.
    Lit (Meta { mtype: Just t }) (Name name) -> do
      let c = setSingleTypeConstraintFor' (bindingIndex binding) t
      pure $ Triple t (Tuple name (Forall Nil t) : Nil) c

    _ -> do
      Triple _ m c1 <- makeBindingEnv binding
      let t = (extractFromBinding >>> getMetaMType >>> fromMaybe UnknownType) binding
      let c2 = setSingleTypeConstraintFor' (bindingIndex binding) t
      pure $ Triple t m (c2 <+> c1)

  | otherwise = makeBindingEnv binding

-- | Choose a new type variable for the given binding and add typing information for the node
-- | index. This function is needed whenever binding environments have to be built: lambda and let
-- | expressions as well as list comprehensions.
makeBindingEnv :: TypedBinding -> Infer (Triple Type TVarMappings Constraints)
makeBindingEnv binding = case binding of
  Lit _ atom@(Bool bool) -> do
    let c = setSingleTypeConstraintFor' (bindingIndex binding) boolType
    pure $ Triple boolType Nil c

  Lit _ atom@(Char char) -> do
    let c = setSingleTypeConstraintFor' (bindingIndex binding) charType
    pure $ Triple charType Nil c

  Lit _ atom@(AInt aint) -> do
    let c = setSingleTypeConstraintFor' (bindingIndex binding) intType
    pure $ Triple intType Nil c

  Lit _ atom@(Name name) -> do
    -- Set the type of the associate tree node to equal the type referred to by `tv`.
    tv <- fresh
    let c = setSingleTypeConstraintFor' (bindingIndex binding) tv
    pure $ Triple tv (Tuple name (Forall Nil tv) : Nil) c

  Lit _ atom@(Constr name) -> do
    mt <- lookupEnv name
    t <- case mt of
         Nothing -> Ex.throwError (UnknownDataConstructor name)
         Just t  -> pure t
    let c = setSingleTypeConstraintFor' (bindingIndex binding) t
    pure $ Triple t Nil c

  ConsLit _ b1 b2 -> do
    Triple t1 m1 c1 <- makeBindingEnvPartial b1
    Triple t2 m2 c2 <- makeBindingEnvPartial b2
    let c3 = setTypeConstraintFor' (bindingIndex binding) (TList t1) t2
    pure $ Triple (TList t1) (m1 <> m2) (c1 <+> c2 <+> c3)

  ListLit _ bs -> do
    Triple ts ms cs <- unzip3 <$> traverse makeBindingEnvPartial bs
    listElementConstraints <- setListConstraints ts
    t <- listType ts
    pure $ Triple t (concat ms) (foldConstraints cs <+> listElementConstraints)

  NTupleLit _ bs -> do
    Triple ts ms cs <- unzip3 <$> traverse makeBindingEnvPartial bs
    let c = setSingleTypeConstraintFor' (bindingIndex binding) (TTuple ts)
    pure $ Triple (TTuple ts) (concat ms) (foldConstraints cs <+> c)

  ConstrLit _ cnstr -> case cnstr of
    PrefixDataConstr constrName _ args -> do
      if String.charAt 0 constrName == Just ':'
         then Ex.throwError $ UnknownDataConstructor $ "(" <> constrName <> ") has been safed as a prefix constructor."
         else pure unit
      mt <- lookupEnv constrName
      -- collect information about the constructor
      tConstr <- case mt of
        Nothing -> Ex.throwError (UnknownDataConstructor constrName)
        Just t -> pure t
      -- collect information about the constructor's arguments
      Triple tArgs mArgs cArgs' <- unzip3 <$> traverse makeBindingEnvPartial args
      let cArgs = foldConstraints cArgs'
      tResult <- fresh
      -- match constructor type with the argument type
      let cConstr = setConstraintFor' (bindingIndex binding) tConstr (toArrowType (tArgs <> (tResult:Nil)))
      -- Result Type
      let cBinding = setSingleTypeConstraintFor' (bindingIndex binding) tResult
      pure $ Triple tResult (concat mArgs) (cArgs <+> cConstr <+> cBinding)

    InfixDataConstr constrName _ _ l r -> do
      mt <- lookupEnv constrName
      -- collect information about the constructor
      Triple tl tr t <- case mt of
        Nothing -> Ex.throwError (UnknownDataConstructor constrName)
        Just (TypArr l (TypArr r t)) -> pure $ Triple l r t
        Just t -> Ex.throwError (UnknownError $ prettyPrintType t <> " can not be the type of " <> constrName)
      -- collect information about the constructor's arguments
      Triple tl' ml cl <- makeBindingEnvPartial l
      Triple tr' mr cr <- makeBindingEnvPartial r
      tResult <- fresh
      -- match constructor type with the argument type
      let cConstr = setConstraintFor' (bindingIndex binding) (TypArr tl (TypArr tr t)) (TypArr tl' (TypArr tr' tResult))
      -- Result Type
      let cBinding = setSingleTypeConstraintFor' (bindingIndex binding) tResult
      pure $ Triple tResult (ml <> mr) (cl <+> cr <+> cConstr <+> cBinding)



  where
  -- Go through the list of given types and set constraints for every to elements of the list.
  setListConstraints Nil = pure emptyConstraints
  setListConstraints (t:Nil) = do
    let c = setSingleTypeConstraintFor' (bindingIndex binding) (TList t)
    pure c
  setListConstraints (t1:t2:ts) = do
    cs <- setListConstraints (t2:ts)
    let c = setConstraintFor' (bindingIndex binding) t1 t2 <+> cs
    pure c

  -- Given a list of types occurring in a list, determine the list type (choose the first element).
  listType Nil = TList <$> fresh
  listType (t:_) = pure $ TList t

-- | Extend the type environment with the new mappings for the evaluation of `m`.
withEnv :: forall a. TVarMappings -> Infer a -> Infer a
withEnv mappings m = local (scope mappings) m
  where
  scope mappings inferEnv =
    { env: removeMultiple inferEnv.env (map fst mappings) `extendMultiple` mappings
    , stopOnError: inferEnv.stopOnError
    }

-- +--------------------+
-- | Lambda Expressions |
-- +--------------------+

-- | Go through list of given bindings and accumulate an corresponding type. Gather environment
-- | information and setup the type information for every binding tree node.
makeBindingEnvLambda :: List TypedBinding
                     -> Infer (Triple (List Type) TVarMappings Constraints)
makeBindingEnvLambda bindings = do
  Triple ts ms cs <- unzip3 <$> traverse makeBindingEnvPartial bindings
  pure $ Triple ts (concat ms) (foldConstraints cs)

-- +----------------------------------------+
-- | Let Expressions and List Comprehension |
-- +----------------------------------------+

-- | Associate a binding with a corresponding expression. Therefore, infer the given expression
-- | and associate its type with the binding.
associate :: TypedBinding -> TypeTree -> Infer (Tuple TVarMappings Constraints)
associate binding expr = do
  Triple _ m _ <- makeBindingEnvPartial binding
  Tuple et c1 <- infer expr
  { env: env } <- ask
  uni <- solveConstraints c1
  let c2 = setSingleTypeConstraintFor' (bindingIndex binding) et
      -- Substitute the bound variables with the corresponding polytype.
      scheme = generalize (apply uni.subst env) (apply uni.subst et)
  -- Map the type scheme on the binding (and sub-bindings).
  Tuple m' c3 <- mapSchemeOnTVarMappingsPartial binding scheme
  checkPattern binding scheme m m'
  pure $ Tuple m' (uni.constraints <+> c1 <+> c2 <+> c3)

-- | Determine the common type variables used.
commonFreeTVars :: List TVar -> Type -> List TVar
commonFreeTVars tvars t = Set.toUnfoldable $ ftv t `Set.intersection` ftv (map TypVar tvars)

-- | Report an pattern mismatch error, if the given type variable mappings don't match up. The
-- | first type variable mapping is determined by shape of the binding, while the second type
-- | variable mapping is determined by the expression scheme.
checkPattern :: TypedBinding -> Scheme -> TVarMappings -> TVarMappings -> Infer Unit
checkPattern binding scheme m1 m2 = if compareTVarMappings m1 m2
  then pure unit
  else do
    t <- schemeToType scheme
    Ex.throwError $ PatternMismatch binding t

-- | Return true, if the given type variable mappings contain exactly the same type variables.
compareTVarMappings :: TVarMappings -> TVarMappings -> Boolean
compareTVarMappings m1 m2 = (toSet m1) == (toSet m2)
  where toSet m = Set.fromFoldable (map fst m)

-- | Map the given scheme to optionally partially typyed bindings.
mapSchemeOnTVarMappingsPartial :: TypedBinding -> Scheme -> Infer (Tuple TVarMappings Constraints)
mapSchemeOnTVarMappingsPartial binding scheme
  -- This case is only encountered, when the encountered binding literal is typed. Just use the
  -- given type instead of the inferred type scheme.
  | isTypedBinding binding = mapSchemeOnTVarMappings binding (Forall Nil t)
    where
    getBindingType = extractFromBinding >>> getMetaMType >>> fromMaybe UnknownType
    t = getBindingType binding
  | otherwise = mapSchemeOnTVarMappings binding scheme

-- | Given a binding and a scheme, try to construct a mapping for every type variable inside the
-- | binding patter to the corresponding polytype. In the process setup type constraints for the
-- | nodes in the binding tree.
mapSchemeOnTVarMappings :: TypedBinding -> Scheme -> Infer (Tuple TVarMappings Constraints)
mapSchemeOnTVarMappings binding scheme@(Forall typeVariables _) = case binding of

  Lit _ (Name name) -> do
    let m = Tuple name (filteredScheme scheme) : Nil
    returnAs m emptyConstraints (schemeType scheme)

  ConsLit _ b1 b2 -> case expectListType scheme of
    Just listType@(TList t) -> do
      Tuple m1 c1 <- mapSchemeOnTVarMappingsPartial b1 (toScheme t)
      Tuple m2 c2 <- mapSchemeOnTVarMappingsPartial b2 (toScheme listType)
      returnAs (m1 <> m2) (c1 <+> c2) listType
    _ -> reportMismatch

  NTupleLit _ bs -> case expectTupleType scheme of
    Just tupleType@(TTuple ts) -> do
      Tuple ms cs <- unzip <$> traverse (\(Tuple binding t) ->
        mapSchemeOnTVarMappingsPartial binding (toScheme t))
        (zip bs ts)
      returnAs (fold ms) (foldConstraints cs) tupleType
    _ -> reportMismatch

  ListLit _ bs -> case expectListType scheme of
    Just listType@(TList t) -> do
      Tuple ms cs <- unzip <$> traverse (\binding ->
        mapSchemeOnTVarMappingsPartial binding (toScheme t)) bs
      returnAs (fold ms) (foldConstraints cs) listType
    _ -> reportMismatch

  ConstrLit _ constr -> case constr of
    PrefixDataConstr constrName _ bs -> case expectConstrType scheme of
      Just bndType@(TTypeCons constrName' ts) -> do
        mt <- lookupEnv constrName
        constrType <- case mt of
          Just t -> pure t
          Nothing -> Ex.throwError (UnknownDataConstructor constrName)
        let ts' = fromArrowType constrType
            c = setTypeConstraintFor' (bindingIndex binding) (last' ts') bndType
        uni <- solveConstraints c
        Tuple ms cs <- unzip <$> traverse
          (\(Tuple b t) -> mapSchemeOnTVarMappingsPartial b (toScheme t))
          (zip bs (apply uni.subst ts'))

        returnAs (fold ms) (c <+> foldConstraints cs) bndType
      _ -> reportMismatch

    InfixDataConstr constrName _ _ lArg rArg -> case expectConstrType scheme of
      Just bndType@(TTypeCons constrName' ts) -> do
        mt <- lookupEnv constrName
        Triple lType rType resType <- case mt of
          Just (TypArr l (TypArr r t)) -> pure $ Triple l r t
          Just t -> Ex.throwError (UnknownError $ prettyPrintType t <> " can not be the type of " <> constrName)
          Nothing -> Ex.throwError (UnknownDataConstructor constrName)
        let c = setTypeConstraintFor' (bindingIndex binding) resType bndType
        uni <- solveConstraints c
        Tuple lM lC <- mapSchemeOnTVarMappingsPartial lArg (toScheme (apply uni.subst lType))
        Tuple rM rC <- mapSchemeOnTVarMappingsPartial rArg (toScheme (apply uni.subst rType))
        returnAs (lM <> rM) (c <+> lC <+> rC) bndType
      _ -> reportMismatch



  _ -> pure $ Tuple Nil emptyConstraints
  where
  -- Set a type constraint for the current binding.
  returnAs mapping constraints t =
    let c = setSingleTypeConstraintFor' (bindingIndex binding) t
    in pure $ Tuple mapping (constraints <+> c)

  reportMismatch = do
      t <- schemeToType scheme
      Ex.throwError $ PatternMismatch binding t

  expectListType (Forall tvs (TList t)) = Just $ TList t
  expectListType _ = Nothing
  expectTupleType (Forall tvs (TTuple ts)) = Just $ TTuple ts
  expectTupleType _ = Nothing
  expectConstrType (Forall tvs (TTypeCons n ts)) = Just $ TTypeCons n ts
  expectConstrType _ = Nothing
  toScheme t = Forall typeVariables t
  filteredScheme (Forall tvs t) = (Forall (commonFreeTVars tvs t) t)
  schemeType (Forall tvs t) = t

-- | Given a list of bindings and corresponding expressions, associate the bindings with the
-- | expressions and collect the type variable/scheme mappings as well as the constraints.
associateAll :: List TypedBinding -> List TypeTree -> Tuple TVarMappings Constraints
             -> Infer (Tuple TVarMappings Constraints)
associateAll (b:bs) (e:es) (Tuple ms cs) = do
  Tuple m c <- associate b e
  withEnv m $ associateAll bs es (Tuple (ms <> m) (cs <+> c))
associateAll _ _ x = pure x

-- | Construct a binding environment to be used in the inference of a let expression.
makeBindingEnvLet :: List (Tuple TypedBinding TypeTree)
                  -> Infer (Tuple TVarMappings Constraints)
makeBindingEnvLet defs = associateAll bindings exprs (Tuple Nil emptyConstraints)
  where
  bindingsAndExprs = unzip defs
  bindings = fst bindingsAndExprs
  exprs = snd bindingsAndExprs

-- +---------------------+
-- | List Comprehensions |
-- +---------------------+

-- | Given a list of qual expressions, infer the types, set the constraints and accumulate a
-- | binding environment. The environment and constraints are returned.
makeBindingEnvListComp :: List TypeQual -> Infer (Tuple TVarMappings Constraints)
makeBindingEnvListComp quals = f quals Nil emptyConstraints
  where f (qual:quals) ms cs = do
          -- Infer the type, set constraints and accumulate binding environment for the current
          -- qual expression. Then pass the environment and constraints and continue with the next
          -- qual expression.
          Tuple m c <- makeBindingEnvQual qual
          withEnv m $ f quals (ms <> m) (cs <+> c)
        f Nil ms cs = pure (Tuple ms cs)

-- | Set constraints and build binding environment for the given qual expression.
makeBindingEnvQual :: TypeQual -> Infer (Tuple TVarMappings Constraints)
makeBindingEnvQual qual = case qual of
  -- Just associate the binding with the expression.
  Let _ binding expr -> associate binding expr
  -- Generate the binding environment for the binding and infer the generator expression.
  Gen _ binding genExpr -> do
    Triple t1 m c1 <- makeBindingEnvPartial binding
    Tuple t2 c2 <- infer genExpr
    let c3 = setConstraintFor genExpr (TList t1) t2
    pure $ Tuple m (c1 <+> c2 <+> c3)
  -- Only infer the expression type and set the constraints.
  Guard _ guardExpr -> do
    Tuple _ c <- infer guardExpr
    pure $ Tuple Nil c

-- +----------------------+
-- | Arithmetic Sequences |
-- +----------------------+

-- | If the given expression is non-empty, infer the type, set and return the constraints.
tryInferRequireEnumType :: Maybe TypeTree -> Type -> Infer Constraints
tryInferRequireEnumType (Just expr) t1 = do
  Tuple t2 c1 <- inferRequireEnumType expr
  let c2 = setSingleTypeConstraintFor expr t2
  let c3 = setConstraintFor expr t1 t2
  pure (c1 <+> c2 <+> c3)
tryInferRequireEnumType _ t = pure emptyConstraints

-- | Infer the type of the given expression, then run the constraint solving in order to retrieve
-- | the expression type. If the type is not an enum type, return with the corresponding type
-- | error.
inferRequireEnumType :: TypeTree -> Infer (Tuple Type Constraints)
inferRequireEnumType expr = do
  Tuple t c <- infer expr
  uni <- solveConstraints c
  -- Get the type hiding behind `t`.
  case Map.lookup (index expr) c.mapped of
    Just (Constraint tv _) -> do
      let exprType = apply uni.subst tv
      if not isEnumType exprType
        then returnWithTypeError expr (NoInstanceOfEnum exprType)
        else pure $ Tuple exprType c
    _ -> pure $ Tuple t c

-- | Return true, if the given type is enumerable.
isEnumType :: Type -> Boolean
isEnumType (TypCon "Int") = true
isEnumType (TypCon "Char") = true
isEnumType (TypCon "Bool") = true
isEnumType _ = false

---------------------------------------------------------------------------------------------------
-- | Constraint Solving                                                                          --
---------------------------------------------------------------------------------------------------

-- | Collect the substitutions by working through the constraints. The substitution represents
-- | the solution to the constraint solving problem.
type Unifier = { subst :: Subst, constraints :: Constraints }

-- | Create an initial unifier containing a substitution with mappings to the unknown type.
initialUnifier :: Constraints -> Unifier
initialUnifier constraints = { subst: nullSubst, constraints: constraints }

-- | Collect the substitutions in the unifier and catch occurring unification errors.
-- | If the flag `stopOnError` is set, unification errors are not reported, instead
-- | a corresponding error constraint is returned.
runSolve :: Boolean -> Constraints -> Either TypeError Unifier
runSolve stopOnError constraints =
  case Ex.runExcept $ solver stopOnError (initialUnifier constraints) of
    Left typeError -> Left typeError
    Right uni ->
      let errorConstraints = uni.constraints
      in Right { subst: uni.subst,
                 constraints: errorConstraints <+> constraints }

-- | Run the constraint solving inside the infer monad and catch occurring errors. Depending on
-- | the state of the `stopOnError` flag, the error is reported immediatlely or a corresponding
-- | constraint is emitted.
solveConstraints :: Constraints -> Infer Unifier
solveConstraints cs = do
  { stopOnError: stopOnError } <- ask
  case runSolve stopOnError cs of
    Left typeError -> Ex.throwError typeError
    Right unifier -> pure unifier

-- | Bind the given type variable to the given type and return the resulting substitution.
bindTVar ::  TVar -> Type -> Either TypeError Subst
bindTVar tv t
  | t == (TypVar tv) = pure $ nullSubst
  | occursCheck tv t = Left $ normalizeTypeError $ InfiniteType tv t
  | otherwise = pure $ Map.singleton tv t

-- | Try to unify the given types and return the resulting substitution or the occurring type
-- | error.
unifies :: Type -> Type -> Either TypeError Subst
unifies (TypArr l1 r1) (TypArr l2 r2) = do
  s1 <- unifies l1 l2
  s2 <- unifies (apply s1 r1) (apply s1 r2)
  pure $ s2 `compose` s1
unifies (TypVar tv) t = tv `bindTVar` t
unifies t (TypVar tv) = tv `bindTVar` t
unifies (TypCon c1) (TypCon c2) | c1 == c2 = pure nullSubst
unifies a b | a == b = pure nullSubst
unifies (TList l1) (TList l2) = unifies l1 l2
unifies (TTuple (a:as)) (TTuple (b:bs)) = do
  s1 <- unifies (TTuple as) (TTuple bs)
  s2 <- unifies a b
  pure $ s1 `compose` s2
unifies (TTuple Nil) (TTuple Nil) = pure nullSubst
unifies t1@(TTypeCons n1 (p1:ps1)) t2@(TTypeCons n2 (p2:ps2))
  | n1 == n2 = do
      s1 <- unifies (TTypeCons n1 ps1) (TTypeCons n2 ps2)
      s2 <- unifies p1 p2
      pure $ s1 `compose` s2
  | otherwise = Left $ normalizeTypeError $ UnificationFail t1 t2
unifies t1@(TTypeCons n1 Nil) t2@(TTypeCons n2 Nil)
  | n1 == n2 = pure nullSubst
  | otherwise = Left $ normalizeTypeError $ UnificationFail t1 t2
unifies UnknownType t = pure nullSubst
unifies t UnknownType = pure nullSubst
unifies t1 t2 = Left $ normalizeTypeError $ UnificationFail t1 t2


-- | Try to find a type variable associated with a specific expression node, given a set of
-- | constraint and the node index.
findTVarForNode :: Constraints -> Index -> Maybe TVar
findTVarForNode c idx = case Map.lookup idx c.mapped of
  Just (Constraint (TypVar tv) _) -> Just tv
  Just (Constraint _ (TypVar tv)) -> Just tv
  _ -> Nothing

-- | Try to solve the constraints.
solver :: Boolean -> Unifier -> Ex.Except TypeError Unifier
solver stopOnError { subst: beginningSubst, constraints: constraints } =
      -- Accumulate the final substitution and error constraints.
  let accumulatorUnifier = { subst: beginningSubst, constraints: emptyConstraints }
      lists = toConstraintAndIndexLists constraints
      indices = fst lists
      constraintList = snd lists
  in solver' accumulatorUnifier indices (apply beginningSubst constraintList)
  where
  -- Work through the list of constraints and the corresponding indices.
  solver' uni (idx:idxs) (c:cs) = do
    uni' <- solveSingleConstraint stopOnError uni idx c
    solver' uni' idxs (apply uni'.subst cs)
  -- Worked through all the constraints.
  solver' uni _ _ = pure uni

  -- | Try to create the unifier for the given constraint.
  --solveSingleConstraint :: Boolean -> Unifier -> Index -> Constraint -> Ex.Except TypeError Unifier
  solveSingleConstraint stopOnError uni idx constraint = case constraint of
    ConstraintError typeError -> pure uni
    Constraint t1 t2 -> case unifies t1 t2 of
      Left error@(InfiniteType _ _) -> Ex.throwError error
      Left error -> if stopOnError
        then Ex.throwError error
        else case findTVarForNode constraints idx of
          Nothing -> pure uni
          Just tv -> case Map.lookup tv uni.subst of
            -- If the given type variable already has a substitution which maps it to the unknown
            -- type, we already have encountered an error and just return the unifier.
            Just UnknownType -> pure uni
            _ -> do
              -- Collect the new error and append it to the previously collected error constraints.
              let errors = constraintError idx (TypVar tv) error <+> uni.constraints
              -- Create an updated initial constraint list, with the additional constraint:
              -- `tv == ?`.
              let mapped' = Map.insert idx (Constraint (TypVar tv) UnknownType) constraints.mapped
              let constraints' = { unmapped: constraints.unmapped, mapped: mapped' }
              -- Create an updated beginning substitution.
              let subst' = Map.alter (const $ Just UnknownType) tv beginningSubst
              -- Restart the constraint solving phase with the error we found just now.
              let lists' = toConstraintAndIndexLists (constraints' <+> errors)
              solver' { subst: subst', constraints: errors } (fst lists') (apply subst' $ snd lists')
      Right newSubst -> pure $ unifier (newSubst `compose` uni.subst)
    where unifier s = { subst: s `compose` uni.subst, constraints: uni.constraints }

-- | Go through tree and assign every tree node its type. In order to do this we rely on the node
-- | indices.
assignTypes :: Unifier -> TypeTree -> TypeTree
assignTypes { subst: subst, constraints: constraints } expr = treeMap identity fb fo f expr
  where
  f (Meta meta) = Meta $ meta { mtype = lookupTVar (meta.index) }
  -- f' (Tuple _ idx) = lookupTVar idx
  fo (Tuple op (Meta meta)) = Tuple op (Meta $ meta {mtype = lookupTVar (meta.index)})
  fb = map f
  lookupTVar idx = case Map.lookup idx constraints.mapped of
    Nothing -> Nothing
    Just (Constraint tv _) -> Just $ subst `apply` tv
    Just (ConstraintError typeError) -> Just typeError

-- +------------------------------------------------------+
-- | Type Inference for Definitions and Definition Groups |
-- +------------------------------------------------------+
--
-- Definition groups are a list of definitions with the same name (hence belonging together).
-- Ungrouped lists of definitions can be grouped together using `buildDefinitionGroups`.

-- | Given a list of definitions create a list of indexed definitions. Note, that the indices
-- | start with 0 and continue growing throughout all expressions and bindings in the given group.
makeIndexedDefinitionGroup :: List Definition -> List IndexedDefinition
makeIndexedDefinitionGroup = f 0
  where
  f _ Nil = Nil
  f beginWith (def:defs) = case makeIndexedDefinition def beginWith of
    Tuple indexedDef nextIdx -> indexedDef : f nextIdx defs

-- | Separate the given list of definitions into indexed definition groups. The indices in the
-- | respective groups start with 0.
makeIndexedDefinitionGroups :: List Definition -> Map.Map String (List IndexedDefinition)
makeIndexedDefinitionGroups = map makeIndexedDefinitionGroup <<< buildDefinitionGroups

-- | Given a list of definitions, infer the definition types and create a typed evaluation
-- | environment.
tryInferEnvironment :: List Definition -> Either TypeError TypeEnv
tryInferEnvironment defs = accumulateMappings emptyTypeEnv (Map.toUnfoldable indexedGroups)
  where
  indexedGroups = makeIndexedDefinitionGroups defs

  accumulateMappings env Nil = Right env
  accumulateMappings env (group:groups) = case getMappingFromGroup env group of
    -- Encountered an unbound variable, this means either:
    -- 1) The unbound variable has not yet been defined, but occurs later in the definition list.
    --    In this case: First infer the type of the (now) unbound definition, afterwards go on
    --    with the current one.
    -- 2) The variable does not occur in the definition list: Return an error.
    Left (UnboundVariable name) -> case Map.lookup name indexedGroups of
      Just defs -> accumulateMappings env ((Tuple name defs) : group : groups)
      Nothing -> Left $ UnboundVariable name
    Left typeError -> Left typeError
    Right (Tuple name scheme) -> accumulateMappings (env `extend` (Tuple name scheme)) groups

  getMappingFromGroup env@(TypeEnv m) (Tuple name defGroup) = case Map.lookup name m of
    -- The definition is already in the type environment, just use it.
    Just scheme -> Right (Tuple name scheme)
    -- The definition has not been found, try to infer the type and it to the environment.
    Nothing -> case runInferWith env true (schemeOfIndexedDefinitionGroup defGroup) of
      Left typeError -> Left typeError
      Right scheme -> Right (Tuple name scheme)

-- | Infer the type scheme of the given definition.
schemeOfDefinition :: Definition -> Infer Scheme
schemeOfDefinition def = do
  Triple t m c <- inferDefinition indexedDef
  uni <- solveConstraints c
  pure $ closeOverType (apply uni.subst t)
  where
  indexedDef = fst $ makeIndexedDefinition def 0

-- | Infer the type scheme of the given unindexed definition group.
schemeOfDefinitionGroup :: List Definition -> Infer Scheme
schemeOfDefinitionGroup = schemeOfIndexedDefinitionGroup <<< makeIndexedDefinitionGroup

-- | Infer the type scheme of the given indexed definition group.
schemeOfIndexedDefinitionGroup :: List IndexedDefinition -> Infer Scheme
schemeOfIndexedDefinitionGroup group = do
  Tuple t c <- inferDefinitionGroup group
  uni <- solveConstraints c
  pure $ closeOverType (apply uni.subst t)

-- | Infer the type (and collect constraints) for the given indexed definition group.
inferDefinitionGroup :: List IndexedDefinition -> Infer (Tuple Type Constraints)
inferDefinitionGroup Nil = Ex.throwError $ UnknownError "Can't infer type of empty definition group"
inferDefinitionGroup (def:Nil) = do
  Triple t m c <- inferDefinition def
  pure $ Tuple t c
inferDefinitionGroup (def:defs) = do
  Triple t1 m c1 <- inferDefinition def
  Tuple t2 c2 <- withEnv m (inferDefinitionGroup defs)
  let c3 = setConstraintFor' (definitionIndex def) t1 t2
  pure $ Tuple t1 (c1 <+> c2 <+> c3)

-- | Infer the type of the given indexed definitions and collect bindings and constraints.
inferDefinition :: IndexedDefinition -> Infer (Triple Type TVarMappings Constraints)
inferDefinition def@(IndexedDef name bindings expr) = do
  tv <- fresh
  let m = Tuple name (Forall Nil tv) : Nil
  Tuple t1 c1 <- withEnv m (infer (Lambda (Meta $ emptyMeta' {index = (-1)}) bindings expr))
  let c2 = setConstraintFor expr tv t1
  pure $ Triple tv m (c1 <+> c2)

-- | Transform the given polytype to a monotype.
schemeToType :: Scheme -> Infer Type
schemeToType scheme = do
  t <- instantiate scheme
  pure $ normalizeType t

-- | Given an expression and a list of definitions, build a typed environment and infer the type
-- | of the expression in the context of the typed environment.
tryInferTypeInContext :: List Definition -> TypeTree -> Either TypeError Type
tryInferTypeInContext defs expr = case tryInferEnvironment defs of
  Left typeError -> Left typeError
  Right typedEnv -> runInferWith typedEnv true (inferExprToType expr)

-- | Given an expression and a list of definitions, build a typed environment and infer the type
-- | of the expression tree as well as all the sub expressions in the context of the typed
-- | environment.
tryInferExprInContext :: List Definition -> TypeTree -> Either TypeError TypeTree
tryInferExprInContext defs expr = case tryInferEnvironment defs of
  Left typeError -> Left typeError
  Right typedEnv -> runInferWith typedEnv true (inferExpr expr)

-- | Perform the type inference on a given expression tree and return the normalized typed tree.
inferExpr :: TypeTree -> Infer TypeTree
inferExpr expr = do
  let indexedTree = makeIndexedTree expr
  Tuple t c <- infer indexedTree
  uni <- solveConstraints c
  let expr' = assignTypes uni indexedTree
  pure $ normalizeTypeTree (apply uni.subst expr')

-- | Represents a result of the type inference process.
type DebugInferResult = { expr :: TypeTree, constraints :: Constraints, subst :: Subst }

-- | Debug version of `inferExpr`.
inferExprDebug :: TypeTree -> Infer DebugInferResult
inferExprDebug expr = do
  let indexedTree = makeIndexedTree expr
  Tuple t c <- infer indexedTree
  uni <- solveConstraints c
  let expr' = normalizeTypeTree (apply uni.subst $ assignTypes uni indexedTree)
  pure { expr: expr', constraints: uni.constraints, subst: uni.subst }

-- | Perform type inference on expression tree and extract top level type.
inferExprToType :: TypeTree -> Infer Type
inferExprToType expr = (extractFromTree >>> \(Meta meta) -> fromMaybe UnknownType meta.mtype) <$> inferExpr expr

-- | Given a list of definitions create a map of definition groups.
buildDefinitionGroups :: List Definition -> Map.Map String (List Definition)
buildDefinitionGroups Nil = Map.empty
buildDefinitionGroups (def@(Def str bin exp):Nil) = Map.singleton str (def:Nil)
buildDefinitionGroups (def@(Def str bin exp):defs) = case binList of
  Just list -> Map.insert str (def:list) defMap
  Nothing -> Map.insert str (def:Nil) defMap
  where
  defMap = buildDefinitionGroups defs
  binList = Map.lookup str defMap

-- +----------------------------------+
-- | Type Tree and Type Normalization |
-- +----------------------------------+

-- | Given an int generate an array of integers used as indices into the alphabet in `getNthName`.
-- | Example: map indexList (700..703) => [[24,25],[25,25],[0,0,0],[1,0,0]]
indexList :: Int -> Array Int
indexList n | n `div` 26 > 0 = n `mod` 26 `Array.cons` indexList (n `div` 26 - 1)
indexList n = [n `mod` 26]

-- | Given an int choose a new name. We choose names simply by indexing into the alphabet. As soon
-- | "z" is reached, begin with "aa" and so on.
-- | Example: map getNthName (700..703) => ["zy","zz","aaa","aab"]
getNthName :: Int -> String
getNthName = indexList >>> Array.reverse >>> toCharArray >>> String.fromCharArray
  where toCharArray = map (((+) 97) >>> Char.fromCharCode >>> fromMaybe 'X')

-- | The state used when normalizing types and type trees.
type NormalizationState =
  { count :: Int         -- ^ Counter, used to keep track of which name should be used next.
  , env :: Map TVar TVar -- ^ Map old type variable names (like `t_4`) to new ones (like `d`).
  }

-- | An empty normalization state.
emptyNormalizationState :: NormalizationState
emptyNormalizationState = { count: 0, env: Map.empty }

-- | Normalize the given type.
normalizeType :: Type -> Type
normalizeType t = evalState (normalizeType' t) emptyNormalizationState

-- | Normalize the given type error.
normalizeTypeError :: TypeError -> TypeError
normalizeTypeError (UnificationFail t1 t2) = UnificationFail (normalizeType t1) (normalizeType t2)
normalizeTypeError (InfiniteType tvar t) = InfiniteType (prettyPrintType $ normalizeType $ TypVar tvar) (normalizeType t)
normalizeTypeError error = error

-- | Normalize the given typed expression tree.
normalizeTypeTree :: TypeTree -> TypeTree
normalizeTypeTree expr = evalState (normalizeTypeTree' expr) emptyNormalizationState

-- | Normalize the type in the given operator tuple.
normalizeOp' :: (Tuple Op Meta) -> State NormalizationState (Tuple Op Meta)
normalizeOp' (Tuple op (Meta meta)) = do
  opType' <- normalizeMType' meta.mtype
  pure $ Tuple op (Meta $ meta {mtype = opType'})

-- | Normalize the given typed binding.
normalizeBinding' :: TypedBinding -> State NormalizationState TypedBinding
normalizeBinding' = AST.traverseBinding
  (\(Meta meta) -> do
    mt <- normalizeMType' meta.mtype
    pure $ Meta meta {mtype = mt})

-- | Normalize the given typed expression tree.
normalizeTypeTree' :: TypeTree -> State NormalizationState TypeTree
normalizeTypeTree' = AST.traverseTree
  normalizeBinding'
  normalizeOp'
  (\(Meta m) -> do
    mt' <- normalizeMType' m.mtype
    pure $ Meta (m {mtype = mt'}))

-- | Normalize the given type. The only interesting part is the type variable case, where all the
-- | work is done.
normalizeType' :: Type -> State NormalizationState Type
normalizeType' t = case t of
  TypVar var -> do
    { env: env } <- get
    -- If the type variable is not yet in the environment, create a new corresponding type variable
    -- and add it to the environment. If the type variable already has a corresponding renamed
    -- variable, just return it.
    case Map.lookup var env of
      Just var' -> pure $ TypVar var'
      Nothing -> do
        { count: count } <- get
        let newVarName = getNthName count
        let env' = Map.insert var newVarName env
        put { count: count + 1, env: env' }
        pure $ TypVar newVarName
  TypArr t1 t2 -> do
    t1' <- normalizeType' t1
    t2' <- normalizeType' t2
    pure $ TypArr t1' t2'
  TList t -> do
    t' <- normalizeType' t
    pure $ TList t'
  TTuple ts -> do
    ts' <- traverse normalizeType' ts
    pure $ TTuple ts'
  TTypeCons n ts -> do
    ts' <- traverse normalizeType' ts
    pure $ TTypeCons n ts'
  a -> pure a

-- | Use `normalizeType'` on `Maybe Type`.
normalizeMType' :: Maybe Type -> State NormalizationState (Maybe Type)
normalizeMType' = traverse normalizeType'
