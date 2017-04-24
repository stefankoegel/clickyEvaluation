module TypeChecker where

import Control.Monad.Except as Ex
import Control.Monad.RWS (ask, evalRWST, local)
import Control.Monad.RWS.Trans (RWST)
import Control.Monad.State (State, evalState, put, get)
import Data.Array as Array
import Data.Bifunctor (rmap)
import Data.Char as Char
import Data.Either (Either(..))
import Data.Foldable (intercalate, fold, foldl, foldr, foldMap, elem)
import Data.List (List(..), (:), concat, concatMap, filter, reverse, singleton, unzip, zip)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(Tuple), snd, fst, uncurry)
import Partial.Unsafe (unsafeCrashWith)
import Prelude (
  class Eq, class Show, Unit,
  ($), (+), (-), (<$>), (<<<), (<>), (==), (>), (>>=), (>>>),
  bind, const, div, flip, id, map, mod, negate, not, otherwise, pure, show)

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
  (map ppTVAndType >>> intercalate ",\n")
  (Map.toList subst)
  where ppTVAndType (Tuple tv t) = "\t" <> tv <> " ~ " <> prettyPrintType t

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
  (map ppTVAndScheme >>> intercalate ",\n")
  (Map.toList env)
  where ppTVAndScheme (Tuple tv scheme) = "\t" <> tv <> " :: " <> ppScheme scheme

-- | Create an empty type environment.
emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv Map.empty

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
  (Map.toList >>> map snd) constraints.mapped <>
  map snd constraints.unmapped

toConstraintAndIndexLists :: Constraints -> Tuple (List Index) (List Constraint)
toConstraintAndIndexLists constraints =
  unzip constraints.unmapped <>
  unzip (Map.toList constraints.mapped)

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
    (map ppTuple >>> intercalate ",\n")
    (Map.toList constraints.mapped) <> "\n" <>
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
type InferEnv = { env :: TypeEnv, stopOnError :: Boolean }

type InferNew a = (RWST
  InferEnv              -- ^ Read from the type environment.
  Unit
  Unique                -- ^ The infer state.
  (Ex.Except TypeError) -- ^ Catch type errors.
  a)

-- | Choose a fresh type variable name.
freshTVarNew :: InferNew TVar
freshTVarNew = do
  Unique s <- get
  put (Unique { count: (s.count + 1) })
  pure $ "t_" <> show s.count

-- | Choose a fresh type variable.
freshNew :: InferNew Type
freshNew = TypVar <$> freshTVarNew

-- | Create a monotype from the given type scheme.
instantiateNew :: Scheme -> InferNew Type
instantiateNew (Forall as t) = do
  as' <- traverse (const freshNew) as
  let s = Map.fromFoldable $ zip as as'
  pure $ apply s t

-- | Lookup a type in the type environment.
lookupEnvNew :: TVar -> InferNew MType
lookupEnvNew tvar = do
  { env: (TypeEnv env) } <- ask
  case Map.lookup tvar env of
    Nothing -> pure Nothing
    Just scheme  -> instantiateNew scheme >>= (pure <<< Just)

-- | Run the type inference and catch type errors. Note that the only possible errors are:
-- |   * `UnboundVariable`
-- |   * `NoInstanceOfEnum`
-- |   * `UnknownError`
-- | All other errors can only be encountered during the constraint solving phase.
runInferNew :: forall a. TypeEnv -> Boolean -> InferNew a -> Either TypeError a
runInferNew env stopOnError m = rmap fst $ Ex.runExcept $ evalRWST m inferEnv initUnique
  where inferEnv = { env: env, stopOnError: stopOnError }

-- | Given an indexed expression, add a type constraint using the given type and expression index.
returnWithConstraint :: IndexedTypeTree -> Type -> InferNew (Tuple Type Constraints)
returnWithConstraint expr t = do
  tv <- freshNew
  pure $ Tuple tv (constraintSingleMapped (index expr) tv t)

-- TODO: Where can this be used instead of `returnWithConstraint`?
returnDirect :: IndexedTypeTree -> Type -> InferNew (Tuple Type Constraints)
returnDirect expr t = pure $ Tuple t (constraintSingleMapped (index expr) t t)

returnWithTypeError :: IndexedTypeTree -> TypeError -> InferNew (Tuple Type Constraints)
returnWithTypeError expr typeError = do
  { stopOnError: stopOnError } <- ask
  if stopOnError
    then Ex.throwError typeError
    else do
      tv <- freshNew
      pure $ Tuple tv (constraintError (index expr) tv typeError)

setTypeConstraintFor' :: Index -> Type -> Type -> Constraints
setTypeConstraintFor' idx t1 t2 = constraintSingleMapped idx t1 t2

-- | Setup a new type constraint for a given expression node.
setTypeConstraintFor :: IndexedTypeTree -> Type -> Type -> Constraints
setTypeConstraintFor expr t1 t2 = constraintSingleMapped (index expr) t1 t2

-- | Setup a new type constraint mapping a type to itself.
setSingleTypeConstraintFor :: IndexedTypeTree -> Type -> Constraints
setSingleTypeConstraintFor expr t = constraintSingleMapped (index expr) t t

setSingleTypeConstraintFor' :: Index -> Type -> Constraints
setSingleTypeConstraintFor' idx t = constraintSingleMapped idx t t

-- | Set a constraint not referring to a node.
setConstraintFor :: IndexedTypeTree -> Type -> Type -> Constraints
setConstraintFor expr t1 t2 = constraintSingleUnmapped (index expr) t1 t2

setConstraintFor' :: Index -> Type -> Type -> Constraints
setConstraintFor' idx t1 t2 = constraintSingleUnmapped idx t1 t2

-- | Determine the type of the given operator.
getOpType :: Op -> InferNew Type
getOpType op = case op of
    Composition -> do
      a <- freshNew
      b <- freshNew
      c <- freshNew
      pure $ (b `TypArr` c) `TypArr` ((a `TypArr` b) `TypArr` (a `TypArr` c))
    Power -> pure intToIntToIntType
    Mul -> pure intToIntToIntType
    Add -> pure intToIntToIntType
    Sub -> pure intToIntToIntType
    Colon -> do
      a <- freshNew
      pure $ a `TypArr` ((AD $ TList a) `TypArr` (AD $ TList a))
    Append -> do
      a <- freshNew
      pure $ (AD $ TList a) `TypArr` ((AD $ TList a) `TypArr` (AD $ TList a))
    Equ -> toBoolType
    Neq -> toBoolType
    Lt -> toBoolType
    Leq -> toBoolType
    Gt -> toBoolType
    Geq -> toBoolType
    And -> pure $ boolType `TypArr` (boolType `TypArr` boolType)
    Or -> pure $ boolType `TypArr` (boolType `TypArr` boolType)
    Dollar -> do
      a <- freshNew
      b <- freshNew
      pure $ (a `TypArr` b) `TypArr` (a `TypArr` b)
    _ -> pure UnknownType
  where
  -- The type `a -> a -> Bool`.
  toBoolType = do
    a <- freshNew
    pure $ a `TypArr` (a `TypArr` boolType)

-- | Given an operator tuple, determine the operator type and put a type constraint on the
-- | corresponding expression node.
inferOpNew :: Tuple Op MIType -> InferNew (Tuple Type Constraints)
inferOpNew (Tuple (InfixFunc name) (Tuple _ idx)) = do
  Tuple t c <- inferNew (Atom (Tuple Nothing idx) (Name name))
  pure $ Tuple t c
inferOpNew opTuple@(Tuple op _) = do
  t <- getOpType op
  let c = setSingleTypeConstraintFor' (opIndex opTuple) t
  pure $ Tuple t c

-- | Traverse the given type tree and collect type constraints.
inferNew :: IndexedTypeTree -> InferNew (Tuple Type Constraints)
inferNew ex = case ex of

  Atom _ atom@(Bool _) -> returnWithConstraint ex boolType
  Atom _ atom@(Char _) -> returnWithConstraint ex charType
  Atom _ atom@(AInt _) -> returnWithConstraint ex intType
  Atom _ atom@(Name name) -> case name of
    -- Built-in functions.
    "mod" -> returnWithConstraint ex intToIntToIntType
    "div" -> returnWithConstraint ex intToIntToIntType
    -- Try to find the variable name in the type environment.
    _     -> do
      mt <- lookupEnvNew name
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
    Tuple t2 c2 <- withEnv bindingEnv (inferNew e)
    -- Given a list of binding types, construct the corresponding type. Conceptually:
    -- `(\a b c -> ...) => typeof a -> typeof b -> typeof c -> t2`
    let lambdaType = toArrowType (t1 <> (t2 : Nil))
    -- Set the type for the current expression.
    let c3 = setSingleTypeConstraintFor ex lambdaType
    pure $ Tuple lambdaType (c1 <+> c2 <+> c3)

  -- Example expression: `mod 2 3`:
  -- The subexpression `e` refers to `mod`, the expression list `es` refers to `2` and `3`.
  App _ e es -> do
    Tuple t1 c1 <- inferNew e
    -- Collect the constraints and type information of the given parameters.
    Tuple ts cs <- unzip <$> traverse inferNew es
    let c2 = foldConstraints cs
    tv <- freshNew
    -- The function type has to match up with the given parameter types.
    let c3 = setConstraintFor ex t1 (toArrowType (ts <> (tv : Nil)))
    -- The application expression has the type referred to by type variable `tv`.
    let c4 = setSingleTypeConstraintFor ex tv
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4)

  LetExpr _ defs e -> do
    -- Construct the binding environment and use it for the type inference of the body
    Tuple bindingEnv c1 <- makeBindingEnvLet defs
    Tuple t2 c2 <- withEnv bindingEnv (inferNew e)
    -- Set the type for the current expression.
    let c3 = setSingleTypeConstraintFor ex t2
    pure $ Tuple t2 (c1 <+> c2 <+> c3)

  IfExpr _ cond l r -> do
    Tuple t1 c1 <- inferNew cond
    Tuple t2 c2 <- inferNew l
    Tuple t3 c3 <- inferNew r
    -- In the condition node: t1 has to be a `Bool`.
    -- Because the `cond` expression has already been given a mapped constraint, we have to use
    -- `setConstraintFor` and not `setTypeConstraintFor`.
    let c4 = setConstraintFor cond t1 boolType
    -- In the node of the if expression: t2 and t3 have to be equal.
    let c5 = setTypeConstraintFor ex t2 t3
    pure $ Tuple t2 (c1 <+> c2 <+> c3 <+> c4 <+> c5)

  Binary _ op e1 e2 -> do
    Tuple t1 c1 <- inferOpNew op
    Tuple t2 c2 <- inferNew e1
    Tuple t3 c3 <- inferNew e2
    tv <- freshNew
    let c4 = setConstraintFor ex t1 (t2 `TypArr` (t3 `TypArr` tv))
    let c5 = setSingleTypeConstraintFor ex tv
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4 <+> c5)

  Unary _ op e -> do
    Tuple t1 c1 <- inferOpNew op
    Tuple t2 c2 <- inferNew e
    tv <- freshNew
    let c3 = setConstraintFor ex t1 (t2 `TypArr` tv)
    let c4 = setSingleTypeConstraintFor ex tv
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4)

  -- Expressions of the form `(4+)`.
  SectL _ e op -> do
    Tuple t1 c1 <- inferOpNew op
    Tuple left c2 <- inferNew e
    right <- freshNew
    tv <- freshNew
    let c3 = setConstraintFor ex t1 (left `TypArr` (right `TypArr` tv))
    let c4 = setSingleTypeConstraintFor ex (right `TypArr` tv)
    pure $ Tuple (right `TypArr` tv) (c1 <+> c2 <+> c3 <+> c4)

  -- Expressions of the form `(^2)`.
  SectR _ op e -> do
    Tuple t1 c1 <- inferOpNew op
    Tuple right c2 <- inferNew e
    left <- freshNew
    tv <- freshNew
    let c3 = setSingleTypeConstraintFor ex (left `TypArr` tv)
    let c4 = setConstraintFor ex t1 (left `TypArr` (right `TypArr` tv))
    pure $ Tuple (left `TypArr` tv) (c1 <+> c2 <+> c3 <+> c4)

  -- Expressions of the form `(:)`.
  PrefixOp _ op -> do
    Tuple t1 c1 <- inferOpNew op
    tv <- freshNew
    let c2 = setSingleTypeConstraintFor ex t1
    pure $ Tuple t1 (c1 <+> c2)

  -- Empty lists.
  List _ Nil -> do
    -- We use `tv` as type variable for the list expression and `tv2` for type of the list
    -- elements.
    tv <- freshNew
    tv2 <- freshNew
    -- tv ~ [tv2]
    let listType = AD $ TList tv2
    let c = setTypeConstraintFor ex tv listType
    pure $ Tuple listType c

  -- Single element lists.
  List _ (e : Nil) -> do
    -- Get the constraints and type of the first list element.
    Tuple t c1 <- inferNew e
    -- The list expression has the type `[t1]` where `t1` denotes the type of the first list
    -- element.
    tv <- freshNew
    let listType = AD $ TList t
    let c2 = setTypeConstraintFor ex tv listType
    pure $ Tuple listType (c1 <+> c2)

  -- List with multiple elements.
  List _ (e : es) -> do
    Tuple t1 c1  <- inferNew e
    Tuple ts cs  <- unzip <$> traverse inferNew es
    -- Also add constraints for the rest of the list elements. All elements should have the same
    -- type as the first list element.
    let c2 = foldConstraints (map (setConstraintFor ex t1) ts)
    let c3 = foldConstraints cs
    -- The list expression has the type `[t1]` where `t1` denotes the type of the first list
    -- element.
    tv <- freshNew
    let listType = AD $ TList t1
    let c4 = setTypeConstraintFor ex tv listType
    pure $ Tuple listType (c1 <+> c2 <+> c3 <+> c4)

  NTuple _ es -> do
    Tuple ts cs <- unzip <$> traverse inferNew es
    tv <- freshNew
    let tupleType = AD $ TTuple ts
    let c = setTypeConstraintFor ex tv tupleType
    pure $ Tuple tupleType (foldConstraints cs <+> c)

  ArithmSeq _ first step last -> do
    -- Infer the type of the beginning expression, which always exists.
    Tuple t1 c1 <- inferRequireEnumType first
    -- Try to infer the types of the `step` and `last` expression if existing and set the
    -- constraints accordingly.
    c2 <- tryInferRequireEnumType step t1
    c3 <- tryInferRequireEnumType last t1
    tv <- freshNew
    let c4 = setTypeConstraintFor ex tv (AD $ TList t1)
    pure $ Tuple tv (c1 <+> c2 <+> c3 <+> c4)

  ListComp  _ body quals -> do
    -- Infer the types of the qual expressions, gather the constraints and the binding environment.
    Tuple bindingEnv c1 <- makeBindingEnvListComp quals
    Tuple t1 c2 <- withEnv bindingEnv (inferNew body)
    tv <- freshNew
    let c4 = setTypeConstraintFor ex tv (AD $ TList t1)
    pure $ Tuple tv (c1 <+> c2 <+> c4)

-- +-----------------------------------+
-- | Bindings and Binding Environments |
-- +-----------------------------------+

-- | Choose a new type variable for the given binding and add typing information for the node
-- | index. This function is needed whenever binding environments have to be built: lambda and let
-- | expressions as well as list comprehensions.
makeBindingEnv :: IndexedTypedBinding -> InferNew (Triple Type TVarMappings Constraints)
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
    tv <- freshNew
    let c = setSingleTypeConstraintFor' (bindingIndex binding) tv
    pure $ Triple tv (Tuple name (Forall Nil tv) : Nil) c

  ConsLit _ b1 b2 -> do
    Triple t1 m1 c1 <- makeBindingEnv b1
    Triple t2 m2 c2 <- makeBindingEnv b2
    let c3 = setTypeConstraintFor' (bindingIndex binding) (AD $ TList t1) t2
    pure $ Triple (AD $ TList t1) (m1 <> m2) (c1 <+> c2 <+> c3)

  ListLit _ bs -> do
    Triple ts ms cs <- unzip3 <$> traverse makeBindingEnv bs
    listElementConstraints <- setListConstraints ts
    t <- listType ts
    pure $ Triple t (concat ms) (foldConstraints cs <+> listElementConstraints)

  NTupleLit _ bs -> do
    Triple ts ms cs <- unzip3 <$> traverse makeBindingEnv bs
    let c = setSingleTypeConstraintFor' (bindingIndex binding) (AD $ TTuple ts)
    pure $ Triple (AD $ TTuple ts) (concat ms) (foldConstraints cs <+> c)

  where
  -- Go through the list of given types and set constraints for every to elements of the list.
  setListConstraints Nil = pure emptyConstraints
  setListConstraints (t:Nil) = do
    let c = setSingleTypeConstraintFor' (bindingIndex binding) (AD $ TList t)
    pure c
  setListConstraints (t1:t2:ts) = do
    cs <- setListConstraints (t2:ts)
    let c = setConstraintFor' (bindingIndex binding) t1 t2 <+> cs
    pure c

  -- Given a list of types occurring in a list, determine the list type (choose the first element).
  listType Nil = freshNew >>= \tv -> pure $ AD $ TList tv
  listType (t:_) = pure $ AD $ TList t

-- | Extend the type environment with the new mappings for the evaluation of `m`.
withEnv :: forall a. TVarMappings -> InferNew a -> InferNew a
withEnv mappings m = local (scope mappings) m
  where
  scope mappings inferEnv = { env: removeMultiple inferEnv.env (map fst mappings) `extendMultiple` mappings
                            , stopOnError: inferEnv.stopOnError
                            }

-- +--------------------+
-- | Lambda Expressions |
-- +--------------------+

-- | Go through list of given bindings and accumulate an corresponding type. Gather environment
-- | information and setup the type information for every binding tree node.
makeBindingEnvLambda :: List IndexedTypedBinding
                     -> InferNew (Triple (List Type) TVarMappings Constraints)
makeBindingEnvLambda bindings = do
  Triple ts ms cs <- unzip3 <$> traverse makeBindingEnv bindings
  pure $ Triple ts (concat ms) (foldConstraints cs)

-- +----------------------------------------+
-- | Let Expressions and List Comprehension |
-- +----------------------------------------+

-- | Associate a binding with a corresponding expression. Therefore, infer the given expression
-- | and associate its type with the binding.
associate :: IndexedTypedBinding -> IndexedTypeTree -> InferNew (Tuple TVarMappings Constraints)
associate binding expr = do
  Triple bt m _ <- makeBindingEnv binding
  Tuple et c1 <- inferNew expr
  { env: env } <- ask
  let uni = runSolve c1
      c2 = setSingleTypeConstraintFor' (bindingIndex binding) et
      -- Substitute the bound variables with the corresponding polytype.
      scheme = generalize (apply uni.subst env) (apply uni.subst et)
  -- Map the type scheme on the binding (and sub-bindings).
  Tuple m' c3 <- mapSchemeOnTVarMappings binding m scheme
  pure $ Tuple m' (uni.constraints <+> c1 <+> c2 <+> c3)

-- | Determine the common type variables used.
commonFreeTVars :: List TVar -> Type -> List TVar
commonFreeTVars tvars t = Set.toUnfoldable $ ftv t `Set.intersection` ftv (map TypVar tvars)

-- | Given a mapping, representing a binding, and a scheme, try to map the scheme onto the mapping.
-- | Example expression: `let (a, b) = (\x -> x, "cake") in a b`
-- | Here we get the mapping `{ a :: t_0, b :: t_1 }` and infer the scheme
-- | `forall t_2. (t_2 -> t_2, [Char])`. The task is now to map the scheme components onto the
-- | mapping, resulting in the mapping `{ a :: forall t_2. t_2 -> t_2, b :: [Char] }`.
mapSchemeOnTVarMappings :: IndexedTypedBinding -> TVarMappings -> Scheme
                        -> InferNew (Tuple TVarMappings Constraints)
mapSchemeOnTVarMappings binding mappings scheme = f (binding : Nil) mappings (scheme : Nil)
  where
  f :: List IndexedTypedBinding -> TVarMappings -> List Scheme
    -> InferNew (Tuple TVarMappings Constraints)
  f (binding@ConsLit _ b1 b2 : Nil) (m : ms) (Forall tvs (AD (TList t)) : ss) = do
    Tuple first c1 <- f (b1 : Nil) (m : Nil) (Forall tvs t : Nil)
    Tuple second c2 <- f (b2 : Nil) ms (Forall tvs (AD (TList t)) : Nil)
    let c3 = setSingleTypeConstraintFor' (bindingIndex binding) (AD $ TList t)
    pure $ Tuple (first <> second) (c1 <+> c2 <+> c3)
  f (binding@ListLit _ bs : Nil) ms (Forall tvs (AD (TList t)) : ss) = do
    Tuple ms cs <- unzip <$> traverse (\(Tuple b m) ->
      mapSchemeOnTVarMappings b (m : Nil) (Forall tvs t))
      (zip bs ms)
    let c = setSingleTypeConstraintFor' (bindingIndex binding) (AD $ TList t)
    pure $ Tuple (fold ms) (foldConstraints cs <+> c)
  f (binding@NTupleLit _ (b:bs) : Nil) (m:ms) (Forall tvs (AD (TTuple (t:ts))) : ss) = do
    Tuple m1 c1 <- mapSchemeOnTVarMappings b (m:Nil) (Forall tvs t)
    Tuple m2 c2 <- f bs ms (map (Forall tvs) ts <> ss)
    let c3 = setSingleTypeConstraintFor' (bindingIndex binding) (AD $ TTuple (t:ts))
    pure $ Tuple (m1 <> m2) (c1 <+> c2 <+> c3)
  f (binding@(Lit _ b) : Nil) (Tuple tv oldScheme : ms) (Forall tvs t : Nil) = do
    let c = setSingleTypeConstraintFor' (bindingIndex binding) t
    let tVarMappings = Tuple tv (Forall (commonFreeTVars tvs t) t) : Nil
    pure $ Tuple tVarMappings c
  f _ _ _ = pure $ Tuple Nil emptyConstraints

-- | Given a list of bindings and corresponding expressions, associate the bindings with the
-- | expressions and collect the type variable/scheme mappings as well as the constraints.
associateAll :: List IndexedTypedBinding -> List IndexedTypeTree -> Tuple TVarMappings Constraints
             -> InferNew (Tuple TVarMappings Constraints)
associateAll (b:bs) (e:es) (Tuple ms cs) = do
  Tuple m c <- associate b e
  withEnv m $ associateAll bs es (Tuple (ms <> m) (cs <+> c))
associateAll _ _ x = pure x

-- | Construct a binding environment to be used in the inference of a let expression.
makeBindingEnvLet :: List (Tuple IndexedTypedBinding IndexedTypeTree)
                  -> InferNew (Tuple TVarMappings Constraints)
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
makeBindingEnvListComp :: List IndexedQualTree -> InferNew (Tuple TVarMappings Constraints)
makeBindingEnvListComp quals = f quals Nil emptyConstraints
  where f (qual:quals) ms cs = do
          -- Infer the type, set constraints and accumulate binding environment for the current
          -- qual expression. Then pass the environment and constraints and continue with the next
          -- qual expression.
          Tuple m c <- makeBindingEnvQual qual
          withEnv m $ f quals (ms <> m) (cs <+> c)
        f Nil ms cs = pure (Tuple ms cs)

-- | Set constraints and build binding environment for the given qual expression.
makeBindingEnvQual :: IndexedQualTree -> InferNew (Tuple TVarMappings Constraints)
makeBindingEnvQual qual = case qual of
  -- Just associate the binding with the expression.
  Let _ binding expr -> associate binding expr
  -- Generate the binding environment for the binding and infer the generator expression.
  Gen _ binding genExpr -> do
    Triple t1 m c1 <- makeBindingEnv binding
    Tuple t2 c2 <- inferNew genExpr
    let c3 = setConstraintFor genExpr (AD $ TList t1) t2
    pure $ Tuple m (c1 <+> c2 <+> c3)
  -- Only infer the expression type and set the constraints.
  Guard _ guardExpr -> do
    Tuple _ c <- inferNew guardExpr
    pure $ Tuple Nil c

-- +----------------------+
-- | Arithmetic Sequences |
-- +----------------------+

-- | If the given expression is non-empty, infer the type, set and return the constraints.
tryInferRequireEnumType :: Maybe IndexedTypeTree -> Type -> InferNew Constraints
tryInferRequireEnumType (Just expr) t1 = do
  Tuple t2 c1 <- inferRequireEnumType expr
  let c2 = setSingleTypeConstraintFor expr t2
  let c3 = setConstraintFor expr t1 t2
  pure (c1 <+> c2 <+> c3)
tryInferRequireEnumType _ t = pure emptyConstraints

-- | Infer the type of the given expression, then run the constraint solving in order to retrieve
-- | the expression type. If the type is not an enum type, return with the corresponding type
-- | error.
inferRequireEnumType :: IndexedTypeTree -> InferNew (Tuple Type Constraints)
inferRequireEnumType expr = do
  Tuple t c <- inferNew expr
  let uni = runSolve c
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
initialUnifier constraints = { subst: unknownSubst, constraints: constraints }
  where unknownSubst = getUnknownSubst $ toConstraintList constraints

-- | Collect the substitutions in the unifier and catch occurring type errors.
runSolve :: Constraints -> Unifier
runSolve constraints = let uni = solver (initialUnifier constraints)
                           errorConstraints = uni.constraints
                       in { subst: uni.subst, constraints: errorConstraints <+> constraints }

-- | Bind the given type variable to the given type and return the resulting substitution.
bindTVar ::  TVar -> Type -> Either TypeError Subst
bindTVar tv t
  | t == (TypVar tv) = pure $ nullSubst
  | occursCheck tv t = Left $ normalizeTypeError $ InfiniteType tv t
  | otherwise = pure $ Map.singleton tv t

-- | Try to unify the given types and return the resulting substitution or the occurring type
-- | error.
unifies :: Type -> Type -> Either TypeError Subst
unifies UnknownType t = pure nullSubst
unifies t UnknownType = pure nullSubst
unifies (TypArr l1 r1) (TypArr l2 r2) = do
  s1 <- unifies l1 l2
  s2 <- unifies (apply s1 r1) (apply s1 r2)
  pure $ s2 `compose` s1
unifies (TypVar tv) t = tv `bindTVar` t
unifies t (TypVar tv) = tv `bindTVar` t
unifies (TypCon c1) (TypCon c2) | c1 == c2 = pure nullSubst
unifies (AD a) (AD b) | a == b = pure nullSubst
unifies (AD a) (AD b) = unifiesAD a b
unifies t1 t2 = Left $ normalizeTypeError $ UnificationFail t1 t2

-- | Try to unify the given AD types and return the resulting substitution or the occurring type
-- | error.
unifiesAD :: AD -> AD -> Either TypeError Subst
unifiesAD (TList l1) (TList l2) = unifies l1 l2
unifiesAD (TTuple (a:as)) (TTuple (b:bs)) = do
  s1 <- unifiesAD (TTuple as) (TTuple bs)
  s2 <- unifies a b
  pure $ s1 `compose` s2
unifiesAD (TTuple Nil) (TTuple Nil) = pure nullSubst
unifiesAD t1 t2 = Left $ normalizeTypeError $ UnificationFail (AD t1) (AD t2)

-- | Given a list of constraints return a tuple containing:
-- | 1. List of all constraints mapping a type variable to another
-- | 2. List of all constraints mapping a type variable to the unknown type.
sortIntoLists :: List Constraint -> Tuple (List Constraint) (List Constraint)
sortIntoLists cs = f cs (Tuple Nil Nil)
  where
  f Nil tuple = tuple
  f (c@(Constraint t UnknownType) : cs) (Tuple pairs unknowns) = f cs (Tuple pairs (c : unknowns))
  f (c@(Constraint UnknownType t) : cs) (Tuple pairs unknowns) = f cs (Tuple pairs (c : unknowns))
  f (c : cs) (Tuple pairs unknowns) = f cs (Tuple (c : pairs) unknowns)

-- | Create a substitution from the given constraint list. Note that only mappings from a type
-- | variable to the unknown type are preserved.
constraintsToSubst :: List Constraint -> Subst
constraintsToSubst cs = foldr compose nullSubst (map constraintToSubst cs)

-- | Create a substitution from the given constraint. Note that only mappings from a type variable
-- | to the unknown type are preserved.
constraintToSubst :: Constraint -> Subst
constraintToSubst (Constraint (TypVar tv) UnknownType) = Map.singleton tv UnknownType
constraintToSubst (Constraint UnknownType (TypVar tv)) = Map.singleton tv UnknownType
constraintToSubst _ = nullSubst

-- | Replace every constraint mapping arrow types to one another `t0 -> t1 = t2 -> t3`, replace
-- | it with corresponding constraints (`t0 = t2` and `t1 = t3`).
replaceArrowType :: List Constraint -> List Constraint
replaceArrowType (Constraint l@(TypArr _ _) r@(TypArr _ _) : cs) = f l r <> replaceArrowType cs
  where
  f (TypArr l1 l2@(TypArr _ _)) (TypArr r1 r2) = Constraint l1 r1 : f l2 r2
  f (TypArr l1 l2) (TypArr r1 r2) = Constraint l1 r1 : Constraint l2 r2 : Nil
  f _ _ = Nil
replaceArrowType (c : cs) = c : replaceArrowType cs
replaceArrowType Nil = Nil

-- | Given a list of constraints, find the substitution mapping type variables to unknown types.
getUnknownSubst :: List Constraint -> Subst
getUnknownSubst cs = uncurry (applyUnknowns nullSubst) lists
  where lists = sortIntoLists (replaceArrowType cs)

applyUnknowns :: Subst -> List Constraint -> List Constraint -> Subst
applyUnknowns subst pairs Nil = subst
applyUnknowns subst pairs unknowns = uncurry (applyUnknowns (newSubst `compose` subst)) lists
  where
  newSubst = constraintsToSubst unknowns
  lists = sortIntoLists $ newSubst `apply` pairs

-- | Try to solve the constraints.
-- TODO: Cleanup.
solver :: Unifier -> Unifier
solver { subst: beginningSubst, constraints: constraints } =
  solver' beginningSubst emptyConstraints indices (apply beginningSubst constraintList)
  where
  lists = toConstraintAndIndexLists constraints
  indices = fst lists
  constraintList = snd lists

  solver' :: Subst -> Constraints -> List Index -> List Constraint -> Unifier
  solver' subst errors (idx:idxs) (ConstraintError typeError : rest) =
    solver' subst errors idxs rest
  solver' subst errors (idx:idxs) (Constraint t1 t2 : rest) = case unifies t1 t2 of
    Left error@(InfiniteType _ _) -> { subst: nullSubst, constraints: constraintError idx t1 error }
    Left error ->
      -- Get type variable name at current index.
      case Map.lookup idx constraints.mapped of
        Just (Constraint (TypVar tv) _) -> case Map.lookup tv subst of
          Just UnknownType -> solver' subst errors idxs rest
          _ -> do
            -- Give the constraint for the node at the current index an unknown type and restart
            -- the constraint solving.
            let errors' = constraintError idx (TypVar tv) error <+> errors
            let mapped' = Map.insert idx (Constraint (TypVar tv) UnknownType) constraints.mapped
            let constraints' = { unmapped: constraints.unmapped, mapped: mapped' }
            let lists' = toConstraintAndIndexLists constraints'
            let unknownSubst = getUnknownSubst (snd lists')
            let subst' = beginningSubst `compose` unknownSubst
            solver' subst' errors' (fst lists') (apply unknownSubst $ snd lists')
        _ -> solver' subst errors idxs rest
    Right subst1 -> solver' (subst1 `compose` subst) errors idxs (apply subst1 rest)
  -- Worked through all the constraints.
  solver' subst errorConstraints _ _ = { subst: subst, constraints: errorConstraints }

-- TODO: Change type to `Unifier -> IndexedTypeTree -> TypeTree`?
-- | Go through tree and assign every tree node its type. In order to do this we rely on the node
-- | indices.
assignTypes :: Unifier -> IndexedTypeTree -> IndexedTypeTree
assignTypes { subst: subst, constraints: constraints } expr = treeMap id fb fo f expr
  where
  f (Tuple _ idx) = Tuple (lookupTVar idx) idx
  fo (Tuple op (Tuple _ idx)) = Tuple op (Tuple (lookupTVar idx) idx)
  fb = map f
  lookupTVar idx = case Map.lookup idx constraints.mapped of
    Nothing -> Nothing
    Just (Constraint tv _) -> Just $ subst `apply` tv
    Just (ConstraintError typeError) -> Just typeError

---------------------------------------------------------------------------------------------------

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
   apply s (AD a) = AD (apply s a)
   apply _ (TypeError err) = TypeError err

   ftv UnknownType = Set.empty
   ftv (TypCon  _)         = Set.empty
   ftv (TypVar a)       = Set.singleton a
   ftv (TypArr t1 t2) =  Set.union (ftv t1) (ftv t2)
   ftv (AD a) = ftv a
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
  ftv (TypeEnv env) = ftv $ snd $ unzip $ Map.toList env

instance subAD :: Substitutable AD where
  apply s (TList t) = TList (apply s t)
  apply s(TTuple t) = TTuple (apply s t)
  ftv (TList t) = ftv t
  ftv (TTuple t) = ftv t

instance subQualTree :: (Substitutable a, Substitutable b, Substitutable c) => Substitutable (QualTree a b c) where
  apply s (Gen a b c) = Gen (apply s a) (apply s b) (apply s c)
  apply s (Let a b c) = Let (apply s a) (apply s b) (apply s c)
  apply s (Guard a c) = Guard (apply s a) (apply s c)

  ftv (Gen a b c) = ftv c
  ftv (Let a b c) = ftv c
  ftv (Guard a c) = ftv c

-- | Substitutable instance for the type tree.
instance subTypeTree :: Substitutable (Tree Atom (Binding (Maybe Type)) (Tuple Op (Maybe Type)) (Maybe Type)) where
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
instance subOpTuple :: Substitutable (Tuple Op (Maybe Type)) where
  apply s (Tuple op t) = Tuple op (apply s t)
  ftv (Tuple op t) = ftv t

instance subTypedBinding :: Substitutable a => Substitutable (Binding a) where
  apply s (Lit t atom) = Lit (apply s t) atom
  apply s (ConsLit t b1 b2) = ConsLit (apply s t) (apply s b1) (apply s b2)
  apply s (ListLit t lb) = ListLit (apply s t) (apply s lb)
  apply s (NTupleLit t lb) = NTupleLit (apply s t) (apply s lb)

  ftv = extractFromBinding >>> ftv

initUnique :: Unique
initUnique = Unique { count : 0 }

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

nullSubst :: Subst
nullSubst = Map.empty

occursCheck :: forall a.  (Substitutable a) => TVar -> a -> Boolean
occursCheck a t = a `Set.member` ftv t

compose :: Subst -> Subst -> Subst
compose s1 s2 = map (apply s1) s2 `Map.union` s1

envUnion :: TypeEnv -> TypeEnv -> TypeEnv
envUnion (TypeEnv a) (TypeEnv b) = TypeEnv $ a `Map.union` b

generalize :: TypeEnv -> Type -> Scheme
generalize env t  = Forall as t
  where as = Set.toUnfoldable $ ftv t `Set.difference` ftv env

-- +------------------------------------------------------+
-- | Type Inference for Definitions and Definition Groups |
-- +------------------------------------------------------+
--
-- Definition groups are a list of definitions with the same name (hence belonging together).
-- Ungrouped lists of definitions can be grouped together using `buildGroups`.

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
makeIndexedDefinitionGroups = map makeIndexedDefinitionGroup <<< buildGroups

-- | Given a list of definitions, infer the definition types and create a typed evaluation
-- | environment.
inferTypeEnvironment :: List Definition -> Either TypeError TypeEnv
inferTypeEnvironment defs = accumulateMappings emptyTypeEnv (Map.toList indexedGroups)
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
    Nothing -> case runInferNew env true (inferDefinitionGroup defGroup) of
      Left typeError -> Left typeError
      Right scheme -> Right (Tuple name scheme)

-- | Infer the type scheme of the given definition.
inferDefinitionToScheme :: Definition -> InferNew Scheme
inferDefinitionToScheme def = do
  Triple t m c <- inferDefinition indexedDef
  let uni = runSolve c
  pure $ closeOverType (Tuple uni.subst t)
  where
  indexedDef = fst $ makeIndexedDefinition def 0

inferDefinitions :: List Definition -> InferNew Scheme
inferDefinitions = inferDefinitionGroup <<< makeIndexedDefinitionGroup

inferDefinitionGroup :: List IndexedDefinition -> InferNew Scheme
inferDefinitionGroup group = do
  Tuple t c <- inferGroupNew group
  let uni = runSolve c
  pure $ closeOverType (Tuple uni.subst t)

inferGroupNew :: List IndexedDefinition -> InferNew (Tuple Type Constraints)
inferGroupNew Nil = Ex.throwError $ UnknownError "Can't infer type of empty definition group"
inferGroupNew (def:Nil) = do
  Triple t m c <- inferDefinition def
  pure $ Tuple t c
inferGroupNew (def:defs) = do
  Triple t1 m c1 <- inferDefinition def
  Tuple t2 c2 <- withEnv m (inferGroupNew defs)
  let c3 = setConstraintFor' (definitionIndex def) t1 t2
  pure $ Tuple t1 (c1 <+> c2 <+> c3)

-- | Infer the type of the given indexed definitions and collect bindings and constraints.
inferDefinition :: IndexedDefinition -> InferNew (Triple Type TVarMappings Constraints)
inferDefinition def@(IndexedDef name bindings expr) = do
  tv <- freshNew
  let m = Tuple name (Forall Nil tv) : Nil
  Tuple t1 c1 <- withEnv m (inferNew (Lambda (Tuple Nothing (-1)) bindings expr))
  let c2 = setConstraintFor expr tv t1
  pure $ Triple tv m (c1 <+> c2)

-- | Transform the given polytype to a monotype.
schemeToType :: Scheme -> InferNew Type
schemeToType scheme = do
  t <- instantiateNew scheme
  pure $ normalizeType t

-- | Given an expression and a list of definitions, build a typed environment and infer the type
-- | of the expression in the context of the typed environment.
inferTypeInContext :: List Definition -> TypeTree -> Either TypeError Type
inferTypeInContext defs expr = case inferTypeEnvironment defs of
  Left typeError -> Left typeError
  Right typedEnv -> runInferNew typedEnv true (inferTypeNew expr >>= schemeToType)


-- | Given an expression and a list of definitions, build a typed environment and infer the type
-- | of the expression tree as well as all the sub expressions in the context of the typed
-- | environment.
inferTypeTreeInContext :: List Definition -> TypeTree -> Either TypeError TypeTree
inferTypeTreeInContext defs expr = case inferTypeEnvironment defs of
  Left typeError -> Left typeError
  Right typedEnv -> runInferNew typedEnv true (inferTree expr)

-- | Perform the type inference on a given expression tree and return the normalized typed tree.
inferTree :: TypeTree -> InferNew TypeTree
inferTree expr = do
  let indexedTree = makeIndexedTree expr
  Tuple t c <- inferNew indexedTree
  let uni = runSolve c
      expr' = assignTypes uni indexedTree
  pure $ closeOverTypeTree $ Tuple uni.subst (removeIndices expr')

inferTypeNew :: TypeTree -> InferNew Scheme
inferTypeNew expr = do
  Tuple _ constraints <- inferNew indexedExpr
  let uni = runSolve constraints
      expr = assignTypes uni indexedExpr
  pure $ topLevelNodeScheme uni.subst expr
  where
  indexedExpr = makeIndexedTree expr
  topLevelNodeScheme subst = closeOverType <<< (\t s -> Tuple t s) subst <<< extractType <<< extractFromTree
  extractType (Tuple (Just mt) idx) = mt
  extractType _ = UnknownType

closeOverType :: (Tuple Subst Type) -> Scheme
closeOverType (Tuple sub ty) = generalize emptyTypeEnv (apply sub ty)

overlappingBindings :: List TypedBinding -> List String
overlappingBindings Nil = Nil
overlappingBindings (Cons x Nil) = Nil
overlappingBindings (Cons x xs) = (filter (\y -> elem y (concatMap boundNames xs)) (boundNames x)) <> overlappingBindings xs
  where
    boundNames :: TypedBinding -> (List String)
    boundNames = go
      where
      go (Lit _ (Name name)) = singleton name
      go (ConsLit _ b1 b2)   = go b1 <> go b2
      go (ListLit _ bs)      = foldMap go bs
      go (NTupleLit _ bs)    = foldMap go bs
      go _                 = Nil

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

data InferRes = InferRes IndexedTypeTree Constraints Subst
twoStageInfer :: TypeEnv -> TypeTree -> Either (Tuple TypeError Constraints) InferRes
twoStageInfer env tt = case runInferNew env false (inferNew indexedTT) of
      Left err -> Left (Tuple err emptyConstraints)
      Right (Tuple t constraints) ->
        let uni = runSolve constraints
            expr = assignTypes uni indexedTT
        in Right $ InferRes expr uni.constraints uni.subst
    where
    indexedTT = makeIndexedTree tt

closeOverTypeTree :: (Tuple Subst TypeTree) -> TypeTree
closeOverTypeTree (Tuple s tt) = normalizeTypeTree (apply s tt)

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
  where toCharArray = map (((+) 97) >>> Char.fromCharCode)

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
normalizeOp' :: (Tuple Op MType) -> State NormalizationState (Tuple Op MType)
normalizeOp' (Tuple op opType) = do
  opType' <- normalizeMType' opType
  pure $ Tuple op opType'

-- | Normalize the given typed binding.
normalizeBinding' :: TypedBinding -> State NormalizationState TypedBinding
normalizeBinding' = AST.traverseBinding normalizeMType'

-- | Normalize the given typed expression tree.
normalizeTypeTree' :: TypeTree -> State NormalizationState TypeTree
normalizeTypeTree' = AST.traverseTree normalizeBinding' normalizeOp' normalizeMType'

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
  AD (TList t) -> do
    t' <- normalizeType' t
    pure $ AD (TList t')
  AD (TTuple ts) -> do
    ts' <- traverse normalizeType' ts
    pure $ AD (TTuple ts')
  a -> pure a

-- | Use `normalizeType'` on `Maybe Type`.
normalizeMType' :: Maybe Type -> State NormalizationState (Maybe Type)
normalizeMType' = traverse normalizeType'
