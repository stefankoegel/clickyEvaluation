module AST where

import Prelude
import Control.Monad.State (State, evalState, runState, get, modify, put)
import Data.Bifunctor (bimap, rmap)
import Data.Foldable (intercalate, foldr, and)
import Data.List (List(..), fold, (:), zipWith, length)
import Data.Maybe (Maybe(..), fromJust)
import Data.Traversable (traverse, for)
import Data.Bitraversable (bisequence)
import Data.Tuple (Tuple(..), fst, snd)

-- | Operators
-- |
-- | Primitive infix operators that are evaluated directly by the `Evaluator`.
-- | (`Colon` is `Cons` but clashes with `Data.List.Cons`)
data Op = Composition
        | Power
        | Mul
        | Add | Sub
        | Colon | Append
        | Equ | Neq | Lt | Leq | Gt | Geq
        | And
        | Or
        | Dollar
        | InfixFunc String
        | InfixConstr String

derive instance eqOp :: Eq Op

instance showOp :: Show Op where
  show op = case op of
    Composition -> "Composition"
    Power  -> "Power"
    Mul    -> "Mul"
    Add    -> "Add"
    Sub    -> "Sub"
    Colon  -> "Colon"
    Append -> "Append"
    Equ    -> "Equ"
    Neq    -> "Neq"
    Lt     -> "Lt"
    Leq    -> "Leq"
    Gt     -> "Gt"
    Geq    -> "Geq"
    And    -> "And"
    Or     -> "Or"
    Dollar -> "Dollar"
    InfixFunc name -> "(InfixFunc " <> name <> ")"
    InfixConstr op -> "(InfixConstr " <> op <> ")"

pPrintOp :: Op -> String
pPrintOp op = case op of
  Composition -> "."
  Power  -> "^"
  Mul    -> "*"
  Add    -> "+"
  Sub    -> "-"
  Colon  -> ":"
  Append -> "++"
  Equ    -> "=="
  Neq    -> "/="
  Lt     -> "<"
  Leq    -> "<="
  Gt     -> ">"
  Geq    -> ">="
  And    -> "&&"
  Or     -> "||"
  Dollar -> "$"
  InfixFunc n -> "`" <> n <> "`"
  InfixConstr o -> o

-- | Atoms
-- |
-- | Primitive data types
data Atom = AInt Int
          | Bool Boolean
          | Char String
          | Name String
          | Constr String

derive instance eqAtom :: Eq Atom

derive instance ordAtom :: Ord Atom

-- | Expressions
-- |
-- | The basic expressions the `Parser` and `Evaluator` recognize.

data Tree a b o m =
    Atom      m a
  | List      m (List (Tree a b o m))
  | NTuple    m (List (Tree a b o m))
  | Binary    m o (Tree a b o m) (Tree a b o m)
  | Unary     m o (Tree a b o m)
  | SectL     m (Tree a b o m) o
  | SectR     m o (Tree a b o m)
  | PrefixOp  m o
  | IfExpr    m (Tree a b o m) (Tree a b o m) (Tree a b o m)
  | ArithmSeq m (Tree a b o m) (Maybe (Tree a b o m)) (Maybe (Tree a b o m))
  | LetExpr   m (List (Tuple b (Tree a b o m))) (Tree a b o m)
  | Lambda    m (List b) (Tree a b o m)
  | App       m (Tree a b o m) (List (Tree a b o m))
  | ListComp  m (Tree a b o m) (List (QualTree b (Tree a b o m) m))


-- | ONLY FOR TEST PURPOSES
-- | compare two TypeTree values on equality ignoring the meta information
eq' :: TypeTree -> TypeTree -> Boolean
eq' (Atom _ a) (Atom _ b) = a == b
eq' (List _ as) (List _ bs) = length as == length bs && (and $ zipWith eq' as bs)
eq' (NTuple _ as) (NTuple _ bs) = and $ zipWith eq' as bs
eq' (Binary _ o l r) (Binary _ o' l' r') = eq'Op o o' && eq' l l' && eq' r r'
eq' (Unary _ o e) (Unary _ o' e') = eq'Op o o' && eq' e e'
eq' (SectL _ e o) (SectL _ e' o') = eq'Op o o' && eq' e e'
eq' (SectR _ o e) (SectR _ o' e') = eq'Op o o' && eq' e e'
eq' (PrefixOp _ o) (PrefixOp _ o') = eq'Op o o'
eq' (IfExpr _ i t e) (IfExpr _ i' t' e') = eq' i i' && eq' t t' && eq' e e'
eq' (ArithmSeq _ a mb mc) (ArithmSeq _ a' mb' mc') = eq' a a' && eq'' mb mb' && eq'' mc mc'
 where
  eq'' Nothing Nothing = true
  eq'' (Just a) (Just b) = eq' a b
  eq'' _ _ = false
eq' (LetExpr _ d e) (LetExpr _ d' e') = and (zipWith eq'' d d') && eq' e e'
 where
  eq'' (Tuple b e) (Tuple b' e') = eq'Binding b b' && eq' e e'
eq' (Lambda _ bs e) (Lambda _ bs' e') = and (zipWith eq'Binding bs bs') && eq' e e'
eq' (App _ f as) (App _ f' as') = eq' f f' && and (zipWith eq' as as')
eq' (ListComp _ e qs) (ListComp _ e' qs') = eq' e e' && and (zipWith eq'QualTree qs qs')
eq' _ _ = false

eq'Op :: Tuple Op Meta -> Tuple Op Meta -> Boolean
eq'Op (Tuple o _) (Tuple o' _) = o == o'

eq'Binding :: TypedBinding -> TypedBinding -> Boolean
eq'Binding (Lit _ a) (Lit _ a') = a == a'
eq'Binding (ConsLit _ a as) (ConsLit _ a' as') = eq'Binding a a' && eq'Binding as as'
eq'Binding (ListLit _ bs) (ListLit _ bs') = and (zipWith eq'Binding bs bs')
eq'Binding (NTupleLit _ bs) (NTupleLit _ bs') = and (zipWith eq'Binding bs bs')
eq'Binding (ConstrLit _ dc) (ConstrLit _ dc') = eq'DataConstr dc dc'
eq'Binding _ _ = false

eq'DataConstr :: DataConstr TypedBinding -> DataConstr TypedBinding -> Boolean
eq'DataConstr (PrefixDataConstr n a ps) (PrefixDataConstr n' a' ps') = n == n' && a == a' && and (zipWith eq'Binding ps ps')
eq'DataConstr (InfixDataConstr n a p l r) (InfixDataConstr n' a' p' l' r') = n == n' && a == a' && p == p' && eq'Binding l l' && eq'Binding r r'
eq'DataConstr _ _ = false

eq'QualTree :: TypeQual -> TypeQual -> Boolean
eq'QualTree (Gen _ b e) (Gen _ b' e') = eq'Binding b b' && eq' e e'
eq'QualTree (Let _ b e) (Let _ b' e') = eq'Binding b b' && eq' e e'
eq'QualTree (Guard _ e) (Guard _ e')  = eq' e e'
eq'QualTree _ _ = false

eq'Def :: Definition -> Definition -> Boolean
eq'Def (Def s bs e) (Def s' bs' e') = s == s' && and (zipWith eq'Binding bs bs') && eq' e e'

toOpTuple :: Op -> Tuple Op Meta
toOpTuple op = Tuple op emptyMeta


{-
exprToTypeTree :: Expr -> TypeTree
exprToTypeTree (Atom _ atom) = Atom emptyMeta atom
exprToTypeTree (List _ exprs) = List emptyMeta (map exprToTypeTree exprs)
exprToTypeTree (NTuple _ exprs) = NTuple emptyMeta (map exprToTypeTree exprs)
exprToTypeTree (Binary _ op t1 t2) = Binary emptyMeta (toOpTuple op)
  (exprToTypeTree t1)
  (exprToTypeTree t2)
exprToTypeTree (Unary _ op t) = Unary emptyMeta (toOpTuple op) (exprToTypeTree t)
exprToTypeTree (SectL _ t op) = SectL emptyMeta (exprToTypeTree t) (toOpTuple op)
exprToTypeTree (SectR _ op t) = SectR emptyMeta (toOpTuple op) (exprToTypeTree t)
exprToTypeTree (PrefixOp _ op) = PrefixOp emptyMeta (toOpTuple op)
exprToTypeTree (IfExpr _ t1 t2 t3) = IfExpr emptyMeta
  (exprToTypeTree t1)
  (exprToTypeTree t2)
  (exprToTypeTree t3)
exprToTypeTree (ArithmSeq _ t1 mt2 mt3) = ArithmSeq emptyMeta
  (exprToTypeTree t1)
  (map exprToTypeTree mt2)
  (map exprToTypeTree mt3)
exprToTypeTree (LetExpr _ bs t) = LetExpr emptyMeta
  (map (\(Tuple b bt) -> Tuple (map (const emptyMeta) b) (exprToTypeTree bt)) bs)
  (exprToTypeTree t)
exprToTypeTree (Lambda _ bindings t) = Lambda emptyMeta
  (map (map (const emptyMeta)) bindings)
  (exprToTypeTree t)
exprToTypeTree (App _ t ts) = App emptyMeta (exprToTypeTree t) (map exprToTypeTree ts)
exprToTypeTree (ListComp _ t qualTrees) = ListComp emptyMeta
  (exprToTypeTree t)
  (map go qualTrees)
    where
    go (Gen _ b t) = Gen emptyMeta (map (const emptyMeta) b) (exprToTypeTree t)
    go (Let _ b t) = Let emptyMeta (map (const emptyMeta) b) (exprToTypeTree t)
    go (Guard _ t) = Guard emptyMeta (exprToTypeTree t)
    -}

binary :: Meta -> Meta -> Op -> TypeTree -> TypeTree -> TypeTree
binary meta metaOp op left right = Binary meta (Tuple op metaOp) left right

-- | Get the expression element from a given qual tree.
getQualTreeExpression :: forall b t m. QualTree b t m -> t
getQualTreeExpression (Gen _ _ e) = e
getQualTreeExpression (Let _ _ e) = e
getQualTreeExpression (Guard _ e) = e

-- TODO: Find better name.
data QualTree b t m = Gen m b t
                    | Let m b t
                    | Guard m t

derive instance eqTree :: (Eq a, Eq b, Eq c, Eq d) => Eq (Tree a b c d)

instance functorQualTree :: Functor (QualTree b e) where
  map f (Gen d b e) = Gen (f d) b e
  map f (Let d b e) = Let (f d) b e
  map f (Guard d e) = Guard (f d) e

instance functorTree :: Functor (Tree a b c) where
  map f (Atom c a) = Atom (f c) a
  map f (List c xs) = List (f c) (map f <$> xs)
  map f (NTuple c xs) = NTuple (f c) (map f <$> xs)
  map f (Binary c op t1 t2) = Binary (f c) op (map f t1) (map f t2)
  map f (Unary c op t) = Unary (f c) op (map f t)
  map f (SectL c t op) = SectL (f c) (map f t) op
  map f (SectR c op t) = SectR (f c) op (map f t)
  map f (PrefixOp c op) = PrefixOp (f c) op
  map f (IfExpr c t1 t2 t3) = IfExpr (f c) (map f t1) (map f t2) (map f t3)
  map f (ArithmSeq c t1 t2 t3) = ArithmSeq (f c) (map f t1) (map f <$> t2) (map f <$> t3)
  map f (LetExpr c bs t) = LetExpr (f c) (map (rmap (map f)) bs) (map f t)
  map f (Lambda c bs t) = Lambda (f c) bs (map f t)
  map f (App c t ts) = App (f c) (map f t) (map f <$> ts)
  map f (ListComp c t ts) = ListComp (f c) (map f t) (map go ts)
    where
    go (Gen d b e) = Gen (f d) b (map f e)
    go (Let d b e) = Let (f d) b (map f e)
    go (Guard d e) = Guard (f d) (map f e)

qualTreeMap :: forall b b' t t' m m'.
     (b -> b')
  -> (t -> t')
  -> (m -> m')
  -> QualTree b t m
  -> QualTree b' t' m'
qualTreeMap fb ft f (Gen x b t) = Gen (f x) (fb b) (ft t)
qualTreeMap fb ft f (Let x b t) = Let (f x) (fb b) (ft t)
qualTreeMap fb ft f (Guard x t) = Guard (f x) (ft t)

treeMap :: forall a a' b b' o o' m m'.
     (a -> a')        -- ^ Function applied to the atom element
  -> (b -> b')        -- ^ Function applied to the binding element
  -> (o -> o')        -- ^ Function applied to the operator element
  -> (m -> m')        -- ^ Function applied to the meta element
  -> Tree a b o m     -- ^ Tree to be transformed
  -> Tree a' b' o' m' -- ^ Transformed tree
treeMap fa fb fo f (Atom x a) = Atom (f x) (fa a)
treeMap fa fb fo f (List x es) = List (f x) (map (treeMap fa fb fo f) es)
treeMap fa fb fo f (NTuple x es) = NTuple (f x) (map (treeMap fa fb fo f) es)
treeMap fa fb fo f (Binary x o e1 e2) =
  Binary (f x) (fo o)
    (treeMap fa fb fo f e1)
    (treeMap fa fb fo f e2)
treeMap fa fb fo f (Unary x o e) = Unary (f x) (fo o) (treeMap fa fb fo f e)
treeMap fa fb fo f (SectL x e o) = SectL (f x) (treeMap fa fb fo f e) (fo o)
treeMap fa fb fo f (SectR x o e) = SectR (f x) (fo o) (treeMap fa fb fo f e)
treeMap fa fb fo f (PrefixOp x o) = PrefixOp (f x) (fo o)
treeMap fa fb fo f (IfExpr x e1 e2 e3) =
  IfExpr (f x)
    (treeMap fa fb fo f e1)
    (treeMap fa fb fo f e2)
    (treeMap fa fb fo f e3)
treeMap fa fb fo f (ArithmSeq x e me1 me2) =
  ArithmSeq (f x)
    (treeMap fa fb fo f e)
    (map (treeMap fa fb fo f) me1)
    (map (treeMap fa fb fo f) me2)
treeMap fa fb fo f (LetExpr x defs e) =
  LetExpr (f x)
    (map (bimap fb (treeMap fa fb fo f)) defs)
    (treeMap fa fb fo f e)
treeMap fa fb fo f (Lambda x bs e) = Lambda (f x) (map fb bs) (treeMap fa fb fo f e)
treeMap fa fb fo f (App x e es) =
  App (f x)
    (treeMap fa fb fo f e)
    (map (treeMap fa fb fo f) es)
treeMap fa fb fo f (ListComp x e qualTrees) =
  ListComp (f x)
    (treeMap fa fb fo f e)
    (map (qualTreeMap fb (treeMap fa fb fo f) f) qualTrees)

-- | Inserts Meta information into the given tree node
insertIntoTree :: forall a b c d. d -> Tree a b c d -> Tree a b c d
insertIntoTree x (Atom _ atom) = Atom x atom
insertIntoTree x (List _ ts) = List x ts
insertIntoTree x (NTuple _ ts) = NTuple x ts
insertIntoTree x (Binary _ op t1 t2) = Binary x op t1 t2
insertIntoTree x (Unary _ op t) = Unary x op t
insertIntoTree x (SectL _ t op) = SectL x t op
insertIntoTree x (SectR _ op t) = SectR x op t
insertIntoTree x (PrefixOp _ op) = PrefixOp x op
insertIntoTree x (IfExpr _ t1 t2 t3) = IfExpr x t1 t2 t3
insertIntoTree x (ArithmSeq _ t1 t2 t3) = ArithmSeq x t1 t2 t3
insertIntoTree x (LetExpr _ bs t) = LetExpr x bs t
insertIntoTree x (Lambda _ b t) = Lambda x b t
insertIntoTree x (App _ t ts) = App x t ts
insertIntoTree x (ListComp _ t ts) = ListComp x t ts

-- | Extracts Meta information from the given node
extractFromTree :: forall a b c d. Tree a b c d -> d
extractFromTree (Atom c _) = c
extractFromTree (List c _) = c
extractFromTree (NTuple c _) = c
extractFromTree (Binary c _ _ _) = c
extractFromTree (Unary c _ _) = c
extractFromTree (SectL c _ _) = c
extractFromTree (SectR c _ _) = c
extractFromTree (PrefixOp c _) = c
extractFromTree (IfExpr c _ _ _) = c
extractFromTree (ArithmSeq c _ _ _) = c
extractFromTree (LetExpr c _ _) = c
extractFromTree (Lambda c _ _) = c
extractFromTree (App c _ _) = c
extractFromTree (ListComp c _ _) = c

extractFromBinding :: forall a. Binding a -> a
extractFromBinding (Lit x _)       = x
extractFromBinding (ConsLit x _ _) = x
extractFromBinding (ListLit x _)   = x
extractFromBinding (NTupleLit x _) = x
extractFromBinding (ConstrLit x _) = x

extractFromQualTree :: forall b t m. QualTree b t m -> m
extractFromQualTree (Gen x _ _) = x
extractFromQualTree (Let x _ _) = x
extractFromQualTree (Guard x _) = x

-- | Return a list of child nodes of a given tree.
getTreeChildren :: forall a b o m. Tree a b o m -> List (Tree a b o m)
getTreeChildren (List _ es) = es
getTreeChildren (NTuple _ es) = es
getTreeChildren (Binary _ _ e1 e2) = e1 : e2 : Nil
getTreeChildren (Unary _ _ e) = e : Nil
getTreeChildren (SectL _ e _) = e : Nil
getTreeChildren (SectR _ _ e) = e : Nil
getTreeChildren (IfExpr _ e1 e2 e3) = e1 : e2 : e3 : Nil
getTreeChildren (ArithmSeq _ e me1 me2) = e : (maybeTreeChilden me1) <> (maybeTreeChilden me2)
  where
  maybeTreeChilden (Just t) = t : Nil
  maybeTreeChilden _ = Nil
getTreeChildren (LetExpr _ defs e) = e : (map snd defs)
getTreeChildren (App _ e es) = e : es
getTreeChildren (ListComp _ e quals) = e : (map getQualTreeExpression quals)
getTreeChildren _ = Nil

type Expr = Tree Atom (Binding Unit) Op Unit

type MType = Maybe Type

type Index = Int
type MIndex = Maybe Index
type MIType = Tuple MType Index

type Meta' = { index :: Index ,mtype :: MType }
newtype Meta = Meta Meta'


emptyMeta' :: Meta'
emptyMeta' = {index: (-1), mtype: Nothing}

emptyMeta :: Meta
emptyMeta = Meta emptyMeta'

idxMeta :: Int -> Meta
idxMeta i = Meta {index: i, mtype: Nothing}

freshIdx :: State Index Index
freshIdx = do
  i <- get
  _ <- modify (\i -> i + 1)
  pure i

freshMeta :: State Index Meta
freshMeta = idxMeta <$> freshIdx

instance showMeta :: Show Meta where
  show (Meta meta) = "Meta { index: " <> show meta.index <> ", mtype: " <> show meta.mtype <> "}"

instance eqMeta :: Eq Meta where
  eq a b = getMetaIndex a `eq` getMetaIndex b && getMetaMType a `eq` getMetaMType b


getMetaIndex :: Meta -> Index
getMetaIndex (Meta meta) = meta.index

getMetaMType :: Meta -> MType
getMetaMType (Meta meta) = meta.mtype

type TypeTree = Tree Atom (Binding Meta) (Tuple Op Meta) Meta

makeIndexTuple :: Meta -> State Index Meta
makeIndexTuple (Meta meta) = do
  idx <- get
  let new = Meta $ meta {index = idx}
  put (idx + 1)
  pure new

makeIndexOpTuple :: (Tuple Op Meta) -> State Index (Tuple Op Meta)
makeIndexOpTuple (Tuple op (Meta meta)) = do
  idx <- get
  let new = Tuple op (Meta $ meta {index = idx})
  put (idx + 1)
  pure new

-- | Transform the given definition into an indexed definition.
makeIndexedDefinition :: Definition -> Index -> Tuple IndexedDefinition Index
makeIndexedDefinition (Def name bindings expr) beginWith =
  let idxAndBindings = runState (toIndexedBindings bindings) beginWith
      idxAndExpr = runState (toIndexedTree expr) (snd idxAndBindings)
  in Tuple (IndexedDef name (fst idxAndBindings) (fst idxAndExpr)) (snd idxAndExpr)
  where
  toIndexedBindings = traverse $ traverseBinding makeIndexTuple
  toIndexedTree expr = traverseTree (traverseBinding makeIndexTuple) makeIndexOpTuple makeIndexTuple expr

makeIndexedTree :: TypeTree -> TypeTree
makeIndexedTree expr = evalState (makeIndexedTree' expr) 0
  where
    -- Traverse the tree and assign indices in ascending order.
    makeIndexedTree' :: TypeTree -> State Index TypeTree
    makeIndexedTree' expr = traverseTree (traverseBinding makeIndexTuple) makeIndexOpTuple makeIndexTuple expr

insertIntoIndexedTree :: MType -> TypeTree -> TypeTree
insertIntoIndexedTree t expr = insertIntoTree (Meta $ meta {mtype = t}) expr
  where
    meta = extractFromTree >>> (\(Meta meta) -> meta) $ expr

definitionIndex :: IndexedDefinition -> Index
definitionIndex (IndexedDef name bindings expr) = index expr

opIndex :: (Tuple Op Meta) -> Index
opIndex = snd >>> getMetaIndex

bindingIndex :: (Binding Meta) -> Index
bindingIndex = extractFromBinding >>> getMetaIndex

index :: TypeTree -> Index
index = extractFromTree >>> getMetaIndex

traverseBinding :: forall m m' f. Monad f =>
     (m -> f m')
  -> Binding m
  -> f (Binding m')
traverseBinding f (Lit t atom) = do
  t' <- f t
  pure $ Lit t' atom
traverseBinding f (ConsLit t b1 b2) = do
  t' <- f t
  b1' <- traverseBinding f b1
  b2' <- traverseBinding f b2
  pure $ ConsLit t' b1' b2'
traverseBinding f (ListLit t bs) = do
  t' <- f t
  bs' <- traverse (traverseBinding f) bs
  pure $ ListLit t' bs'
traverseBinding f (NTupleLit t bs) = do
  t' <- f t
  bs' <- traverse (traverseBinding f) bs
  pure $ NTupleLit t' bs'
traverseBinding f (ConstrLit t constr) = do
  t' <- f t
  constr' <- case constr of
                  PrefixDataConstr name len ps -> do
                    ps' <- for ps (traverseBinding f)
                    pure $ PrefixDataConstr name len ps'
                  InfixDataConstr op a p l r -> do
                    l' <- traverseBinding f l
                    r' <- traverseBinding f r
                    pure $ InfixDataConstr op a p l' r'
  pure $ ConstrLit t' constr'

traverseQualTree :: forall b b' e e' m m' f. Monad f =>
     (b -> f b')
  -> (e -> f e')
  -> (m -> f m')
  -> QualTree b e m
  -> f (QualTree b' e' m')
traverseQualTree fb fe f (Gen t b e) = do
  t' <- f t
  b' <- fb b
  e' <- fe e
  pure $ Gen t' b' e'
traverseQualTree fb fe f (Let t b e) = do
  t' <- f t
  b' <- fb b
  e' <- fe e
  pure $ Let t' b' e'
traverseQualTree fb fe f (Guard t e) = do
  t' <- f t
  e' <- fe e
  pure $ Guard t' e'

traverseTree :: forall b b' o o' m m' f. Monad f =>
     (b -> f b')
  -> (o -> f o')
  -> (m -> f m')
  -> Tree Atom b o m
  -> f (Tree Atom b' o' m')
traverseTree fb fo f expr@(Atom t atom) = do
  t' <- f t
  pure $ Atom t' atom
traverseTree fb fo f expr@(List t es) = do
  t' <- f t
  es' <- traverse (traverseTree fb fo f) es
  pure $ List t' es'
traverseTree fb fo f expr@(NTuple t es) = do
  t' <- f t
  es' <- traverse (traverseTree fb fo f) es
  pure $ NTuple t' es'
traverseTree fb fo f expr@(Binary t o e1 e2) = do
  t' <- f t
  o' <- fo o
  e1' <- traverseTree fb fo f e1
  e2' <- traverseTree fb fo f e2
  pure $ Binary t' o' e1' e2'
traverseTree fb fo f expr@(Unary t o e) = do
  t' <- f t
  o' <- fo o
  e' <- traverseTree fb fo f e
  pure $ Unary t' o' e'
traverseTree fb fo f expr@(SectL t e o) = do
  t' <- f t
  e' <- traverseTree fb fo f e
  o' <- fo o
  pure $ SectL t' e' o'
traverseTree fb fo f expr@(SectR t o e) = do
  t' <- f t
  o' <- fo o
  e' <- traverseTree fb fo f e
  pure $ SectR t' o' e'
traverseTree fb fo f expr@(PrefixOp t o) = do
  t' <- f t
  o' <- fo o
  pure $ PrefixOp t' o'
traverseTree fb fo f expr@(IfExpr t e1 e2 e3) = do
  t' <- f t
  e1' <- traverseTree fb fo f e1
  e2' <- traverseTree fb fo f e2
  e3' <- traverseTree fb fo f e3
  pure $ IfExpr t' e1' e2' e3'
traverseTree fb fo f expr@(ArithmSeq t e me1 me2) = do
  t' <- f t
  e' <- traverseTree fb fo f e
  me1' <- traverse (traverseTree fb fo f) me1
  me2' <- traverse (traverseTree fb fo f) me2
  pure $ ArithmSeq t' e' me1' me2'
traverseTree fb fo f expr@(LetExpr t defs e) = do
  t' <- f t
  defs' <- traverse (bimap fb (traverseTree fb fo f) >>> bisequence) defs
  e' <- traverseTree fb fo f e
  pure $ LetExpr t' defs' e'
traverseTree fb fo f expr@(Lambda t bs e) = do
  t' <- f t
  bs' <- traverse fb bs
  e' <- traverseTree fb fo f e
  pure $ Lambda t' bs' e'
traverseTree fb fo f expr@(App t e es) = do
  t' <- f t
  e' <- traverseTree fb fo f e
  es' <- traverse (traverseTree fb fo f) es
  pure $ App t' e' es'
traverseTree fb fo f expr@(ListComp t e quals) = do
  t' <- f t
  e' <- traverseTree fb fo f e
  quals' <- traverse (traverseQualTree fb (traverseTree fb fo f) f) quals
  pure $ ListComp t' e' quals'

type ExprQualTree = QualTree (Binding Unit) Expr Unit
type TypeQual = QualTree (Binding Meta) TypeTree Meta

type TVar = String

data Type
    = TypVar TVar -- Typ Variables x.x. a
    | TypCon String -- Typ Constants e.x Int
    | TypArr Type Type -- e.x Int -> Int
    | TList Type
    | TTuple (List Type)
    | TTypeCons String (List Type)
    | TypeError TypeError
    | UnknownType

-- ADT Definition
--
-- The definition of a Type consists of the name of the type,
-- followd by type variables, over which it is parametrized
-- and a list of Data Constructors, each having a name,
-- and a list of types, which are their parameters.
data ADTDef
  = ADTDef String (List TVar) (List (DataConstr Type))

-- Translates an ADT definition into a list of Definitions
--
-- e.g:
--
-- the definition
--
--  data Maybe a
--    = Nothing
--    | Just a
--
-- will be translated to
--
--  Nothing :: Maybe a
--  Nothing = Nothing
--  Just :: a -> Maybe a
--  Just = Just
--
-- where the left hand side is just the name,
-- and the right hand side is an actual expression.
compileADTDef :: ADTDef -> State Index (List Definition)
compileADTDef (ADTDef tname tvars constrs) =
  traverse (compileDataConstr (TTypeCons tname (map TypVar tvars))) constrs

derive instance eqADTDef :: Eq ADTDef

instance showADTDef :: Show ADTDef where
  show (ADTDef n vs cs) =
    "data "
    <> n
    <> " "
    <> intercalate " " (map show vs)
    <> "\n  = "
    <> intercalate "\n  | " (map show cs)


-- DataConstrtructor parameterized over its parameters,
-- to use it for both, type definitions and data.

data Associativity
  = LEFTASSOC
  | RIGHTASSOC
  | ASSOC

derive instance eqAssociativity :: Eq Associativity

data DataConstr param
  = PrefixDataConstr String Int (List param)
  | InfixDataConstr String Associativity Int param param

-- This will be called by compileADTDef and does the actual work.
compileDataConstr :: Type -> DataConstr Type -> State Index Definition
compileDataConstr t (PrefixDataConstr name _ ps) = do
  i <- freshIdx
  pure $ Def name Nil (Atom (Meta ({index: i, mtype: Just (foldr TypArr t ps)})) (Constr name))
compileDataConstr t (InfixDataConstr op assoc prec l r) = do
  i <- freshIdx
  i' <- freshIdx
  pure $ Def op Nil (PrefixOp (Meta emptyMeta' {index = i, mtype = Just typ}) (Tuple (InfixConstr op) (Meta emptyMeta' {index = i', mtype = Just typ})))
 where
  typ = TypArr l (TypArr r t)

instance functorDataConstr :: Functor DataConstr where
  map f (PrefixDataConstr s i ps) = PrefixDataConstr s i (map f ps)
  map f (InfixDataConstr s a i p1 p2) = InfixDataConstr s a i (f p1) (f p2)

instance showDataConstr :: (Show param) => Show (DataConstr param) where
  show (PrefixDataConstr n _ ts)
    = n <> " " <> intercalate " " (map show ts)
  show (InfixDataConstr o ASSOC _ l r)
    = show l <> " " <> o <> " " <> show r
  show (InfixDataConstr o RIGHTASSOC _ l r)
    = show l <> " " <> o <> " (" <> show r <> ")"
  show (InfixDataConstr o LEFTASSOC _ l r)
    = "(" <> show l <> ") " <> o <> " " <> show r

derive instance eqDataConstr :: (Eq params) => Eq (DataConstr params)

data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  | UnknownDataConstructor String
  | UnknownError String
  | NoInstanceOfEnum Type
  | PatternMismatch TypedBinding Type

derive instance eqQualTree :: (Eq a, Eq b, Eq c) => Eq (QualTree a b c)

-- | Bindings
-- |
-- | Binding forms for pattern matching on lists and tuples
data Binding m = Lit       m Atom
               | ConsLit   m (Binding m) (Binding m)
               | ListLit   m (List (Binding m))
               | NTupleLit m (List (Binding m))
               | ConstrLit m (DataConstr (Binding m))

derive instance eqBinding :: (Eq a) => Eq (Binding a)

instance functorBinding :: Functor Binding where
  map f (Lit x atom) = Lit (f x) atom
  map f (ConsLit x binding1 binding2) = ConsLit (f x) (f <$> binding1) (f <$> binding2)
  map f (ListLit x bindings) = ListLit (f x) (map f <$> bindings)
  map f (NTupleLit x bindings) = NTupleLit (f x) (map f <$> bindings)
  map f (ConstrLit x c) = ConstrLit (f x) (map (map f) c)

-- | Given a binding, return a list of (direct) children bindings.
getBindingChildren :: forall m. Binding m -> List (Binding m)
getBindingChildren (ConsLit _ b1 b2) = b1 : b2 : Nil
getBindingChildren (ListLit _ bs) = bs
getBindingChildren (NTupleLit _ bs) = bs
getBindingChildren _ = Nil

type TypedBinding = Binding Meta

-- | Definitions
-- |
-- | Definitions for functions and constants
data Definition = Def String (List (Binding Meta)) TypeTree

-- | A definition with indexed bindings and an indexed expression.
data IndexedDefinition = IndexedDef String (List TypedBinding) TypeTree

derive instance eqDefintion :: Eq Definition
derive instance eqIndexedDefintion :: Eq IndexedDefinition

instance showAtom :: Show Atom where
  show atom = case atom of
    AInt number -> "AInt " <> show number
    Bool bool   -> "Bool " <> show bool
    Char string -> "Char " <> show string
    Name string -> "Name " <> show string
    Constr string -> "Constr " <> show string

instance showQualTree :: (Show a, Show b, Show c) => Show (QualTree a b c) where
  show (Gen a b c) = "Gen (" <> show a <> " " <> show b <> " " <> show c <> ")"
  show (Let a b c) = "Let (" <> show a <> " " <> show b <> " " <> show c <> ")"
  show (Guard a c)  = "Guard (" <> show a <> " " <> show c <> ")"

instance showTree :: (Show a, Show b, Show c, Show d) => Show (Tree a b c d) where
  show tree = case tree of
    Atom c atom         -> "(Atom " <> show c <> " "<> show atom <> ")"
    List c ls           -> "(List " <> show c <> " "<> show ls <>  ")"
    NTuple c ls         -> "(NTuple " <> show c <> " "<> show ls <>  ")"
    Binary c op e1 e2   -> "(Binary " <> show c <> " "<> show op <> " " <> show e1 <> " " <> show e2 <>  ")"
    Unary c op e        -> "(Unary " <> show c <> " "<> show op <> " " <> show e <>  ")"
    SectL c expr op     -> "(SectL " <> show c <> " "<> show expr <> " " <> show op <>  ")"
    SectR c op expr     -> "(SectR " <> show c <> " "<> show op <> " " <> show expr <>  ")"
    PrefixOp c op       -> "(PrefixOp " <> show c <> " " <> show op <> ")"
    IfExpr c ce te ee   -> "(IfExpr " <> show c <> " "<> show ce <> " " <> show te <> " " <> show ee <>  ")"
    ArithmSeq c s by e  -> "(ArithmSeq " <> show c <> "(" <> show s <> ")" <> show by <> ".." <> show e <> ")"
    LetExpr c bs e     -> "(LetExpr " <> show c <> " (" <> show bs <> ") " <> " " <> show e <>  ")"
    Lambda c binds body -> "(Lambda " <> show c <> " " <> show binds <> " " <> show body <>  ")"
    App c func args     -> "(App " <> show c <> " "<> show func <> " " <> show args <>  ")"
    ListComp c expr quals -> "(ListComp " <> show c <> "(" <> show expr <> ")" <> "(" <> show quals <> "))"

instance showBinding :: (Show a) => Show (Binding a) where
  show binding = case binding of
    Lit m atom     -> "(Lit " <> show m <> " " <> show atom <> ")"
    ConsLit m b bs -> "(ConsLit " <> show m <> " " <> show b <> " " <> show bs <> ")"
    ListLit m bs   -> "(ListLit " <> show m <> " " <> show bs <> ")"
    NTupleLit m ls -> "(NTupleLit " <> show m <> " " <> show ls <> ")"
    ConstrLit m c  -> "(ConstrLit " <> show m <> " " <> show c <> ")"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "Def " <> show name <> " (" <> show bindings <> ") (" <> show body <> ")"

instance showIndexedDefinition :: Show IndexedDefinition where
  show (IndexedDef name bindings body) = "IndexedDef " <> show name <> " (" <> show bindings <> ") (" <> show body <> ")"

instance showType :: Show Type where
  show (UnknownType) = "(UnknownType)"
  show (TypVar var) = "(TypVar  " <> show var <> ")"
  show (TypCon con) = "(TypCon " <> show con <> ")"
  show (TypArr t1 t2) = "(TypArr "<> show t1 <>" " <> show t2 <> ")"
  show (TList t) = "(TList "<> show t <>")"
  show (TTuple tl) = "(TTuple ("<> show tl <> "))"
  show (TTypeCons name ps) = "(TTypeCons " <> show name <> " " <> intercalate " " (map show ps) <> ")"
  show (TypeError err) ="(TypeError "<> show err <>")"

derive instance eqType :: Eq Type

instance showTypeError :: Show TypeError where
  show (UnificationFail a b) = "(UnificationFail "<> show a <> " " <> show b <>")"
  show (InfiniteType a b ) = "(InfiniteType " <> show a <> " " <> show b <> ")"
  show (UnboundVariable a) = "(UnboundVariable " <> show a <> ")"
  show (UnknownDataConstructor a) = "(UnknownDataConstructor " <> show a <> ")"
  show (UnknownError s) = "(UnknownError " <> s <> ")"
  show (PatternMismatch b t) = "(PatternMismatch " <> show b <> " " <> show t <> ")"
  show (NoInstanceOfEnum t) = "(" <> show t <> "is no instance of Enum)"

derive instance eqTypeError :: Eq TypeError

prettyPrintAtom :: Atom -> String
prettyPrintAtom (AInt n) = show n
prettyPrintAtom (Bool b) = show b
prettyPrintAtom (Char c) = c
prettyPrintAtom (Name s) = s
prettyPrintAtom (Constr s) = s

prettyPrintBinding :: forall m. Binding m -> String
prettyPrintBinding (Lit _ atom) = prettyPrintAtom atom
prettyPrintBinding (ConsLit _ b1 b2) = "("
    <> prettyPrintBinding b1
    <> ":"
    <> prettyPrintBinding b2
    <> ")"
prettyPrintBinding (ListLit _ bs) = "[" <> intercalate ", " (map prettyPrintBinding bs) <> "]"
prettyPrintBinding (NTupleLit _ bs) = "(" <> intercalate ", " (map prettyPrintBinding bs) <> ")"
prettyPrintBinding (ConstrLit _ (PrefixDataConstr name _ ps)) = "(" <> name <> " " <> intercalate " " (map prettyPrintBinding ps) <> ")"
prettyPrintBinding (ConstrLit _ (InfixDataConstr name _ _ l r)) = "(" <> prettyPrintBinding l <> " " <> name <> " " <> prettyPrintBinding r <> ")"

prettyPrintType :: Type -> String
prettyPrintType (UnknownType) = "?"
prettyPrintType (TypVar tvar) = tvar
prettyPrintType (TypCon str) = str
prettyPrintType (TypeError err) = prettyPrintTypeError err
prettyPrintType (TypArr t1@(TypArr _ _) t2) = "(" <> prettyPrintType t1 <> ")" <> " -> " <> prettyPrintType t2
prettyPrintType (TypArr t1 t2) = prettyPrintType t1 <> " -> " <> prettyPrintType t2
prettyPrintType (TList t) = "[" <> prettyPrintType t <> "]"
prettyPrintType (TTuple ts) = "(" <> (fold <<< separateWith ", " <<< map prettyPrintType $ ts) <> ")"
    where
    separateWith :: String -> List String -> List String
    separateWith _ Nil = "" : Nil
    separateWith sep (t:ts) = t : map ((<>) sep) ts
prettyPrintType (TTypeCons name ps)
  = name <> " " <> intercalate " " (map prettyPrintType ps)

prettyPrintTypeError :: TypeError -> String
prettyPrintTypeError (UnificationFail t1 t2) = "UnificationFail: Can't unify " <> prettyPrintType t1 <> " with " <> prettyPrintType t2
prettyPrintTypeError (InfiniteType tvar t) = "InfiniteType: cannot construct the infinite type: " <> tvar <> " ~ " <> prettyPrintType t
prettyPrintTypeError (UnboundVariable var) = "UnboundVariable: Not in scope " <> var
prettyPrintTypeError (UnknownDataConstructor var) = "UnknownDataConstructor: Not in scope " <> var
prettyPrintTypeError (NoInstanceOfEnum t) = "No instance for Enum " <> prettyPrintType t <> " defined."
prettyPrintTypeError (PatternMismatch b t) = "PatternMismatch: The pattern " <> prettyPrintBinding b <> " doesn't match with " <> prettyPrintType t
prettyPrintTypeError (UnknownError str) = "UnknownError: " <> str
