module AST where

import Prelude
import Data.List (List(..), fold, (:))
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Data.Bifunctor (rmap)

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

-- | Atoms
-- |
-- | Primitive data types
data Atom = AInt Int
          | Bool Boolean
          | Char String
          | Name String

derive instance eqAtom :: Eq Atom

derive instance ordAtom :: Ord Atom

-- | Expressions
-- |
-- | The basic expressions the `Parser` and `Evaluator` recognize.

data Tree a b o m =
    Atom      m  a
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

data QualTree b t m = Gen m b t
                    | Let m b t
                    | Guard m t

foldTree :: forall a b o m u v.
                      (m -> a -> u)
                   -> (m -> List u -> u)
                   -> (m -> List u -> u)
                   -> (m -> o -> u -> u -> u)
                   -> (m -> o -> u -> u)
                   -> (m -> u -> o -> u)
                   -> (m -> o -> u -> u)
                   -> (m -> o -> u)
                   -> (m -> u -> u -> u -> u)
                   -> (m -> u -> Maybe u -> Maybe u -> u)
                   -> (m -> List (Tuple b u) -> u -> u)
                   -> (m -> List b -> u -> u)
                   -> (m -> u -> List u -> u)
                   -> (m -> u -> List v -> u)
                   -> (m -> b -> u -> v)
                   -> (m -> b -> u -> v)
                   -> (m -> u -> v)
                   -> Tree a b o m -> u
foldTree atom list ntuple binary unary sectl sectr prefixop ifexpr arithmseq letexpr lambda app listcomp gen let' guard = go
  where
    go (Atom m a)               = atom m a
    go (List m us)              = list m (go <$> us)
    go (NTuple m us)            = ntuple m (go <$> us)
    go (Binary m o u1 u2)       = binary m o (go u1) (go u2)
    go (Unary m o u)            = unary m o (go u)
    go (SectL m u o)            = sectl m (go u) o
    go (SectR m o u)            = sectr m o (go u)
    go (PrefixOp m o)           = prefixop m o
    go (IfExpr m u1 u2 u3)      = ifexpr m (go u1) (go u2) (go u3)
    go (ArithmSeq m u1 mu2 mu3) = arithmseq m (go u1) (go <$> mu2) (go <$> mu3)
    go (LetExpr m tus u)        = letexpr m (rmap go <$> tus) (go u)
    go (Lambda m bs u)          = lambda m bs (go u)
    go (App m u us)             = app m (go u) (go <$> us)
    go (ListComp m u qs)        = listcomp m (go u) (qual <$> qs)
      where
        qual :: QualTree b (Tree a b o m) m -> v
        qual (Gen m b u) = gen m b (go u)
        qual (Let m b u) = let' m b (go u)
        qual (Guard m u) = guard m (go u)

idFoldTree :: forall a b o m. Tree a b o m -> Tree a b o m
idFoldTree = foldTree Atom List NTuple Binary Unary SectL SectR PrefixOp IfExpr ArithmSeq LetExpr Lambda App ListComp Gen Let Guard

derive instance eqTree :: (Eq a, Eq b, Eq c, Eq d) => Eq (Tree a b c d)

instance functorTree :: Functor (Tree a b c) where
  map f = foldTree
          (Atom <<< f)
          (List <<< f)
          (NTuple <<< f)
          (Binary <<< f)
          (Unary <<< f)
          (SectL <<< f)
          (SectR <<< f)
          (PrefixOp <<< f)
          (IfExpr <<< f)
          (ArithmSeq <<< f)
          (LetExpr <<< f)
          (Lambda <<< f)
          (App <<< f)
          (ListComp <<< f)
          (Gen <<< f)
          (Let <<< f)
          (Guard <<< f)

extract :: forall a b c d. Tree a b c d -> d
extract (Atom c _) = c
extract (List c _) = c
extract (NTuple c _) = c
extract (Binary c _ _ _) = c
extract (Unary c _ _) = c
extract (SectL c _ _) = c
extract (SectR c _ _) = c
extract (PrefixOp c _) = c
extract (IfExpr c _ _ _) = c
extract (ArithmSeq c _ _ _) = c
extract (LetExpr c _ _) = c
extract (Lambda c _ _) = c
extract (App c _ _) = c
extract (ListComp c _ _) = c

type Expr = Tree Atom (Binding Unit) Op Unit

type MType = Maybe Type

type TypeTree = Tree MType (Binding MType) (Tuple Op MType) MType 

type ExprQualTree = QualTree (Binding Unit) Expr Unit

type TypeQual  = QualTree (Binding Type) TypeTree Type

type TVar = String

data Type
    = TypVar TVar -- Typ Variables e.x. a
    | TypCon String -- Typ Constants e.x Int
    | TypArr Type Type -- e.x Int -> Int
    | AD AD
    | TypeError TypeError

data AD
    = TList Type
    | TTuple (List Type)


data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  | UnknownError String
  | NoInstanceOfEnum Type

-- derive instance eqQual :: (Eq b, Eq e) => Eq (Qual b e)

derive instance eqQualTree :: (Eq a, Eq b, Eq c) => Eq (QualTree a b c) 

-- | Bindings
-- |
-- | Binding forms for pattern matching on lists and tuples
data Binding m = Lit       m Atom
               | ConsLit   m (Binding m) (Binding m)
               | ListLit   m (List (Binding m))
               | NTupleLit m (List (Binding m))

derive instance eqBinding :: Eq Binding

-- | Definitions
-- |
-- | Definitions for functions and constants
data Definition = Def String (List (Binding Unit)) Expr

derive instance eqDefintion :: Eq Definition

instance showAtom :: Show Atom where
  show atom = case atom of
    AInt number -> "AInt " <> show number
    Bool bool   -> "Bool " <> show bool
    Char string -> "Char " <> show string
    Name string -> "Name " <> show string

-- instance showQual :: (Show b, Show e) => Show (Qual b e) where
--   show q = case q of
--     Gen b e -> "Gen (" <> show b <> " " <> show e <> ")"
--     Let b e -> "Let (" <> show b <> " " <> show e <> ")"
--     Guard e -> "Guard (" <> show e <> ")"

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
    ConsLit m b bs -> "(ConsLit " <> show m <> " " <> show b <> ") (" <> show bs <> ")"
    ListLit m bs   -> "(ListLit " <> show m <> " " <> show bs <> ")"
    NTupleLit m ls -> "(NTupleLit " <> show m <> " " show ls <> ")"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "Def " <> show name <> " (" <> show bindings <> ") (" <> show body <> ")"

instance showType :: Show Type where
  show (TypVar var) = "(TypVar  " <> show var <> ")"
  show (TypCon con) = "(TypCon " <> show con <> ")"
  show (TypArr t1 t2) = "(TypArr "<> show t1 <>" " <> show t2 <> ")"
  show (AD ad) = "(AD "<> show ad <> ")"
  show (TypeError err) ="(TypeError "<> show err <>")"

derive instance eqType :: Eq Type

instance showAD :: Show AD where
  show (TList t) = "(TList "<> show t <>")"
  show (TTuple tl) = "(TTuple ("<> show tl <> "))"

derive instance eqAD :: Eq AD

instance showTypeError :: Show TypeError where
  show (UnificationFail a b) = "(UnificationFail "<> show a <> " " <> show b <>")"
  show (InfiniteType a b ) = "(InfiniteType " <> show a <> " " <> show b <> ")"
  show (UnboundVariable a) = "(UnboundVariable " <> show a <> ")"
  show (UnknownError s) = "(UnknownError " <> s <> ")"
  show (NoInstanceOfEnum t) = "(" <> show t <> "is no instance of Enum)"

derive instance eqTypeError :: Eq TypeError

prettyPrintType :: Type -> String
prettyPrintType (TypVar tvar) = tvar
prettyPrintType (TypCon str) = str
prettyPrintType (TypeError err) = prettyPrintTypeError err
prettyPrintType (TypArr t1@(TypArr _ _) t2) = "(" <> prettyPrintType t1 <> ")" <> " -> " <> prettyPrintType t2
prettyPrintType (TypArr t1 t2) = prettyPrintType t1 <> " -> " <> prettyPrintType t2
prettyPrintType (AD (TList t)) = "[" <> prettyPrintType t <> "]"
prettyPrintType (AD (TTuple ts)) = "(" <> (fold <<< separateWith ", " <<< map prettyPrintType $ ts) <> ")"
    where
    separateWith :: String -> List String -> List String
    separateWith _ Nil = "" : Nil
    separateWith sep (t:ts) = t : map ((<>) sep) ts

prettyPrintTypeError :: TypeError -> String
prettyPrintTypeError (UnificationFail t1 t2) = "UnificationFail: Can't unify " <> prettyPrintType t1 <> " with " <> prettyPrintType t2
prettyPrintTypeError (InfiniteType tvar t) = "InfiniteType: cannot construct the infinite type: " <> tvar <> " ~ " <> prettyPrintType t
prettyPrintTypeError (UnboundVariable var) = "UnboundVariable: Not in scope " <> var
prettyPrintTypeError (NoInstanceOfEnum t) = "No instance for Enum " <> prettyPrintType t <> " defined."
prettyPrintTypeError (UnknownError str) = "UnknownError: " <> str
