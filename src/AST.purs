module AST where

import Prelude
import Data.List (List(..), fold, (:))
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)

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

data Tree a b c = 
    Atom      c a
  | List      c (List (Tree a b c))
  | NTuple    c (List (Tree a b c))
  | Binary    c Op (Tree a b c) (Tree a b c)
  | Unary     c Op (Tree a b c)
  | SectL     c (Tree a b c) Op
  | SectR     c Op (Tree a b c)
  | PrefixOp  c Op
  | IfExpr    c (Tree a b c) (Tree a b c) (Tree a b c)
  | ArithmSeq c (Tree a b c) (Maybe (Tree a b c)) (Maybe (Tree a b c))
  | LetExpr   c (List (Tuple Binding (Tree a b c))) (Tree a b c)
  | Lambda    c (List b) (Tree a b c)
  | App       c (Tree a b c) (List (Tree a b c))
  | ListComp  c (Tree a b c) (List (Qual b (Tree a b c)))

derive instance eqTree :: (Eq a, Eq b, Eq c) => Eq (Tree a b c)

type Expr = Tree Atom Binding Unit

data Qual b e = Gen b e | Let b e | Guard e

data QualTree b e t = TGen b e t
                    | TLet b e t
                    | TGuard e t 

type ExprQual = Qual Binding Expr

-- last type para is type of expr at this level
-- e.x. Binary (Op_Type) (Exp1_TypeTree) (Exp2_TypeTree)

type TypeTree = Tree Unit TypeBinding Type

type IndexTree = Tree Unit IBinding Int

type TypeQual  = QualTree TypeBinding TypeTree Type

type IndexQual = QualTree IBinding IndexTree Int

data TypeBinding  = TLit                              Type
                  | TConsLit TypeBinding TypeBinding  Type
                  | TListLit (List TypeBinding)       Type
                  | TNTupleLit (List TypeBinding)     Type

data IBinding  = ILit                       Int
               | IConsLit IBinding IBinding  Int
               | IListLit (List IBinding)    Int
               | INTupleLit (List IBinding)  Int

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

derive instance eqQual :: (Eq b, Eq e) => Eq (Qual b e)

derive instance eqQualTree :: (Eq a, Eq b, Eq c) => Eq (QualTree a b c) 

-- | Bindings
-- |
-- | Binding forms for pattern matching on lists and tuples
data Binding = Lit Atom
             | ConsLit Binding Binding
             | ListLit (List Binding)
             | NTupleLit (List Binding)

derive instance eqBinding :: Eq Binding

-- | Definitions
-- |
-- | Definitions for functions and constants
data Definition = Def String (List Binding) Expr

derive instance eqDefintion :: Eq Definition

type Output = {
    expr :: Expr,
    typ :: TypeTree,
    idTree :: IndexTree
  }


instance showAtom :: Show Atom where
  show atom = case atom of
    AInt number -> "AInt " <> show number
    Bool bool   -> "Bool " <> show bool
    Char string -> "Char " <> show string
    Name string -> "Name " <> show string

instance showQual :: (Show b, Show e) => Show (Qual b e) where
  show q = case q of
    Gen b e -> "Gen (" <> show b <> " " <> show e <> ")"
    Let b e -> "Let (" <> show b <> " " <> show e <> ")"
    Guard e -> "Guard (" <> show e <> ")"

instance showQualTree :: (Show a, Show b, Show c) => Show (QualTree a b c) where
  show (TGen a b c) = "TGen (" <> show a <> " " <> show b <> " " <> show c <> ")"
  show (TLet a b c) = "TLet (" <> show a <> " " <> show b <> " " <> show c <> ")"
  show (TGuard a c)  = "TGuard (" <> show a <> " " <> show c <> ")"

instance showTree :: (Show a, Show b, Show c) => Show (Tree a b c) where
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

instance showBinding :: Show Binding where
  show binding = case binding of
    Lit atom     -> "Lit (" <> show atom <> ")"
    ConsLit b bs -> "ConsLit (" <> show b <> ") (" <> show bs <> ")"
    ListLit bs   -> "ListLit (" <> show bs <> ")"
    NTupleLit ls -> "NTupleLit (" <> show ls <> ")"

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

-- instance showTypeTree :: Show TypeTree where
--   show (TAtom t) = "(TAtom " <> show t <> ")"
--   show (TListTree lt t) = "(TListTree (" <> show lt <> ") " <> show t <> ")"
--   show (TNTuple lt t) = "(TNTuple ("<> show lt <> ") " <> show t <> ")"
--   show (TBinary t1 tt1 tt2 t) = "(TBinary " <> show t1 <> " " <> show tt1 <>  " " <> show tt2 <> " " <> show t <> ")"
--   show (TUnary t1 tt t) = "(TUnary "<> show t1 <> " " <> show tt <> " " <> show t <> ")"
--   show (TSectL tt t1 t) = "(TSectL "<> show tt <> " "<> show t1 <> " " <> show t <> ")"
--   show (TSectR t1 tt t) = "(TSectR " <> show t1 <> " " <> show tt <> " " <> show t <> ")"
--   show (TPrefixOp t) = "(TPrefixOp " <> show t <> ")"
--   show (TIfExpr tt1 tt2 tt3 t) = "(TIfExpr " <> show tt1 <> " " <> show tt2 <> " " <> show tt3 <> " " <> show t <> ")"
--   show (TArithmSeq s b e t) = "(TArithmSeq " <> show s <> " " <> show b <> " " <> show e <> ".." <> show t <> ")"
--   show (TLetExpr bin tt t) = "(TLetExpr " <> show bin <> " " <> show tt <> " " <> show t <> ")"
--   show (TLambda lb tt t ) = "(TLambda " <> show lb <> " " <> show tt <> " " <> show t <> ")"
--   show (TApp tt1 tl t) = "(TApp " <> show tt1 <> " (" <> show tl <> ") " <> show t <> ")"
--   show (TListComp e qs t) = "(TListComp " <> show e <> " (" <> show qs <> ") " <> show t <> ")"

instance showTypeBinding:: Show TypeBinding where
  show (TLit t) = "(TLit "<> show t <>")"
  show (TConsLit b1 b2 t) = "(TConsLit "<> show b1 <> " " <> show b2 <> " " <> show t <>")"
  show (TListLit lb t) = "(TListLit " <> show lb <> " "<> show t <>")"
  show (TNTupleLit lb t) = "(TNTupleLit " <> show lb <> " "<> show t <>")"

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

-- extractType:: TypeTree -> Type
-- extractType (TAtom t)            = t
-- extractType (TListTree _ t)      = t
-- extractType (TNTuple _ t)        = t
-- extractType (TBinary _ _ _ t)    = t
-- extractType (TUnary _ _ t)       = t
-- extractType (TSectL _ _ t)       = t
-- extractType (TSectR _ _ t)       = t
-- extractType (TPrefixOp t)        = t
-- extractType (TIfExpr _ _ _ t)    = t
-- extractType (TArithmSeq _ _ _ t) = t
-- extractType (TLetExpr _ _ t)     = t
-- extractType (TLambda _ _ t)      = t
-- extractType (TApp _ _ t)         = t
-- extractType (TListComp _ _ t)    = t

-- extractIndex :: IndexTree -> Int
-- extractIndex (IAtom i)            = i
-- extractIndex (IListTree _ i)      = i
-- extractIndex (INTuple _ i)        = i
-- extractIndex (IBinary _ _ _ i)    = i
-- extractIndex (IUnary _ _ i)       = i
-- extractIndex (ISectL _ _ i)       = i
-- extractIndex (ISectR _ _ i)       = i
-- extractIndex (IPrefixOp i)        = i
-- extractIndex (IIfExpr _ _ _ i)    = i
-- extractIndex (IArithmSeq _ _ _ i) = i
-- extractIndex (ILetExpr _ _ i)     = i
-- extractIndex (ILambda _ _ i)      = i
-- extractIndex (IApp _ _ i)         = i
-- extractIndex (IListComp _ _ i)    = i

-- extractBindingType:: TypeBinding -> Type
-- extractBindingType (TLit t)         = t
-- extractBindingType (TConsLit _ _ t) = t
-- extractBindingType (TListLit _ t)   = t
-- extractBindingType (TNTupleLit _ t) = t
