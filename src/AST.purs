module AST 
  ( Tree(..)
  , Atom(..)
  , Op(..)
  , pPrintOp
  , Binding(..)
  , Definition(..)
  , Expr
  ) where

import Prelude
import Data.List (List)

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

data Tree a b c = 
    Atom c a
  | List c (List Expr)
  | NTuple c (List Expr)
  | Binary c Op Expr Expr
  | Unary c Op Expr
  | SectL c Expr Op
  | SectR c Op Expr
  | PrefixOp c Op
  | IfExpr c Expr Expr Expr
  | LetExpr c Binding Expr Expr
  | Lambda c (List b) Expr
  | App c Expr (List Expr)

derive instance eqTree :: (Eq a, Eq b, Eq c) => Eq (Tree a b c)

type Expr = Tree Atom Binding Unit


-- last type para is type of expr at this level
-- e.x. Binary (Op_Type) (Exp1_TypeTree) (Exp2_TypeTree)
type TypeTree = Tree Unit TypeBinding Type

type IndexTree = Tree Unit IBinding Int

data TypeBinding  = TLit                              Type
                  | TConsLit TypeBinding TypeBinding  Type
                  | TListLit (List TypeBinding)       Type
                  | TNTupleLit (List TypeBinding)     Type


data IBinding  = ILit                       Int
              | IConsLit IBinding IBinding  Int
              | IListLit (List IBinding)    Int
              | INTupleLit (List IBinding)  Int

data TVar = TVar String

data Type
    = TypVar TVar -- Typ Variables e.x. a
    | TypCon String -- Typ Constants e.x Int
    | TypArr Type Type -- e.x Int -> Int
    | AD AD
    | TypeError TypeError

data AD
    = TList Type
    | TTuple (List Type)


data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  | UnificationMismatch (List Type) (List Type)
  | UnknownError String


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
    InfixFunc name -> "(InfixFunc " ++ name ++ ")"

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
  InfixFunc n -> "`" ++ n ++ "`"

instance showAtom :: Show Atom where
  show atom = case atom of
    AInt number -> "AInt " ++ show number
    Bool bool   -> "Bool " ++ show bool
    Char string -> "Char " ++ show string
    Name string -> "Name " ++ show string

instance showExpr :: (Show a, Show b, Show c) => Show (Tree a b c) where
  show expr = case expr of
    Atom c atom         -> "(Atom " ++ show c ++ " "++ show atom ++ ")"
    List c ls           -> "(List " ++ show c ++ " "++ show ls ++  ")"
    NTuple c ls         -> "(NTuple " ++ show c ++ " "++ show ls ++  ")"
    Binary c op e1 e2   -> "(Binary " ++ show c ++ " "++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++  ")"
    Unary c op e        -> "(Unary " ++ show c ++ " "++ show op ++ " " ++ show e ++  ")"
    SectL c expr op     -> "(SectL " ++ show c ++ " "++ show expr ++ " " ++ show op ++  ")"
    SectR c op expr     -> "(SectR " ++ show c ++ " "++ show op ++ " " ++ show expr ++  ")"
    PrefixOp c op       -> "(PrefixOp " ++ show c ++ " " ++ show op ++ ")"
    IfExpr c ce te ee   -> "(IfExpr " ++ show c ++ " "++ show ce ++ " " ++ show te ++ " " ++ show ee ++  ")"
    LetExpr c b l e     -> "(LetExpr " ++ show c ++ " "++ show b ++ " " ++ show l ++ " " ++ show e ++  ")"
    Lambda c binds body -> "(Lambda " ++ show c ++ " "++ show binds ++ " " ++ show body ++  ")"
    App c func args     -> "(App " ++ show c ++ " "++ show func ++ " " ++ show args ++  ")"

instance showBinding :: Show Binding where
  show binding = case binding of
    Lit atom     -> "Lit (" ++ show atom ++ ")"
    ConsLit b bs -> "ConsLit (" ++ show b ++ ") (" ++ show bs ++ ")"
    ListLit bs   -> "ListLit (" ++ show bs ++ ")"
    NTupleLit ls -> "NTupleLit (" ++ show ls ++ ")"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "Def " ++ show name ++ " (" ++ show bindings ++ ") (" ++ show body ++ ")"

instance showType :: Show Type where
  show (TypVar var) = "(TypVar  " ++ show var ++ ")"
  show (TypCon con) = "(TypCon " ++ show con ++ ")"
  show (TypArr t1 t2) = "(TypArr "++ show t1 ++" " ++ show t2 ++ ")"
  show (AD ad) = "(AD "++ show ad ++ ")"
  show (TypeError err) ="(TypeError "++ show err ++")"

derive instance eqType :: Eq Type

derive instance ordTVar :: Ord TVar

derive instance eqTVar :: Eq TVar

instance showTVar :: Show TVar where
  show (TVar a) = "(TVar " ++ show a ++ ")"

instance showAD :: Show AD where
  show (TList t) = "(TList "++ show t ++")"
  show (TTuple tl) = "(TTuple ("++ show tl ++ "))"

derive instance eqAD :: Eq AD

instance showTypeError :: Show TypeError where
  show (UnificationFail a b) = "(UnificationFail "++ show a ++ " " ++ show b ++")"
  show (InfiniteType a b ) = "(InfiniteType " ++ show a ++ " " ++ show b ++ ")"
  show (UnboundVariable a) = "(UnboundVariable " ++ show a ++ ")"
  show (UnificationMismatch a b) = "(UnificationMismatch " ++ show a ++ " " ++ show b ++ ")"
  show (UnknownError a) = "(UnknownError " ++ show a ++ ")"

derive instance eqTypeError :: Eq TypeError

instance showTypeBinding:: Show TypeBinding where
  show (TLit t) = "(TLit "++ show t ++")"
  show (TConsLit b1 b2 t) = "(TConsLit "++ show b1 ++ " " ++ show b2 ++ " " ++ show t ++")"
  show (TListLit lb t) = "(TListLit " ++ show lb ++ " "++ show t ++")"
  show (TNTupleLit lb t) = "(TNTupleLit " ++ show lb ++ " "++ show t ++")"
