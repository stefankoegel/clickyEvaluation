module AST where

import Prelude
import Data.List

-- | Operators
-- |
-- | Primitive infix operators that are evaluated directly by the `Evaluator`.
-- | (`Colon` is `Cons` but clashes with `Data.List.Cons`)
data Op = Composition
        | Power
        | Mul | Div | Mod
        | Add | Sub
        | Colon | Append
        | Equ | Neq | Lt | Leq | Gt | Geq
        | And
        | Or
        | Dollar

instance eqOp :: Eq Op where
  eq Composition Composition = true
  eq Power Power = true
  eq Mul  Mul  = true
  eq Div  Div  = true
  eq Mod Mod = true
  eq Add  Add  = true
  eq Sub Sub = true
  eq Colon  Colon  = true
  eq Append Append = true
  eq Equ  Equ  = true
  eq Neq  Neq  = true
  eq Lt  Lt  = true
  eq Leq  Leq  = true
  eq Gt  Gt  = true
  eq Geq Geq = true
  eq And And = true
  eq Or Or = true
  eq Dollar Dollar = true
  eq _ _ = false

-- | Atoms
-- |
-- | Primitive data types
data Atom = AInt Int
          | Bool Boolean
          | Char String
          | Name String

instance eqAtom :: Eq Atom where
  eq (AInt i)   (AInt j) =  i == j
  eq (Bool b1) (Bool b2) = b1 == b2
  eq (Char s1) (Char s2) = s1 == s2
  eq (Name s1) (Name s2) = s1 == s2
  eq _ _ = false

instance ordAtom :: Ord Atom where
  compare (AInt a) (AInt b) = compare a b
  compare (Bool a) (Bool b) = compare a b
  compare (Char a) (Char b) = compare a b
  compare (Name a) (Name b) = compare a b
  compare _ _ = EQ

-- | Expressions
-- |
-- | The basic expressions the `Parser` and `Evaluator` recognize.
data Expr = Atom Atom
          | List (List Expr)
          | NTuple (List Expr)
          | Binary Op Expr Expr
          | Unary Op Expr
          | SectL Expr Op
          | SectR Op Expr
          | PrefixOp Op
          | IfExpr Expr Expr Expr
          | LetExpr Binding Expr Expr
          | Lambda (List Binding) Expr
          | App Expr (List Expr)


-- last type para is type of expr at this level
-- e.x. Binary (Op_Type) (Exp1_TypeTree) (Exp2_TypeTree)
-- bindings are ignored
data TypeTree
          = Atom                                Type
          | List (List TypeTree)                Type
          | NTuple (List TypeTree)              Type
          | Binary Type TypeTree TypeTree       Type
          | Unary Type TypeTree                 Type
          | SectL TypeTree Type                 Type
          | SectR Type TypeTree                 Type
          | PrefixOp                            Type
          | IfExpr TypeTree TypeTree TypeTree   Type
          | LetExpr TypeTree TypeTree           Type
          | Lambda TypeTree                     Type
          | App TypeTree (List TypeTree)        Type


instance eqExpr :: Eq Expr where
  eq (Atom a1)           (Atom a2)         = a1 == a2
  eq (List l1)           (List l2)         = l1 == l2
  eq (NTuple l1)         (NTuple l2)       = l1 == l2
  eq (Binary o1 e1 e2)   (Binary o2 e3 e4) = o1 == o2 && e1 == e3 && e2 == e4
  eq (Unary o1 e1)       (Unary o2 e2)     = o1 == o2 && e1 == e2
  eq (SectL e1 o1)       (SectL e2 o2)     = e1 == e2 && o1 == o2
  eq (SectR o1 e1)       (SectR o2 e2)     = o1 == o2 && e1 == e2
  eq (PrefixOp o1)       (PrefixOp o2)     = o1 == o2
  eq (IfExpr c1 t1 e1)   (IfExpr c2 t2 e2) = c1 == c2 && t1 == t2 && e1 == e2
  eq (LetExpr a b c)     (LetExpr d e f)   = a == d && b == e && c == f
  eq (Lambda bs1 e1)     (Lambda bs2 e2)   = bs1 == bs2 && e1 == e2
  eq (App e1 l1)         (App e2 l2)       = e1 == e2 && l1 == l2
  eq _                   _                 = false

-- | Bindings
-- |
-- | Binding forms for pattern matching on lists and tuples
data Binding = Lit Atom
             | ConsLit Binding Binding
             | ListLit (List Binding)
             | NTupleLit (List Binding)

instance eqBinding :: Eq Binding where
  eq (Lit a1) (Lit a2) = a1 == a2
  eq (ConsLit b1 b2) (ConsLit b3 b4) = b1 == b3 && b2 == b4
  eq (ListLit l1) (ListLit l2) = l1 == l2
  eq (NTupleLit l1) (NTupleLit l2) = l1 == l2
  eq _ _ = false

-- | Definitions
-- |
-- | Definitions for functions and constants
data Definition = Def String (List Binding) Expr

instance eqDefinition :: Eq Definition where
  eq (Def n1 b1 e1) (Def n2 b2 e2) = n1 == n2 && b1 == b2 && e1 == e2

instance showOp :: Show Op where
  show op = case op of
    Composition -> "Composition"
    Power  -> "Power"
    Mul    -> "Mul"
    Div    -> "Div"
    Mod    -> "Mod"
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

instance showAtom :: Show Atom where
  show atom = case atom of
    AInt number -> "AInt " ++ show number
    Bool bool   -> "Bool " ++ show bool
    Char string -> "Char " ++ show string
    Name string -> "Name " ++ show string

instance showExpr :: Show Expr where
  show expr = case expr of
    Atom atom       -> "Atom (" ++ show atom ++ ")"
    List ls         -> "List (" ++ show ls ++ ")"
    NTuple ls       -> "NTuple (" ++ show ls ++ ")"
    Binary op e1 e2 -> "Binary " ++ show op ++ " (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
    Unary op e      -> "Unary " ++ show op ++ " (" ++ show e ++ ")"
    SectL expr op   -> "SectL (" ++ show expr ++ ") " ++ show op
    SectR op expr   -> "SectR " ++ show op ++ " (" ++ show expr ++ ")"
    PrefixOp op     -> "PrefixOp " ++ show op
    IfExpr ce te ee  -> "IfExpr (" ++ show ce ++ ") (" ++ show te ++ ") (" ++ show ee ++ ")"
    LetExpr b l e   -> "LetExpr (" ++ show b ++ ") (" ++ show l ++ ") (" ++ show e ++ ")"
    Lambda binds body -> "Lambda (" ++ show binds ++ ") (" ++ show body ++ ")"
    App func args   -> "App (" ++ show func ++ ") (" ++ show args ++ ")"

instance showBinding :: Show Binding where
  show binding = case binding of
    Lit atom     -> "Lit (" ++ show atom ++ ")"
    ConsLit b bs -> "ConsLit (" ++ show b ++ ") (" ++ show bs ++ ")"
    ListLit bs   -> "ListLit (" ++ show bs ++ ")"
    NTupleLit ls -> "NTupleLit (" ++ show ls ++ ")"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "Def " ++ show name ++ " (" ++ show bindings ++ ") (" ++ show body ++ ")"
