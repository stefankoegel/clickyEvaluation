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
          | IfExpr Expr Expr Expr
          | Lambda (List Binding) Expr
          | App Expr (List Expr)

instance eqEpr :: Eq Expr where
  eq (Atom a1)           (Atom a2)         = a1 == a2
  eq (List l1)           (List l2)         = l1 == l2
  eq (NTuple l1)         (NTuple l2)       = l1 == l2
  eq (Binary o1 e1 e2)   (Binary o2 e3 e4) = o1 == o2 && e1 == e3 && e2 == e4
  eq (Unary o1 e1)       (Unary o2 e2)     = o1 == o2 && e1 == e2
  eq (SectL e1 o1)       (SectL e2 o2)     = e1 == e2 && o1 == o2
  eq (SectR o1 e1)       (SectR o2 e2)     = o1 == o2 && e1 == e2
  eq (IfExpr c1 t1 e1)   (IfExpr c2 t2 e2) = c1 == c2 && t1 == t2 && e1 == e2
  eq (Lambda bs1 e1)     (Lambda bs2 e2)   = bs1 == bs2 && e1 == e2
  eq (App e1 l1)         (App e2 l2)       = e1 == e2 && l1 == l2
  eq _                   _                 = false


foldExpr :: forall a.
               (Atom -> a)
            -> ((List a) -> a)
            -> ((List a) -> a)
            -> (Op -> a -> a -> a)
            -> (Op -> a -> a)
            -> (a -> Op -> a)
            -> (Op -> a -> a)
            -> (a -> a -> a -> a)
            -> ((List Binding) -> a -> a)
            -> (a -> (List a) -> a)
            -> Expr -> a
foldExpr atom list ntuple binary unary sectl sectr ifexpr lambda app = go
  where
  go (Atom a)          = atom a
  go (List es)         = list (go <$> es)
  go (NTuple es)       = ntuple (go <$> es)
  go (Binary op e1 e2) = binary op (go e1) (go e2)
  go (Unary op e)      = unary op (go e)
  go (SectL e op)      = sectl (go e) op
  go (SectR op e)      = sectr op (go e)
  go (IfExpr c te ee)  = ifexpr (go c) (go te) (go ee)
  go (Lambda bs e)     = lambda bs (go e)
  go (App e es)        = app (go e) (go <$> es)


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
    AInt number -> "(AInt " ++ show number ++ ")"
    Bool bool   -> "(Bool " ++ show bool ++ ")"
    Char string -> "(Char " ++ string ++ ")"
    Name string -> "(Name " ++ string ++ ")"

instance showExpr :: Show Expr where
  show expr = case expr of
    Atom atom       -> "(Atom " ++ show atom ++ ")"
    List ls         -> "(List " ++ show ls ++ ")"
    NTuple ls       -> "(NTuple " ++ show ls ++ ")"
    Binary op e1 e2 -> "(Binary " ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
    Unary op e      -> "(Unary " ++ show op ++ " " ++ show e ++ ")"
    SectL expr op   -> "(SectL " ++ show expr ++ " " ++ show op ++ ")"
    SectR op expr   -> "(SectR " ++ show op ++ " " ++ show expr ++ ")"
    IfExpr c te ee  -> "(IfExpr " ++ show c ++ " " ++ show te ++ " " ++ show ee ++ ")"
    Lambda binds body -> "(Lambda " ++ show binds ++ " " ++ show body ++ ")"
    App func args   -> "(App " ++ show func ++ " " ++ show args ++ ")"

instance showBinding :: Show Binding where
  show binding = case binding of
    Lit atom     -> "(Lit " ++ show atom ++ ")"
    ConsLit b bs -> "(ConsLit " ++ show b ++ ":" ++ show bs ++ ")"
    ListLit bs   -> "(ListLit " ++ show bs ++ ")"
    NTupleLit ls -> "(NTupleLit " ++ show ls ++ ")"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "(Def " ++ name ++ " " ++ show bindings ++ " " ++ show body ++ ")"
