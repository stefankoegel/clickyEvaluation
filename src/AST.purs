module AST where

import Prelude
import Data.String (joinWith)
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
          | Prefix Op
          | IfExpr Expr Expr Expr
          | Lambda (List Binding) Expr
          | App Expr (List Expr)

foldExpr :: forall a.
               (Atom -> a)
            -> ((List a) -> a)
            -> ((List a) -> a)
            -> (Op -> a -> a -> a)
            -> (Op -> a -> a)
            -> (a -> Op -> a)
            -> (Op -> a -> a)
            -> (Op -> a)
            -> (a -> a -> a -> a)
            -> ((List Binding) -> a -> a)
            -> (a -> (List a) -> a)
            -> Expr -> a
foldExpr atom list ntuple binary unary sectl sectr prefix ifexpr lambda app = go
  where
  go (Atom a)          = atom a
  go (List es)         = list (go <$> es)
  go (NTuple es)       = ntuple (go <$> es)
  go (Binary op e1 e2) = binary op (go e1) (go e2)
  go (Unary op e)      = unary op (go e)
  go (SectL e op)      = sectl (go e) op
  go (SectR op e)      = sectr op (go e)
  go (Prefix op)       = prefix op
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
    Binary op e1 e2 -> "(Binary " ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
    Unary op e      -> "(Unary " ++ show op ++ " " ++ show e ++ ")"
    SectL expr op   -> "(SectL " ++ show expr ++ " " ++ show op ++ ")"
    SectR op expr   -> "(SectR " ++ show op ++ " " ++ show expr ++ ")"
    Prefix op       -> "(Prefix " ++ show op ++ ")"
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
