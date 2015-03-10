module AST where

import Data.String (joinWith)
import Data.Array  ()

data Op = Composition
        | Power
        | Mul | Div | Mod
        | Add | Sub
        | Cons | Append
        | Eq | Neq | Lt | Leq | Gt | Geq
        | And
        | Or
        | Dollar

data Atom = Num Number
          | Bool Boolean
          | Name String

data Expr = Atom Atom
          | List [Expr]
          | Binary Op Expr Expr
          | Unary Op Expr
          | SectL Expr Op
          | SectR Op Expr
          | Prefix Op
          | App Expr [Expr]

data Binding = Lit Atom
             | ConsLit Binding Binding
             | ListLit [Binding]

data Definition = Def String [Binding] Expr

instance showOp :: Show Op where
  show op = case op of
    Composition -> "."
    Power  -> "^"
    Mul    -> "*"
    Div    -> "`div`"
    Mod    -> "`mod`"
    Add    -> "+"
    Sub    -> "-"
    Cons   -> ":"
    Append -> "++"
    Eq     -> "=="
    Neq    -> "/="
    Lt     -> "<"
    Leq    -> "<="
    Gt     -> ">"
    Geq    -> ">="
    And    -> "&&"
    Or     -> "||"
    Dollar -> "$"

instance showAtom :: Show Atom where
  show atom = case atom of
    Num number  -> "(Num " ++ show number ++ ")"
    Bool bool   -> "(Bool " ++ show bool ++ ")"
    Name string -> "(Name " ++ string ++ ")"

instance showExpr :: Show Expr where
  show expr = case expr of
    Atom atom       -> "(Atom " ++ show atom ++ ")"
    List ls         -> "(List [" ++ joinWith ", " (show <$> ls) ++ "])"
    Binary op e1 e2 -> "(Binary " ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
    Unary op e      -> "(Unary " ++ show op ++ " " ++ show e ++ ")"
    SectL expr op   -> "(SectL " ++ show expr ++ " " ++ show op ++ ")"
    SectR op expr   -> "(SectR " ++ show op ++ " " ++ show expr ++ ")"
    App func args   -> "(App " ++ show func ++ " [" ++ joinWith ", " (show <$> args) ++ "])"

instance showBinding :: Show Binding where
  show binding = case binding of
    Lit atom     -> "(Lit " ++ show atom ++ ")"
    ConsLit b bs -> "(ConsLit " ++ show b ++ ":" ++ show bs ++ ")"
    ListLit bs   -> "(ListLit [" ++ joinWith ", " (show <$> bs) ++ "])"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "(Def " ++ name ++ " " ++ show bindings ++ " " ++ show body ++ ")"
