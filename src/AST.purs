module AST where

import Data.String (joinWith)
import Data.Array  ()

data Op = Add | Sub | Mul | Div | And | Or | Cons | Append

data Atom = Num Number
          | Bool Boolean
          | Name String

data Expr = Atom Atom
          | List [Expr]
          | Infix Expr Op Expr
          | SectL Expr Op
          | SectR Op Expr
          | App String [Expr]

data Binding = Lit Atom
             | ListLit Atom Binding

data Definition = Def String [Binding] Expr

instance showOp :: Show Op where
  show op = case op of
    Add    -> "+"
    Sub    -> "-"
    Mul    -> "*"
    Div    -> "`div`"
    And    -> "&&"
    Or     -> "||"
    Cons   -> ":"
    Append -> "++"

instance showAtom :: Show Atom where
  show atom = case atom of
    Num number  -> "(Num " ++ show number ++ ")"
    Bool bool   -> "(Bool " ++ show bool ++ ")"
    Name string -> "(Name " ++ string ++ ")"

instance showExpr :: Show Expr where
  show expr = case expr of
    Atom atom      -> "(Atom " ++ show atom ++ ")"
    List ls        -> "(List [" ++ joinWith ", " (show <$> ls) ++ "])"
    Infix e1 op e2 -> "(Infix " ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
    SectL expr op  -> "(SectL" ++ show expr ++ " " ++ show op ++ ")"
    SectR op expr  -> "(SectR" ++ show op ++ " " ++ show expr ++ ")"
    App name args  -> "(App " ++ name ++ " [" ++ joinWith ", " (show <$> args) ++ "])"

instance showBinding :: Show Binding where
  show binding = case binding of
    Lit atom              -> "(Lit " ++ show atom ++ ")"
    ListLit atom bindings -> "(ListLit " ++ show atom ++ " " ++ show bindings ++ ")"

instance showDefinition :: Show Definition where
  show (Def name bindings body) = "(Def " ++ name ++ " " ++ show bindings ++ show body ++ ")"
