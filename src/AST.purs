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
data TypeTree
          = TAtom                                   Type
          | TListTree (List TypeTree)               Type
          | TNTuple (List TypeTree)                 Type
          | TBinary Type TypeTree TypeTree          Type
          | TUnary Type TypeTree                    Type
          | TSectL TypeTree Type                    Type
          | TSectR Type TypeTree                    Type
          | TPrefixOp                               Type
          | TIfExpr TypeTree TypeTree TypeTree      Type
          | TLetExpr TypeBinding TypeTree TypeTree  Type
          | TLambda (List TypeBinding) TypeTree     Type
          | TApp TypeTree (List TypeTree)           Type



data TypeBinding  = TLit                              Type
                  | TConsLit TypeBinding TypeBinding  Type
                  | TListLit (List TypeBinding)       Type
                  | TNTupleLit (List TypeBinding)     Type

data TVar = TVar String

data Type
    = TypVar TVar -- Typ Variables e.x. a
    | TypCon String -- Typ Constants e.x Int
    | TypArr Type Type -- e.x Int -> Int
    | AD AD

data AD
    = TList Type
    | TTuple (List Type)


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

type Output = {
    expr :: Expr,
    typ :: TypeTree
  }

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

pPrintOp :: Op -> String
pPrintOp op = case op of
  Composition -> "."
  Power  -> "^"
  Mul    -> "*"
  Div    -> "`div`"
  Mod    -> "`mod`"
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

instance showType :: Show Type where
  show (TypVar var) = "(TypVar  " ++ show var ++ ")"
  show (TypCon con) = "(TypCon " ++ show con ++ ")"
  show (TypArr t1 t2) = "(TypArr "++ show t1 ++" " ++ show t2 ++ ")"
  show (AD ad) = "(AD "++ show ad ++ ")"

instance eqType :: Eq Type where
  eq (TypVar a) (TypVar b) = a == b
  eq (TypCon a) (TypCon b) = a == b
  eq (TypArr a b) (TypArr a' b') = (a == a') && (b == b')
  eq (AD a) (AD b) = eq a b
  eq _ _ = false

instance ordTVar :: Ord TVar where
  compare (TVar a) (TVar b) = compare a b

instance eqTVar :: Eq TVar where
  eq (TVar a) (TVar b) = a == b

instance showTVar :: Show TVar where
  show (TVar a) = "(TVar " ++ show a ++ ")"

instance showAD :: Show AD where
  show (TList t) = "(TList "++ show t ++")"
  show (TTuple tl) = "(TTuple ("++ show tl ++ "))"

instance eqAD :: Eq AD where
  eq (TList a) (TList b) = eq a b
  eq (TTuple a) (TTuple b) = eq a b

instance showTypeTree :: Show TypeTree where
  show (TAtom t) = "(TAtom " ++ show t ++ ")"
  show (TListTree lt t) = "(TListTree (" ++ show lt ++ ") " ++ show t ++ ")"
  show (TNTuple lt t) = "(TNTuple ("++ show lt ++ ") " ++ show t ++ ")"
  show (TBinary t1 tt1 tt2 t) = "(TBinary " ++ show t1 ++ " " ++ show tt1 ++  " " ++ show tt2 ++ " " ++ show t ++ ")"
  show (TUnary t1 tt t) = "(TUnary "++ show t1 ++ " " ++ show tt ++ " " ++ show t ++ ")"
  show (TSectL tt t1 t) = "(TSectL "++ show tt ++ " "++ show t1 ++ " " ++ show t ++ ")"
  show (TSectR t1 tt t) = "(TSectR " ++ show t1 ++ " " ++ show tt ++ " " ++ show t ++ ")"
  show (TPrefixOp t) = "(TPrefixOp " ++ show t ++ ")"
  show (TIfExpr tt1 tt2 tt3 t) = "(TIfExpr " ++ show tt1 ++ " " ++ show tt2 ++ " " ++ show tt3 ++ " " ++ show t ++ ")"
  show (TLetExpr b tt1 tt2 t) = "(TLetExpr " ++ show b ++ " " ++ show tt1 ++ " " ++ show tt2 ++ " " ++ show t ++ ")"
  show (TLambda lb tt t ) = "(TLambda " ++ show lb ++ " " ++ show tt ++ " " ++ show t ++ ")"
  show (TApp tt1 tl t) = "(TApp " ++ show tt1 ++ " (" ++ show tl ++ ") " ++ show t ++ ")"


instance showTypeBinding:: Show TypeBinding where
  show (TLit t) = "(TLit "++ show t ++")"
  show (TConsLit b1 b2 t) = "(TConsLit "++ show b1 ++ " " ++ show b2 ++ " " ++ show t ++")"
  show (TListLit lb t) = "(TListLit " ++ show lb ++ " "++ show t ++")"
  show (TNTupleLit lb t) = "(TNTupleLit " ++ show lb ++ " "++ show t ++")"
