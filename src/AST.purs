module AST where

import Prelude (class Show, class Eq,class Ord, show, (++), (==), (&&),eq, compare,Ordering(..))
import Data.List (List)

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


data IndexTree
          = IAtom                                  Int
          | IListTree (List IndexTree)             Int
          | INTuple (List IndexTree)               Int
          | IBinary Int  IndexTree IndexTree           Int
          | IUnary Int IndexTree                      Int
          | ISectL IndexTree Int                      Int
          | ISectR Int IndexTree                      Int
          | IPrefixOp                              Int
          | IIfExpr IndexTree IndexTree IndexTree  Int
          | ILetExpr IBinding IndexTree IndexTree  Int
          | ILambda (List IBinding) IndexTree      Int
          | IApp IndexTree (List IndexTree)        Int



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


derive instance eqExpr :: Eq Expr

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

type Output = {
    expr :: Expr,
    typ :: TypeTree,
    idTree :: IndexTree
  }

data Path = Nth Int Path
          | Fst Path
          | Snd Path
          | Thrd Path
          | End

instance showPath :: Show Path where
  show p = case p of
    Nth i p -> "(Nth " ++ show i ++ " " ++ show p ++")"
    Fst   p -> "(Fst " ++ show p ++")"
    Snd   p -> "(Snd " ++ show p ++")"
    Thrd   p -> "(Thrd " ++ show p ++")"
    End     -> "End"

derive instance eqDefinition :: Eq Definition

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
