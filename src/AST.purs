module AST where

import Prelude (class Eq, class Ord, class Show, map, show, (<>), (<<<), ($))
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
          | ArithmSeq Expr (Maybe Expr) (Maybe Expr)
          | LetExpr (List (Tuple Binding Expr)) Expr
          | Lambda (List Binding) Expr
          | App Expr (List Expr)
          | ListComp Expr (List (ExprQual))          

data Qual b e = Gen b e | Let b e | Guard e

data QualTree b e t = 
    TGen b e t
  | TLet b e t
  | TGuard e t 

type ExprQual = Qual Binding Expr

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
          | TArithmSeq TypeTree (Maybe TypeTree) (Maybe TypeTree) Type
          | TLetExpr (List (Tuple TypeBinding TypeTree)) TypeTree  Type
          | TLambda (List TypeBinding) TypeTree     Type
          | TApp TypeTree (List TypeTree)           Type
          | TListComp TypeTree (List TypeQual) Type

type TypeQual  = QualTree TypeBinding TypeTree Type

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
          | IArithmSeq IndexTree (Maybe IndexTree) (Maybe IndexTree) Int
          | ILetExpr (List (Tuple IBinding IndexTree)) IndexTree  Int
          | ILambda (List IBinding) IndexTree      Int
          | IApp IndexTree (List IndexTree)        Int
          | IListComp IndexTree (List IndexQual) Int

type IndexQual = QualTree IBinding IndexTree Int

data TypeBinding  = TLit                              Type
                  | TConsLit TypeBinding TypeBinding  Type
                  | TListLit (List TypeBinding)       Type
                  | TNTupleLit (List TypeBinding)     Type

data IBinding  = ILit                       Int
              | IConsLit IBinding IBinding  Int
              | IListLit (List IBinding)    Int
              | INTupleLit (List IBinding)  Int

type TVar = String

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
  | UnknownError String
  | NoInstanceOfEnum Type

derive instance eqExpr :: Eq Expr

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
    Nth i p -> "(Nth " <> show i <> " " <> show p <>")"
    Fst   p -> "(Fst " <> show p <>")"
    Snd   p -> "(Snd " <> show p <>")"
    Thrd   p -> "(Thrd " <> show p <>")"
    End     -> "End"

derive instance eqDefinition :: Eq Definition

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

instance showExpr :: Show Expr where
  show expr = case expr of
    Atom atom       -> "Atom (" <> show atom <> ")"
    List ls         -> "List (" <> show ls <> ")"
    NTuple ls       -> "NTuple (" <> show ls <> ")"
    Binary op e1 e2 -> "Binary " <> show op <> " (" <> show e1 <> ") (" <> show e2 <> ")"
    Unary op e      -> "Unary " <> show op <> " (" <> show e <> ")"
    SectL expr op   -> "SectL (" <> show expr <> ") " <> show op
    SectR op expr   -> "SectR " <> show op <> " (" <> show expr <> ")"
    PrefixOp op     -> "PrefixOp " <> show op
    IfExpr ce te ee  -> "IfExpr (" <> show ce <> ") (" <> show te <> ") (" <> show ee <> ")"
    ArithmSeq s by e -> "ArithmSeq (" <> show s <> ")" <> show by <> ".." <> show e <> ")"
    LetExpr b e   -> "LetExpr (" <> show b <> ") (" <> show e <> ")"
    Lambda binds body -> "Lambda (" <> show binds <> ") (" <> show body <> ")"
    App func args   -> "App (" <> show func <> ") (" <> show args <> ")"
    ListComp expr quals -> "ListComp (" <> show expr <> ")" <> "(" <> show quals <> "))"

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

instance showTypeTree :: Show TypeTree where
  show (TAtom t) = "(TAtom " <> show t <> ")"
  show (TListTree lt t) = "(TListTree (" <> show lt <> ") " <> show t <> ")"
  show (TNTuple lt t) = "(TNTuple ("<> show lt <> ") " <> show t <> ")"
  show (TBinary t1 tt1 tt2 t) = "(TBinary " <> show t1 <> " " <> show tt1 <>  " " <> show tt2 <> " " <> show t <> ")"
  show (TUnary t1 tt t) = "(TUnary "<> show t1 <> " " <> show tt <> " " <> show t <> ")"
  show (TSectL tt t1 t) = "(TSectL "<> show tt <> " "<> show t1 <> " " <> show t <> ")"
  show (TSectR t1 tt t) = "(TSectR " <> show t1 <> " " <> show tt <> " " <> show t <> ")"
  show (TPrefixOp t) = "(TPrefixOp " <> show t <> ")"
  show (TIfExpr tt1 tt2 tt3 t) = "(TIfExpr " <> show tt1 <> " " <> show tt2 <> " " <> show tt3 <> " " <> show t <> ")"
  show (TArithmSeq s b e t) = "(TArithmSeq " <> show s <> " " <> show b <> " " <> show e <> ".." <> show t <> ")"
  show (TLetExpr bin tt t) = "(TLetExpr " <> show bin <> " " <> show tt <> " " <> show t <> ")"
  show (TLambda lb tt t ) = "(TLambda " <> show lb <> " " <> show tt <> " " <> show t <> ")"
  show (TApp tt1 tl t) = "(TApp " <> show tt1 <> " (" <> show tl <> ") " <> show t <> ")"
  show (TListComp e qs t) = "(TListComp " <> show e <> " (" <> show qs <> ") " <> show t <> ")"

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

extractType:: TypeTree -> Type
extractType (TAtom t)            = t
extractType (TListTree _ t)      = t
extractType (TNTuple _ t)        = t
extractType (TBinary _ _ _ t)    = t
extractType (TUnary _ _ t)       = t
extractType (TSectL _ _ t)       = t
extractType (TSectR _ _ t)       = t
extractType (TPrefixOp t)        = t
extractType (TIfExpr _ _ _ t)    = t
extractType (TArithmSeq _ _ _ t) = t
extractType (TLetExpr _ _ t)     = t
extractType (TLambda _ _ t)      = t
extractType (TApp _ _ t)         = t
extractType (TListComp _ _ t)    = t

extractIndex :: IndexTree -> Int
extractIndex (IAtom i)            = i
extractIndex (IListTree _ i)      = i
extractIndex (INTuple _ i)        = i
extractIndex (IBinary _ _ _ i)    = i
extractIndex (IUnary _ _ i)       = i
extractIndex (ISectL _ _ i)       = i
extractIndex (ISectR _ _ i)       = i
extractIndex (IPrefixOp i)        = i
extractIndex (IIfExpr _ _ _ i)    = i
extractIndex (IArithmSeq _ _ _ i) = i
extractIndex (ILetExpr _ _ i)     = i
extractIndex (ILambda _ _ i)      = i
extractIndex (IApp _ _ i)         = i
extractIndex (IListComp _ _ i)    = i

extractBindingType:: TypeBinding -> Type
extractBindingType (TLit t)         = t
extractBindingType (TConsLit _ _ t) = t
extractBindingType (TListLit _ t)   = t
extractBindingType (TNTupleLit _ t) = t
