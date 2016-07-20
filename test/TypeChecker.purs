module Test.TypeChecker where

import AST (AD(TList, TTuple), Atom(AInt, Name, Char), Binding(Lit, ConsLit, ListLit, NTupleLit), Definition(Def), Expr(Atom, List, SectR, App, Binary, PrefixOp, Lambda, NTuple, LetExpr, SectL), Op(Power, Colon, Add, Append), TVar(TVar), Type(TypCon, TypVar, AD, TypArr), TypeError(InfiniteType, UnificationFail, UnknownError))
import TypeChecker (Subst, Infer, TypeEnv, Scheme(Forall), inferGroup, inferType, inferDef, prettyPrintType, emptyTyenv, runInfer, typeProgramn, eqScheme)
import Parser (expression, definition)

import Prelude (Unit, bind, ($), show, (==), (++))
import Data.Either (Either(..))
import Data.List (List(..), toList)
import Data.Tuple (Tuple(..))

import Text.Parsing.Parser (ParseError, runParser)

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)

import Control.Monad.State

testInfer:: forall a  eff. String -> a -> (TypeEnv -> a -> Infer (Tuple Subst Type))
 -> Either TypeError Scheme -> Eff (console :: CONSOLE | eff ) Unit
testInfer name input f expected
  = test name  expected $ runInfer $ f emptyTyenv input

testProgramm:: forall eff. String -> List Definition -> Expr
 -> Either TypeError Scheme -> Eff (console :: CONSOLE | eff ) Unit
testProgramm name defs exp expected
 = test name expected $ typeProgramn defs exp

-- test  name -> expected -> actuall -> Eff ...
test:: forall eff. String -> Either TypeError Scheme -> Either TypeError Scheme
 -> Eff (console :: CONSOLE | eff ) Unit
test name expected actuall = if eqTypErrScheme expected actuall
  then log $ "Typing success ("  ++ name ++ ")"
  else log $ "\n \n Typing fail (" ++ name ++ ") :  expected result: \n"
    ++ show expected ++ "\n actuall result: \n" ++ show actuall ++ "\n \n"
     ++ "Pretty Print expected: \n" ++ prettyPrint expected
      ++ "\n Pretty Print actuall: \n" ++ prettyPrint actuall ++ "\n \n"

eqTypErrScheme:: Either TypeError Scheme -> Either TypeError Scheme -> Boolean
eqTypErrScheme (Left a) (Left a') = (a == a')
eqTypErrScheme (Right a) (Right a') = eqScheme a a'
eqTypErrScheme _ _ = false


aint :: Int -> Expr
aint i = Atom $ AInt i

aname :: String -> Expr
aname s = Atom $ Name s

tvar :: String -> Type
tvar s = TypVar $ TVar s

out::forall eff. String -> Eff (console :: CONSOLE | eff ) Unit
out s = log s

parseExp:: String -> Either ParseError Expr
parseExp exp = runParser exp expression

parseDef:: String -> Either ParseError Definition
parseDef def = runParser def definition

typeStr:: String -> Either TypeError Scheme
typeStr expS = case runParser expS expression of
  Right exp -> runInfer $ inferType emptyTyenv exp
  Left _ -> Left $ UnknownError "Parse Error"

typeStrPre:: String -> Either TypeError Scheme
typeStrPre expS = case runParser expS expression of
  Right exp -> typeProgramn Test.Parser.parsedPrelude exp
  Left _ -> Left $ UnknownError "Parse Error"

typeExp:: Expr -> Either TypeError Scheme
typeExp exp = runInfer $ inferType emptyTyenv exp

typeDef:: Definition -> Either TypeError Scheme
typeDef def = runInfer $ inferDef emptyTyenv def

prettyPrint:: Either TypeError Scheme -> String
prettyPrint a@(Left _) = show a
prettyPrint (Right (Forall _ t)) = prettyPrintType t

printTypeExp::forall eff. Expr -> Eff (console :: CONSOLE | eff ) Unit
printTypeExp e = out $ prettyPrint $ typeExp e

printTypeStr::forall eff. String -> Eff (console :: CONSOLE | eff ) Unit
printTypeStr s = out $ prettyPrint $ typeStr s

-- default 1
d1 = Right (Forall Nil $ tvar "a")

runTests :: forall eff. Eff (console :: CONSOLE | eff) Unit
runTests = do
  log "Running Typing Tests"

  testInfer "SectL" (SectL (aint 3) Power)
    inferType(Right (Forall Nil $ TypArr (TypCon "Int") (TypCon "Int")))
  testInfer "SectR" (SectR Power (aint 3))
    inferType(Right (Forall (Nil) (TypArr (TypCon "Int") (TypCon "Int"))))
  testInfer "Lambda1" (Lambda (toList $ [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c",Lit $ Name "d"]) (App (aname "a") (toList [aname "b", aname "c", aname "d"])))
    inferType(Right (Forall (toList [TVar "b",TVar "c", TVar "d", TVar "e"]) (TypArr (TypArr (tvar "b") (TypArr (tvar "c") (TypArr (tvar "d") (tvar "e")))) (TypArr ( tvar "b")  ((TypArr (tvar "c") (TypArr (tvar "d") (tvar "e"))))))))
  testInfer "Lambda2" (Lambda (toList [Lit $ Name "a", Lit $ Name "b"]) (App (aname "a") (toList [aname "b"])))
    inferType(Right (Forall (Cons ((TVar "t_3")) (Cons ((TVar "t_4")) (Nil))) (TypArr (TypArr (TypVar  (TVar "t_3")) (TypVar  (TVar "t_4"))) (TypArr (TypVar  (TVar "t_3")) (TypVar  (TVar "t_4"))))))
  testInfer "List1" (List (toList [aint 1, aint 2, aint 3, aint 4, aint 5])) inferType(Right (Forall (Nil) (AD (TList (TypCon "Int")))))
  testInfer "List2" (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4)])
    inferType(Right (Forall (Nil) (AD (TList (TypCon "Int")))))
  testInfer "List3" (List $ toList [PrefixOp Add, aint 4])
    inferType(Left ((UnificationFail (TypCon "Int") (TypArr (TypCon "Int") (TypArr (TypCon "Int") (TypCon "Int"))))))
  testInfer "Nil List" (List Nil)
    inferType  (Right (Forall (Cons ((TVar "t_0")) (Nil)) (AD (TList (TypVar  (TVar "t_0"))))))
  testInfer "Append" (Binary Append
    (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4)])
    (List Nil))
    inferType(Right (Forall (Nil) (AD (TList (TypCon "Int")))))
  testInfer "Colon" (Binary Colon (aint 3) (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4),Atom $ Char "Hallo"]))
    inferType(Left ((UnificationFail (TypCon "Char") (TypCon "Int"))))
  testInfer "NTuple" (NTuple (toList [Binary Add (aint 1) (aint 2), aint 3]))
    inferType(Right (Forall (Nil) (AD (TTuple (Cons ((TypCon "Int")) (Cons ((TypCon "Int")) (Nil)))))))
  testInfer "SectR Colon" (SectR Colon $ List $ toList [aint 3])
    inferType(Right (Forall (Nil) (TypArr (TypCon "Int") (AD (TList (TypCon "Int"))))))
  testInfer "Def ~map" (Def "map" (toList [Lit $ Name "f", Lit $ Name "xs"]) (App (aname "map") (toList [aname "f",aname"xs"])))
    inferDef (Right (Forall (Cons ((TVar "t_2")) (Cons ((TVar "t_4")) (Cons ((TVar "t_5")) (Nil)))) (TypArr (TypVar  (TVar "t_2")) (TypArr (TypVar  (TVar "t_4")) (TypVar  (TVar "t_5"))))))
  testInfer "Lambda Wildcard" (Lambda (toList [Lit (Name "_"), Lit (Name "_")]) (aint 5))
    inferType(Right (Forall (Cons ((TVar "t_1")) (Cons ((TVar "t_3")) (Nil))) (TypArr (TypVar  (TVar "t_1")) (TypArr (TypVar  (TVar "t_3")) (TypCon "Int")))))
  testInfer "Lambda ConsBinding" (Lambda (toList [ConsLit (Lit $ Name "x") (Lit $ Name "xs")]) (aname "x"))
    inferType(Right (Forall (Cons ((TVar "t_2")) (Nil)) (TypArr (AD (TList (TypVar  (TVar "t_2")))) (TypVar  (TVar "t_2")))))
  testInfer "singel map" (Def "map" (toList [Lit $ Name "f", ConsLit (Lit $ Name "x") (Lit $ Name "xs")]) (App  (PrefixOp Colon) (toList [App (aname "f") $ toList [(aname"x")], App (aname "map") (toList [aname"f", aname"xs"])])))
    inferDef (Right (Forall (Cons ((TVar "t_11")) (Cons ((TVar "t_5")) (Nil))) (TypArr (TypArr (TypVar  (TVar "t_5")) (TypVar  (TVar "t_11"))) (TypArr (AD (TList (TypVar  (TVar "t_5")))) (AD (TList (TypVar  (TVar "t_11"))))))))
  testInfer "foldr" (Def "foldr" (toList [Lit $ Name "f", Lit $ Name "ini", ConsLit (Lit $ Name "x") (Lit $ Name "xs")]) (App (aname "f") (toList [aname "x",App (aname "foldr") (toList [aname "f", aname "ini" ,aname "xs"  ] )])))
    inferDef (Right (Forall (Cons ((TVar "t_5")) (Cons ((TVar "t_4")) (Cons ((TVar "t_7")) Nil))) (TypArr (TypArr (TypVar  (TVar "t_7")) (TypArr (TypVar  (TVar "t_4")) (TypVar  (TVar "t_4")))) (TypArr (TypVar  (TVar "t_5")) (TypArr (AD (TList (TypVar  (TVar "t_7")))) (TypVar  (TVar "t_4")))))))
  testInfer "let Expr" (LetExpr (Cons (Tuple (Lit $ Name "x") (aint 3)) Nil) (Lambda (toList [Lit (Name "_"), Lit (Name "_")]) (aname "x")))
    inferType (Right (Forall (Cons ((TVar "t_2")) (Cons ((TVar "t_4")) (Nil))) (TypArr (TypVar  (TVar "t_2")) (TypArr (TypVar  (TVar "t_4")) (TypCon "Int")))))
  testInfer "ConsLit Binding 1" (Def "list" (toList [ConsLit (Lit $ Name "x") (ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "x"))
    inferDef (Right (Forall (Cons ((TVar "t_2")) (Nil)) (TypArr (AD (TList (TypVar  (TVar "t_2")))) (TypVar  (TVar "t_2")))))
  testInfer "ConsLit Binding 2" (Def "list" (toList [ConsLit (Lit $ Name "x") (ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "xs"))
    inferDef (Right (Forall (Cons ((TVar "t_2")) (Nil)) (TypArr (AD (TList (TypVar  (TVar "t_2")))) (TypVar  (TVar "t_2")))))
  testInfer "ConsLit Binding 3" (Def "list" (toList [ConsLit (Lit $ Name "x") (ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "xss"))
    inferDef (Right (Forall (Cons ((TVar "t_2")) (Nil)) (TypArr (AD (TList (TypVar  (TVar "t_2")))) (AD (TList (TypVar  (TVar "t_2")))))))
  testInfer "Binding Tuple 1" (Def "tuple" (toList [NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])]) (aname "a"))
    inferDef (Right (Forall (Cons ((TVar "t_2")) (Cons ((TVar "t_3")) (Nil))) (TypArr (AD (TTuple $ Cons ((TypVar  (TVar "t_2"))) (Cons ((TypVar  (TVar "t_3"))) (Nil)))) (TypVar  (TVar "t_2")))))
  testInfer "Binding Tuple 2" (Def "tuple" (toList [NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])]) (aname "b"))
    inferDef (Right (Forall (Cons ((TVar "t_2")) (Cons ((TVar "t_3")) (Nil))) (TypArr (AD (TTuple (Cons ((TypVar  (TVar "t_2"))) (Cons ((TypVar  (TVar "t_3"))) (Nil))))) (TypVar  (TVar "t_3")))))
  testInfer "Binding Tuple 3" (Def "tuple" (toList [NTupleLit (toList [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c"])]) (App (aname "a") (toList [aname "b", aname "c"])))
    inferDef (Right (Forall (Cons ((TVar "t_3")) (Cons ((TVar "t_4")) (Cons ((TVar "t_5")) (Nil)))) (TypArr (AD (TTuple (Cons ((TypArr (TypVar  (TVar "t_3")) (TypArr (TypVar  (TVar "t_4")) (TypVar  (TVar "t_5"))))) (Cons ((TypVar  (TVar "t_3"))) (Cons ((TypVar  (TVar "t_4"))) (Nil)))))) (TypVar  (TVar "t_5")))))
  testInfer "ListLit Binding" (Def "list" (toList [ListLit (toList [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c"])]) (App (aname "a") (toList [aname "b", aname "c"])))
    inferDef (Left ((InfiniteType (TVar "t_3") (TypArr (TypVar  (TVar "t_3")) (TypVar  (TVar "t_6"))))))
  testInfer "NTupleLit Binding LetExp" (LetExpr (Cons (Tuple (NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])) (NTuple (toList [(Lambda (toList [Lit $ Name "f"]) (aname "f")), (Atom $ Char "Hello")]))) Nil) (App (aname "a") (toList [aname "b"])))
    inferType (Right (Forall (Nil) (TypCon "Char")))
  testInfer "Lambda App" (App (Lambda (Cons (Lit (Name "f")) (Cons (Lit (Name "a")) (Cons (Lit (Name "b")) (Nil)))) (App (Atom (Name "f")) (Cons (Atom (Name "a")) (Cons (Atom (Name "b")) (Nil))))) (Cons (PrefixOp Add) (Cons (Atom (AInt 3)) (Cons (Atom (AInt 4)) (Nil)))))
    inferType (Right (Forall (Nil) (TypCon "Int")))
  testInfer "zipWith - Group" (toList [Def "zipWith" (toList [Lit $ Name "f", ConsLit (Lit $ Name "x") (Lit $ Name "xs"), ConsLit (Lit $ Name "y") (Lit $ Name "ys")])
      (App (PrefixOp Colon) (toList [App (aname "f") (toList [aname "x",aname "y"]), App (aname "zipWith") (toList [aname "f",aname"xs",aname "ys"])])),
      Def "zipWith" (toList [Lit $ Name "_",ListLit Nil,Lit $ Name "_"]) (List Nil),
      Def "zipWith" (toList [Lit $ Name "_",Lit $ Name "_",ListLit Nil]) (List Nil)])
    inferGroup (Right (Forall (Cons ((TVar "t_23")) (Cons ((TVar "t_33")) (Cons ((TVar "t_34")) (Nil)))) (TypArr (TypArr (TypVar  (TVar "t_23")) (TypArr (TypVar  (TVar "t_33")) (TypVar  (TVar "t_34")))) (TypArr (AD (TList (TypVar  (TVar "t_23")))) (TypArr (AD (TList (TypVar  (TVar "t_33")))) (AD (TList (TypVar  (TVar "t_34")))))))))

  testInfer "real foldr - Group" (toList [(Def "foldr" (Cons (Lit (Name "f")) (Cons (Lit (Name "ini")) (Cons (ListLit (Nil)) (Nil)))) (Atom (Name "ini"))),
      (Def "foldr" (Cons (Lit (Name "f")) (Cons (Lit (Name "ini")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (App (Atom (Name "f")) (Cons (Atom (Name "x")) (Cons (App (Atom (Name "foldr")) (Cons (Atom (Name "f")) (Cons (Atom (Name "ini")) (Cons (Atom (Name "xs")) (Nil))))) (Nil)))))])
    inferGroup ((Right (Forall ((Cons ((TVar "t_4")) (Cons ((TVar "t_7")) Nil))) (TypArr (TypArr (TypVar  (TVar "t_7")) (TypArr (TypVar  (TVar "t_4")) (TypVar  (TVar "t_4")))) (TypArr (TypVar  (TVar "t_4")) (TypArr (AD (TList (TypVar  (TVar "t_7")))) (TypVar  (TVar "t_4"))))))))

  testInfer "scanl - Group" (toList [Def "scanl" (Cons (Lit (Name "f")) (Cons (Lit (Name "b")) (Cons (ListLit (Nil)) (Nil)))) (List (Cons (Atom (Name "b")) (Nil))),
                                     Def "scanl" (Cons (Lit (Name "f")) (Cons (Lit (Name "b")) (Cons (ConsLit (Lit (Name "x")) (Lit (Name "xs"))) (Nil)))) (Binary Colon (Atom (Name "b")) (App (Atom (Name "scanl")) (Cons (Atom (Name "f")) (Cons (App (Atom (Name "f")) (Cons (Atom (Name "b")) (Cons (Atom (Name "x")) (Nil)))) (Cons (Atom (Name "xs")) (Nil))))))])
          inferGroup (Right (Forall (Cons ((TVar "t_39")) (Cons ((TVar "t_48")) (Nil))) (TypArr (TypArr (TypVar  (TVar "t_48")) (TypArr (TypVar  (TVar "t_39")) (TypVar  (TVar "t_48")))) (TypArr (TypVar  (TVar "t_48")) (TypArr (AD (TList (TypVar  (TVar "t_39")))) (AD (TList (TypVar  (TVar "t_48")))))))))

  testProgramm "Prelude with exp" Test.Parser.parsedPrelude
    ((App (Atom (Name "sum")) (Cons (App (Atom (Name "map")) (Cons (SectR Power (Atom (AInt 2))) (Cons (List (Cons (Atom (AInt 1)) (Cons (Atom (AInt 2)) (Cons (Atom (AInt 3)) (Cons (Atom (AInt 4)) (Nil)))))) (Nil)))) (Nil))))
    (Right (Forall (Nil) (TypCon "Int")))