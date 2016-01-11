module Test.TypeChecker where

import AST
import TypeChecker
import Parser

import Prelude hiding (apply,compose)
import Data.Either
import Data.List
import Data.Tuple
import Data.Map as Map
import Data.Maybe

import Text.Parsing.Parser

import Control.Monad.Eff
import Control.Monad.Eff.Console

import Control.Monad.Except.Trans
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
  else log $ "Typing fail (" ++ name ++ ") :  expected result: "
    ++ show expected ++ " actuall result: " ++ show actuall

eqTypErrScheme:: Either TypeError Scheme -> Either TypeError Scheme -> Boolean
eqTypErrScheme (Left a) (Left a') = (a == a')
eqTypErrScheme (Right a) (Right a') = eqScheme a a'
  -- let m =  unify a a' in  case evalState (runExceptT m) initUnique of
  -- Left _ -> false
  -- Right _ -> true
eqTypErrScheme _ _ = false

eqScheme :: Scheme -> Scheme -> Boolean
eqScheme (Forall l1 t1) (Forall l2 t2) = ((length l1) == (length l2)) && (fst (eqType Map.empty t1 t2))

eqType:: Map.Map TVar TVar -> Type -> Type ->Tuple Boolean (Map.Map TVar TVar)
eqType map (TypVar a) (TypVar b) = case  Map.lookup a map of
  (Just b') -> Tuple (b' == b) (map)
  Nothing -> Tuple true (Map.insert a b map)
eqType map (TypCon a) (TypCon b) = Tuple (a == b) map
eqType map (TypArr a b) (TypArr a' b') = Tuple (fst tup1 && fst tup2) (snd tup2)
  where
  tup1 = eqType map a a'
  tup2 = eqType (snd tup1) b b'
eqType map (AD (TList a)) (AD (TList b)) = eqType map a b
eqType map (AD (TTuple a)) (AD (TTuple b)) = eqTypeList map a b

eqTypeList:: Map.Map TVar TVar -> List Type -> List Type -> Tuple Boolean (Map.Map TVar TVar)
eqTypeList map (Cons a as) (Cons b bs) = let tup1 = eqType map a b in if (fst tup1)
  then eqTypeList (snd tup1) as bs
  else Tuple false (snd tup1)
eqTypeList map Nil Nil = Tuple true map
eqTypeList map _ _ = Tuple false map

aint :: Int -> Expr
aint i = Atom $ AInt i

aname :: String -> Expr
aname s = Atom $ Name s

tvar :: String -> Type
tvar s = TypVar $ TVar s

out::forall eff. String -> Eff (console :: CONSOLE | eff ) Unit
out s = log s

typeStr:: String -> Either TypeError Scheme
typeStr expS = case runParser expS expression of
  Right exp -> runInfer $ infer emptyTyenv exp
  Left _ -> Left $ UnknownError "Parse Error"

typeExp:: Expr -> Either TypeError Scheme
typeExp exp = runInfer $ infer emptyTyenv exp

prettyPrint:: Either TypeError Scheme -> String
prettyPrint a@(Left _) = show a
prettyPrint (Right (Forall _ t)) = f t
  where
  f (TypVar a) = show a
  f (TypCon a) = show a
  f (TypArr t1 t2) = "(" ++ f t1 ++ " -> " ++ f t2 ++ ")"
  f (AD a) = show a

printTypeExp::forall eff. Expr -> Eff (console :: CONSOLE | eff ) Unit
printTypeExp e = out $ prettyPrint $ typeExp e

printTypeStr::forall eff. String -> Eff (console :: CONSOLE | eff ) Unit
printTypeStr s = out $ prettyPrint $ typeStr s

runTests :: forall eff. Eff (console :: CONSOLE | eff) Unit
runTests = do
  log "Running Typing Tests"

  testInfer "SectL" (SectL (aint 3) Power) infer (Right (Forall Nil $ TypArr (TypCon "Int") (TypCon "Int")))
  testInfer "Lambda1" (Lambda (toList $ [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c",Lit $ Name "d"]) (App (aname "a") (toList [aname "b", aname "c", aname "d"])))
    infer (Right (Forall (toList [TVar "b",TVar "c", TVar "d", TVar "e"]) (TypArr (TypArr (tvar "b") (TypArr (tvar "c") (TypArr (tvar "d") (tvar "e")))) (TypArr ( tvar "b")  ((TypArr (tvar "c") (TypArr (tvar "d") (tvar "e"))))))))
  testInfer "Lambda2" (Lambda (toList [Lit $ Name "a", Lit $ Name "b"]) (App (aname "a") (toList [aname "b"])))
    infer (Right (Forall (Cons ((TVar "t_3")) (Cons ((TVar "t_4")) (Nil))) (TypArr (TypArr (TypVar  (TVar "t_3")) (TypVar  (TVar "t_4"))) (TypArr (TypVar  (TVar "t_3")) (TypVar  (TVar "t_4"))))))


testExp2 = (Lambda (toList [Lit $ Name "a", Lit $ Name "b"]) (App (aname "a") (toList [aname "b"])))
testExp3 = (SectL (aint 3) Power)
testExp4 = (SectR  Power (aint 3))
testExp5 = (List (toList [aint 1, aint 2, aint 3, aint 4, aint 5]))
testExp6 = (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4)])
testExp7 = (List $ toList [PrefixOp Add, aint 4])
testExp8 = (List Nil)
testExp9 = (Binary Append
  (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4)])
  (List Nil))
testExp10 = (Binary Colon (aint 3) (List $ toList [Binary Add (aint 1) (aint 2), Binary Add (aint 3) (aint 4),Atom $ Char "Hallo"]))
testExp11 = NTuple (toList [Binary Add (aint 1) (aint 2), aint 3])
testExp12 = (SectR Colon $ List $ toList [aint 3])
testExp13 = (SectL (aint 3) Colon)
testExp14 = (Def "map" (toList [Lit $ Name "f", Lit $ Name "xs"]) (App (aname "map") (toList [aname "f",aname"xs"])))
testExp15 = (Lambda (toList [Lit (Name "_"), Lit (Name "_")]) (aint 5))
testExp16 = (Lambda (toList [ConsLit (Lit $ Name "x") (Lit $ Name "xs")]) (aname "x"))
testExp17 = Def "map" (toList [Lit $ Name "f", ConsLit (Lit $ Name "x") (Lit $ Name "xs")]) (App  (PrefixOp Colon) (toList [App (aname "f") $ toList [(aname"x")], App (aname "map") (toList [aname"f", aname"xs"])]))
testExp18 = Def "foldr" (toList [Lit $ Name "f", Lit $ Name "ini", ConsLit (Lit $ Name "x") (Lit $ Name "xs")]) (App (aname "f") (toList [aname "x",App (aname "foldr") (toList [aname "f", aname"ini", aname"xs"])]))
testExp19 = Def "fold" (toList [Lit $ Name "f", Lit $ Name "ini", Lit $ Name "x", Lit $ Name "xs"]) (App (aname "f") (toList [aname "x", App (aname "fold") (toList [aname "f", aname "ini", aname"x", aname"xs"])]))
testExp20 = Def "f" (toList [Lit $ Name "fs",Lit $ Name "x"]) (App (aname "fs") (toList [aname "x", App (aname "f") (toList [aname "fs",aname "x"])]))
testExp21 = Def "f" (toList [Lit $ Name "x"]) (App (aname "f") (toList [aname "x"]))
testExp22 = (LetExpr (Lit $ Name "x") (aint 3) (Lambda (toList [Lit (Name "_"), Lit (Name "_")]) (aname "x")))
testExp24 = Def "list" (toList [ListLit (toList [(Lit $ Name "x1"),Lit $ Name "x2"])]) (aname "x1")

testExp25 = Def "list" (toList [ConsLit (Lit $ Name "x") (ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "xs")
testExp26 = Def "list" (toList [ConsLit (Lit $ Name "x") (ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "xss")
testExp27 = Def "list" (toList [(ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "xss")

testExp23 = Def "list" (toList [ConsLit (Lit $ Name "x") (ConsLit (Lit $ Name "xs")(Lit $ Name "xss"))]) (aname "x") --wrong

testExp30 = Def "tuple" (toList [NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])]) (aname "b")
testExp31 = Def "tuple" (toList [NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])]) (aname "a")
testExp32 = Def "tuple" (toList [NTupleLit (toList [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c"])]) (App (aname "a") (toList [aname "b", aname "c"]))
testExp33 = Def "list" (toList [ListLit (toList [Lit $ Name "a",Lit $ Name "b",Lit $ Name "c"])]) (App (aname "a") (toList [aname "b", aname "c"]))

testExp34 = LetExpr (NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])) (NTuple (toList [(Lambda (toList [Lit $ Name "f"]) (aname "f")), (Atom $ Char "Hello")])) (App (aname "a") (toList [aname "b"]))
testExp35 = LetExpr (NTupleLit (toList [Lit $ Name "a",Lit $ Name "b"])) (NTuple (toList [(Lambda (toList [Lit $ Name "f"]) (aname "f")), (Atom $ Char "Hello")])) (aname "a")

testExp36 = toList [testExp17,testExp37]
testExp37 = Def "map" (toList [Lit $ Name "f", ListLit Nil]) (List Nil)

testExp40 = toList [Def "a" (Nil) (aint 3),Def "a" (toList [Lit $ Name "x"]) (aint 5)]

testExp41 = Def "zipWith" (toList [Lit $ Name "f", ConsLit (Lit $ Name "x") (Lit $ Name "xs"), ConsLit (Lit $ Name "y") (Lit $ Name "ys")])
  (App (PrefixOp Colon) (toList [App (aname "f") (toList [aname "x",aname "y"]), App (aname "zipWith") (toList [aname "f",aname"xs",aname "ys"])]))
textExp42 = Def "zipWith" (toList [Lit $ Name "_",ListLit Nil,Lit $ Name "_"]) (List Nil)
textExp43 = Def "zipWith" (toList [Lit $ Name "_",Lit $ Name "_",ListLit Nil]) (List Nil)
testExp44 = toList [textExp42,textExp43,testExp41]

testExp45 = Def "zip" (toList [ ConsLit (Lit $ Name "x") (Lit $ Name "xs"), ConsLit (Lit $ Name "y") (Lit $ Name "ys")])
  (App (PrefixOp Colon) (toList [NTuple (toList [aname "x",aname "y"]), App (aname "zip") (toList [aname "xs",aname "ys"])]))
testExp46 = Def "zip" (toList [ListLit Nil,Lit $ Name "_"]) (List Nil)
testExp47 = Def "zip" (toList [Lit $ Name "_",ListLit Nil]) (List Nil)

testExp55 = Def "zip2" (toList [ ConsLit (Lit $ Name "x") (Lit $ Name "xs"), ConsLit (Lit $ Name "y") (Lit $ Name "ys")])
  (App (PrefixOp Colon) (toList [NTuple (toList [aname "x",aname "y"]), App (aname "zip") (toList [aname "xs",aname "ys"])]))
testExp56 = Def "zip2" (toList [ListLit Nil,Lit $ Name "_"]) (List Nil)
testExp57 = Def "zip2" (toList [Lit $ Name "_",ListLit Nil]) (List Nil)
testExp60 = Def "f" Nil (aname "zip")
