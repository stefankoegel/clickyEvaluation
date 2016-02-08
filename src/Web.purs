module Web
  ( exprToJQuery
  , getPath
  , idExpr
  , txToABC
  , prettyPrintTypeError
  ) where

import Prelude (class Monad, Unit, return, flip, bind, (<<<), (<$>), (++), (&&), (>), (>>=), void, ($), unit, show, id, (-),(+),map,(==), class Show, div ,mod)
import Data.Foldable (all,foldr)
import Data.Traversable (for)
import Data.List (List(Nil, Cons), singleton, fromList, toList, length, (..), zipWithA,concat,zip, (!!))
import Data.String (joinWith, toCharArray)
import Data.Foreign (unsafeFromForeign, Foreign(), isUndefined)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..),fst,snd)
import Data.Map (Map(..), insert, lookup, empty)
import Data.List.WordsLines (fromCharList)

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import Control.Monad.State
import DOM (DOM)


import AST (Atom(..), Binding(..), Expr(..), Op(), pPrintOp,Output(..),Type(..), TVar (..),IndexTree(..),IBinding(..),TypeTree(..),TypeBinding(..),AD(..))
import Evaluator (Path(..))
import TypeChecker (prettyPrintType,extractType,mapM,TypeError(..))
import JSHelpers

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) (Maybe Path)
getPath j = do
  fpath <- J.getProp pathPropName j
  if isUndefined fpath
    then return Nothing
    else return $ Just $ unsafeFromForeign fpath

exprToJQuery:: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery output = go (output.expr)
  where
    go (Atom (Name _)) = exprToJQuery' output
    go (Atom _) = topLevel
    go (Binary _ _ _) = topLevel
    go (PrefixOp _) = topLevel
    go _ = exprToJQuery' output

    topLevel = do
      jtypExp <- makeDiv "" (singleton "top typExpContainer")
      jExpand <- buildExpandDiv (extractType output.typ)
      J.append jExpand jtypExp
      jExpr <- exprToJQuery' output
      J.addClass "expr" jExpr
      J.append jExpr jtypExp
      return jtypExp

-- TODO rename to fit new Type
exprToJQuery' :: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery' output = go id output
  where
  go :: (Path -> Path) -> Output -> Eff (dom :: DOM | eff) J.JQuery
  go p o = J.setProp pathPropName (p End) =<< case o of
    {expr:(Atom a), typ:(TAtom t), idTree:(IAtom i)} -> atom a t i
    {expr:(Binary op e1 e2), typ:(TBinary opt tt1 tt2 t), idTree:(IBinary opi i1 i2 i)} -> do
      j1 <- go (p <<< Fst) {expr:e1, typ:tt1, idTree:i1}
      j2 <- go (p <<< Snd) {expr:e2, typ:tt2, idTree:i2}
      binary op opt opi t i j1 j2
    {expr:(List es), typ:(TListTree ts t), idTree:(IListTree is i)} -> case toStr es of
                  Just str  -> string str t i
                  Nothing -> do js <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t, idTree:i'}) (0 .. (length es - 1)) (zip is (zip es ts))
                                list js t i
    {expr:NTuple es, typ:TNTuple ts t,idTree: INTuple is i} -> do
      js <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t,idTree:i'}) (0 .. (length es - 1)) (zip is (zip es ts))
      tuple js t i
    {expr:SectL e op, typ:TSectL tt opt t, idTree:(ISectL i opi i')} -> do
      j <- go (p <<< Fst) {expr:e, typ:tt, idTree: i}
      jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
      section j jop t i'
    {expr:SectR op e, typ:TSectR opt tt t, idTree: (ISectR opi i i')} -> do
      jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
      j <- go (p <<< Snd) {expr:e, typ:tt, idTree: i}
      section jop j t i'
    {expr:PrefixOp op, typ:TPrefixOp t, idTree: (IPrefixOp i)} -> makeDiv ("(" ++ pPrintOp op ++ ")") (toList ["prefix", "op"]) >>= addTypetoDiv t >>= addIdtoDiv i
    {expr:IfExpr cond thenExpr elseExpr, typ:TIfExpr tt1 tt2  tt3 t,idTree:IIfExpr i1 i2 i3 i} -> do
      jc <- go (p <<< Fst) {expr:cond, typ:tt1, idTree: i1}
      jt <- go (p <<< Snd) {expr:thenExpr, typ:tt2, idTree: i2}
      je <- go (p <<< Thrd) {expr:elseExpr, typ:tt3, idTree: i3}
      ifexpr jc jt je t i
    {expr:Lambda binds body, typ:TLambda lb tt t, idTree: (ILambda bis i i')} -> do
      jBinds <- for (zip bis (zip binds lb)) binding
      jBody <- go (p <<< Fst) {expr:body, typ:tt, idTree: i}
      lambda jBinds jBody t i'
    {expr:App func args, typ:TApp tt ts t, idTree:IApp i1 is i} -> do
      jFunc <- go (p <<< Fst) {expr:func, typ:tt, idTree: i1}
      jArgs <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t, idTree: i'}) (0 .. (length args - 1)) (zip is (zip args ts))
      app jFunc jArgs t i
    {} -> makeDiv "You found a Bug" Nil



atom :: forall eff. Atom -> Type -> Int ->  Eff (dom :: DOM | eff) J.JQuery
atom (AInt n) t  i   = makeDiv (show n) (toList ["atom", "num"]) >>= addTypetoDiv t >>= addIdtoDiv i
atom (Bool true) t i = makeDiv "True"  (toList ["atom", "bool"]) >>= addTypetoDiv t >>= addIdtoDiv i
atom (Bool false) t i= makeDiv "False" (toList ["atom", "bool"]) >>= addTypetoDiv t >>= addIdtoDiv i
atom (Char c) t  i  = (makeDiv ("'" ++ c ++ "'") (toList ["atom", "char"])) >>= addTypetoDiv t >>= addIdtoDiv i
atom (Name name) t i = do
 jtypExp <- makeDiv "" (singleton "atom name typExpContainer")
 jExpand <- buildExpandDiv t
 J.append jExpand jtypExp
 jName <- makeDiv name (toList ["atom", "name", "expr"]) >>= addTypetoDiv t >>= addIdtoDiv i
 J.append jName jtypExp
 return jtypExp

binding :: forall eff. Tuple IBinding (Tuple Binding  TypeBinding) -> Eff (dom :: DOM | eff) J.JQuery
binding b = case b of
  Tuple (ILit i) (Tuple (Lit a) (TLit t))       -> atom a t i
  Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))-> do
    jCons <- makeDiv "" Nil >>= addTypetoDiv t >>= addIdtoDiv i
    makeDiv "(" (singleton "brace") >>= flip J.append jCons
    binding (Tuple i1 (Tuple b tb))            >>= flip J.append jCons
    makeDiv ":" (singleton "colon") >>= flip J.append jCons
    binding (Tuple i2 (Tuple bs tbs))           >>= flip J.append jCons
    makeDiv ")" (singleton "brace") >>= flip J.append jCons
  Tuple (IListLit is i)(Tuple (ListLit bs) (TListLit tbs t)) -> do
    jList <- makeDiv "" Nil >>= addTypetoDiv t >>= addIdtoDiv i
    makeDiv "[" (singleton "brace") >>= flip J.append jList
    let bx = zip is (zip bs tbs)
    for bx $ \b -> do
      binding b >>= flip J.append jList
      makeDiv "," (singleton "comma") >>= flip J.append jList
    makeDiv "]" (singleton "brace") >>= flip J.append jList
  Tuple (INTupleLit is i)(Tuple (NTupleLit bs) (TNTupleLit tbs t))-> do
    jTuple <- makeDiv "" Nil >>= addTypetoDiv t >>= addIdtoDiv i
    makeDiv "(" (singleton "brace") >>= flip J.append jTuple
    let b = (zip is (zip bs tbs))
    interleaveM_ (binding >=> flip J.append jTuple) (makeDiv "," (singleton "comma") >>= flip J.append jTuple) b
    makeDiv ")" (singleton "brace") >>= flip J.append jTuple
    return jTuple

lambda :: forall eff. List J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
lambda jBinds jBody t i = do
  jtypExp <- makeDiv "" (singleton "lambda typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  jLam <- makeDiv "" (singleton "lambda expr") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "(" (singleton "brace")
  J.append open jLam
  bs <- makeDiv "\\" (singleton "backslash")
  J.append bs jLam
  for jBinds (flip J.append jLam)
  arrow <- makeDiv "->" (singleton "arrow")
  J.append arrow jLam
  J.append jBody jLam
  close <- makeDiv ")" (singleton "brace")
  J.append close jLam
  J.append jLam jtypExp
  return jtypExp

binary :: forall eff. Op -> Type -> Int -> Type -> Int -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
binary op opt opi t i j1 j2 = do
  dBin <- makeDiv "" (singleton "binary") >>= addTypetoDiv t >>= addIdtoDiv i
  J.append j1 dBin
  dOp <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
  J.append dOp dBin
  J.append j2 dBin
  return dBin

section :: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
section j1 j2 t i = do
  jtypExp <- makeDiv "" (singleton "section typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  jSect <- makeDiv "" (singleton "section expr") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "(" (singleton "brace")
  J.append open jSect
  J.append j1 jSect
  J.append j2 jSect
  close <- makeDiv ")" (singleton "brace")
  J.append close jSect
  J.append jSect jtypExp
  return jtypExp

ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
ifexpr cond thenExpr elseExpr t i = do
  jtypExp <- makeDiv "" (singleton "if typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dIf <- makeDiv "" (singleton "if expr") >>= addTypetoDiv t >>= addIdtoDiv i
  makeDiv "if" (singleton "keyword") >>= flip J.append dIf
  J.append cond dIf
  makeDiv "then" (singleton "keyword") >>= flip J.append dIf
  J.append thenExpr dIf
  makeDiv "else" (singleton "keyword") >>= flip J.append dIf
  J.append elseExpr dIf
  J.append dIf jtypExp
  return jtypExp

interleaveM_ :: forall a b m. (Monad m) => (a -> m b) -> m b -> List a -> m Unit
interleaveM_ f sep = go
  where
  go Nil     = return unit
  go (Cons x Nil)    = void $ f x
  go (Cons x xs) = f x *> sep *> go xs

tuple :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
tuple js t i = do
  jtypExp <- makeDiv "" (singleton "tuple  typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dtuple <- makeDiv "" (singleton "tuple  expr") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "(" (singleton "brace")
  J.append open dtuple
  interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js
  close <- makeDiv ")" (singleton "brace")
  J.append close dtuple
  J.append dtuple jtypExp
  return jtypExp

list :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
list js t   i  = do
  jtypExp <- makeDiv "" (singleton "list typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dls <- makeDiv "" (singleton "list expr") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "[" (singleton "brace")
  J.append open dls
  interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js
  close <- makeDiv "]" (singleton "brace")
  J.append close dls
  J.append dls jtypExp
  return jtypExp

isString :: List Expr -> Boolean
isString es = length es > 0 && all isChar es
  where
  isChar (Atom (Char _)) = true
  isChar _               = false

string :: forall eff. String -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
string str t i = do
  jtypExp <- makeDiv "" (singleton "list string typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  jString <- makeDiv ("\"" ++ str ++ "\"") (toList ["list", "string", "expr"]) >>= addTypetoDiv t >>= addIdtoDiv i
  J.append jString  jtypExp

toStr :: List Expr -> Maybe String
toStr Nil = Nothing
toStr ls  = (joinWith "" <<< fromList) <$> for ls extract
  where
   extract:: Expr -> Maybe String
   extract (Atom (Char s)) = Just s
   extract _               = Nothing

app :: forall eff. J.JQuery -> List J.JQuery -> Type -> Int  -> Eff (dom :: DOM | eff) J.JQuery
app jFunc jArgs t i = do
  jtypExp <- makeDiv "" (singleton "app typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dApp <- makeDiv "" (singleton "app expr") >>= addTypetoDiv t >>= addIdtoDiv i
  J.addClass "func" jFunc
  J.addClass "funcContainer" jFunc
  innerExpr <- J.find ".expr" jFunc
  innerTyp <- J.find ".type" jFunc
  typeArr <- J.find ".type-arr" jFunc
  J.css {transform: "rotate(180deg)"} typeArr
  J.setVisible false innerTyp
  J.addClass "func" innerExpr
  J.append jFunc dApp
  for jArgs (flip J.append dApp)
  J.append dApp jtypExp
  return jtypExp

type Class = String

makeDiv :: forall eff. String -> List Class -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for classes (flip J.addClass d)
  return d

emptyJQuery:: forall eff . Eff (dom :: DOM | eff) J.JQuery
emptyJQuery = J.create ""


addTypetoDiv:: forall eff. Type -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addTypetoDiv typ d = do
  text <- J.getText d
  J.clear d
  outer <- makeDiv "" $ Cons "tooltip-outer" Nil
  inner <- makeDiv (prettyPrintType typ) $ Cons "tooltip-inner" Nil
  J.append inner outer
  J.append outer d
  J.appendText text d
  J.on "mouseenter" (\e div -> showTooltip div outer e) d


addIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addIdtoDiv id d = do
    J.setAttr "id" ("expr"++(show id)) d

addTypIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addTypIdtoDiv id d = do
    J.setAttr "id" ("typ"++(show id)) d

addResultIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addResultIdtoDiv id d = do
    J.setAttr "id" ("typ" ++ (show id) ++ "result") d


buildExpandDiv:: forall eff. Type  -> Eff (dom :: DOM | eff) J.JQuery
buildExpandDiv t  = do
  typC <- makeDiv (prettyPrintType t) $ Cons "type" Nil
  expandC <- makeDiv "" $ Cons "expand"  Nil
  jArrow <- makeDiv "▾" $ Cons "type-arr" Nil
  J.append jArrow expandC
  J.append typC expandC
  J.on "click" (\e _ -> do
      J.stopPropagation e
      J.setVisible true typC
      J.css {transform: "rotate(0deg)"} jArrow
      ) expandC
  J.on "click" (\e _ -> do
      J.stopPropagation e
      J.setVisible false typC
      J.css {transform: "rotate(180deg)"} jArrow
      ) typC
  J.on "mouseenter" (\e _ -> J.stopImmediatePropagation e) expandC -- otherwise tooltip shows
  J.on "mousemove" (\e _ -> J.stopImmediatePropagation e) expandC
  J.setAttr "title" "show Type" expandC
  J.setAttr "title" "hide Type" typC
  J.css {display: "inline-block"} typC
  return expandC

idExpr:: Expr -> IndexTree
idExpr e = fst $ runState (indexExpr e) {count:0}

indexExpr:: Expr -> State {count:: Int} IndexTree
indexExpr (Atom _) = do
                  i <- fresh
                  return $ IAtom i
indexExpr (List es) = do
                  is <- mapM indexExpr es
                  i <- fresh
                  return $ IListTree is i
indexExpr (NTuple es) = do
                  is <- mapM indexExpr es
                  i <- fresh
                  return $ INTuple is i
indexExpr (Binary _ e1 e2) = do
                  i1 <- indexExpr e1
                  i2 <- indexExpr e2
                  i <- fresh
                  i' <- fresh
                  return $ (IBinary i' i1 i2 i)
indexExpr (Unary _ e) = do
                  i <- indexExpr e
                  i' <- fresh
                  i'' <- fresh
                  return $ IUnary i'' i i'
indexExpr (SectL e _) = do
                  i <- indexExpr e
                  i' <- fresh
                  i'' <- fresh
                  return $ ISectL i i'' i'
indexExpr (SectR _ e) = do
                  i <- indexExpr e
                  i' <- fresh
                  i'' <- fresh
                  return $ ISectR i'' i i'
indexExpr (PrefixOp _) = do
                  i <- fresh
                  return $ IPrefixOp i
indexExpr (IfExpr e1 e2 e3) = do
                  i1 <- indexExpr e1
                  i2 <- indexExpr e2
                  i3 <- indexExpr e3
                  i <- fresh
                  return $ IIfExpr i1 i2 i3 i
indexExpr (LetExpr b e1 e2) = do
                  ib <- indexBinding b
                  i1 <- indexExpr e1
                  i2 <- indexExpr e2
                  i <- fresh
                  return $ ILetExpr ib i1 i2 i
indexExpr (Lambda bs e) = do
                 ibs <- mapM indexBinding bs
                 i <- indexExpr e
                 i' <- fresh
                 return $ ILambda ibs i i'
indexExpr (App e es) = do
                e1 <- indexExpr e
                is <- mapM indexExpr es
                i <- fresh
                return $ IApp e1 is i


indexBinding:: Binding -> State {count :: Int} IBinding
indexBinding (Lit _) = do
                    i <- fresh
                    return $ ILit i
indexBinding (ConsLit b1 b2 ) = do
                      i1 <- indexBinding b1
                      i2 <- indexBinding b2
                      i <- fresh
                      return $ IConsLit i1 i2 i
indexBinding (ListLit bs) = do
                        is <- mapM indexBinding bs
                        i <- fresh
                        return $ IListLit is i
indexBinding (NTupleLit bs) = do
                      is <- mapM indexBinding bs
                      i <- fresh
                      return $ INTupleLit is i

fresh ::State {count:: Int} Int
fresh = do
  {count = count} <- get
  put {count:count+1}
  return count


extractIndex:: IndexTree -> Int
extractIndex (IAtom i)  =  i
extractIndex (IListTree _ i)  =  i
extractIndex (INTuple _ i)  =  i
extractIndex (IBinary _ _ _ i)  =  i
extractIndex (IUnary _ _ i)  =  i
extractIndex (ISectL _ _ i)  =  i
extractIndex (ISectR _ _ i)  =  i
extractIndex (IPrefixOp i)  =  i
extractIndex (IIfExpr _ _ _ i)  =  i
extractIndex (ILetExpr _ _ _ i)  =  i
extractIndex (ILambda _ _ i)  =  i
extractIndex (IApp _ _ i)  =  i



txToABC:: TypeTree -> TypeTree
txToABC tt = fst $ runState (helptxToABC tt) {count : 0, env : empty}

helptxToABC:: TypeTree -> State {count:: Int, env:: Map String String} TypeTree
helptxToABC tt = go tt
  where
    go (TAtom t) = helpTypeToABC t >>= \t -> return $ TAtom t
    go (TListTree tts t) = do
      tts' <- mapM helptxToABC tts
      t' <- helpTypeToABC t
      return $ TListTree tts' t'
    go (TNTuple tts t) = do
      tts' <- mapM helptxToABC tts
      t' <- helpTypeToABC t
      return $ TNTuple tts' t'
    go (TBinary t1 tt1 tt2 t) = do
      t1' <- helpTypeToABC t1
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      t' <- helpTypeToABC t
      return $ TBinary t1' tt1' tt2' t'
    go (TUnary t1 tt t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ (TUnary t1' tt' t')
    go (TSectL tt t1 t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ TSectL tt' t1' t'
    go (TSectR t1 tt t) = do
      t1' <- helpTypeToABC t1
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ TSectR t1' tt' t'
    go (TPrefixOp t) = helpTypeToABC t >>= \t -> return $ TPrefixOp t
    go (TIfExpr tt1 tt2 tt3 t) = do
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      tt3' <- helptxToABC tt3
      t' <- helpTypeToABC t
      return $ TIfExpr tt1' tt2' tt3' t'
    go (TLetExpr tb tt1 tt2 t) = do
      tb' <- helpBindingToABC tb
      tt1' <- helptxToABC tt1
      tt2' <- helptxToABC tt2
      t' <- helpTypeToABC t
      return $ TLetExpr tb' tt1' tt2' t'
    go (TLambda tbs tt t) = do
      tbs' <- mapM helpBindingToABC tbs
      tt' <- helptxToABC tt
      t' <- helpTypeToABC t
      return $ TLambda tbs' tt' t'
    go (TApp tt tts t) = do
      tt' <- helptxToABC tt
      tts' <- mapM helptxToABC tts
      t' <- helpTypeToABC t
      return $ TApp tt' tts' t'

typeToABC:: Type -> Type
typeToABC t = fst $ runState (helpTypeToABC t) {count: 0, env: empty}


helpTypeToABC:: Type  -> State {count :: Int, env:: (Map String String)} Type
helpTypeToABC t = go t
  where
   go (TypVar (TVar var)) = do
      {env = env :: Map String String} <- get
      case lookup var env of
        Just var' -> return $ TypVar (TVar var')
        Nothing -> do
          var' <- freshLetter
          let env' = (insert var var' env)
          {count=count:: Int} <- get
          put {count:count, env:env'}
          return $ TypVar (TVar var')
   go (TypArr t1 t2) = do
        t1' <- helpTypeToABC t1
        t2' <- helpTypeToABC t2
        return $ TypArr t1' t2'
   go (AD a) = helpADTypeToABC a >>= \a -> return $ AD a
   go a = return a

helpADTypeToABC:: AD -> State {count :: Int, env:: (Map String String)} AD
helpADTypeToABC (TList t) = helpTypeToABC t >>= \t -> return $ TList t
helpADTypeToABC (TTuple ts) = mapM helpTypeToABC ts >>= \ts -> return $ TTuple ts

helpBindingToABC:: TypeBinding -> State {count :: Int, env:: (Map String String)} TypeBinding
helpBindingToABC bin = go bin
  where
    go (TLit t) = helpTypeToABC t >>= \t ->return $ TLit t
    go (TConsLit tb1 tb2 t) = do
      tb1' <- helpBindingToABC tb1
      tb2' <- helpBindingToABC tb2
      t' <- helpTypeToABC t
      return $ TConsLit tb1' tb2' t'
    go (TListLit tbs t) = do
      tbs' <- mapM helpBindingToABC tbs
      t' <- helpTypeToABC t
      return $ TListLit tbs' t'
    go (TNTupleLit tbs t) = do
      tbs' <- mapM helpBindingToABC tbs
      t' <- helpTypeToABC t
      return $ TNTupleLit tbs' t'

freshLetter:: State {count:: Int, env:: Map String String} String
freshLetter = do
    {count = count, env = env :: Map String String} <- get
    put {count:count+1, env:env}
    return $ fromCharList $ newTypVar count


letters:: List Char
letters = (toList $ toCharArray "abcdefghijklmnopqrstuvwxyz")

letters1:: List Char
letters1 = (toList $ toCharArray " abcdefghijklmnopqrstuvwxyz")

newTypVar:: Int -> List Char
newTypVar i = case (letters !! i) of
  Just c ->  Cons c Nil
  Nothing -> let i1 = (i `div` 26) in let i2 = (i `mod` 26) in (newTypVar1 i1) ++ (newTypVar i2)

-- workaround
-- if i  subtract one from i => stack overflow at ~50
newTypVar1:: Int -> List Char
newTypVar1 i = case (letters1 !! (i)) of
  Just c ->  Cons c Nil
  Nothing -> let i1 = (i `div` 26) in let i2 = (i `mod` 26) in (newTypVar1 i1) ++ (newTypVar i2)



prettyPrintTypeError:: TypeError -> String
prettyPrintTypeError (UnificationFail t1 t2) = let t1t2 = twoTypesToABC t1 t2  in
                                                "UnificationFail: Can't unify "
                                                ++ prettyPrintType (fst t1t2) ++ " with "
                                                ++ prettyPrintType (snd t1t2)
prettyPrintTypeError (InfiniteType a b) = let ab = twoTypesToABC (TypVar a) b in
                                              "InfiniteType: cannot construct the infinite type: "
                                              ++ prettyPrintType (fst ab)++ " ~ "
                                              ++ prettyPrintType (snd ab)
prettyPrintTypeError (UnboundVariable var) = "UnboundVariable: Not in scope "
                                              ++ var
prettyPrintTypeError (UnificationMismatch ts1 ts2) = let ts1ts2 = twoTypeListsToABC ts1 ts2 in
    "UnificationMismatch: " ++ toStr (fst ts1ts2) ++ " " ++ toStr (snd ts1ts2)
  where
    toStr ts = "[" ++ (foldr (\t s -> t ++ "," ++ s) "]" (map (\a -> prettyPrintType (typeToABC a)) ts))
prettyPrintTypeError (UnknownError str) = "UnknownError: " ++ str


twoTypesToABC t1 t2 = (\(TypArr t1' t2') -> Tuple t1' t2') (typeToABC (TypArr t1 t2))
twoTypeListsToABC t1 t2 = (\(TypArr (AD (TTuple t1')) (AD (TTuple t2'))) -> Tuple t1' t2') (typeToABC (TypArr (AD (TTuple t1)) (AD (TTuple t2)) ))
