module Web
  ( exprToJQuery
  , getPath
  , topLevelTypetoJQuery
  , idExpr
  , drawLines
  , findConnections
  ) where

import Control.Monad.Eff
import Control.Monad.Eff.JQuery as J
import DOM
import Prelude

import Data.Foldable (all,foldr)
import Data.Traversable (for)
import Data.List
import Data.Tuple
import Data.String (joinWith)
import Data.Foreign (unsafeFromForeign, Foreign())
import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.State
import Control.Monad.Eff.Class

import AST
import Evaluator (Path(..))
import TypeChecker (prettyPrintType,extractType,mapM)
import JSHelpers

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) Path
getPath j = unsafeFromForeign <$> J.getProp pathPropName j

-- TODO rename to fit new Type
exprToJQuery :: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery output = go id output
  where
  go :: (Path -> Path) -> Output -> Eff (dom :: DOM | eff) J.JQuery
  go p o = J.setProp pathPropName (p End) =<< case o of
    {expr:(Atom a), typ:(TAtom t), idTree:(IAtom i)} -> atom a t i
    {expr:(Binary op e1 e2), typ:(TBinary opt tt1 tt2 t), idTree:(IBinary opi i1 i2 i)} -> do
      j1 <- go (p <<< Fst) {expr:e1, typ:tt1, idTree:i1}
      j2 <- go (p <<< Snd) {expr:e2, typ:tt2, idTree:i2}
      binary op opt opi t i j1 j2

    {expr:(List es), typ:(TListTree ts t), idTree:(IListTree is i)} -> case isString es of
                  true  -> string es t i
                  false -> do js <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t, idTree:i'}) (0 .. (length es - 1)) (zip is (zip es ts))
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
    {expr:PrefixOp op, typ:TPrefixOp t, idTree: (IPrefixOp i)} -> makeDiv ("(" ++ pPrintOp op ++ ")") (toList ["prefix", "op"]) >>= addTypetoDiv t
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
atom (Name name) t i = makeDiv name (toList ["atom", "name"]) >>= addTypetoDiv t >>= addIdtoDiv i

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
  jLam <- makeDiv "" (singleton "lambda") >>= addTypetoDiv t >>= addIdtoDiv i
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
  return jLam

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
  jSect <- makeDiv "" (singleton "section") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "(" (singleton "brace")
  J.append open jSect
  J.append j1 jSect
  J.append j2 jSect
  close <- makeDiv ")" (singleton "brace")
  J.append close jSect
  return jSect

ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
ifexpr cond thenExpr elseExpr t i = do
  dIf <- makeDiv "" (singleton "if") >>= addTypetoDiv t >>= addIdtoDiv i
  makeDiv "if" (singleton "keyword") >>= flip J.append dIf
  J.append cond dIf
  makeDiv "then" (singleton "keyword") >>= flip J.append dIf
  J.append thenExpr dIf
  makeDiv "else" (singleton "keyword") >>= flip J.append dIf
  J.append elseExpr dIf
  return dIf

interleaveM_ :: forall a b m. (Monad m) => (a -> m b) -> m b -> List a -> m Unit
interleaveM_ f sep = go
  where
  go Nil     = return unit
  go (Cons x Nil)    = void $ f x
  go (Cons x xs) = f x *> sep *> go xs

tuple :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
tuple js t i = do
  dtuple <- makeDiv "" (singleton "tuple") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "(" (singleton "brace")
  J.append open dtuple
  interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js
  close <- makeDiv ")" (singleton "brace")
  J.append close dtuple
  return dtuple

list :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
list js t   i  = do
  dls <- makeDiv "" (singleton "list") >>= addTypetoDiv t >>= addIdtoDiv i
  open <- makeDiv "[" (singleton "brace")
  J.append open dls
  interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js
  close <- makeDiv "]" (singleton "brace")
  J.append close dls
  return dls

isString :: List Expr -> Boolean
isString es = length es > 0 && all isChar es
  where
  isChar (Atom (Char _)) = true
  isChar _               = false

string :: forall eff. List Expr -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
string es t i = do
  let str = "\"" ++ joinWith "" (fromList ((\(Atom (Char s)) -> s) <$> es)) ++ "\""
  dstring <- makeDiv str (toList ["list", "string"]) >>= addTypetoDiv t >>= addIdtoDiv i
  return dstring

app :: forall eff. J.JQuery -> List J.JQuery -> Type -> Int  -> Eff (dom :: DOM | eff) J.JQuery
app jFunc jArgs t i = do
  dApp <- makeDiv "" (singleton "app") >>= addTypetoDiv t >>= addIdtoDiv i
  J.addClass "func" jFunc
  J.append jFunc dApp
  for jArgs (flip J.append dApp)
  return dApp

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
  J.setAttr "title" (prettyPrintType typ) d


addIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addIdtoDiv id d = do
    J.setAttr "id" ("expr"++(show id)) d

addTypIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addTypIdtoDiv id d = do
    J.setAttr "id" ("typ"++(show id)) d

addResultIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addResultIdtoDiv id d = do
    J.setAttr "id" ("typ" ++ (show id) ++ "result") d

dummyExpr:: Expr
dummyExpr =  Atom $ AInt 0

typetoJQuery:: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
typetoJQuery {typ:TListTree ls t, idTree: IListTree is i} = do
    container <- makeDiv "" $ Cons "output" Nil
    list <- mapM (\(Tuple t i) -> typetoJQuery {typ:t , idTree:i ,expr:dummyExpr}) (zip ls is)
    for list $ (\l -> J.append l container)
    containerContent <- J.getText container
    if Data.String.length containerContent == 0 then J.setAttr "class" "" container else emptyJQuery
    return $ container
typetoJQuery {typ:TNTuple ls t, idTree: INTuple is i} = do
    container <- makeDiv "" $ Cons "output" Nil
    list <- mapM (\(Tuple t i) -> typetoJQuery {typ:t , idTree:i ,expr:dummyExpr}) (zip ls is)
    for list $ (\l -> J.append l container)
    containerContent <- J.getText container
    if Data.String.length containerContent == 0 then J.setAttr "class" "" container else emptyJQuery
    return $ container
typetoJQuery {typ:TBinary t1 tt1 tt2 t, idTree:IBinary i1 it1 it2 i} = do
    container <- makeDiv "" Nil
    subContainer <- makeDiv "" $ Cons "subtypes output" Nil
    jExp1 <- typetoJQuery {typ:tt1 ,idTree:it1, expr:dummyExpr}
    jExp2 <- typetoJQuery {typ:tt2 ,idTree:it2, expr:dummyExpr}
    J.append jExp1 subContainer
    J.append jExp2 subContainer
    contentSub <- J.getText subContainer
    if Data.String.length contentSub == 0 then J.setAttr "class" "" subContainer else emptyJQuery
    J.append subContainer container
typetoJQuery {typ: TUnary t1 tt t, idTree: IUnary i1 it i} = emptyJQuery --TODO

typetoJQuery {typ: TSectL tt _ _, idTree: ISectL it _ _} = typetoJQuery {typ:tt, idTree:it, expr:dummyExpr}
typetoJQuery {typ: TSectR _ tt _, idTree: ISectR _ it _} = typetoJQuery {typ:tt, idTree:it, expr:dummyExpr}

typetoJQuery {typ: TIfExpr t1 t2 t3 t, idTree: IIfExpr i1 i2 i3 i} = do
    container <- makeDiv "" $ Cons "output" Nil
    div1 <- typetoJQuery {typ:t1,idTree:i1,expr:dummyExpr}
    div2 <- typetoJQuery {typ:t2,idTree:i2,expr:dummyExpr}
    div3 <- typetoJQuery {typ:t3,idTree:i3,expr:dummyExpr}
    J.append div1 container
    J.append div2 container
    J.append div3 container
    containerContent <- J.getText container
    if Data.String.length containerContent == 0 then J.setAttr "class" "" container else emptyJQuery
    return container

typetoJQuery {typ: TLetExpr _ tt1 tt2 t,idTree: ILetExpr _ it1 it2 i} = emptyJQuery --TODO

typetoJQuery {typ: TLambda _ tt t, idTree: ILambda _ it i} = typetoJQuery {typ:tt,idTree:it,expr:dummyExpr}

typetoJQuery {typ:TApp t1 tl t, idTree:IApp i1 is i} = do
    container <- makeDiv "" Nil
    typContainer <- (makeDiv "" $ Cons "output" Nil) >>= addTypIdtoDiv (extractIndex i1)
    list <- mapM (\(Tuple t i) -> (makeDiv (prettyPrintType (extractType t)) $ Cons "output" Nil) >>= (addTypIdtoDiv (extractIndex i))) (zip tl is)
    for list $ (\l -> do
                  J.append l typContainer
                  arr <- makeDiv " -> " Nil
                  J.append arr typContainer)
    exprType <- (makeDiv (prettyPrintType t) $ Cons "output" Nil) >>= addResultIdtoDiv i
    J.append exprType typContainer
    J.append typContainer container
    br <- J.create "<br>"
    J.append br container
    subContainer <- makeDiv "" $ Cons "subtypes output" Nil
    divExpr <- typetoJQuery {typ: t1,idTree:i1,expr:dummyExpr}
    J.append divExpr subContainer
    list <- mapM (\(Tuple t i) -> typetoJQuery {typ:t,idTree:i, expr:dummyExpr}) (zip tl is)
    for list $ (\l -> J.append l subContainer)
    contentSub <- J.getText subContainer
    if Data.String.length contentSub == 0 then J.setAttr "class" "" subContainer else emptyJQuery
    J.append subContainer container


typetoJQuery {typ:typ} = emptyJQuery

-- to show type even is no application
topLevelTypetoJQuery :: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
topLevelTypetoJQuery {typ:TBinary t1 tt1 tt2 t, idTree:IBinary i1 it1 it2 i} = do
        container <- makeDiv "" Nil
        typContainer <- (makeDiv "" $ Cons "output" Nil) >>= addTypIdtoDiv i1
        div1 <- (makeDiv (prettyPrintType (extractType tt1)) $ Cons "output" Nil) >>= (addTypIdtoDiv (extractIndex it1))
        div2 <- (makeDiv (prettyPrintType (extractType tt2)) $ Cons "output" Nil) >>= (addTypIdtoDiv (extractIndex it2))
        div3 <- (makeDiv (prettyPrintType t) $ Cons "output" Nil) >>= (addResultIdtoDiv i)
        arr <- makeDiv " -> " Nil
        arr2 <- makeDiv " -> " Nil
        J.append div1 typContainer
        J.append arr typContainer
        J.append div2 typContainer
        J.append arr2 typContainer
        J.append div3 typContainer
        J.append typContainer container
        br <- J.create "<br>"
        J.append br container
        subContainer <- makeDiv "" $ Cons "subtypes output" Nil
        jExp1 <- typetoJQuery {typ:tt1 ,idTree:it1, expr:dummyExpr}
        jExp2 <- typetoJQuery {typ:tt2 ,idTree:it2, expr:dummyExpr}
        J.append jExp1 subContainer
        J.append jExp2 subContainer
        contentSub <- J.getText subContainer
        if Data.String.length contentSub == 0 then J.setAttr "class" "" subContainer else emptyJQuery
        J.append subContainer container

topLevelTypetoJQuery t@{typ:tt, idTree: it} = do
        container <- makeDiv "" Nil
        typContainer <- makeDiv (prettyPrintType (extractType tt)) $ Cons "output" Nil
        addTypIdtoDiv (extractIndex it) typContainer
        J.append typContainer container
        br <- J.create "<br>"
        J.append br container
        types <- typetoJQuery t
        J.append types container





findConnections:: IndexTree -> List (Tuple String String)
findConnections (IBinary i1 it1 it2 i) = Cons (buildPairResult i) $  Cons (buildPair i1) $ Cons (buildPair (extractIndex it1)) $ Cons (buildPair (extractIndex it2)) $ findOtherConnections it1 ++ findOtherConnections it2
findConnections id = Cons (buildPair (extractIndex id)) $ findOtherConnections id

findOtherConnections:: IndexTree -> List (Tuple String String)
findOtherConnections (IListTree ls _) = concat $ map findOtherConnections ls
findOtherConnections (INTuple ls _) = concat $ map findOtherConnections ls
findOtherConnections (IBinary _ it1 it2 _) = findOtherConnections it1 ++ findOtherConnections it2
findOtherConnections (IUnary _ it _) = findOtherConnections it
findOtherConnections (ISectL it _ _ ) = findOtherConnections it
findOtherConnections (ISectR _ it _ ) = findOtherConnections it
findOtherConnections (IIfExpr it1 it2 it3 _ ) = findOtherConnections it1 ++ findOtherConnections it2 ++ findOtherConnections it3
findOtherConnections (ILetExpr _ it1 it2 _ ) = findOtherConnections it1 ++ findOtherConnections it2
findOtherConnections (ILambda _ it _) = findOtherConnections it
findOtherConnections (IApp it its i) =  Cons (buildPair (extractIndex it))  $  Cons (buildPairResult i) $ (map (\i -> buildPair $ extractIndex i) its) ++ (concat (map findOtherConnections its)) -- Cons buildPair i
findOtherConnections _ = Nil -- atom prefixOP

buildPair:: Int -> (Tuple String String)
buildPair i = Tuple ("typ" ++ show i) ("expr" ++ show i)

buildPairResult:: Int -> (Tuple String String)
buildPairResult i = Tuple ("expr" ++ show i) ("typ"++ (show i) ++ "result")

-- draws a line between two divs
-- canvas obj1 obj2 svgContainer
-- Foreign JQuery JQuery JQuery
drawLines::forall eff. Foreign -> J.JQuery -> List (Tuple String String) -> Eff (dom :: DOM | eff) Unit
drawLines canvas svgContainer lines' = do
      lines <- mapM toJQueryPair lines'
      for lines $ (\(Tuple l1 l2) -> do
              y1 <- yOffset l1
              x1 <- xOffset l1
              y2 <- yOffset l2
              x2 <- xOffset l2
              path canvas $ "M" ++ (show x1) ++ " " ++ (show y1) ++ "L" ++ (show x2) ++ " " ++ (show y2)
          )
      return unit
    where
    -- calculates x and y offset to svgContainer
    yOffset jObj = offsetTop jObj >>= (\y -> offsetTop svgContainer >>= (\x -> return (y - x)))
    xOffset jObj = offsetLeft jObj >>= (\y -> offsetLeft svgContainer >>= (\x -> return (y - x)))


-- fings matching typ expr pair
toJQueryPair::forall eff. Tuple String String -> Eff (dom :: DOM | eff) (Tuple J.JQuery J.JQuery)
toJQueryPair (Tuple id1 id2) = do
  typ <- J.select ("#" ++ id1)
  expr <- J.select ("#" ++ id2)
  return $ Tuple typ expr

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
