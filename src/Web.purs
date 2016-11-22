module Web
  ( exprToJQuery
  , getPath
  , idExpr
  , makeDiv
  ) where

import Prelude (class Show, class Monad, Unit, (+), bind, ($), (==), (/=), show, (<>), (>>=), flip, pure, (<<<), (<$>), (&&), (>), void, unit, id, (-))
import Data.Foldable (all)
import Data.String (joinWith)
import Data.List (List(Nil, Cons), singleton, fromFoldable, toUnfoldable, length, zip, (..), zipWithA)
import Data.Foreign (unsafeFromForeign, isUndefined)
import Data.Maybe (Maybe(..), isJust, fromJust)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Traversable (for, for_, traverse)
import Data.Array as Array

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
--import Control.Monad (when)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import Control.Monad.State (State, put, get, runState)
import DOM (DOM)


import AST (Atom(..), Binding(..), Expr(..), Qual(..), ExprQual, TypeQual, IndexQual, QualTree(..), Op(), pPrintOp, Output(),Type(..), IndexTree(..),IBinding(..),TypeTree(..),TypeBinding(..), Path(..), extractType, prettyPrintType)
import JSHelpers (showTooltip, children)

data Triple a b c = Triple a b c

pathPropName :: String
pathPropName = "clickyEvaluation_path"

getPath :: forall eff. J.JQuery -> Eff (dom :: DOM | eff) (Maybe Path)
getPath j = do
  fpath <- J.getProp pathPropName j
  if isUndefined fpath
    then pure Nothing
    else pure $ Just $ unsafeFromForeign fpath

exprToJQuery:: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery output = go (output.expr)
  where
    go (Atom (Name _)) = exprToJQuery' output
    go (Atom _) = topLevel
    go (Binary _ _ _) = exprToJQuery' output
    go (PrefixOp _) = topLevel
    go _ = exprToJQuery' output

    topLevel = case extractType output.typ of
        TypeError _ -> exprToJQuery' output
        _ -> do
          jtypExp <- makeDiv "" (singleton "top typExpContainer")
          jExpand <- buildExpandDiv (extractType output.typ)
          J.append jExpand jtypExp
          jExpr <- exprToJQuery' output
          J.addClass "expr" jExpr
          J.append jExpr jtypExp
          pure jtypExp

-- TODO rename to fit new Type
-- TODO: Needs refactoring.
exprToJQuery' :: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
exprToJQuery' output = go id output
  where
  go :: (Path -> Path) -> Output -> Eff (dom :: DOM | eff) J.JQuery
  go p o =
    (\jObj -> do
          let f = J.setProp pathPropName (p End)
          jExpr <- children ".expr" jObj
          isNotEmpty <- J.hasClass "expr" jExpr
          if isNotEmpty then f jExpr else f jObj
          pure jObj
          )
    =<<
    case o of
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
    {expr:PrefixOp op, typ:TPrefixOp t, idTree: (IPrefixOp i)} -> makeDiv ("(" <> pPrintOp op <> ")") (Array.toUnfoldable ["prefix", "op"]) >>= addTypetoDiv t >>= addIdtoDiv i
    {expr:IfExpr cond thenExpr elseExpr, typ:TIfExpr tt1 tt2  tt3 t,idTree:IIfExpr i1 i2 i3 i} -> do
      jc <- go (p <<< Fst) {expr:cond, typ:tt1, idTree: i1}
      jt <- go (p <<< Snd) {expr:thenExpr, typ:tt2, idTree: i2}
      je <- go (p <<< Thrd) {expr:elseExpr, typ:tt3, idTree: i3}
      ifexpr jc jt je t i

    -- TODO: Remove nested case expressions.
    {expr:(ArithmSeq start step end), typ:(TArithmSeq tstart tstep tend t), idTree:(IArithmSeq istart istep iend i)} -> do
      jStart <- go (p <<< Fst)  {expr:start, typ:tstart, idTree:istart}
      case Triple step tstep istep of
        Triple (Just jstep) (Just jtstep) (Just jistep) ->
          case Triple end tend iend of
            Triple (Just jend) (Just jtend) (Just jiend) -> do
              jStep <- go (p <<< Snd) {expr: jstep, typ: jtstep, idTree: jistep}
              jEnd  <- go (p <<< Thrd) {expr: jend, typ: jtend, idTree: jiend}
              arithmeticSequence jStart (Just jStep) (Just jEnd) t i
            _ -> do
              jStep <- go (p <<< Snd) {expr: jstep, typ: jtstep, idTree: jistep}
              arithmeticSequence jStart (Just jStep) Nothing t i
        _ ->
          case Triple end tend iend of
            Triple (Just jend) (Just jtend) (Just jiend) -> do
              jEnd  <- go (p <<< Thrd) {expr: jend, typ: jtend, idTree: jiend}
              arithmeticSequence jStart Nothing (Just jEnd) t i
            _ -> arithmeticSequence jStart Nothing Nothing t i

    {expr:(ListComp expr quals), typ:(TListComp texpr tquals t), idTree:(IListComp iexpr iquals i)} -> do
      jExpr  <- go (p <<< Fst) {expr:expr, typ:texpr, idTree:iexpr}
      jQuals <- zipWithA (\i (Tuple i' (Tuple e t)) -> qualifier (p <<< Nth i) e t i')
        (0 .. (length quals - 1)) (zip iquals (zip quals tquals))
      listComp jExpr jQuals t i

    {expr:Lambda binds body, typ:TLambda lb tt t, idTree: (ILambda bis i i')} -> do
      jBinds <- for (zip bis (zip binds lb)) binding
      jBody <- go (p <<< Fst) {expr:body, typ:tt, idTree: i}
      lambda jBinds jBody t i'
    {expr:App func args, typ:TApp tt ts t, idTree:IApp i1 is i} -> do
      jFunc <- go (p <<< Fst) {expr:func, typ:tt, idTree: i1}
      jArgs <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t, idTree: i'}) (0 .. (length args - 1)) (zip is (zip args ts))
      app jFunc jArgs (extractType tt) t i
    {expr: Unary op exp, typ: TUnary opt tt t, idTree:IUnary opi is i} -> do
      jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
      jexpr <- go (p <<< Fst) {expr: exp, typ: tt, idTree: is}
      unary jop jexpr t i

    {expr: LetExpr binds exp, typ: TLetExpr tbinds texp t, idTree: ILetExpr ibinds iexp i} -> case checkLength binds tbinds ibinds of
      false -> makeDiv "oops! LetExpr bindings length error!" Nil
      true  -> do
        let fstBoundle = zip (fst <$> ibinds) (zip (fst <$> binds) (fst <$> tbinds))
            sndBoundle = zip (snd <$> ibinds) (zip (snd <$> binds) (snd <$> tbinds))

        jbinds <- traverse binding fstBoundle
        jexprs <- zipWithA (\x (Tuple i (Tuple b t)) -> go (p <<< Nth x) {expr: b, typ: t, idTree: i}) (1 .. (length sndBoundle)) sndBoundle
        jletBinds <- zipWithA letBinding jbinds jexprs

        jexpr <- go (p <<< Fst) {expr: exp, typ: texp, idTree: iexp}
        letExpr jletBinds jexpr t i

    {} -> makeDiv "You found a Bug" Nil

  qualifier :: (Path -> Path) -> ExprQual -> TypeQual -> IndexQual -> Eff (dom :: DOM | eff) J.JQuery
  qualifier p (Gen b e) (TGen tb te t) (TGen ib ie i) = do
      result <- makeDiv "" Nil
      addTypetoDiv t result
      addIdtoDiv i result
      binding (Tuple ib (Tuple b tb)) >>= flip J.append result
      makeDiv "<-" Nil >>= flip J.append result
      go p {expr:e, typ:te, idTree:ie} >>= flip J.append result
      pure result
  qualifier p (Let b e) (TLet tb te t) (TLet ib ie i) = do
      result <- makeDiv "let" Nil >>= addTypetoDiv t >>= addIdtoDiv i
      binding (Tuple ib (Tuple b tb)) >>= flip J.append result
      makeDiv "=" Nil >>= flip J.append result
      go p {expr:e, typ:te, idTree:ie} >>= flip J.append result
      pure result
  qualifier p (Guard e) (TGuard te t) (TGuard ie i) = go p {expr:e, typ:te, idTree:ie}
  qualifier _ _ _ _ = makeDiv "You found a Bug in Web.exprToJquery'.qualifier" Nil

checkLength :: forall a b c. List a -> List b -> List c -> Boolean
checkLength a b c = length a /= 0 && length a == length b && length a == length c && length b == length c

atom :: forall eff. Atom -> Type -> Int ->  Eff (dom :: DOM | eff) J.JQuery
atom (AInt n) t  i   = do
  div <- makeDiv (show n) (Array.toUnfoldable ["atom", "num"])
  addTypetoDiv t div
  addIdtoDiv i div
  pure div
atom (Bool true) t i = do
  div <- makeDiv "True"  (Array.toUnfoldable ["atom", "bool"])
  addTypetoDiv t div
  addIdtoDiv i div
  pure div
atom (Bool false) t i = do
  div <- makeDiv "False" (Array.toUnfoldable ["atom", "bool"])
  addTypetoDiv t div
  addIdtoDiv i div
  pure div
atom (Char c) t  i  = do
  div <- makeDiv ("'" <> c <> "'") (Array.toUnfoldable ["atom", "char"])
  addTypetoDiv t div
  addIdtoDiv i div
  pure div
atom (Name name) t i = do
 jtypExp <- makeDiv "" (singleton "atom name typExpContainer")
 jExpand <- buildExpandDiv t
 J.append jExpand jtypExp
 jName <- makeDiv name (Array.toUnfoldable ["atom", "name", "expr"])
 addTypetoDiv t jName
 addIdtoDiv i jName
 J.append jName jtypExp
 pure jtypExp

binding :: forall eff. Tuple IBinding (Tuple Binding TypeBinding) -> Eff (dom :: DOM | eff) J.JQuery
binding b = case b of
  Tuple (ILit i) (Tuple (Lit a) (TLit t))       -> atom a t i
  cl@(Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))) -> do
    jCons <- makeDiv "" Nil
    addTypetoDiv t jCons
    addIdtoDiv i jCons
    makeDiv "(" (singleton "brace") >>= flip J.append jCons
    consBinding cl jCons
    div <- makeDiv ")" (singleton "brace")
    J.append div jCons
    pure div
  Tuple (IListLit is i)(Tuple (ListLit bs) (TListLit tbs t)) -> do
    jList <- makeDiv "" Nil
    addTypetoDiv t jList
    addIdtoDiv i jList
    makeDiv "[" (singleton "brace") >>= flip J.append jList
    interleaveM_
      (\b -> binding b >>= flip J.append jList)
      (makeDiv "," (singleton "comma") >>= flip J.append jList)
      (zip is (zip bs tbs))
    div <- makeDiv "]" (singleton "brace")
    J.append div jList
    pure div
  Tuple (INTupleLit is i)(Tuple (NTupleLit bs) (TNTupleLit tbs t))-> do
    jTuple <- makeDiv "" Nil
    addTypetoDiv t jTuple
    addIdtoDiv i jTuple
    makeDiv "(" (singleton "brace") >>= flip J.append jTuple
    let b = (zip is (zip bs tbs))
    interleaveM_ (binding >=> flip J.append jTuple) (makeDiv "," (singleton "comma") >>= flip J.append jTuple) b
    makeDiv ")" (singleton "brace") >>= flip J.append jTuple
    pure jTuple

  _ -> makeDiv ("congrats you found a bug in Web.binding") Nil
  where
    consBinding :: Tuple IBinding (Tuple Binding  TypeBinding) -> J.JQuery-> Eff (dom :: DOM | eff) Unit
    consBinding (Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))) jCons = do
      binding (Tuple i1 (Tuple b tb)) >>= flip J.append jCons
      makeDiv ":" (singleton "colon") >>= flip J.append jCons
      consBinding (Tuple i2 (Tuple bs tbs)) jCons
    consBinding b jCons = void $ binding b >>= flip J.append jCons

lambda :: forall eff. List J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
lambda jBinds jBody t i = do
  jtypExp <- makeDiv "" (singleton "lambda typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  jLam <- makeDiv "" (singleton "lambda expr")
  addTypetoDiv t jLam
  addIdtoDiv i jLam
  open <- makeDiv "(\\" (Cons "brace" (Cons "backslash" Nil))
  J.append open jLam
  for jBinds (flip J.append jLam)
  arrow <- makeDiv "->" (singleton "arrow")
  J.append arrow jLam
  J.append jBody jLam
  close <- makeDiv ")" (singleton "brace")
  J.append close jLam
  J.append jLam jtypExp
  pure jtypExp

binary :: forall eff. Op -> Type -> Int -> Type -> Int -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
binary op opt opi t i j1 j2 = do
  dBin <- makeDiv "" (singleton "binary")
  addTypetoDiv t dBin
  addIdtoDiv i dBin
  J.append j1 dBin
  dOp <- makeDiv (pPrintOp op) (singleton "op")
  addTypetoDiv opt dOp
  addIdtoDiv opi dOp
  J.append dOp dBin
  J.append j2 dBin
  jtypExp <- makeDiv "" (singleton "binary typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  J.addClass "expr" dBin
  J.append dBin jtypExp
  pure jtypExp

unary:: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
unary jop jexpr t i = do
  jtypExp <- makeDiv "" (singleton "unary typExpContainer")
  jExpand <-  buildExpandDiv t
  J.append jExpand jtypExp
  jUnary <- makeDiv "" (singleton "unary expr")
  addTypetoDiv t jUnary
  addIdtoDiv i jUnary
  J.append jop jUnary
  J.append jexpr jUnary
  J.append jUnary jtypExp
  pure jtypExp

section :: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
section j1 j2 t i = do
  jtypExp <- makeDiv "" (singleton "section typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  jSect <- makeDiv "" (singleton "section expr")
  addTypetoDiv t jSect
  addIdtoDiv i jSect
  open <- makeDiv "(" (singleton "brace")
  J.append open jSect
  J.append j1 jSect
  J.append j2 jSect
  close <- makeDiv ")" (singleton "brace")
  J.append close jSect
  J.append jSect jtypExp
  pure jtypExp

ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
ifexpr cond thenExpr elseExpr t i = do
  jtypExp <- makeDiv "" (singleton "if typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dIf <- makeDiv "" (singleton "if expr")
  addTypetoDiv t dIf
  addIdtoDiv i dIf
  makeDiv "if" (singleton "keyword") >>= flip J.append dIf
  J.append cond dIf
  makeDiv "then" (singleton "keyword") >>= flip J.append dIf
  J.append thenExpr dIf
  makeDiv "else" (singleton "keyword") >>= flip J.append dIf
  J.append elseExpr dIf
  J.append dIf jtypExp
  pure jtypExp

arithmeticSequence :: forall eff. J.JQuery -> Maybe J.JQuery -> Maybe J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
arithmeticSequence start mstep mend t i = do
  jtypExp <- makeDiv "" (singleton "list typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  das <- makeDiv "" (singleton "list expr")
  addTypetoDiv t das
  addIdtoDiv i das
  makeDiv "[" (singleton "brace") >>= flip J.append das
  J.append start das
  maybeStep das mstep
  makeDiv ".." (singleton "dot") >>= flip J.append das
  maybeEnd das mend
  makeDiv "]" (singleton "brace") >>= flip J.append das
  J.append das jtypExp
  pure jtypExp
  where
    maybeStep :: J.JQuery -> Maybe J.JQuery -> Eff (dom :: DOM | eff) Unit
    maybeStep jquery Nothing = pure unit
    maybeStep jquery (Just step) = do
      makeDiv "," (singleton "comma") >>= flip J.append jquery
      J.append step jquery

    maybeEnd :: J.JQuery -> Maybe J.JQuery -> Eff (dom :: DOM | eff) Unit
    maybeEnd jquery Nothing = pure unit
    maybeEnd jquery (Just end) = J.append end jquery

listComp :: forall eff. J.JQuery -> List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
listComp jExpr jQuals t i = do
  jtypExp <- makeDiv "" (singleton "list typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  das <- makeDiv "" (singleton "list expr")
  addTypetoDiv t das
  addIdtoDiv i das
  makeDiv "[" (singleton "brace") >>= flip J.append das
  J.append jExpr das
  makeDiv "|" (singleton "comma") >>= flip J.append das
  interleaveM_ (flip J.append das) (makeDiv "," (singleton "comma") >>= flip J.append das) jQuals
  makeDiv "]" (singleton "brace") >>= flip J.append das
  J.append das jtypExp
  pure jtypExp

--TODO: create css entry for "let typExpContainer" and "let expr"
letExpr :: forall eff. List J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
letExpr jBinds jExpr t i = do
  jtypExp <- makeDiv "" (singleton "list typExpContainer")
  --jtypExp <- makeDiv "" (singleton "let typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dlet <- makeDiv "" (singleton "list expr")
  addTypetoDiv t dlet
  addIdtoDiv i dlet
  --dlet <- makeDiv "" (singleton "let expr") >>= addTypetoDiv t >>= addIdtoDiv i
  makeDiv "let" (singleton "keyword") >>= flip J.append dlet
  interleaveM_ (flip J.append dlet) (makeDiv ";" (singleton "semicolon") >>= flip J.append dlet) jBinds
  makeDiv "in" (singleton "keyword") >>= flip J.append dlet
  J.append jExpr dlet
  J.append dlet jtypExp
  pure jtypExp

letBinding :: forall eff. J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
letBinding jBind jExpr = do
  jtypExp <- makeDiv "" (singleton "letBinding  typExpContainer")
  dlet <- makeDiv "" (singleton "letBinding  expr")
  J.append jBind dlet
  makeDiv "=" Nil >>= flip J.append dlet
  J.append jExpr dlet
  J.append dlet jtypExp
  pure jtypExp

interleaveM_ :: forall a b m. (Monad m) => (a -> m b) -> m b -> List a -> m Unit
interleaveM_ f sep = go
  where
  go Nil     = pure unit
  go (Cons x Nil)    = void $ f x
  go (Cons x xs) = f x *> sep *> go xs

tuple :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
tuple js t i = do
  jtypExp <- makeDiv "" (singleton "tuple  typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dtuple <- makeDiv "" (singleton "tuple  expr")
  addTypetoDiv t dtuple
  addIdtoDiv i dtuple
  open <- makeDiv "(" (singleton "brace")
  J.append open dtuple
  interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js
  close <- makeDiv ")" (singleton "brace")
  J.append close dtuple
  J.append dtuple jtypExp
  pure jtypExp

list :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
list js t   i  = do
  jtypExp <- makeDiv "" (singleton "list typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dls <- makeDiv "" (singleton "list expr")
  addTypetoDiv t dls
  addIdtoDiv i dls
  open <- makeDiv "[" (singleton "brace")
  J.append open dls
  interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js
  close <- makeDiv "]" (singleton "brace")
  J.append close dls
  J.append dls jtypExp
  pure jtypExp

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
  jString <- makeDiv ("\"" <> str <> "\"") (Array.toUnfoldable ["list", "string", "expr"])
  addTypetoDiv t jString
  addIdtoDiv i jString
  J.append jString  jtypExp
  pure jtypExp

toStr :: List Expr -> Maybe String
toStr Nil = Nothing
toStr ls  = (joinWith "" <<< Array.fromFoldable) <$> for ls extract
  where
   extract:: Expr -> Maybe String
   extract (Atom (Char s)) = Just s
   extract _               = Nothing

app :: forall eff. J.JQuery -> List J.JQuery -> Type -> Type -> Int  -> Eff (dom :: DOM | eff) J.JQuery
app jFunc jArgs tFunc t i = do
  jtypExp <- makeDiv "" (singleton "app typExpContainer")
  jExpand <- buildExpandDiv t
  J.append jExpand jtypExp
  dApp <- makeDiv "" (singleton "app expr")
  addTypetoDiv t dApp
  addIdtoDiv i dApp
  J.addClass "func" jFunc
  J.addClass "funcContainer" jFunc
  innerExpr <- children ".expr" jFunc
  jExpand2 <- children ".expand" jFunc
  innerTyp <- children ".type" jExpand2
  typeArr <- children ".type-arr" jExpand2
  J.css {transform: "rotate(180deg)"} typeArr
  case tFunc of
    TypeError _ -> J.setVisible true innerTyp
    _ -> J.setVisible false innerTyp
  J.addClass "func" innerExpr
  J.append jFunc dApp
  for jArgs (flip J.append dApp)
  J.append dApp jtypExp
  pure jtypExp

type Class = String

makeDiv :: forall eff. String -> List Class -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for_ classes (flip J.addClass d)
  pure d

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
  J.on "mouseenter" (\e div -> J.stopPropagation e >>= \_ -> showTooltip div outer e) d
  pure d


addIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addIdtoDiv id d = do
    J.setAttr "id" ("expr"<>(show id)) d
    pure d

addTypIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addTypIdtoDiv id d = do
    J.setAttr "id" ("typ"<>(show id)) d
    pure d

addResultIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
addResultIdtoDiv id d = do
    J.setAttr "id" ("typ" <> (show id) <> "result") d
    pure d

buildExpandDiv:: forall eff. Type  -> Eff (dom :: DOM | eff) J.JQuery
buildExpandDiv t  = do
  typC <- makeDiv ("::" <> prettyPrintType t) $ Cons "type" Nil
  case t of
    (TypeError _) -> do
      J.css {color: "red"} typC
      pure typC
    _ -> pure typC
  expandC <- makeDiv "" $ Cons "expand"  Nil
  jArrow <- makeDiv "▼" $ Cons "type-arr" Nil
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
  pure expandC

idExpr:: Expr -> IndexTree
idExpr e = fst $ runState (indexExpr e) {count:0}

indexExpr:: Expr -> State {count:: Int} IndexTree
indexExpr (Atom _) = do
                  i <- fresh
                  pure $ IAtom i
indexExpr (List es) = do
                  is <- traverse indexExpr es
                  i <- fresh
                  pure $ IListTree is i
indexExpr (NTuple es) = do
                  is <- traverse indexExpr es
                  i <- fresh
                  pure $ INTuple is i
indexExpr (Binary _ e1 e2) = do
                  i1 <- indexExpr e1
                  i2 <- indexExpr e2
                  i <- fresh
                  i' <- fresh
                  pure $ (IBinary i' i1 i2 i)
indexExpr (Unary _ e) = do
                  i <- indexExpr e
                  i' <- fresh
                  i'' <- fresh
                  pure $ IUnary i'' i i'
indexExpr (SectL e _) = do
                  i <- indexExpr e
                  i' <- fresh
                  i'' <- fresh
                  pure $ ISectL i i'' i'
indexExpr (SectR _ e) = do
                  i <- indexExpr e
                  i' <- fresh
                  i'' <- fresh
                  pure $ ISectR i'' i i'
indexExpr (PrefixOp _) = do
                  i <- fresh
                  pure $ IPrefixOp i
indexExpr (IfExpr e1 e2 e3) = do
                  i1 <- indexExpr e1
                  i2 <- indexExpr e2
                  i3 <- indexExpr e3
                  i <- fresh
                  pure $ IIfExpr i1 i2 i3 i
indexExpr (ArithmSeq e1 e2 e3) = do
                  i1 <- indexExpr e1
                  i2 <- traverse indexExpr e2
                  i3 <- traverse indexExpr e3
                  i <- fresh
                  pure $ IArithmSeq i1 i2 i3 i
indexExpr (LetExpr bin e) = do
                  ib <- traverse (indexBinding <<< fst) bin
                  ie <- traverse (indexExpr <<< snd) bin
                  i2 <- indexExpr e
                  i  <- fresh
                  pure $ ILetExpr (zip ib ie) i2 i
indexExpr (Lambda bs e) = do
                 ibs <- traverse indexBinding bs
                 i <- indexExpr e
                 i' <- fresh
                 pure $ ILambda ibs i i'
indexExpr (App e es) = do
                e1 <- indexExpr e
                is <- traverse indexExpr es
                i <- fresh
                pure $ IApp e1 is i
indexExpr (ListComp e qs) = do
                e1 <- indexExpr e
                is <- traverse indexQual qs
                i <- fresh
                pure $ IListComp e1 is i

indexQual :: ExprQual -> State {count :: Int} IndexQual
indexQual (Gen b e) = do
  b' <- indexBinding b
  e' <- indexExpr e
  i  <- fresh
  pure $ TGen b' e' i
indexQual (Let b e) = do
  b' <- indexBinding b
  e' <- indexExpr e
  i  <- fresh
  pure $ TLet b' e' i
indexQual (Guard e) = do
  e' <- indexExpr e
  i  <- fresh
  pure $ TGuard e' i

indexBinding:: Binding -> State {count :: Int} IBinding
indexBinding (Lit _) = do
                    i <- fresh
                    pure $ ILit i
indexBinding (ConsLit b1 b2 ) = do
                      i1 <- indexBinding b1
                      i2 <- indexBinding b2
                      i <- fresh
                      pure $ IConsLit i1 i2 i
indexBinding (ListLit bs) = do
                        is <- traverse indexBinding bs
                        i <- fresh
                        pure $ IListLit is i
indexBinding (NTupleLit bs) = do
                      is <- traverse indexBinding bs
                      i <- fresh
                      pure $ INTupleLit is i

fresh ::State {count:: Int} Int
fresh = do
  {count: count} :: {count :: Int} <- get
  put {count:count+1}
  pure count