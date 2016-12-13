module Web where

import Prelude
import Data.Foldable (all, class Foldable)
import Data.Unfoldable (fromMaybe)
import Data.String (joinWith)
import Data.List (List(Nil, Cons), singleton, fromFoldable, length, zip, (..), zipWithA, snoc)
import Data.Foreign (unsafeFromForeign, isUndefined)
import Data.Maybe (Maybe(..), isJust, fromJust, maybe)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Traversable (for, for_, traverse)
import Data.Array as Arr
import Data.String as Str

import Control.Apply ((*>))
import Control.Bind ((=<<), (>=>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery as J
import DOM (DOM)

import AST (Expr, Tree(..), Binding(..), Atom(..), Op, pPrintOp)

data RoseTree a = Node a (List (RoseTree a))

type Div = RoseTree { content :: String, classes :: (List String), zipper :: Maybe (Tuple Expr (Expr -> Expr)) }

type DivHole = Expr -> (Expr -> Expr) -> Div

nodeHole :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Expr -> (Expr -> Expr) -> Div
nodeHole content classes children expr hole =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: (Just (Tuple expr hole))
    }
    (fromFoldable children)


node :: forall f1 f2. (Foldable f1, Foldable f2) => String -> f1 String -> f2 Div -> Div
node content classes children =
  Node
    { content: content
    , classes: (fromFoldable classes)
    , zipper: Nothing
    }
    (fromFoldable children)

zipList :: ((Expr -> Expr) -> Expr -> Div) -> (List Expr -> Expr) -> List Expr -> List Div
zipList zipp hole Nil = Nil
zipList zipp hole (Cons x xs) = Cons (zipp (\x -> hole $ Cons x xs) x) (zipList zipp (hole <<< Cons x) xs)

exprToDiv:: Expr -> Div
exprToDiv = go id
  where
    go :: (Expr -> Expr) -> Expr -> Div
    go hole      (Atom _ a)            = atom a
    go hole expr@(List _ ls)           = case toString ls of
                                           Nothing  -> list (zipList go (hole <<< List unit) ls) expr hole
                                           Just str -> node ("\"" <> str <> "\"") ["list", "string"] []
    go hole expr@(NTuple _ ls)         = ntuple (zipList go (hole <<< NTuple unit) ls) expr hole
    go hole expr@(Binary _ op e1 e2)   = binary op
                                           (go (\e1 -> hole $ Binary unit op e1 e2) e1)
                                           (go (\e2 -> hole $ Binary unit op e1 e2) e2)
                                           expr hole
    go hole expr@(Unary _ op e)        = unary op (go (hole <<< Unary unit op) e) expr hole
    go hole expr@(SectL _ e op)        = sectl (go (\e -> hole $ SectL unit e op) e) op expr hole
    go hole expr@(SectR _ op e)        = sectr op (go (hole <<< SectR unit op) e) expr hole
    go hole      (PrefixOp _ op)       = prefixOp op
    go hole expr@(IfExpr _ ce te ee)   = ifexpr
                                           (go (\ce -> hole $ IfExpr unit ce te ee) ce)
                                           (go (\te -> hole $ IfExpr unit ce te ee) te)
                                           (go (\ee -> hole $ IfExpr unit ce te ee) ee)
                                           expr hole
    go hole expr@(LetExpr _ bes body)  = letexpr ((\(Tuple b e) -> Tuple (binding b) (go hole e)) <$> bes) (go hole body) -- TODO
    go hole expr@(Lambda _ binds body) = lambda (binding <$> binds) (go (hole <<< Lambda unit binds) body) expr hole

    go hole expr@(ArithmSeq _ start next end)
                                       = arithmseq
                                           (go (\x -> hole $ ArithmSeq unit x next end) start)
                                           (go (\x -> hole $ ArithmSeq unit start (Just x) end) <$> next)
                                           (go (\x -> hole $ ArithmSeq unit start next (Just x)) <$> end)
                                           expr hole
                                                    
    go hole      (ListComp _ _ _)      = node "" [] [] -- TODO
    go hole expr@(App _ func args)     = app (go funcHole func) argsDivs expr hole
      where
        funcHole func = hole $ App unit func args
        argsDivs = zipList go (hole <<< App unit func) args

atom :: Atom -> Div
atom (AInt n) = node (show n) ["atom", "num"] []
atom (Bool b) = node (if b then "True" else "False") ["atom", "bool"] []
atom (Char c) = node ("'" <> c <> "'") ["atom", "char"] []
atom (Name n) = node n ["atom", "name"] []

interleave :: forall a. a -> List a -> List a
interleave _ Nil          = Nil
interleave _ (Cons x Nil) = Cons x Nil
interleave a (Cons x xs)  = Cons x $ Cons a $ interleave a xs

listify :: String -> String -> String -> List Div -> List Div
listify b s e ls = (Cons begin (snoc (interleave sep ls) end))
  where
    begin = node b ["brace", "left"] []
    sep = node s ["separator", "comma"] []
    end = node e ["brace", "right"] []

list :: List Div -> DivHole
list Nil = nodeHole "[]" ["list empty"] []
list ls  = nodeHole "" ["list"] $ listify "[" "," "]" ls

ntuple :: List Div -> DivHole
ntuple ls = nodeHole "" ["tuple"] $ listify "(" "," ")" ls

opToDiv :: Op -> Div
opToDiv op = node (pPrintOp op) ["op"] []

binary :: Op -> Div -> Div -> DivHole
binary op d1 d2 = nodeHole "" ["binary"] [d1, opToDiv op, d2]

openBrace :: Div
openBrace = node "(" ["brace", "left"] []

closeBrace :: Div
closeBrace = node ")" ["brace", "right"] []

unary :: Op -> Div -> DivHole
unary op div = nodeHole "" ["unary"] [openBrace, opToDiv op, div, closeBrace]

sectl :: Div -> Op -> DivHole
sectl div op = nodeHole "" ["section"] [openBrace, div, opToDiv op, closeBrace]

sectr :: Op -> Div -> DivHole
sectr op div = nodeHole "" ["section"] [openBrace, opToDiv op, div, closeBrace]

prefixOp :: Op -> Div
prefixOp op = node "" ["prefixOp"] [openBrace, opToDiv op, closeBrace]

ifexpr :: Div -> Div -> Div -> DivHole
ifexpr cd td ed = nodeHole "" ["if"] [ifDiv, cd, thenDiv, td, elseDiv, ed]
  where
    ifDiv = node "if" ["keyword"] []
    thenDiv = node "then" ["keyword"] []
    elseDiv = node "else" ["keyword"] []

letexpr :: List (Tuple Div Div) -> Div -> Div
letexpr _ _ = node "" [] [] -- TODO

lambda :: List Div -> Div -> DivHole
lambda params body = nodeHole "" ["lambda"] (Cons open (Cons bslash (params <> (Cons arrow (Cons body (Cons close Nil))))))
  where
    open = node "(" ["brace", "left"] []
    bslash = node "\\" ["backslash", "separator"] []
    arrow = node "->" ["arrow", "separator"] []
    close = node ")" ["brace", "right"] []

app :: Div -> List Div -> DivHole
app func args = nodeHole "" ["app"] (Cons func args)

arithmseq :: Div -> Maybe Div -> Maybe Div -> DivHole
arithmseq start mnext mend = nodeHole "" ["arithmseq", "list"] $ [open, start] <> commaNext <> [dots] <> end <> [close]
 where
    open      = node "[" ["brace"] []
    comma     = node "," ["comma"] []
    commaNext = maybe [] (\next -> [comma, next]) mnext
    dots      = node ".." ["dots"] []
    end       = fromMaybe mend
    close     = node "]" ["brace"] []

binding :: Binding -> Div
binding (Lit a)         = node "" ["binding", "lit"] [atom a]
binding (ConsLit b1 b2) = node "" ["binding", "conslit"] $ listify "(" ":" ")" (Cons (binding b1) (Cons (binding b2) Nil))
binding (ListLit ls)    = node "" ["binding", "listlit"] $ listify "[" "," "]" (binding <$> ls)
binding (NTupleLit ls)   = node "" ["binding", "tuplelit"] $ listify "(" "," ")" (binding <$> ls)

type Callback = forall eff. Expr -> (Expr -> Expr) -> (J.JQueryEvent -> J.JQuery -> Eff (dom :: DOM | eff) Unit)

divToJQuery :: forall eff. Callback -> Div -> Eff (dom :: DOM | eff) J.JQuery
divToJQuery callback (Node { content: content, classes: classes, zipper: zipper } children) = do
  div <- makeDiv content classes
  for children (divToJQuery callback >=> flip J.append div)
  case zipper of
    Nothing                -> pure unit
    Just (Tuple expr hole) -> do
      J.on "click" (callback expr hole) div
      J.on "mouseover" (callback expr hole) div
      J.on "mouseout" (callback expr hole) div
      pure unit
  pure div

toString :: List Expr -> Maybe String
toString ls = Str.fromCharArray <$> go [] ls
  where
    go :: Array Char -> List Expr -> Maybe (Array Char)
    go acc (Cons (Atom _ (Char c)) rs) = case Str.toChar c of
                                           Just char -> go (Arr.snoc acc char) rs
                                           Nothing   -> Nothing
    go []  Nil                         = Nothing
    go acc Nil                         = Just acc
    go _   _                           = Nothing


-- exprToJQuery:: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
-- exprToJQuery output = go (output.expr)
--   where
--     go (Atom (Name _)) = exprToJQuery' output
--     go (Atom _) = topLevel
--     go (Binary _ _ _) = exprToJQuery' output
--     go (PrefixOp _) = topLevel
--     go _ = exprToJQuery' output

--     topLevel = case extractType output.typ of
--         TypeError _ -> exprToJQuery' output
--         _ -> do
--           jtypExp <- makeDiv "" (singleton "top typExpContainer")
--           jExpand <- buildExpandDiv (extractType output.typ)
--           J.append jExpand jtypExp
--           jExpr <- exprToJQuery' output
--           J.addClass "expr" jExpr
--           J.append jExpr jtypExp
--           pure jtypExp

-- -- TODO rename to fit new Type
-- -- TODO: Needs refactoring.
-- exprToJQuery' :: forall eff. Output -> Eff (dom :: DOM | eff) J.JQuery
-- exprToJQuery' output = go id output
--   where
--   go :: (Path -> Path) -> Output -> Eff (dom :: DOM | eff) J.JQuery
--   go p o =
--     (\jObj -> do
--           let f = J.setProp pathPropName (p End)
--           jExpr <- children ".expr" jObj
--           isNotEmpty <- J.hasClass "expr" jExpr
--           if isNotEmpty then f jExpr else f jObj
--           pure jObj
--           )
--     =<<
--     case o of
--     {expr:(Atom a), typ:(TAtom t), idTree:(IAtom i)} -> atom a t i
--     {expr:(Binary op e1 e2), typ:(TBinary opt tt1 tt2 t), idTree:(IBinary opi i1 i2 i)} -> do
--       j1 <- go (p <<< Fst) {expr:e1, typ:tt1, idTree:i1}
--       j2 <- go (p <<< Snd) {expr:e2, typ:tt2, idTree:i2}
--       binary op opt opi t i j1 j2
--     {expr:(List es), typ:(TListTree ts t), idTree:(IListTree is i)} -> case toStr es of
--                   Just str  -> string str t i
--                   Nothing -> do js <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t, idTree:i'}) (0 .. (length es - 1)) (zip is (zip es ts))
--                                 list js t i
--     {expr:NTuple es, typ:TNTuple ts t,idTree: INTuple is i} -> do
--       js <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t,idTree:i'}) (0 .. (length es - 1)) (zip is (zip es ts))
--       tuple js t i
--     {expr:SectL e op, typ:TSectL tt opt t, idTree:(ISectL i opi i')} -> do
--       j <- go (p <<< Fst) {expr:e, typ:tt, idTree: i}
--       jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
--       section j jop t i'
--     {expr:SectR op e, typ:TSectR opt tt t, idTree: (ISectR opi i i')} -> do
--       jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
--       j <- go (p <<< Snd) {expr:e, typ:tt, idTree: i}
--       section jop j t i'
--     {expr:PrefixOp op, typ:TPrefixOp t, idTree: (IPrefixOp i)} -> makeDiv ("(" <> pPrintOp op <> ")") (Arr.toUnfoldable ["prefix", "op"]) >>= addTypetoDiv t >>= addIdtoDiv i
--     {expr:IfExpr cond thenExpr elseExpr, typ:TIfExpr tt1 tt2  tt3 t,idTree:IIfExpr i1 i2 i3 i} -> do
--       jc <- go (p <<< Fst) {expr:cond, typ:tt1, idTree: i1}
--       jt <- go (p <<< Snd) {expr:thenExpr, typ:tt2, idTree: i2}
--       je <- go (p <<< Thrd) {expr:elseExpr, typ:tt3, idTree: i3}
--       ifexpr jc jt je t i

--     -- TODO: Remove nested case expressions.
--     {expr:(ArithmSeq start step end), typ:(TArithmSeq tstart tstep tend t), idTree:(IArithmSeq istart istep iend i)} -> do
--       jStart <- go (p <<< Fst)  {expr:start, typ:tstart, idTree:istart}
--       case Triple step tstep istep of
--         Triple (Just jstep) (Just jtstep) (Just jistep) ->
--           case Triple end tend iend of
--             Triple (Just jend) (Just jtend) (Just jiend) -> do
--               jStep <- go (p <<< Snd) {expr: jstep, typ: jtstep, idTree: jistep}
--               jEnd  <- go (p <<< Thrd) {expr: jend, typ: jtend, idTree: jiend}
--               arithmeticSequence jStart (Just jStep) (Just jEnd) t i
--             _ -> do
--               jStep <- go (p <<< Snd) {expr: jstep, typ: jtstep, idTree: jistep}
--               arithmeticSequence jStart (Just jStep) Nothing t i
--         _ ->
--           case Triple end tend iend of
--             Triple (Just jend) (Just jtend) (Just jiend) -> do
--               jEnd  <- go (p <<< Thrd) {expr: jend, typ: jtend, idTree: jiend}
--               arithmeticSequence jStart Nothing (Just jEnd) t i
--             _ -> arithmeticSequence jStart Nothing Nothing t i

--     {expr:(ListComp expr quals), typ:(TListComp texpr tquals t), idTree:(IListComp iexpr iquals i)} -> do
--       jExpr  <- go (p <<< Fst) {expr:expr, typ:texpr, idTree:iexpr}
--       jQuals <- zipWithA (\i (Tuple i' (Tuple e t)) -> qualifier (p <<< Nth i) e t i')
--         (0 .. (length quals - 1)) (zip iquals (zip quals tquals))
--       listComp jExpr jQuals t i

--     {expr:Lambda binds body, typ:TLambda lb tt t, idTree: (ILambda bis i i')} -> do
--       jBinds <- for (zip bis (zip binds lb)) binding
--       jBody <- go (p <<< Fst) {expr:body, typ:tt, idTree: i}
--       lambda jBinds jBody t i'
--     {expr:App func args, typ:TApp tt ts t, idTree:IApp i1 is i} -> do
--       jFunc <- go (p <<< Fst) {expr:func, typ:tt, idTree: i1}
--       jArgs <- zipWithA (\i (Tuple i' (Tuple e t)) -> go (p <<< Nth i) {expr:e, typ:t, idTree: i'}) (0 .. (length args - 1)) (zip is (zip args ts))
--       app jFunc jArgs (extractType tt) t i
--     {expr: Unary op exp, typ: TUnary opt tt t, idTree:IUnary opi is i} -> do
--       jop <- makeDiv (pPrintOp op) (singleton "op") >>= addTypetoDiv opt >>= addIdtoDiv opi
--       jexpr <- go (p <<< Fst) {expr: exp, typ: tt, idTree: is}
--       unary jop jexpr t i

--     {expr: LetExpr binds exp, typ: TLetExpr tbinds texp t, idTree: ILetExpr ibinds iexp i} -> case checkLength binds tbinds ibinds of
--       false -> makeDiv "oops! LetExpr bindings length error!" Nil
--       true  -> do
--         let fstBoundle = zip (fst <$> ibinds) (zip (fst <$> binds) (fst <$> tbinds))
--             sndBoundle = zip (snd <$> ibinds) (zip (snd <$> binds) (snd <$> tbinds))

--         jbinds <- traverse binding fstBoundle
--         jexprs <- zipWithA (\x (Tuple i (Tuple b t)) -> go (p <<< Nth x) {expr: b, typ: t, idTree: i}) (1 .. (length sndBoundle)) sndBoundle
--         jletBinds <- zipWithA letBinding jbinds jexprs

--         jexpr <- go (p <<< Fst) {expr: exp, typ: texp, idTree: iexp}
--         letExpr jletBinds jexpr t i

--     {} -> makeDiv "You found a Bug" Nil

--   qualifier :: (Path -> Path) -> ExprQual -> TypeQual -> IndexQual -> Eff (dom :: DOM | eff) J.JQuery
--   qualifier p (Gen b e) (TGen tb te t) (TGen ib ie i) = do
--       result <- makeDiv "" Nil
--       addTypetoDiv t result
--       addIdtoDiv i result
--       binding (Tuple ib (Tuple b tb)) >>= flip J.append result
--       makeDiv "<-" Nil >>= flip J.append result
--       go p {expr:e, typ:te, idTree:ie} >>= flip J.append result
--       pure result
--   qualifier p (Let b e) (TLet tb te t) (TLet ib ie i) = do
--       result <- makeDiv "let" Nil >>= addTypetoDiv t >>= addIdtoDiv i
--       binding (Tuple ib (Tuple b tb)) >>= flip J.append result
--       makeDiv "=" Nil >>= flip J.append result
--       go p {expr:e, typ:te, idTree:ie} >>= flip J.append result
--       pure result
--   qualifier p (Guard e) (TGuard te t) (TGuard ie i) = go p {expr:e, typ:te, idTree:ie}
--   qualifier _ _ _ _ = makeDiv "You found a Bug in Web.exprToJquery'.qualifier" Nil

-- checkLength :: forall a b c. List a -> List b -> List c -> Boolean
-- checkLength a b c = length a /= 0 && length a == length b && length a == length c && length b == length c

-- atom :: forall eff. Atom -> Type -> Int ->  Eff (dom :: DOM | eff) J.JQuery
-- atom (AInt n) t  i   = do
--   div <- makeDiv (show n) (Arr.toUnfoldable ["atom", "num"])
--   addTypetoDiv t div
--   addIdtoDiv i div
--   pure div
-- atom (Bool true) t i = do
--   div <- makeDiv "True"  (Arr.toUnfoldable ["atom", "bool"])
--   addTypetoDiv t div
--   addIdtoDiv i div
--   pure div
-- atom (Bool false) t i = do
--   div <- makeDiv "False" (Arr.toUnfoldable ["atom", "bool"])
--   addTypetoDiv t div
--   addIdtoDiv i div
--   pure div
-- atom (Char c) t  i  = do
--   div <- makeDiv ("'" <> c <> "'") (Arr.toUnfoldable ["atom", "char"])
--   addTypetoDiv t div
--   addIdtoDiv i div
--   pure div
-- atom (Name name) t i = do
--  jtypExp <- makeDiv "" (singleton "atom name typExpContainer")
--  jExpand <- buildExpandDiv t
--  J.append jExpand jtypExp
--  jName <- makeDiv name (Arr.toUnfoldable ["atom", "name", "expr"])
--  addTypetoDiv t jName
--  addIdtoDiv i jName
--  J.append jName jtypExp
--  pure jtypExp

-- binding :: forall eff. Tuple IBinding (Tuple Binding TypeBinding) -> Eff (dom :: DOM | eff) J.JQuery
-- binding b = case b of
--   Tuple (ILit i) (Tuple (Lit a) (TLit t))       -> atom a t i
--   cl@(Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))) -> do
--     jCons <- makeDiv "" Nil
--     addTypetoDiv t jCons
--     addIdtoDiv i jCons
--     makeDiv "(" (singleton "brace") >>= flip J.append jCons
--     consBinding cl jCons
--     div <- makeDiv ")" (singleton "brace")
--     J.append div jCons
--     pure div
--   Tuple (IListLit is i)(Tuple (ListLit bs) (TListLit tbs t)) -> do
--     jList <- makeDiv "" Nil
--     addTypetoDiv t jList
--     addIdtoDiv i jList
--     makeDiv "[" (singleton "brace") >>= flip J.append jList
--     interleaveM_
--       (\b -> binding b >>= flip J.append jList)
--       (makeDiv "," (singleton "comma") >>= flip J.append jList)
--       (zip is (zip bs tbs))
--     div <- makeDiv "]" (singleton "brace")
--     J.append div jList
--     pure div
--   Tuple (INTupleLit is i)(Tuple (NTupleLit bs) (TNTupleLit tbs t))-> do
--     jTuple <- makeDiv "" Nil
--     addTypetoDiv t jTuple
--     addIdtoDiv i jTuple
--     makeDiv "(" (singleton "brace") >>= flip J.append jTuple
--     let b = (zip is (zip bs tbs))
--     interleaveM_ (binding >=> flip J.append jTuple) (makeDiv "," (singleton "comma") >>= flip J.append jTuple) b
--     makeDiv ")" (singleton "brace") >>= flip J.append jTuple
--     pure jTuple

--   _ -> makeDiv ("congrats you found a bug in Web.binding") Nil
--   where
--     consBinding :: Tuple IBinding (Tuple Binding  TypeBinding) -> J.JQuery-> Eff (dom :: DOM | eff) Unit
--     consBinding (Tuple (IConsLit i1 i2 i) (Tuple (ConsLit b bs) (TConsLit tb tbs t))) jCons = do
--       binding (Tuple i1 (Tuple b tb)) >>= flip J.append jCons
--       makeDiv ":" (singleton "colon") >>= flip J.append jCons
--       consBinding (Tuple i2 (Tuple bs tbs)) jCons
--     consBinding b jCons = void $ binding b >>= flip J.append jCons

-- lambda :: forall eff. List J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- lambda jBinds jBody t i = do
--   jtypExp <- makeDiv "" (singleton "lambda typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   jLam <- makeDiv "" (singleton "lambda expr")
--   addTypetoDiv t jLam
--   addIdtoDiv i jLam
--   open <- makeDiv "(\\" (Cons "brace" (Cons "backslash" Nil))
--   J.append open jLam
--   for jBinds (flip J.append jLam)
--   arrow <- makeDiv "->" (singleton "arrow")
--   J.append arrow jLam
--   J.append jBody jLam
--   close <- makeDiv ")" (singleton "brace")
--   J.append close jLam
--   J.append jLam jtypExp
--   pure jtypExp

-- binary :: forall eff. Op -> Type -> Int -> Type -> Int -> J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
-- binary op opt opi t i j1 j2 = do
--   dBin <- makeDiv "" (singleton "binary")
--   addTypetoDiv t dBin
--   addIdtoDiv i dBin
--   J.append j1 dBin
--   dOp <- makeDiv (pPrintOp op) (singleton "op")
--   addTypetoDiv opt dOp
--   addIdtoDiv opi dOp
--   J.append dOp dBin
--   J.append j2 dBin
--   jtypExp <- makeDiv "" (singleton "binary typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   J.addClass "expr" dBin
--   J.append dBin jtypExp
--   pure jtypExp

-- unary:: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- unary jop jexpr t i = do
--   jtypExp <- makeDiv "" (singleton "unary typExpContainer")
--   jExpand <-  buildExpandDiv t
--   J.append jExpand jtypExp
--   jUnary <- makeDiv "" (singleton "unary expr")
--   addTypetoDiv t jUnary
--   addIdtoDiv i jUnary
--   J.append jop jUnary
--   J.append jexpr jUnary
--   J.append jUnary jtypExp
--   pure jtypExp

-- section :: forall eff. J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- section j1 j2 t i = do
--   jtypExp <- makeDiv "" (singleton "section typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   jSect <- makeDiv "" (singleton "section expr")
--   addTypetoDiv t jSect
--   addIdtoDiv i jSect
--   open <- makeDiv "(" (singleton "brace")
--   J.append open jSect
--   J.append j1 jSect
--   J.append j2 jSect
--   close <- makeDiv ")" (singleton "brace")
--   J.append close jSect
--   J.append jSect jtypExp
--   pure jtypExp

-- ifexpr :: forall eff. J.JQuery -> J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- ifexpr cond thenExpr elseExpr t i = do
--   jtypExp <- makeDiv "" (singleton "if typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dIf <- makeDiv "" (singleton "if expr")
--   addTypetoDiv t dIf
--   addIdtoDiv i dIf
--   makeDiv "if" (singleton "keyword") >>= flip J.append dIf
--   J.append cond dIf
--   makeDiv "then" (singleton "keyword") >>= flip J.append dIf
--   J.append thenExpr dIf
--   makeDiv "else" (singleton "keyword") >>= flip J.append dIf
--   J.append elseExpr dIf
--   J.append dIf jtypExp
--   pure jtypExp

-- arithmeticSequence :: forall eff. J.JQuery -> Maybe J.JQuery -> Maybe J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- arithmeticSequence start mstep mend t i = do
--   jtypExp <- makeDiv "" (singleton "list typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   das <- makeDiv "" (singleton "list expr")
--   addTypetoDiv t das
--   addIdtoDiv i das
--   makeDiv "[" (singleton "brace") >>= flip J.append das
--   J.append start das
--   maybeStep das mstep
--   makeDiv ".." (singleton "dot") >>= flip J.append das
--   maybeEnd das mend
--   makeDiv "]" (singleton "brace") >>= flip J.append das
--   J.append das jtypExp
--   pure jtypExp
--   where
--     maybeStep :: J.JQuery -> Maybe J.JQuery -> Eff (dom :: DOM | eff) Unit
--     maybeStep jquery Nothing = pure unit
--     maybeStep jquery (Just step) = do
--       makeDiv "," (singleton "comma") >>= flip J.append jquery
--       J.append step jquery

--     maybeEnd :: J.JQuery -> Maybe J.JQuery -> Eff (dom :: DOM | eff) Unit
--     maybeEnd jquery Nothing = pure unit
--     maybeEnd jquery (Just end) = J.append end jquery

-- listComp :: forall eff. J.JQuery -> List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- listComp jExpr jQuals t i = do
--   jtypExp <- makeDiv "" (singleton "list typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   das <- makeDiv "" (singleton "list expr")
--   addTypetoDiv t das
--   addIdtoDiv i das
--   makeDiv "[" (singleton "brace") >>= flip J.append das
--   J.append jExpr das
--   makeDiv "|" (singleton "comma") >>= flip J.append das
--   interleaveM_ (flip J.append das) (makeDiv "," (singleton "comma") >>= flip J.append das) jQuals
--   makeDiv "]" (singleton "brace") >>= flip J.append das
--   J.append das jtypExp
--   pure jtypExp

-- --TODO: create css entry for "let typExpContainer" and "let expr"
-- letExpr :: forall eff. List J.JQuery -> J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- letExpr jBinds jExpr t i = do
--   jtypExp <- makeDiv "" (singleton "list typExpContainer")
--   --jtypExp <- makeDiv "" (singleton "let typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dlet <- makeDiv "" (singleton "list expr")
--   addTypetoDiv t dlet
--   addIdtoDiv i dlet
--   --dlet <- makeDiv "" (singleton "let expr") >>= addTypetoDiv t >>= addIdtoDiv i
--   makeDiv "let" (singleton "keyword") >>= flip J.append dlet
--   interleaveM_ (flip J.append dlet) (makeDiv ";" (singleton "semicolon") >>= flip J.append dlet) jBinds
--   makeDiv "in" (singleton "keyword") >>= flip J.append dlet
--   J.append jExpr dlet
--   J.append dlet jtypExp
--   pure jtypExp

-- letBinding :: forall eff. J.JQuery -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
-- letBinding jBind jExpr = do
--   jtypExp <- makeDiv "" (singleton "letBinding  typExpContainer")
--   dlet <- makeDiv "" (singleton "letBinding  expr")
--   J.append jBind dlet
--   makeDiv "=" Nil >>= flip J.append dlet
--   J.append jExpr dlet
--   J.append dlet jtypExp
--   pure jtypExp

-- interleaveM_ :: forall a b m. (Monad m) => (a -> m b) -> m b -> List a -> m Unit
-- interleaveM_ f sep = go
--   where
--   go Nil     = pure unit
--   go (Cons x Nil)    = void $ f x
--   go (Cons x xs) = f x *> sep *> go xs

-- tuple :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- tuple js t i = do
--   jtypExp <- makeDiv "" (singleton "tuple  typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dtuple <- makeDiv "" (singleton "tuple  expr")
--   addTypetoDiv t dtuple
--   addIdtoDiv i dtuple
--   open <- makeDiv "(" (singleton "brace")
--   J.append open dtuple
--   interleaveM_ (flip J.append dtuple) (makeDiv "," (singleton "comma") >>= flip J.append dtuple) js
--   close <- makeDiv ")" (singleton "brace")
--   J.append close dtuple
--   J.append dtuple jtypExp
--   pure jtypExp

-- list :: forall eff. List J.JQuery -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- list js t   i  = do
--   jtypExp <- makeDiv "" (singleton "list typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dls <- makeDiv "" (singleton "list expr")
--   addTypetoDiv t dls
--   addIdtoDiv i dls
--   open <- makeDiv "[" (singleton "brace")
--   J.append open dls
--   interleaveM_ (flip J.append dls) (makeDiv "," (singleton "comma") >>= flip J.append dls) js
--   close <- makeDiv "]" (singleton "brace")
--   J.append close dls
--   J.append dls jtypExp
--   pure jtypExp

-- isString :: List Expr -> Boolean
-- isString es = length es > 0 && all isChar es
--   where
--   isChar (Atom (Char _)) = true
--   isChar _               = false

-- string :: forall eff. String -> Type -> Int -> Eff (dom :: DOM | eff) J.JQuery
-- string str t i = do
--   jtypExp <- makeDiv "" (singleton "list string typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   jString <- makeDiv ("\"" <> str <> "\"") (Arr.toUnfoldable ["list", "string", "expr"])
--   addTypetoDiv t jString
--   addIdtoDiv i jString
--   J.append jString  jtypExp
--   pure jtypExp

-- toStr :: List Expr -> Maybe String
-- toStr Nil = Nothing
-- toStr ls  = (joinWith "" <<< Arr.fromFoldable) <$> for ls extract
--   where
--    extract:: Expr -> Maybe String
--    extract (Atom (Char s)) = Just s
--    extract _               = Nothing

-- app :: forall eff. J.JQuery -> List J.JQuery -> Type -> Type -> Int  -> Eff (dom :: DOM | eff) J.JQuery
-- app jFunc jArgs tFunc t i = do
--   jtypExp <- makeDiv "" (singleton "app typExpContainer")
--   jExpand <- buildExpandDiv t
--   J.append jExpand jtypExp
--   dApp <- makeDiv "" (singleton "app expr")
--   addTypetoDiv t dApp
--   addIdtoDiv i dApp
--   J.addClass "func" jFunc
--   J.addClass "funcContainer" jFunc
--   innerExpr <- children ".expr" jFunc
--   jExpand2 <- children ".expand" jFunc
--   innerTyp <- children ".type" jExpand2
--   typeArr <- children ".type-arr" jExpand2
--   J.css {transform: "rotate(180deg)"} typeArr
--   case tFunc of
--     TypeError _ -> J.setVisible true innerTyp
--     _ -> J.setVisible false innerTyp
--   J.addClass "func" innerExpr
--   J.append jFunc dApp
--   for jArgs (flip J.append dApp)
--   J.append dApp jtypExp
--   pure jtypExp

type Class = String

makeDiv :: forall eff. String -> List Class -> Eff (dom :: DOM | eff) J.JQuery
makeDiv text classes = do
  d <- J.create "<div></div>"
  J.setText text d
  for_ classes (flip J.addClass d)
  pure d

-- emptyJQuery:: forall eff . Eff (dom :: DOM | eff) J.JQuery
-- emptyJQuery = J.create ""


-- addTypetoDiv:: forall eff. Type -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
-- addTypetoDiv typ d = do
--   text <- J.getText d
--   J.clear d
--   outer <- makeDiv "" $ Cons "tooltip-outer" Nil
--   inner <- makeDiv (prettyPrintType typ) $ Cons "tooltip-inner" Nil
--   J.append inner outer
--   J.append outer d
--   J.appendText text d
--   J.on "mouseenter" (\e div -> J.stopPropagation e >>= \_ -> showTooltip div outer e) d
--   pure d


-- addIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
-- addIdtoDiv id d = do
--     J.setAttr "id" ("expr"<>(show id)) d
--     pure d

-- addTypIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
-- addTypIdtoDiv id d = do
--     J.setAttr "id" ("typ"<>(show id)) d
--     pure d

-- addResultIdtoDiv:: forall eff a. (Show a) => a -> J.JQuery -> Eff (dom :: DOM | eff) J.JQuery
-- addResultIdtoDiv id d = do
--     J.setAttr "id" ("typ" <> (show id) <> "result") d
--     pure d

-- buildExpandDiv:: forall eff. Type  -> Eff (dom :: DOM | eff) J.JQuery
-- buildExpandDiv t  = do
--   typC <- makeDiv ("::" <> prettyPrintType t) $ Cons "type" Nil
--   case t of
--     (TypeError _) -> do
--       J.css {color: "red"} typC
--       pure typC
--     _ -> pure typC
--   expandC <- makeDiv "" $ Cons "expand"  Nil
--   jArrow <- makeDiv "▼" $ Cons "type-arr" Nil
--   J.append jArrow expandC
--   J.append typC expandC
--   J.on "click" (\e _ -> do
--       J.stopPropagation e
--       J.setVisible true typC
--       J.css {transform: "rotate(0deg)"} jArrow
--       ) expandC
--   J.on "click" (\e _ -> do
--       J.stopPropagation e
--       J.setVisible false typC
--       J.css {transform: "rotate(180deg)"} jArrow
--       ) typC
--   J.on "mouseenter" (\e _ -> J.stopImmediatePropagation e) expandC -- otherwise tooltip shows
--   J.on "mousemove" (\e _ -> J.stopImmediatePropagation e) expandC
--   J.setAttr "title" "show Type" expandC
--   J.setAttr "title" "hide Type" typC
--   J.css {display: "inline-block"} typC
--   pure expandC

-- idExpr:: Expr -> IndexTree
-- idExpr e = fst $ runState (indexExpr e) {count:0}

-- indexExpr:: Expr -> State {count:: Int} IndexTree
-- indexExpr (Atom _) = do
--                   i <- fresh
--                   pure $ IAtom i
-- indexExpr (List es) = do
--                   is <- traverse indexExpr es
--                   i <- fresh
--                   pure $ IListTree is i
-- indexExpr (NTuple es) = do
--                   is <- traverse indexExpr es
--                   i <- fresh
--                   pure $ INTuple is i
-- indexExpr (Binary _ e1 e2) = do
--                   i1 <- indexExpr e1
--                   i2 <- indexExpr e2
--                   i <- fresh
--                   i' <- fresh
--                   pure $ (IBinary i' i1 i2 i)
-- indexExpr (Unary _ e) = do
--                   i <- indexExpr e
--                   i' <- fresh
--                   i'' <- fresh
--                   pure $ IUnary i'' i i'
-- indexExpr (SectL e _) = do
--                   i <- indexExpr e
--                   i' <- fresh
--                   i'' <- fresh
--                   pure $ ISectL i i'' i'
-- indexExpr (SectR _ e) = do
--                   i <- indexExpr e
--                   i' <- fresh
--                   i'' <- fresh
--                   pure $ ISectR i'' i i'
-- indexExpr (PrefixOp _) = do
--                   i <- fresh
--                   pure $ IPrefixOp i
-- indexExpr (IfExpr e1 e2 e3) = do
--                   i1 <- indexExpr e1
--                   i2 <- indexExpr e2
--                   i3 <- indexExpr e3
--                   i <- fresh
--                   pure $ IIfExpr i1 i2 i3 i
-- indexExpr (ArithmSeq e1 e2 e3) = do
--                   i1 <- indexExpr e1
--                   i2 <- traverse indexExpr e2
--                   i3 <- traverse indexExpr e3
--                   i <- fresh
--                   pure $ IArithmSeq i1 i2 i3 i
-- indexExpr (LetExpr bin e) = do
--                   ib <- traverse (indexBinding <<< fst) bin
--                   ie <- traverse (indexExpr <<< snd) bin
--                   i2 <- indexExpr e
--                   i  <- fresh
--                   pure $ ILetExpr (zip ib ie) i2 i
-- indexExpr (Lambda bs e) = do
--                  ibs <- traverse indexBinding bs
--                  i <- indexExpr e
--                  i' <- fresh
--                  pure $ ILambda ibs i i'
-- indexExpr (App e es) = do
--                 e1 <- indexExpr e
--                 is <- traverse indexExpr es
--                 i <- fresh
--                 pure $ IApp e1 is i
-- indexExpr (ListComp e qs) = do
--                 e1 <- indexExpr e
--                 is <- traverse indexQual qs
--                 i <- fresh
--                 pure $ IListComp e1 is i

-- indexQual :: ExprQual -> State {count :: Int} IndexQual
-- indexQual (Gen b e) = do
--   b' <- indexBinding b
--   e' <- indexExpr e
--   i  <- fresh
--   pure $ TGen b' e' i
-- indexQual (Let b e) = do
--   b' <- indexBinding b
--   e' <- indexExpr e
--   i  <- fresh
--   pure $ TLet b' e' i
-- indexQual (Guard e) = do
--   e' <- indexExpr e
--   i  <- fresh
--   pure $ TGuard e' i

-- indexBinding:: Binding -> State {count :: Int} IBinding
-- indexBinding (Lit _) = do
--                     i <- fresh
--                     pure $ ILit i
-- indexBinding (ConsLit b1 b2 ) = do
--                       i1 <- indexBinding b1
--                       i2 <- indexBinding b2
--                       i <- fresh
--                       pure $ IConsLit i1 i2 i
-- indexBinding (ListLit bs) = do
--                         is <- traverse indexBinding bs
--                         i <- fresh
--                         pure $ IListLit is i
-- indexBinding (NTupleLit bs) = do
--                       is <- traverse indexBinding bs
--                       i <- fresh
--                       pure $ INTupleLit is i

-- fresh ::State {count:: Int} Int
-- fresh = do
--   {count: count} :: {count :: Int} <- get
--   put {count:count+1}
--   pure count

