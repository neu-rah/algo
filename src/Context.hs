{-# LANGUAGE OverloadedStrings #-}
module Context where

import AlgData
import Utils
import AlgShow
import {-# SOURCE #-} Evid
import {-# SOURCE #-} Solver
import Lib.Debug
import Lib.Colors
import AlgAux
import Derive
import Neighbor
import Intervals

import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Control.Applicative
import Control.Exception.Base (assert)
import Control.Monad

--------------------------------------------------------------------------------
-- insert a variable into the context
insertVar :: Algo -> Algo -> Ctx -> Ctx
insertVar k v m = Map.insert k ((D_CTX,"insert new variable "++show k++"("++show v++"):")←jo) m
  where
    vv=mkNeighbor v<|>Just v
    (Just jo)=(comb<$>Map.lookup k m<*>vv)<|>vv
    comb (Op And m) v=(D_CTX," combining with existing 'And' value ")←(Op And (v:m))
    comb o v=(D_CTX," combining with existing single value ")←(Op And [v,o])

--check if expression is an assignment, always an (in)equation
-- valid l-value and some checks on legal r-values
-- circular definitions are not allowed
isAssign e@(Op Equation (_:(Op op _):_))
  | op == Equals = isAssign' e
  | otherwise = False
isAssign' (Op Equation (k@(Lit _):v@(Op op (_:[])):[]))=not$elem op [ElementOf,NotElementOf] || has (==k) v
isAssign' (Op Equation (k@(Op Func (_:args)):v@(Op op (_:_)):[]))=not$elem op [ElementOf,NotElementOf] || has (==k) v || (null $ intersect args (literals v))
isAssign' ((Op Equation (k@(Op InvFunc (_:args)):v@(Op op (_:_)):[])))=not$elem op [ElementOf,NotElementOf] || has (==k) v || (null $ intersect args (literals v))
isAssign' (Op Equation ((Dim _):(Op op (_:[])):[]))=not$elem op [ElementOf,NotElementOf]
isAssign' _ = False

------------------------------------------------------------------------
-- replace all definitions withj context conclusions
repDefs :: Map.Map Algo Algo -> Algo -> Maybe Algo
repDefs ctx o@(Op Equation [a,b])
  | isAssign o=Map.lookup a ctx
  | otherwise=Nothing
repDefs ctx (Op Resol m)=repDefs ctx $last m
repDefs ctx (Op Simpl m)=repDefs ctx $last m
repDefs ctx o@(Op op m)
  | elem op ([Document,System,And,Or]++resolSteps)=(D_SOLVER,show o++" repDefs ")←(rebuild (repDefs ctx) o)
  | otherwise= Nothing
repDefs ctx o=Nothing

------------------------------------------------------------------------
getVars::Algo->Ctx
getVars o =getVars' emptyCtx o

getVars' :: Ctx -> Algo -> Ctx
getVars' ctx o=getDefs' ctx  $ conclusion o

getDefs::Algo->Ctx
getDefs=getDefs' emptyCtx

getDefs' :: Ctx -> Algo -> Ctx
getDefs' ctx o=(D_CTX,show o++" getDefs:")←(toVars$varsRange$onDefs insertVar ctx o)

onDefs :: (Algo -> Algo -> Ctx -> Ctx) -> Ctx -> Algo -> Ctx
onDefs action ctx (Op Or m)
  = Map.map (Op Or)
  $ Map.map (map fromJust)
  $ (Map.map (filter isJust))
  $ (Map.mapWithKey (\k v->map (Map.lookup k) s) (Map.unions s))
  where s=(D_CTX,"onDefs s:")←(map (onDefs action emptyCtx) m)
onDefs action ctx o@(Op Equation [a,b])
  | isAssign o = action a b ctx
  | otherwise = ctx
onDefs action ctx (Op Resol (o:_))=onDefs action ctx o
onDefs action ctx (Op Simpl (o:_))=onDefs action ctx o
onDefs action ctx (Op op m)
  | elem op ([Document,System,And,Or]++resolSteps)=foldl (onDefs action) ctx m
  | otherwise= ctx
onDefs action ctx _=ctx

--------------------------------------------------------------------------------
-- context transformations

-- vars to expressions
fromVar::Algo->Algo->Algo
fromVar var n@(Neighbor _ _)=Op Equation [var,fromNeighbor n]
fromVar var n@(Sets _)=Op Equation [var,Op ElementOf [n]]
fromVar var o@(Op Set m)
  |m#=0=Bool False
  |m#=1=Op Equation [var,Op Equals m]
  |otherwise=Op Equation [var,Op ElementOf [o]]
fromVar var (Op op e)=Op op $ (map (\o->Op Equation [var,fromNeighbor o]) e)
fromVar var (Bool False)=Bool False
fromVar _ o=error $ "fromVar of "++show o

fromVars v=Map.mapWithKey fromVar v

infNeighbor (Neighbor _ "+Inf")=True
infNeighbor (Neighbor _ "-Inf")=True
infNeighbor _=False

-- expression to var
toVar::Algo->Algo
--toVar v@(Neighbor _ _)=v
toVar (Op Set [])={-Neighbor Equals $-} Bool False
toVar (Op Intersect m)=chkQuant$Op And $ filter (not . infNeighbor)$ map toVar m
toVar (Op Union m)=Op Or $ map toVar m
toVar (Sets (Range a b))
  | a==b = Neighbor Equals $ wingExpr a
  | otherwise=chkQuant$Op And $ filter (not . infNeighbor) [
      Neighbor (if wingIncl a then GreaterOrEqual else Greater) (wingExpr a),
      Neighbor (if wingIncl b then LessOrEqual else Less) (wingExpr b)]
toVar o=o

-- expressions to vars
toVars::Ctx->Ctx
toVars=Map.map toVar

-- var to range
varRange :: Algo -> Algo
varRange v= varSolved$chkQuant $ (case v of
  (Op Or m) -> Op Union $ algRebuild (map toRange m) m
  otherwise  -> Op Intersect $ algRebuild (map toRange $membersOf v) (membersOf v))

-- vars to ranges
varsRange::Ctx->Ctx
varsRange v =Map.map varRange v

-- old compatibility (chkAssign)
getAssigns ctx o
  = fromJust (r <|> (Just ctx))
  where r=chkAssign ctx o

chkAssign :: Ctx -> Algo -> Maybe Ctx
chkAssign ctx e=Just $ getDefs' ctx e --_chkAssign (Just ctx) e

_chkAssign::Maybe Ctx->Algo->Maybe Ctx
_chkAssign=onAssign Map.insert

onAssign::(Algo->Algo->Ctx->Ctx)->Maybe Ctx->Algo->Maybe Ctx
-- "Or" operator generates a special kind of assignment...
-- a=1 | a=2 <=> a=1|2
onAssign action (Just ctx) e@(Op Or m)
  | null proc=Nothing
  | otherwise=(D_ASSIGN,show e++" onAssign ")←(Just $Map.fromList ops)
  where
    proc=filter ok $map (chkAssign ctx) m
    lits=literals e
    maps x=map fromJust $filter ok $map ((Map.lookup x) . fromJust) proc
    ops=map (\(l,v)->(l,fromJust v)) (filter (\(_,v)->ok v) (zip lits (map mkop $map maps lits)))

onAssign action ctx (Op Resol m)=onAssign action ctx $last m
onAssign action ctx (Op Simpl m)=onAssign action ctx $last m
onAssign action ctx (Op System m)=foldl (onAssign action) ctx m
onAssign action ctx e@(Op Equation ((Op Func (_:_)):(Op _ (_:_)):[])) =chkAssignFuncs action ctx e
onAssign action ctx e@(Op Equation ((Op InvFunc (_:_)):(Op _ (_:_)):[])) =chkAssignFuncs action ctx e
onAssign action ctx (Op Equation (a@(Lit _):m@(Op op (b:[])):[]))=chkAssignMain action ctx op a b m
onAssign action ctx (Op Equation (a@(Dim _):m@(Op op (b:[])):[]))=chkAssignMain action ctx op a b m
onAssign action ctx (Op And m)=(D_CTX,"And op chkAssign to:")←(foldl (onAssign action) ctx m)
-- search assignments on childs
onAssign action c@(Just ctx) o@(Op op (m:mm))
  | dInfo(D_CTX,show ctx++"onAssign Op on "++show o)=undefined
  | elem op resolSteps=(D_CTX,"op is a resolStep:")←(onAssign action c m)
  | otherwise=(D_CTX,"op is otherwise:")←(Just$Map.union ctx (Map.fromList$map (\o->(o,Und)) (literals o)))
onAssign action (Just ctx) l@(Lit _)
  | ok has=Just ctx
  | otherwise = Just $ action l Und ctx
  where has=Map.lookup l ctx
onAssign action ctx _=ctx

chkAssignMain:: (Algo->Algo->Ctx->Ctx)->Maybe Ctx->Ops->Algo->Algo->Algo->Maybe Ctx
chkAssignMain action (Just ctx) op a raw val
  | dInfo(D_CTX,"chkAssignMain "++show op++" "++show a++","++show raw++" "++show val)=undefined
  | op == ElementOf || op==NotElementOf = Nothing
  | ok o=(onAssign action (Just$action a (comb (fromJust (mkNeighbor val<|>Just val)) jo) ctx) raw)<|>Just ctx
  | valid=(D_CTX,"chkAssignMain ")←((onAssign action (Just$action a (fromJust (mkNeighbor val<|>Just val)) ctx) raw)<|>Just ctx)
  | otherwise=onAssign action (Just ctx) raw
  where
    comb (Op And m) v=Op And (v:m)
    comb o v=Op And [v,o]
    o=Map.lookup a ctx
    (Just jo)=o
    valid=(D_CTX,"valid "++show a++" to value "++show raw++" :")
      ←(not(has (==a) val)) -- does not contain self in definition and is not defined yet-}

chkAssignFuncs action (Just ctx) e@(Op Equation (a@(Op t (o:oo)):m@(Op op (b:_)):[]))
  | dInfo(D_CTX,show e++" chkAssignFuncs "++show ctx)=undefined
  | op == ElementOf || op==NotElementOf = Nothing
  | valid=Just $action a m ctx
  | otherwise=Just ctx
  where
    lits=literals (Op Params oo) -- does not contain self in definition and is not defined yet
    usedVars=intersect lits $ literals m
    def=Map.toList $Map.filterWithKey (\(Op _ (n:_)) def->n==o) $Map.filterWithKey (\k _->isOp Func k||isOp InvFunc k) ctx
    valid=not((def#>0)||(has (==a) m)||null lits||null usedVars)

-- =============================================================================
-- replace context definitions and variables -----------------------------------
useCtx :: Ctx->Algo->Maybe Algo
useCtx vars expr@(Op Resol m)
  | Map.null vars = Nothing
  | ok hasVars=hasVars --Just$Op Resol ((init m) ++ [fromJust hasVars])
  | otherwise=Nothing
  where
    hasVars=useCtx vars $last m
useCtx vars expr@(Op Simpl m)
  | Map.null vars = Nothing
  | ok hasVars=Just$Op Simpl ((init m) ++ [fromJust hasVars])
  | otherwise=Nothing
  where
    hasVars=useCtx vars $last m
-- take special care on assignments, no self replacing
useCtx vars expr@(Op Equiv [Op Equation (l@(Lit _):r@(Op _ (rv:[])):[])])=useCtxResStep vars expr
useCtx vars expr@(Op Implic [Op Equation (l@(Lit _):r@(Op _ (rv:[])):[])])=useCtxResStep vars expr
useCtx vars expr@(Op Equation (l@(Dim _):r:[])) = useCtxEquation vars expr l r
useCtx vars expr@(Op Equation (l@(Lit _):r:[])) = useCtxEquation vars expr l r
useCtx vars expr@(Op Equation ((Op InvFunc _):_:[])) = neighbourMove=<<(useCtxEqFunc vars expr)
useCtx vars expr@(Op Equation ((Op Func _):_:[])) = neighbourMove=<<(useCtxEqFunc vars expr)
useCtx vars expr@(Op DerivedFunc (_:_)) = neighbourMove=<<(useCtxFunc vars expr)
useCtx vars expr@(Op InvFunc (_:_)) = neighbourMove=<<(useCtxFunc vars expr)
useCtx vars expr@(Op Func (_:_)) = useCtxFunc vars expr
useCtx vars expr@(Neighbor op e)=Neighbor op <$> useCtx vars e
useCtx vars expr@(Sets (SetExpr e d)) = (Just . Sets) =<<(((Just .SetExpr )=<<(useCtx vars e))<*>(useCtx vars d))
useCtx vars expr@(Op And _)
  = (rebuild
    (\o->if (Map.lookup o vars)==(Just$Bool False)||((Map.lookup o vars)==(Just$Bool True)) then Map.lookup o vars else Nothing)
    =<< s) <|> s
  where s=useCtxOp vars expr
useCtx vars expr@(Op _ _)=useCtxOp vars expr
useCtx vars expr
  -- | Map.null vars = Nothing
  | at==(Just$Bool False)=Nothing
  | isJust at =  if fromJust at==Und then Nothing else at
  | otherwise = Nothing
  where
    at=getVar expr vars

-- useCtx aux functions
useCtxResStep vars expr@(Op op [Op Equation (l@(Lit _):r@(Op _ (rv:[])):[])])
  | dInfo (D_CTX, "useCtxResStep "++show expr++" vars:"++show vars)=undefined
  | Map.null vars = Nothing
  -- | ok isdef && (plex (fromJust isdef)>plex rv)=Nothing
  -- | (not$ok isdef) && ok isvar && (fromJust isvar)==rv =Nothing
  -- | ok p1
  --  =if hasNeighbor okp1 then neighbourMove okp1 else Just okp1
  -- | ok p2' =(D_CTX,"equiv2 "++show expr++" vars:"++show vars++" useCtx:")
  --  ←(if hasNeighbor okp2 then neighbourMove okp2 else Just okp2)
  | otherwise=Nothing
  where
    --isdef=(D_CTX,"isdef:")←(Map.lookup l defs)
    --isvar=(D_CTX,"isvar:")←(Map.lookup l vars)
    --p1=useCtx defs defs l
    --p2=useCtx defs defs r
    --p2'=if ok p2 then p2 else useCtx vars r
    --okp1=Op Equiv [Op Equation [fromJust p1,r]]
    --okp2=Op Equiv [Op Equation [l,fromJust p2']]

useCtxOp::Ctx -> Algo -> Maybe Algo
useCtxOp vars expr@(Op op m)
  | dInfo (D_CTX, "useCtxOp "++show expr++" vars:"++show vars)=undefined
  | Map.null vars = (D_CTX,"useCtxOp:")←Nothing
  -- | ok useDefs=useDefs
  | ok at = (D_CTX,"ok at:")←(if fromJust at==Und then Nothing else at)
  | oks=(D_CTX,"oks:")←(if hasN then ((neighbourMove=<<rebuild)<|>rebuild) else rebuild)
  | otherwise = Nothing
  where
    -- useDefs=(D_CTX,"use defs:")←(useCtxOp emptyCtx defs expr)
    at=Map.lookup expr vars
    sub=map (useCtx vars) m
    oks=or $map ok sub
    rebuild=Just $Op op $ algRebuild sub m
    hasN=(hasNeighbor<$>rebuild)==(Just True)

-- remove local variables from vars list to avoid self replacement
filterVarPlex :: Algo -> Algo -> Maybe Algo
filterVarPlex v o@(Op And m)
  = case nvs of
    [] -> Nothing
    m' -> Just $ chkQuant $ Op And $ m'
  where
    nvs=filter (\o->case o of {(Neighbor Equals _)->True;_->False}) $map fromJust $ filter isJust $ map (filterVarPlex v) $ delete v m
filterVarPlex v o
  | v==o || plex v < plex o = (D_CTX,"plexing "++show v++" with "++show o++" => ")←Nothing
  | otherwise=(D_CTX,"plexing "++show v++" with "++show o++" => ")←(Just o)

useCtxEquation::Ctx->Algo->Algo->Algo->Maybe Algo
useCtxEquation vars expr l r -- @(Op rop (o:_))
  =(D_CTX,show expr++" useCtxEquation vars:"++show vars++" l:"++show l++" r:"++show r++":")
    ← (case getVar l nv of
      (Just(Bool b)) -> Just$Bool b -- replace the whole eq. with a final boolean conclusion
      otherwise -> (lv<|>rv)*> (Just$Op Equation []) <+ (lv<|>Just l) <+ (rv<|>Just r))
  where
    lv=(D_CTX,"\tuseCtxEquation lv:")←(neighbourMove=<<useCtx nv l)
    rv=(D_CTX,"\tuseCtxEquation rv:")←(neighbourMove=<<useCtx nv r)
    localVars=getVar l vars -- this could be moved with advantage to solve' but leaving useCtx without the hability
    nv=(D_CTX,"\tuseCtxEquation new vars:")←
      case filterVarPlex r=<<(localVars) of
        (Just v) -> Map.insert l v vars
        _ -> Map.delete l vars

useCtxFunc :: Ctx -> Algo -> Maybe Algo
useCtxFunc vars expr@(Op o (name:params))
  | dInfo(D_CTX,"useCtx on function "++show expr++" from:"++show def)=undefined
  | ok match=(D_CTX,show expr++" DIRECT MATCH! ")←match
  | def#=0=(D_CTX,show expr++" no defs ")←((\p->Op o (name:p)) <$> (membersOf<$>(useCtx vars $Op Params params)))
  | def#=1=(D_CTX,"one def found "++show def)←(applyFunc vars (head def) expr)
  | def#>1=(D_CTX,"multiple defs found "++show def)←Nothing
  | otherwise=Nothing
  where
    match=getVar expr vars
    def=Map.toList $Map.filterWithKey (\(Op _ (n:_)) def->n==name) $Map.filterWithKey (\k _->isOp Func k || isOp InvFunc k || isOp DerivedFunc k) vars

useCtxEqFunc :: Ctx -> Algo -> Maybe Algo
useCtxEqFunc vars expr@(Op Equation (l@(Op t (name:p)):r:[]))
  | dInfo(D_CTX,show expr++" useCtx on function equation"++" vars:"++show vars++" to:"++show def)=undefined
  -- | ok match=undefined
  | (def#>1)&&(odef#>0)=(D_CTX,"concurrent definitions ")
    ←((\o->Just $ Op Equation (o:[r]))=<<(applyFunc vars (head odef) l))
  | null def=(D_CTX,"no definitions yet.")←Nothing
  | null i && def#>0= (D_CTX,"equation as function app found "++show def)
    ←((\o->Just $ Op Equation (o:[r]))=<<(applyFunc vars (head def) l))
  | otherwise=(D_CTX,"\tsome form of function definition here!"++show def)←Nothing
  where
    i=intersect (literals (Op Params p)) (literals r)
    -- match=Map.lookup l vars
    defMap=Map.filterWithKey (\(Op _ (n:_)) def->n==name) $Map.filterWithKey (\k _->isOp Func k||isOp InvFunc k) vars
    def=Map.toList defMap
    odef=Map.toList $ Map.filterWithKey (\(Op t' _) _->t' /= t) defMap -- other definitions

applyFunc :: Ctx->(Algo, Algo) -> Algo -> Maybe Algo
applyFunc vars (e@(Op f (name:params)),def) expr@(Op g (n:p))
  | dInfo(D_CTX,show name++" "++show expr++"applyFunc from:"++show def)=undefined
  | name/=n = (D_CTX,"name mismatch")←Nothing
  | f==g = (D_CTX,"f==g ")←(neighbourMove=<<((useCtx pvs def) <|> ((D_CTX," from original def ")←Just def)))
  | (invRel f g) && (dlits#>0) && (lits#>0) && ok inv =
    (D_CTX,"invRel ")←(((useCtx pvs)=<<inv) <|> inv)
  | (derivRel f g) && (dlits#>0) && (lits#>0) && ok deriv =
    (D_CTX,"derivRel ")←(((useCtx pvs)=<<deriv) <|> deriv)
  | (dlits#>0) && (lits#>0) && f==InvFunc && ok inv  &&  g == DerivedFunc && ok invDerive =
    (D_CTX,"invDerive ")←(((useCtx pvs)=<<invDerive) <|> invDerive)
  | (dlits#>0) && (lits#>0) && f==DerivedFunc && ok inv  &&  g == InvFunc && ok deriveInv =
    (D_CTX,"deriveInv ")←(((useCtx pvs)=<<deriveInv) <|> deriveInv)
  | otherwise= Nothing
  where
    pvs=(D_CTX,"pvs:")←(Map.fromList $ zip params p)
    lits=literals (Op Params params)
    dlits=literals def
    inv=assert (dlits#>0&&lits#>0) $ (D_CTX,show pvs++" inverse evided "++show (head dlits)++" from "++show def++" using lit:"++show (head lits)++" to:")
      ←((\ð->evided (head dlits) ð (head dlits))=<<((Just def·>useCtx vars)<|>(Just def)))
    deriv=assert (dlits#>0&&lits#>0) $(D_CTX,"\tderived:")
      ←derive (head dlits) def
    deriveInv=assert (dlits#>0&&lits#>0) $(D_CTX,"\tderive inverse:")
      ←(derive (head dlits) =<< evided (head dlits) def (head lits))
    invDerive=assert (dlits#>0&&lits#>0) $(D_CTX,"\tinverse derive:")
      ←((\o->evided (head dlits) o (head lits)) =<< derive (head dlits) def)

invRel Func InvFunc = True
invRel InvFunc Func = True
invRel _ _ = False
derivRel Func DerivedFunc = True
derivRel DerivedFunc Func = True
derivRel _ _ = False

-- EOF
