module AlgAux where

import AlgData
import Utils
import AlgShow
import {-# SOURCE #-} Evid
import {-# SOURCE #-} Context
import Lib.Debug
import Lib.Colors

import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Control.Applicative
import Control.Exception.Base (assert)
import Control.Monad

conclusion :: Algo -> Algo
conclusion (Op Document m)=Op Document $map conclusion m
conclusion (Op Resol m)=last$membersOf$last m
conclusion (Op Simpl m)=last$membersOf$last m
conclusion o=o

conclusionStep (Op Resol m)=last m
conclusionStep (Op Simpl m)=last m
conclusionStep o=o

resolPrec Equiv Equiv = Equiv
resolPrec _ _ = Implic

isNeighbor::Algo->Bool
isNeighbor (Neighbor _ _)=True
isNeighbor _=False

hasNeighbor::Algo->Bool
hasNeighbor (Op op m)=or (map hasNeighbor m)
hasNeighbor (Neighbor _ _)=True
hasNeighbor _=False

isFunc (Op Func _)=True
isFunc (Op InvFunc _)=True
isFunc (Op DerivedFunc _)=True
isFunc _=False

repVars :: Ctx -> Algo -> Algo
repVars vars e=fromJust ((_repVars vars e)<|>Just e)
_repVars :: Ctx -> Algo -> Maybe Algo
_repVars vars o@(Op op m)=__repVars vars o <|> rebuild (_repVars vars) o
_repVars vars e=__repVars vars e
__repVars vars e=((isNeighbor<$>v)==(Just True))?(Nothing,v) where v=getVar e vars

-- aux function. heck context for function variant and return it with translated variables
-- f(n) -> [(f(x),=2*x)] -> =2*n
--_getFuncVar::Algo->Ctx->Maybe Algo
_getFuncVar (Op op (n:p)) vars
  | null funcs=Nothing
  | otherwise=useCtx ps def -- translate parameter names
  where
    (Op _ (_:p'),def)=head funcs
    ps=Map.fromList $ zip p' p
    funcs=Map.toList$Map.filterWithKey (\k _->case k of
      (Op op' (n':_))->op==op'&&n==n'
      otherwise->False) vars
getVar :: Algo -> Ctx -> Maybe Algo
--getVar e@(Op Func _) vars =_getFuncVar e vars
--getVar e@(Op InvFunc _) vars =_getFuncVar e vars
getVar expr vars=case Map.lookup expr vars of
  (Just (Neighbor Equals n))->Just n
  (Just (Op Set [n]))->Just n
  n@(Just _)->n
  otherwise->Nothing

---getVarList::[Algo]->Ctx->Ctx
getVarList vl vars=Map.fromList$zip vl (algRebuild (map (`getVar` vars) vl) $ repeat Und)

append::Algo->Algo->Algo
append o@(Op op m) e = Op op $ m++[e]
append _ _ = error "no reach! append to non-operator"

appendList::Algo->[Algo]->Algo
appendList o@(Op op m) e = Op op $ m++e
appendList _ _ = error "no reach! append to non-operator"

(<+)=(liftM2 append)::Maybe Algo->Maybe Algo->Maybe Algo
(<++)=(liftM2 appendList)::Maybe Algo->Maybe [Algo]->Maybe Algo
(<++|) o m=appendList<$>o<*>Just m

--rebuild members using processed ones and originals for non processed
algRebuild::[Maybe Algo]->[Algo]->[Algo]
{-# INLINE algRebuild #-}
algRebuild ma a=map (\(a,b)->if ok a then fromJust a else b) $zip ma a

rebuildOp::Algo->[Maybe Algo]->Maybe Algo
rebuildOp (Op op m) o
  |f#>0=Just$ Op op (algRebuild o m)
  |otherwise=Nothing
  where f=filter ok o

rebuild::(Algo->Maybe Algo)->Algo->Maybe Algo
rebuild f o@(Op op m)=rebuildOp o (map f m)

isAlgOp::Algo->Bool
isAlgOp=isJust . getOp

setOp::Ops->Algo->Algo
setOp op (Op _ m)=Op op m
setOps _ _ = error "setOp needs an operator!"

sortOnDegree :: Algo -> Algo -> Algo
sortOnDegree i e@(Op op m)
  | prior op==Arithmetic=Op op $map snd s
  | otherwise=Op op $ map (sortOnDegree i) m
  where s=sortBy (\a b->compare (fst b) (fst a)) $zip (degrees i e) m
sortOnDegree i e=e

getDegrees :: Algo -> [(Algo, Algo)]
{-# INLINE getDegrees #-}
getDegrees e=map (\(a,b)->(a,head$reverse$sort b)) $zip lits $map (`degrees` e) lits
  where lits=literals e

degree :: Algo -> Algo -> Algo
{-# INLINE degree #-}
degree i (Op Resol m)=degree i (last m)
degree i e=head$reverse$sort$degrees i e

degrees::Algo->Algo->[Algo]
degrees i e@(Op Resol m) = degrees i $last m
degrees i e@(Op Equation m@(a:Op ro (r:[]):[])) = [degree i a,degree i r]
degrees i e@(Op Root m@(a:[]))
  | a==i=[Nom 0.5]
  | otherwise=[Nom 0]
degrees i e@(Op Root m@(a:(Nom b):[]))
  | a==i=[Nom (1/b)]
  | otherwise=[Nom 0]
degrees i e@(Op Root m@(a:b:[]))
  | a==i=[Op Div [Nom 1,b]]
  | otherwise=[Nom 0]
degrees i e@(Op Exp m@(a:b:[]))
  | a==i=[b]
  | otherwise=[Nom 0]
degrees i e@(Op op m)
  | i==e=[Nom 1]
  | elem op (arithmeticOps++signalOps)=opDegree i e
  | prior op==Geometric=[foldl max d dd]
  | otherwise=map (degree i) m -- [Nom 0]
  where (d:dd)=opDegree i e
degrees i e
  | i==e=[Nom 1]
  | otherwise=[Nom 0]

opDegree :: Algo -> Algo -> [Algo]
{-# INLINE opDegree #-}
opDegree i (Op _ m)=concat$map (degrees i) m
opDegree _ _=undefined
-- apply a function definition -> target -> application

sameFunc :: Algo -> Algo -> Bool
sameFunc a@(Op Func _) b@(Op Func _)=_sameFunc a b
sameFunc a@(Op InvFunc _) b@(Op Func _)=_sameFunc a b
sameFunc a@(Op Func _) b@(Op InvFunc _)=_sameFunc a b
sameFunc a@(Op InvFunc _) b@(Op InvFunc _)=_sameFunc a b
sameFunc _ _=False
_sameFunc (Op _ (na:_)) (Op _ (nb:_))=(D_ANY,"_sameFunc "++show na++"=="++show nb++"=")←(na==nb)

dist::Ops->Ops->Bool
{-# INLINE dist #-}
dist a b=distOver (prior a) (prior b)

--calculate expression complexity
plex::Algo->Int
plex (Op Identity [o])=plex o
plex (Bool _)=1
plex (Nom _)=2
plex (Unit s@(Scale _ _ _ _ e base))=(if base==s then 3 else 4)+plex e
plex (Quant (w,u))=plex w+plex (Unit u)
plex (Neighbor Equals e)=plex e
plex (Neighbor op e)=plex $ Op op [e]
plex (Op Equals m)=(sum $map plex m)
plex (Op _ m@((Unit s@(Scale _ _ _ _ _ base)):_))=(if base==s then 1 else 2)+10+(sum $map plex (tail m))
plex (Op _ m)=10+(sum $map plex m)
plex Und=maxBound::Int -- this should be Infinit!
plex _=20 -- literals are more expensives of all (except undefined)

plexOn::Algo->Algo->Int
plexOn x y@(Lit _)=if x==y then 10 else 1
plexOn x (Op Exp [y,n])=if x==y then 100 else 1
plexOn x (Op Identity [o])=plexOn x o
plexOn x (Unit s@(Scale _ _ _ _ e base))=(if base==s then 3 else 4)*plexOn x e
plexOn x (Quant (w,u))=plexOn x w*plexOn x (Unit u)
plexOn x (Neighbor Equals e)=plexOn x e
plexOn x (Neighbor op e)=plexOn x $ Op op [e]
plexOn x (Op Equals m)=(foldl1 (*) $map (plexOn x) m)
plexOn x (Op _ m@((Unit s@(Scale _ _ _ _ _ base)):_))=(if base==s then 1 else 2)*(foldl1 (*) $map (plexOn x) (tail m))
plexOn x (Op _ m)=2*(foldl1 (*) $map (plexOn x) m)
plexOn x Und=1
plexOn x _=1
-- EOF --
