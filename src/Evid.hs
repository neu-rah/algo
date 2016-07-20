module Evid where

import AlgData
import Calc
import Rules
import AlgShow
import Utils
import AlgAux
import AlgParser
import Lib.Debug
import Lib.Colors
import {-# SOURCE #-} Solver
import Context
import Steps

import Data.List
import Data.List.Split
import Data.Maybe
import qualified Data.Map as Map
import Debug.Trace
import Control.Applicative
import Data.Monoid hiding (Sum)

evidRules=map _algo [
  "a*?+b*?=(a+b)*?"
  ,"a/?+b/n=(a+b)/?"
  ,"(?+n)²=?²+2*?*n+n²"
  ,"(a+?)/n=a/n+?/n"
  ]

----------------------------------------------------------------------
-- evid strategy
evidStrat e=[[(eq,l,plexOn l eq)|l<-lits]|eq<-eqs]
  where
    eqs=filter (isOp Equation) e
    lits=literals (Op System eqs)

-- evid need revision!
-- improve stepping
evidOn x n (Op op oo)
  | n >= (length oo) || (not$ok r) = Nothing
  | otherwise=Just$Op op $take n oo ++ [fromJust r] ++ drop (n + 1) oo
  where
    r=evid x $oo!!n

------------------------------------------------
evided::Algo->Algo->Algo->Maybe Algo
evided pref e o = ((useCtx (Map.fromList [(Pref,o)])) =<< (_evid pref e))<|>(_evid pref e)

evid::Algo->Algo->Maybe Algo
evid pref expr@(Op Document m)
  | null f=Nothing
  | otherwise= Just $Op Document $algRebuild s m
  where
    s=map (evid pref) m
    f=filter isJust s

--evid pref (Op Resol m)=evid pref $last m
--evid pref (Op Simpl m)=evid pref $last m
evid pref e
  | dInfo (D_EVID,"evid "++show pref++" from "++show e) = undefined
  | ev#>1=last ev
  | otherwise=Nothing
  where
    ev=takeWhile ok $iterate ((=<<) (steps (debugEvid pref))) (Just e)

debugEvid pref e=(D_EVID,"evid "++show pref++" on "++show e++" to:")←(_evid pref e)

_evid::Algo->Algo->Maybe Algo
_evid pref (Neighbor Equals e)=_evid pref e
_evid pref (Op Equation (_:[(Op _ (_:[Bool False]))]))=Nothing -- conditions evaluated to False, no further development
--_evid pref expr@(Op Equation (_:(Op _ (_:[Bool False])):[]))=Nothing
_evid pref e@(Op Equation (f@(Op Func (_:p)):d@(Op Equals _):_))
  | null i || has (==f) d=_evid' pref e
  | otherwise= Nothing
  where
    i=intersect (literals (Op Params p)) (literals d)
_evid pref expr@(Op Equation (p1:(Op op (p2:_)):[]))
  | dInfo (D_EVID,"_evid "++show pref++" from "++show expr) = undefined
  | evr#>0=(D_EVID,show expr++" done by ev rules ")←(head evr)
  | elem pref (literals p1) && elem pref (literals p2)=Just $(D_EVID,show expr++" join preference to ")←(Op Equation [Op Sub [p1,p2],Op op [Nom 0]])
  | otherwise=(D_EVID,"try _evid' to: ")←(_evid' pref expr)
  where
    evr=filter ok $applyRules (Map.fromList[(Pref,pref)]) expr evidRules True

_evid pref target =_evid' pref target

_evid' pref target -- =__evid pref target
  | dInfo (D_EVID,"_evid' "++show pref++" from "++show target) = undefined
  | ok simp=(D_EVID,show target++" evid of simplifyable expr! ")←simp -- ((_evid' pref=<<simp)<|>simp)
  | null prep=(D_EVID,show target++" no rules applyed")←(__evid pref target)
  | otherwise= (D_EVID,show target++" evidRules applyed to "++show target)←res
  where
    simp=(D_EVID,info target++" simplify:")←(simplify target)
    prep=filter ok $applyRules (Map.fromList [(Pref,pref)]) target evidRules True
    oks=not $ null $ filter ok prep
    res=head prep

(↓) (Just a)=a
(↓) _=False

__evid::Algo->Algo->Maybe Algo
__evid pref (Op Exp [a,b])
  | a==b=Nothing
  | a==pref=Just$Op Root [Pref,b]
  | b==pref=Just$Op Log [Pref,a]
  | otherwise=Nothing
__evid pref (Op Resol m)=
  (D_EVID,"1º __evid "++show pref++" from Resol"++show m) ←
  (_evid pref $last m)
__evid pref (Op Simpl m)=
  (D_EVID,"1º __evid "++show pref++" from Simpl"++show m) ←
  (_evid pref $last m)

__evid _ (Op Equation (_:[(Op _ (_:[Bool False]))]))=Nothing
__evid _ (Op Equation (_:[Op ElementOf _]))=Nothing
__evid _ (Op Intersect _)=Nothing
__evid _ (Op Union _)=Nothing

__evid pref expr@(Op Func def@(fn:p:[]))
  | p==pref = (D_EVID,show expr++" __evid on function ")←(Just $ Op InvFunc (fn:Pref:[]))
  | otherwise=(D_EVID,show expr++" __evid on function ")←Nothing
__evid pref expr@(Op Func def@(fn:p:_))=Nothing

__evid pref expr@(Op Equation (p1:(Op op (p2:c)):[]))
  | dInfo (D_EVID,"2º __evid "++show pref++" from "++show expr) = undefined
  -- | cond && p2==0 = Nothing
  | ok p2' && (not $ ok p1')=Just$(D_EVID,show expr++" second part evid to ")
    ←(Op Equiv [Op Equation [pref,Op (inverse op) [repVars (Map.fromList [(Pref,p1)]) (fromJust p2')]]])
  | ok p2'=Just$(D_EVID,show expr++" second part evid to ")
    ←(Op Equiv [Op Equation ((Op Sub [p1,p2]):(Op op' [Nom 0]):[])])
  | p1==pref=(D_EVID,show expr++" p1 is pref, quiting ")←Nothing
  | ok p1'= Just$(D_EVID,show expr++" first part evid to ")
    ←(Op (
      if cond && (not isEquiv)
      then Implic
      else Equiv) [Op Equation [pref,Op op' ((repVars (Map.fromList [(Pref,p2)]) (fromJust p1')):condlst)]])
  | otherwise=(D_EVID,show expr++" no conclusion ")←Nothing
  where
    (p1',p2')=(__evid pref p1,__evid pref p2)
    inv=(D_EVID,"negs count:")
      ←(length$(filter (\o->not(o==Pref||(isNom o&&(o>=Nom 0))||isOp Neg o)) $ membersOf $fromJust p1')++(if ok p1' && (isOp Neg $fromJust p1') then [Und] else []))
    op'=if (((`elem` [Geometric,Relational]) <$> prior <$> (getOp expr))==Just True) && ((rem inv 2)/=0) then inverse op else op
    p1p=prior<$>getOp p1
    cond = (D_EVID,"cond:")←(((>=Geometric)<$>p1p)==(Just True)&&((<Function)<$>p1p)==(Just True))
    nonpref=filter (\o->not (has (==pref) o)) $membersOf p1
    nonprefOp=chkQuant$Op (fromJust$getOp p1) nonpref
    conds=(D_EVID,"st")←(if cond then (solved$Op Equation [if p2==0 || (not$null nonpref) then nonprefOp else p2,Op NotEqual [0]]):c else c)
    isEquiv=conds==[Bool True]
    condlst=if isEquiv then [] else conds

__evid pref expr@(Op Equiv [m])=(D_EVID,"__evid "++show pref++" from Equiv "++show m)← __evid pref m

__evid pref expr@(Op Floor [x])
  | x==pref= algo "(x>=?)&(x<(?+1))"
  | otherwise=Nothing

__evid pref expr@(Op And [])=(D_EVID,"__evid And remainder [] ")←Nothing --Just $ Op Equiv [Op And []]
__evid pref expr@(Op And (e@(Op Equation _):m))
  | ok r=Just$
    if ok rec
    then Op (resolPrec rop rec_op) (Op And (rv:[rec_v]):c++rec_c)
    else Op rop (Op And (rv:m):c)
  | ok rec=Just$Op rec_op (Op And (e:[rec_v]):rec_c)
  | otherwise=Nothing
  where
    r=(D_EVID,"Evid And r:")←(conclusionStep<$>evid pref e)
    (Just (Op rop (rv:c)))=r
    rec=(D_EVID,"Evid And rec1:")←(conclusionStep<$> __evid pref (Op And m))
    (Just(Op rec_op (rec_v:rec_c)))=rec
__evid pref expr@(Op And (e:m))
  | dInfo (D_EVID,"__evid "++show pref++" from "++show expr++":") = undefined
  | ok rec=Just$Op rec_op (Op And (e:[rec_v]):rec_c)
  | otherwise=Nothing
  where
    rec=(D_EVID,show expr++" Evid And rec2:")←(__evid pref (Op And m))
    (Just(Op rec_op (rec_v:rec_c)))=rec

__evid pref expr@(Op op m)
  | dInfo (D_EVID,"__evid "++show pref++" from "++show expr++":") = undefined
  -- | expr==pref = Just Pref
  | fails=(D_EVID,"__evid fails (multiplicity) ")←Nothing
  | oks && elem op parallelOps = (D_EVID,"__evid oks && parallelOps ")←Just inv --error$"parallels "++show op++" "++show m++" => "++show inv++" rem: "++show rem
  | wp#>1=(D_EVID,show expr++" __evid resuming coz of concluded wp ")←Nothing -- multiple preferences
  | oks=algTrace (D_EVID,"__evid "++show pref++" on "++show expr++" to "++show inv) Just inv
  | otherwise=(D_EVID,"__evid resuming ")←Nothing
  where
    sub=map (_evid pref) m
    fails=not $null (filter ((has (==pref)) . fst) $filter (not . ok . snd) $zip m sub)
    oks=(filter ok sub)#=1
    prefix=map snd $takeWhile (not . ok . fst) (zip sub m)
    sufix=map snd (dropWhile (ok . fst) $dropWhile (not . ok . fst) (zip sub m))
    (wp,wop)=(D_EVID,"part:")←(partition (ok . fst) $zip sub m)
    rem=map snd wop
    proc=(D_EVID,show expr++"proc:")←map (fromJust .fst) wp
    (fop:remop)=map (\(Op op _)->op) proc
    ie=if and $map (==fop) remop then fop else Implic
    vars=
      if (not $ok $ head sub) && (not $canComut op)
      then Map.fromList [(Pref,Op op (prefix++if null sufix then [Pref] else [Op (inverse op) (Pref:sufix)]))] --(Map.fromList [(Pref,Op op (rem++[Pref]))])
      else (Map.fromList [(Pref,Op (inverse op) (Pref:rem))])
    strip=concat $map (\(Op _ e)->e) proc
    inv=
      if elem op parallelOps || (memberOf (head proc) resolSteps && (not $elem op resolSteps)) || ((inverse op) == Identity)
      then Op ie [Op op (strip++rem)]
      else repVars vars (head proc)

__evid pref expr
  | dInfo (D_EVID,"__evid "++show pref++" from "++show expr) = undefined
  | pref==expr=Just Pref
  | otherwise=Nothing

-- EOF --
