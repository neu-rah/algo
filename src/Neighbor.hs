module Neighbor where

import AlgData
import Utils
import AlgAux
import Calc
import Lib.Debug
import {-# SOURCE #-} Solver

import Data.Maybe
import Control.Applicative

ldistrib _ []=[]
ldistrib a (o:oo)=([a,o]:ldistrib a oo)
rdistrib _ []=[]
rdistrib a (o:oo)=([o,a]:rdistrib a oo)
distribIn a@(Op opa ma) b@(Op opb mb)
  =(D_NEIGH,show a++" distibuting from "++show b++": ")←(Op opb $ map (Op opa) (concatMap (`rdistrib` mb) (filter (/=b) ma)))
distribIn a@(Op opa ma@(o:_)) b@(Neighbor op be)
  | b==o =(D_NEIGH,show a++" distibuting from first "++show b++": ")←(Neighbor op (Op opa (be:(filter (/=b) ma))))
  | otherwise =(D_NEIGH,show a++" distibuting from other "++show b++": ")←(Neighbor op (Op opa ((filter (/=b) ma)++[be])))
distribIn a b=error ("distribution requirements not met, provided\n\ta:"++show a++"\n\tb:"++show b)

-- *********************************************************************************************
-- NEIGHBOURS
mkNeighbor e@(Op op ((Op _ _):[]))=_mkNeighbor e
mkNeighbor e@(Op op (o:[]))=algElement o?(_mkNeighbor e,Nothing)
mkNeighbor _=Nothing
_mkNeighbor (Op op (o:[]))
  | elem op equatOps = Just $ Neighbor op o
  | otherwise=Nothing

fromNeighbor (Neighbor op v)=Op op [v]
--fromNeighbor (Sets op v)=Op op [v]
--fromNeighbor o@(Op And _)=rebuild fromNeighbor o
fromNeighbor o=error$"fromNeighbor of non neighbor object "++show o

invNeigh (Neighbor op v)=Neighbor (inverse op) v
invNeigh o=error ("inverse of non neighbor object "++show o)

neighbourMove::Algo->Maybe Algo
neighbourMove o=(Just o)~>_neighbourMove

_neighbourMove::Algo->Maybe Algo
_neighbourMove o@(Neighbor Equals n)=Just n
_neighbourMove o@(Neighbor r e) = Nothing
_neighbourMove (Op Equation ((Op And am):m))=Just$Op And (map (\o->Op Equation ([o]++m)) am)
{-_neighbourMove (Op Equation (a:[b@(Op op o)]))
  | ok p && ok s=Nothing
  | ok p = Just$ Op Equation [neighbourExpr jp,Op (inverse$neighbourOp jp) o]
  | ok s = Just$ Op Equation [a,Op (neighbourOp js) [js]]
  where
    p=neighbourMove a
    s=algProc _neighbourMove b
    (Just jp)=p
    (Just js)=s-}
_neighbourMove e@(Op And m)
  | dInfo (D_NEIGH, "neighbourMove And _ "++show e)=undefined
  |hasOp Equation e && f#>0 = Just $ (D_NEIGH, "neighbourMove And: ")←(Op And $ algRebuild s m)
  |otherwise=Nothing
  where
    s=map _neighbourMove m
    f=filter ok s
_neighbourMove e@(Op Equation [a,b@(Op rop (o:oo))])
  | dInfo (D_NEIGH, "neighbourMove Equation [a,b] "++show e)=undefined
  | ok na || ok nb=(D_NEIGH, "neighbourMove Equation: ")←((Just$Op Equation [])<+(na<|>Just a)<+(nb<|>Just b))
  | hasNeighbor a = (D_NEIGH, "neighbourMove swapping Equation: ")←(_neighbourMove $ Op Equation [o,Op (inverse rop) (a:oo)])
  | otherwise=Nothing
  where
    na=_neighbourMove a
    nb=_neighbourMove b
--_neighbourMove o@(Op op ((Op sop m):oo))
_neighbourMove o@(Op op m@(º:ºº))
  | dInfo (D_NEIGH, show op++" neighbourMove Op "++show o)=undefined
  | elem op equatOps = (D_NEIGH,show op++" then neighbourRelat ")←(neighbourRelat o)
  | elem op [Resol,Simpl] =(D_NEIGH,"neighbourMove on resolOp:")←((Just$Op op (init m))<+(_neighbourMove $ last m))
  | elem op resolSteps = (D_NEIGH,"neighbourMove on resolStep:")←(rebuild _neighbourMove o)
  | hasN#>1 = error "need infinitesimals!"
  | null neis && ((hasN#>0 && canComut op) || (isNeighbor$head m)) =(D_NEIGH,"neighbourMove distributing:")←(Just$distribIn o (head hasN) )
  | null neis && op == Div && ndn#>0 =(D_NEIGH,"neighbourMove inverse distributing:")←(Just$invNeigh$distribIn o (head$ndn))
  | null neis = (D_NEIGH,"no neighbourMove operation ")←Nothing
  | neis#=1=(D_NEIGH,"neighbourMove with sub-neighbors:")←Just $Neighbor r (Op op res)
  | otherwise = (D_NEIGH,"neighbourMove ")←Nothing
  where
    sub=map _neighbourMove m
    neis=filter (\o->isJust o&&(isNeighbor$fromJust o)) sub
    hasN=filter hasNeighbor m
    (Just (Neighbor r e))=head neis
    res=map (\(n,o)->if isJust n then neighbourExpr $ fromJust n else o) $ zip sub m
    ndn=filter isNeighbor ºº

_neighbourMove _=Nothing

neighbourRelat a@(Op Equals (o@(Neighbor nop nv):oo))=Just$Op nop (nv:oo)
neighbourRelat a@(Op op (o@(Neighbor Equals nv):oo))=Just$Op op (nv:oo)
neighbourRelat a@(Op op (o:oo))
  | dInfo (D_NEIGH, show a++" neighbourRelat ")=undefined
  | isNothing proc=(D_NEIGH,"no process ")←Nothing -- TODO: use infinitesimals in this case!
  | isOp Mul o = (D_NEIGH,"relat mul ")←(Just$Op (inverse r) (e:oo))
  | otherwise = (D_NEIGH,"relat otherwise ")←(Just$Op r (e:oo))
  where
    proc=(D_NEIGH,"relat op process members ")←(_neighbourMove o) -- <|>Just e
    (Just (Neighbor r e))=proc
--neighbourRelat o=error $"error "++show o
