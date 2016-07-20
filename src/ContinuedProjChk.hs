module ContinuedProjChk where

import AlgData
import AlgAux
import Utils
import Lib.Debug
import Calc
import Rules
import Solver
import AlgShow
import Lib.Noms

import Data.Maybe
import Data.List
import Data.Ratio

e0="1/(1+2/...)"::Algo
e1="1+2+..."::Algo
e2="1/(1+1/(2+...))"::Algo
e3 = "2+1/(2²+...)"::Algo
e4="4/(1+1²/(2+3²/(2+5²/...)))"::Algo -- pi
e5="3+1²/(6+3²/(6+5²/...))"::Algo -- pi
e6="1+1/(1+...)"::Algo -- phi
e7="a+a²+..."::Algo
e8="a+2/(a²+3/...)"::Algo
e9="1+2+1+3+1+4+1+5+..."::Algo
ee=[e0,e1,e2,e3,e4,e5,e6,e7,e8,e9]

list o=(mapM_ (putStrLn . show))o

localCalc o=(D_CONT,show o++" localCalc:")←(case (Just o) ·> calc  of {(Just r) -> r;_ -> o})
termCalc o=Op Identity [localCalc o]

(|-|) a b = delta dif b a b "..."
(|+|) a b = delta add b a b "..."

oplex::Algo->Int
oplex (Op Identity _)=1
oplex (Op _ m)=length m + sum (map oplex m)
oplex _=0

dabs (Op _ m)=sum $ map dabs m
dabs (Nom n)=abs n
dabs _ = 1

_cln (Op Identity [o])=_cln o
_cln (Op o m)=Op o $ map _cln m
_cln o = o

dif a b=termCalc$Op Sub [b,a]
add a b=localCalc$Op Sum [_cln a,_cln b]
cpa a b=a

sortKeys [o]=o
sortKeys (o:oo)=if o==EQ then sortKeys oo else o

stp o=delta cpa e o o (stepWith e c) True
  where
    (_,e,c,_,_,_)=head$projs o
    d=delta dif c e c Ellipsis

stepWith e c= delta cpa c e e (delta cpa Ellipsis c d (delta add Ellipsis c d Ellipsis True) True) True
  where d=(D_CONT,"d:")←(delta dif c e c Ellipsis True)

projs e=id
  $sortBy (\(_,_,c1,_,r1,n1) (_,_,c2,_,r2,n2)->(sortKeys[compare r1 r2,compare n1 n2]))
  $filter (\(v,_,_,_,_,n)->v)
  $_projs e
_projs e=concat$map __projs $reverse$walk e
__projs e=map (proj e) (reverse$tail$walk e)

-- test projection
proj e c = (nd == d,e,c,d,
    abs$toRational$localCalc$ 1-1/(Nom$NrRatio$(toInteger$length$walk e)%(2*(toInteger$length$walk c))),
    Nom$dabs d
  )
  where
    d=(D_CONT,"d:")←(delta dif c e c "..." False)
    nc=(D_CONT,"nc:")←(delta add "..." c d "..." False)
    ne=(D_CONT,"ne:")←(delta add c e d nc False)
    nd=(D_CONT,"nd:")←(delta dif nc ne nc "..." False)

-- debug -> deltas o=concat$[[[e,c,delta dif Ellipsis e c Ellipsis True] | c<-tail$walk e] | e<-reverse$init$walk o]

delta:: (Algo->Algo->Algo)->Algo->Algo->Algo->Algo->Bool->Algo
delta _ l a@(Op _ []) _ _ _= a
delta _ l _ b@(Op _ []) _ _= b
delta f l a@(Op _ [Ellipsis]) b@(Op _ [Ellipsis]) c _=c
delta f l a@(Op _ [Ellipsis]) b c complement
  | Ellipsis==l = delta cpa Ellipsis b b c complement
  | otherwise = (error "5") -- b
delta f l a b@(Op _ [Ellipsis]) c complement
  | complement = (delta cpa l a a c complement)
  | otherwise =c
delta f l oa@(Op opa (a:aa)) ob@(Op opb (b:bb)) c complement
  | oa==l = c
  | opa/=opb = f oa ob
  | otherwise =
      if isOp opa r
      then Op opa $ i : (membersOf r)
      else Op opa [i,r]
  where
    r=delta f l (Op opa aa) (Op opb bb) c complement
    i=delta f l a b c complement
delta f l a b@(Op opb mb) c complement
  | a==l=(error "11") -- c
  | ok rsz = delta f l (fromJust rsz) b c complement
  | otherwise= f a b
  where rsz=liberalSizeTo (Op opb [a]) (length mb)
delta f l a b c _= f a b

walk o= takeWhile isAlgOp $ iterate ws o
ws (Op op (o:oo))=chkQuant $ Op op oo
ws o = o
