module Continued where

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
e10="1,(-2),3,(-4),5,..."::Algo
e11="{1,2,...}"::Algo
e12="1,2,..."::Algo
e13="{1,2,3,...}"::Algo
ee=[e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13]

list o=(mapM_ (putStrLn . show))o
len=length . membersOf

localCalc o=(D_CONT,show o++" localCalc:")←(case (Just o) ·> calc  of {(Just r) -> r;_ -> o})
termCalc o=Op Identity [localCalc o]

_cln (Op Identity [o])=_cln o
_cln (Op o m)=Op o $ map _cln m
_cln o = o

dabs (Op _ m)=sum $ map dabs m
dabs (Nom n)=abs n
dabs _ = 1

sortKeys [o]=o
sortKeys (o:oo)=if o==EQ then sortKeys oo else o

dif a b=termCalc$Op Sub [b,a]
add a b=localCalc$Op Sum [_cln a,_cln b]
cpa a b=a

continued o n t
  -- | n==0=Just o
  | cs#>0=h *> delta cpa r r Ellipsis t
  | otherwise=Nothing
  where
    cs=drop n $ contSteps o
    h=head$ cs
    (Just (r,(e,c,d)))=h

contSteps::Algo->[Maybe (Algo,(Algo,Algo,Algo))]
contSteps o
  | ds#=0 = []
  | (length$walk c)<(length$walk d) && isJust s= s:contSteps n -- conpensating definition iatus
  | otherwise=iterate _stp $Just (o,hd)
  where
    ds=deltas o
    hd@(e,c,d)=head$ds
    s=_stp (Just (o,hd))
    (Just (n,_))=s

stp::Algo->Maybe Algo
stp o
  | d#>0=r *> (\(Just(ð,_))->Just ð) r
  | otherwise=Nothing
  where
    d=deltas o
    r=_stp $Just (o,head d)

_stp::Maybe (Algo,(Algo,Algo,Algo))->Maybe (Algo,(Algo,Algo,Algo))
_stp Nothing=Nothing
_stp (Just (o,s@(e,c,d)))
  | dInfo(D_CONT,"_stp:"++show s)=undefined
  |otherwise=c'' *> e'' *> o'' *> Just (o',(e',c',d))
  where
    c''=delta add c (_cln d) "..." "..."
    (Just c')=c''
    e''=delta add e (_cln d) c c'
    (Just e')=e''
    o''=delta cpa o o e =<<(stepWith s)
    (Just o')=o''

stepWith::(Algo,Algo,Algo)->Maybe Algo
stepWith (e,c,d) = {-d' *>-} (delta cpa e e c =<<(delta cpa c d' Ellipsis=<<(delta add c d' Ellipsis Ellipsis)))
  where d'=_cln d
    -- d'=(D_CONT,"d:")←(delta dif e c c Ellipsis)
    -- (Just d)=_cln<$>d'

-- test projection
proj e c xd'= isJust fd' && isJust d' && isJust nc' && isJust ne' && nd == d'
  where
    fd'=(D_CONT,"fd:")←(_delta dif e c c "..." True)
    (Just fd)=_cln<$>fd'
    d'=(D_CONT,"d:")←(_delta dif e c c "..." False)
    (Just d)=_cln<$>d'
    nc'=(D_CONT,"nc:")←(_delta add c d "..." "..." False)
    (Just nc)=nc'
    ne'=(D_CONT,"ne:")←(_delta add e fd c nc False)
    (Just ne)=ne'
    nd=(D_CONT,"nd:")←(_delta dif ne nc nc "..." False)

deltas::Algo->[(Algo, Algo, Algo)]
deltas e=[(e,c,d) | (_,_,e,c,d)<-_deltas e]
_deltas::Algo->[(Double, Double, Algo, Algo, Algo)]
_deltas e=id
  -- $sortBy (\(r1,n1,_,_,_) (r2,n2,_,_,_)->(sortKeys[compare n1 n2,compare r1 r2]))
  $sortBy (\(r1,n1,_,_,_) (r2,n2,_,_,_)->(sortKeys[compare n1 n2,compare r2 r1]))
  $concat$[__deltas o | o<-reverse$walk e,not$null$__deltas o]
__deltas::Algo->[(Double, Double, Algo, Algo, Algo)]
__deltas e=id
  $map (\(e,o,Just r)->let n=fromRational$toRational$dabs r::Double in (
    n*(abs$2-1/((fromIntegral$length$walk e)/(2.0*(fromIntegral$length$walk o)))::Double),
    n,e,o,r))
  $filter (\(e,c,i)->isJust i && (proj e c i))
  $ ___deltas e
___deltas::Algo->[(Algo, Algo, Maybe Algo)]
___deltas e=
  map (\o->(e,o,_delta dif e o o "..." True))
  $filter (\o->2*((length$walk e) - 1)>=3*((length$walk o) - 1))
  $tail$walk e

-- recursive apply f a' b' on all members of a and b
-- require a operators to have same structure as b
-- replace l with e
delta:: (Algo -> Algo -> Algo)-> Algo -> Algo -> Algo -> Algo -> Maybe Algo
delta f a b l e
  | dInfo(D_CONT,"delta "++(concat$intersperse " "$map show [a,b,l,e])) = undefined
  | otherwise = _delta f a b l e True
_delta:: (Algo -> Algo -> Algo)-> Algo -> Algo -> Algo -> Algo -> Bool -> Maybe Algo
_delta f (Op opa [Ellipsis]) (Op opb [Ellipsis]) l e s
  | l==Ellipsis=Just e
  | opa==opb=Just$Op opa [Ellipsis]
  | otherwise = Nothing
_delta f (Op opa [Ellipsis]) b l e s =_delta cpa b b Ellipsis e s
_delta f a (Op opb [Ellipsis]) l e s
  | a==l=Just e
  |otherwise=
    if s
    then _delta cpa a a l e s
    else Just$Op opb [Ellipsis]
_delta f (Op opa []) (Op opb []) l e s
  | opa==opb=Just$Op opa []
  | otherwise=Nothing
_delta f oa@(Op opa (a:ma)) (Op opb (b:mb)) l e s
  | oa==l = Just e
  | opa==opb =
    if (getOp=<<sub) == Just opa
    then Op opa <$> ((:)<$>(_delta f a b l e s)<*>(membersOf<$>sub))
    else Op opa <$> ((:)<$>(_delta f a b l e s)<*>((:[])<$>sub))
  | otherwise= Nothing
  where sub=(D_CONT,show opa++" sub:")←(_delta f (Op opa ma) (Op opb mb) l e s)
_delta f a b@(Op opb mb) l e s
  | a==l = Just e
  | ok rsz = _delta f (fromJust rsz) b l e s
  | otherwise= Nothing -- strict
  where rsz=liberalSizeTo (Op opb [a]) (length mb)
_delta f a b l e s= Just $ f a b

walk o= takeWhile (\o->isAlgOp o && (not$null$membersOf o)) $ iterate ws o
ws (Op op [])=Op op []
ws (Op op (o:oo))=chkQuant $ Op op oo
ws o = o
