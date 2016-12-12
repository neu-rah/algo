module Sample where

import AlgData
import AlgAux
import Utils
import Intervals
import {-# SOURCE #-} Solver
import Lib.Debug
import Lib.ISUnits
import Lib.Noms

import Data.Maybe

sample::Ops->Algo->Algo->Maybe Algo
--sample op Ellipsis _ = Just Ellipsis
--sample op _ Ellipsis = Just Ellipsis
sample Sub Ellipsis Ellipsis=Just 0
sample Sum Ellipsis (Op Neg [Ellipsis])=Just 0
sample Sum a (Op Neg [b])=sample Sub a b
sample op o (Op Neg [Nom n]) = sample op o (Nom (-n))
sample op (Op Neg [Nom n]) o = sample op (Nom (-n)) o
sample op r@(Sets (Range (RangeWing ai a) (RangeWing bi b))) x
  | elem op exprOps =Just$Sets(Range (RangeWing ai (Op op [a,x])) (RangeWing bi (Op op [b,x])))
  | otherwise = _sample op r x
sample op x r@(Sets (Range (RangeWing ai a) (RangeWing bi b)))
  | elem op exprOps=Just$Sets(Range (RangeWing ai (Op op [x,a])) (RangeWing bi (Op op [x,b])))
  | otherwise=_sample op x r
sample op x Infinit
  | elem op equatOps = _sample op x Infinit
  | otherwise=Just Infinit
sample op Infinit x
  | elem op equatOps = _sample op Infinit x
  | otherwise=Just Infinit
sample op x o@(Op Pos [Infinit])
  | elem op equatOps = _sample op x o
  | otherwise=Just o
sample op o@(Op Pos [Infinit]) x
  | elem op equatOps = _sample op o x
  | otherwise=Just o
sample op x o@(Op PosOrNeg [Infinit])
  | elem op equatOps = _sample op x o
  | otherwise=Just o
sample op o@(Op PosOrNeg [Infinit]) x
  | elem op equatOps = _sample op o x
  | otherwise=Just o
sample op x o@(Op Neg [Infinit])
  | elem op equatOps = _sample op x o
  | otherwise=Just o
sample op o@(Op Neg [Infinit]) x
  | elem op equatOps = _sample op o x
  | otherwise=Just o
sample op (Quant (v,ua)) ub@(Unit _)
  =(\(Unit x)->Quant (v,x))<$>(base=<<Dim<$>(deriveDim=<<solvedAsLits<$>(compo (Op op [Unit ua,ub]))))
sample op ua@(Unit _) (Quant (v,ub))
  =(\(Unit x)->Quant (v,x))<$>(base=<<Dim<$>(deriveDim=<<solvedAsLits<$>(compo (Op op [ua,Unit ub]))))
sample op ua@(Unit a) ub@(Unit b)
  | op==Equals = Just $ Bool (a==b)
  | prior op < Geometric || (dim ua == dim ub && op == Div) = Nothing
  | otherwise=base=<<Dim<$>(deriveDim=<<(solvedAsLits<$>compo (Op op [ua,ub]))) -- this will call solved->calc->sample and make a cycle! unless units module call operations over literals instead of units
sample op qa@(Quant (a, as@(Scale am _ _ fa _ ba))) qb@(Quant (b, bs@(Scale bm _ _ fb _ _)))
  | dInfo(D_UNITS,show op++" "++show qa++" "++show qb++" sampling units...")=undefined
  | s==1 && op == Div = Just$Op op [a,b]
  | am==bm && op==Div=(D_UNITS,"same dimension => unitless")←(Just$Op op [toBase qa,toBase qb])
  | am==bm = (D_UNITS,"same dimension result:")←(fitScale<$> (\o->Quant (o, ba))<$>sub)
  | prior op == Geometric && ok u = (D_UNITS,"composed result:")←(fitScale <$> (\o->(Quant (o, fromJust u )))<$>sub)
  | otherwise=Nothing
  where
    sub=(D_UNITS,"values to base:")←sample op (toBase qa) (toBase qb)
    s=(D_UNITS,"solved composed unit to:")←(solved (Op op [Unit as,Unit bs]))
    u=(D_UNITS,"derived unit:")←(deriveUnit =<< base =<< (Dim <$> deriveDim s))

sample op a@(Quant (aa, s@(Scale m _ _ _ _ _))) x  = fitScale<$>(\o->Quant (o, s))<$>sample op aa x
sample op x a@(Quant (aa, s@(Scale m _ _ _ _ _))) = fitScale<$>(\o->Quant (o, s))<$>sample op x aa
{-sample op (Neighbor ra a) (Neighbor rb b) =Neighbor <$> conjugate ra rb <*> sample op a b
sample op (Neighbor ra a) b =Neighbor <$> conjugate ra Equals <*> sample op a b
sample op a (Neighbor rb b) =Neighbor <$> conjugate Equals rb <*> sample op a b-}
sample op a b=_sample op a b

_sample::Ops->Algo->Algo->Maybe Algo
_sample _    Und _ = Just Und
_sample _ _  Und = Just Und
_sample And  a@(Bool b) x | b= Just x  | otherwise= Just a
_sample And  x a@(Bool b) | b=   Just x  | otherwise= Just a
_sample Or   a@(Bool b) x  | b = Just a | otherwise= Just x
_sample Or   x a@(Bool b)  | b = Just a | otherwise= Just x
_sample Sum  (Nom 0) o= Just o
_sample Sum  o (Nom 0) = Just o
_sample Sum  (Nom a) (Nom b) = Just (Nom (a+b))
_sample Sub  (Nom a) (Nom b) = Just (Nom (a-b))
_sample Sub  (Lit a) (Lit b) | a==b = Just (Nom 0) | otherwise=Nothing
_sample Mul  (Nom 0) _ = Just (Nom 0)
_sample Mul  _ (Nom 0) = Just (Nom 0)
_sample Mul  (Nom 1) o = Just o
_sample Mul  o (Nom 1) = Just o
_sample Mul  (Nom a) (Nom b) = Just (Nom (a*b))
_sample Mul (Unit _) (Unit _)=Nothing
_sample Mul a (Unit u)=Just $Quant (a,u)
_sample Div  _ (Nom 0) = Just Und
_sample Div  a (Nom 1) = Just a
_sample Div  a@(Op Div m) b = Just $Op Div (m++[b])
_sample Div  (Nom a) (Nom b)
  | a<0 && b<0 = Just $Op Div [Nom (-a),Nom (-b)]
  | a<0 = Just $Op Neg [Op Div [Nom (-a),Nom b]]
  | b<0 = Just $Op Neg [Op Div [Nom a,Nom (-b)]]
  | a==b=Just $Nom 1
  | a<0 = Nothing
  | a==0 = Just $ Nom 0
  | a==1 = Just $Nom (a/b)
  | isInt ab = Just$Nom $ (a/fab) / (b/fab)
  | isInt ba = Just$Nom $ (a/fba) / (b/fba)
  | otherwise = Just $Nom (a/b)
  where
    ab=a/b
    ba=b/a
    fba=b/ba
    fab=a/ab
_sample Exp  (Nom 0) _ = Just $Nom 0
_sample Exp  _ (Nom 0) = Just $Nom 1
_sample Exp  (Nom a) (Nom b)
  | a<0 =if isInt b then Just $Nom sr else Nothing
  | otherwise= Just $Nom (a**b)
  where
    r=(-a)**b
    sr=if isInt (b/2) then r else -r
_sample Exp  a (Nom 1) = Just a
_sample Log  (Nom a) (Nom b) = Just $Nom $ log a / log b
_sample Log  _ (Nom 1) = Just $Nom 0
_sample Root (Nom 0) (Nom b)=Just$Nom 0
_sample Root (Nom a) (Nom b)
  | a<0 && p = Nothing
  | a<0 = Just$Nom$(-(-a)**(1/b))
  | otherwise = Just$Nom$a**(1/b)
  where p=isInt (b/2)
_sample Equals (Bool a) (Bool b)=Just (Bool (a==b))
_sample Equals (Nom a) (Nom b)=Just (Bool (a==b))
_sample Equals (Nom _) (Op _ [Infinit])=Just (Bool False)
_sample Equals (Op Pos [Infinit]) (Nom _)=Just (Bool False)
--_sample Equals (Unit a) (Unit b)=Just (Bool (a==b))
_sample Equals a b
  | a==b = Just$Bool True
  | otherwise=Nothing
_sample Greater _ (Op Pos [Infinit])=Just $ Bool False
_sample Greater _ (Op Neg [Infinit])=Just $ Bool True
_sample Greater (Op Pos [Infinit]) _=Just $ Bool True
_sample Greater (Op Neg [Infinit]) _=Just $ Bool False
_sample Greater (Nom a) (Nom b)=Just $ Bool (a>b)
_sample Greater a b=if a==b then Just$Bool False else Nothing
_sample Less _ (Op Pos [Infinit])=Just $ Bool True
_sample Less _ (Op Neg [Infinit])=Just $ Bool False
_sample Less (Op Pos [Infinit]) _=Just $ Bool False
_sample Less (Op Neg [Infinit]) _=Just $ Bool True
_sample Less (Nom a) (Nom b)=Just $ Bool (a<b)
_sample Less a b=if a==b then Just$Bool False else Nothing
_sample GreaterOrEqual a b
  = (\(Bool a) (Bool b)->Bool (a||b))<$>sample Greater a b<*>sample Equals a b
_sample LessOrEqual a b
  = (\(Bool a) (Bool b)->Bool (a||b))<$>sample Less a b<*>sample Equals a b
_sample NotEqual (Bool a) (Bool b)=Just (Bool (a/=b))
_sample NotEqual (Nom a) (Nom b)=Just (Bool (a/=b))
_sample NotEqual a b=if a==b then Just$Bool False else Nothing
_sample Union a b = rangeUnion a b
_sample Intersect a b = rangeInters a b
_sample Index (Nom (NrRatio a)) (Op Set o)
  | o#>=fa=Just $ o!!(fa-1)
  | otherwise=Nothing
  where fa=floor a
_sample System a b=sample And a b
_sample Document a b=sample System a b
_sample Set _ _=Nothing
_sample op (Op Set ma) b=Just$Op Set $ map (\e->(Op op [e,b])) ma
_sample op a (Op Set mb)=Just$Op Set $ map (\e->(Op op [a,e])) mb
_sample op a@(Op opa m) b -----«[ generic sampling ]» ----------------------------
  | not $canComut op || elem opa rawSequenceOps= Nothing
  | algTrace (D_SAMPLE,"sample1 "++show op++show m) False=undefined
  | dist op opa =(D_SAMPLE,show op++" sampling1 "++show a++","++show b++" to ")←(Just $Op opa es)
  | otherwise=Nothing
  where es=map (\e->(Op op [e,b])) m
_sample op a b@(Op opb m)
  | not $canComut op || elem opb rawSequenceOps= Nothing
  | dist op opb =(D_SAMPLE,show op++" sampling2 "++show a++","++show b++" to ")←(Just $Op opb es)
  | otherwise = Nothing
  where es=map (\e->(Op op [a,e])) m
_sample op a b
  | not $canComut op = Nothing
  | not $ok n=Nothing
  | a==nv=(D_SAMPLE,show op++" sampling3 "++show a++","++show b++" to ")←(Just b)
  | b==nv=(D_SAMPLE,show op++" sampling4 "++show a++","++show b++" to ")←(Just a)
  | otherwise=Nothing
  where
    n=neutral op
    (Just nv)=n
