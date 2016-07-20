module Calc where

import AlgData
import AlgAux
import Utils
import Sample
import Lib.Debug
import Lib.Noms
import {-# SOURCE #-} Solver
import {-# SOURCE #-} AlgSets

import Data.Maybe
import Data.List
import Control.Applicative
import Data.Ratio
import Data.Number.CReal

calc::Algo->Maybe Algo
calc o=_calc $ conclusion o

_calc::Algo->Maybe Algo
_calc (Op Pos [Infinit])=Nothing
_calc (Op Pos [o])=Just o
_calc (Op SuchThat [_,Bool False])=Nothing
_calc (Op Equation (_:[(Op _ (_:[Bool False]))]))=Nothing -- conditions evaluated to False, no further development
_calc (Sets(Range (RangeWing ai a) (RangeWing bi b)))
  =  (\x->Sets(Range (RangeWing ai x) (RangeWing bi b)))<$>calc a
  <|>(\x->Sets(Range (RangeWing ai a) (RangeWing bi x)))<$>calc b
_calc (Op Intersect [Op Mul[Nom (NrRatio n), Sets (AlgSet "N" _ _ _) ], Sets (AlgSet "N" _ _ _) ])
  = Just $ Op Mul [Nom (NrRatio $ fromIntegral (numerator n)),_N]
_calc (Op Intersect (o@(Op Set _):[]))=Just o -- empty intersection for resursiveness
_calc (Op Intersect (o@(Op Set mo):oo))
  = Just $ Op Set [x | x<-mo,solved (Op Equation [x,Op ElementOf [r]])==(Bool True)]
  where r=solved $chkQuant $ Op Intersect oo
_calc (Op Union m@(Op Set _:Op Set _:[])) = (D_CALC,show m++" -> ") ← (Just $ Op Set $ nub$concat$map membersOf m)
_calc (Op Union (Op Set m:Op Set n:oo)) =  (D_CALC,show m++" -> ") ← (Just $ Op Union (Op Set (nub$m++n):oo))
_calc o@(Op Equation [x,Op NotElementOf m])
  | not (ok jt)=Nothing
  | t==(Bool True)=Just (Bool False)
  | t==(Bool False)=Just (Bool True)
  | otherwise=Nothing--error ("check this result"++show t)
  where
    jt=_solved emptyCtx (Op Equation [x,Op ElementOf m])
    (Just t)=jt
_calc (Op Equation [Op Params o,Op ElementOf oo])
  = Just $ Op And (map (\i->Op Equation [i,Op ElementOf oo]) o)
_calc (Op Equation [Op Set o,Op ElementOf oo])
  =(D_SETS,"1º ElementOf Set "++show o++" :"++show oo++"=")←(Just $ Op And (map (\e->Op Equation [e,Op ElementOf oo]) o))
-- a,b ∈ ...
_calc (Op Equation[Op List o,Op ElementOf oo])
  =(D_SETS,"2º ElementsOf List =")←(Just $ Op And (map (\e->Op Equation[e,Op ElementOf oo]) o))
-- x ∈ {}
_calc (Op Equation [_,Op ElementOf [Op Set []]]) = (Just $Bool False)
-- 2 ∈ {...}
_calc expr@(Op Equation [n@(Nom _),Op ElementOf [r@(Op Set m)]])
  | dInfo(D_SETS,"1º calc elementOf ["++show n++","++show r++"]")=undefined
  | e = Just $Bool True
  | (literals r)#=0 = Just $ Bool e
  | otherwise=Nothing
  where
    e=elem n m
-- x ∈ {..}
_calc e@(Op Equation [n,Op ElementOf [Op Set m]]) -- = Just $ Bool (elem n m)
  | dInfo(D_SETS,"2º calc "++show n++" elementOf "++show m++" ")=undefined
  | elem n m = (Just $ Bool True)
  | otherwise = Nothing
-- x ∈ [a;b]
_calc (Op Equation [n,Op ElementOf [(Sets (Range l@(RangeWing il lo) r@(RangeWing ir ro)))]])
  | dInfo(D_SETS,"3º calc elementOf ["++show n++","++show r++"]")=undefined
  | lo==ro && lo==n = Just $Bool (il || ir)
  | n==lo = Just $ Bool il
  | n==ro = Just $ Bool ir
  | otherwise = Just $ Op And [chkLeftWing n l,chkRightWing n r]
-- x ∈ { a/b : a,b ∈ ℕ }
_calc o@(Op Equation [n,Op ElementOf [Sets (AlgSet _ _ m _)]])
  = (D_SETS,show n++" elementOf AlgSet ")←( (rebuild calc o) <|> m n)
_calc e@(Op Equation [a,Op r [o]]) = sample r a o <|> rebuild calc e-- with no conditions
_calc (Op Neg ((Nom 0):[]))=Just$Nom 0
_calc (Op Neg ((Nom n):[]))=Just$Nom (-n)
_calc (Op Neg [Op Sum m])=Just$Op Sum$map (\o->Op Neg [o]) m
_calc (Op Sub (o:oo))=Just$Op Sum (o:map (\ð->Op Neg [ð]) oo)
_calc (Op Floor (Nom (NrReal n):[]))=Just$Nom (NrRatio (fromIntegral (floor n)))
_calc (Op Floor (Nom (NrRatio n):[]))=Just$Nom (NrRatio (fromIntegral (floor (((fromIntegral $ numerator n)/(fromIntegral $ denominator n))::CReal))))
_calc o@(Op Set m)
  | ok s=s
  | not (or (map (isOp Set) m))=Nothing
  | otherwise=Just$Op Set$concatMap (\o->if isOp Set o then membersOf o else [o]) m
  where s=rebuild calc o
_calc o@(Op op m)
  = (D_CALC,show o++" calc: ") ← (rebuild calc o <|> if canComut op then comutCalc op m else linearCalc op m)
_calc _=Nothing

-- aux _calc functions
linearCalc :: Ops -> [Algo] -> Maybe Algo
--linearCalc op (Ellipsis:oo)=Nothing --Just Ellipsis
linearCalc op (o:oo)
  | null r && elem op partialCalc && proc#>1=last proc
  | proc #> 1 =Just $ chkQuant $ Op op $ (fromJust$last proc) : r
  | otherwise=Nothing
  where
    proc=takeWhile ok (scanl ((sample op) . fromJust) (Just o) oo)
    r=(snd (splitAt (length proc) (o:oo)) )

comutCalc::Ops->[Algo]->Maybe Algo
comutCalc op m
  | not (canComut op) = Nothing
  | [ x | x<-proc,x #> 1] #>0 = Just $Op op $concat proc
  | otherwise = comutCalc' op m
  where
    proc=map (\o->if getOp o==(Just op) then membersOf o else [o]) m

comutCalc'::Ops->[Algo]->Maybe Algo
--comutCalc' op m@(Ellipsis:oo)=Just Ellipsis
comutCalc' op m@(o:oo)
  | oks=(D_CALC,"comut _calc1 ")←(Just$chkQuant$Op op (sampled++rem))
  | ok rec=(D_CALC,"comut _calc2 ")←(Just$Op op [o,fromJust rec])
  | otherwise=(D_CALC,"comut _calc3 ")←(if ok rec then Just$chkQuant$Op op (o:(membersOf $fromJust rec)) else Nothing)
  where
    rec=comutCalc op oo -- recursive
    tails=if ok rec then (membersOf $fromJust rec) else oo
    samples=map (sample op o) tails
    oks= or $ map ok samples -- Bool<-[Bool]
    sampled=map fromJust $filter ok samples
    rem=map snd $ filter (\(e,_)->not(ok e)) $zip samples tails
comutCalc' _ _=Nothing

chkLeftWing :: Algo -> RangeWing -> Algo
chkLeftWing o (RangeWing i l)
  | i = Op Equation [o,Op GreaterOrEqual [l]]
  | otherwise = Op Equation [o,Op Greater [l]]

chkRightWing :: Algo -> RangeWing -> Algo
chkRightWing o (RangeWing i l)
  | i = Op Equation [o,Op LessOrEqual [l]]
  | otherwise = Op Equation [o,Op Less [l]]
