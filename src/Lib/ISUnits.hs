{-# LANGUAGE OverloadedStrings #-}

module Lib.ISUnits where

import AlgData
import Lib.Noms
import AlgNum
import AlgShow
import {-# SOURCE #-} AlgParser
import {-# SOURCE #-} Solver
import {-# SOURCE #-} Evid
import Utils
import AlgAux
import Lib.Debug

import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Data.Number.CReal
import Data.List.Ordered
import Text.Regex
import Control.Applicative
import Control.Monad

--metric system
ism::MetricSystem
ism=MetricSystem "International System of measures" [
  electricPotential,
  electricCurrent,
  electricResistance,
  electricPower,
  timeScale,
  frequencyScale,
  lengthScale,
  temperatureScale
  ]

-- base scale units
dimensionless=Scale unitless "" "" "1" Und dimensionless
volts=Scale electricPotential "V" "Volts" "1" Und volts
amps=Scale electricCurrent "A" "Ampers" "1" Und amps
ohms=Scale electricResistance "Ω" "Ohms" "1" Und ohms
watts=Scale electricPower "W"  "Whatt" "1" Und watts
seconds=Scale timeScale "s" "Seconds" "1" Und seconds
hertz=Scale frequencyScale "Hz" "Hertz" "1" Und hertz
meters=Scale lengthScale "m" "Meter" "1" Und meters
kelvins=Scale temperatureScale "K" "Kelvin" "1" Und kelvins
celsius=Scale temperatureScale "ºC" "Celsius" "?+273.15" Und kelvins


-- scales
unitless=Dimension ism "dimenssionless" "" "" "1" [dimensionless] dimensionless
temperatureScale=Dimension ism "Temperature" "T" "T" "T" [
  kelvins,celsius
  ] celsius
lengthScale=Dimension ism "Length" "l" "l" "l" [
  meters,
  Scale lengthScale "km" "Kilometers" "1e3" Und meters,
  Scale lengthScale "cm" "Centimeters" "1e-2" Und meters,
  Scale lengthScale "mm" "Milimeters" "1e-3" Und meters,
  Scale lengthScale "μm" "Microns" "1e-6" Und meters,
  Scale lengthScale "nm" "Nanometers" "1e-9" Und meters
  ] meters
frequencyScale=Dimension ism "Frequency" "fr" "fr" "fr" [
  hertz,
  Scale frequencyScale "KHz" "Kilohertz" "1e3" Und hertz,
  Scale frequencyScale "MHz" "Megahertz" "1e6" Und hertz,
  Scale frequencyScale "GHz" "Gigahertz" "1e9" Und hertz
  ] hertz
timeScale=Dimension ism "Time" "t" "t" "t" [
  seconds,
  Scale timeScale "min" "Minuts" "60" Und seconds,
  Scale timeScale "h" "Hours" "3600" Und seconds,
  Scale timeScale "ms" "Miliseconds" "1e-3" Und seconds,
  Scale timeScale "μs" "Microseconds" "1e-6" Und seconds,
  Scale timeScale "ns" "Nanoseconds" "1e-9" Und seconds
  ] seconds
electricPotential=Dimension ism "Electric potential" "E" "E" "E" [
  volts,
  Scale electricPotential "mV" "Milivolts" "1e-3" Und volts,
  Scale electricPotential "KV" "Kilovolts" "1e3" Und volts
  ] volts
electricCurrent=Dimension ism "Electric current" "I" "I" "I" [
  amps,
  Scale electricCurrent "mA" "Miliamps" "1e-3" Und amps
  ] amps
electricResistance=Dimension ism "Electric resistence" "R" "R" "E/I" [
  ohms,
  Scale electricResistance "KΩ" "Kilo Ohms" "1e3" Und amps,
  Scale electricResistance "MΩ" "Mega Ohms" "1e6" Und amps
  ] ohms
electricPower=Dimension ism "Electric power" "P" "P" "E*I" [watts,
  Scale electricPower "mW" "Miliwatts" "1e-3" Und watts,
  Scale electricPower "KW" "Kilowatts" "1e3" Und watts,
  Scale electricPower "GW" "Kilowatts" "1e6" Und watts
  ] watts

-- scales map for faster search
is_scales=concatMap dimScales $ metricSystemDims ism
is_scale_matchers=map (\v->(splitRegex (mkRegex (scaleSymbol v++"$")),v))$sortBy (\a b->compare (length$scaleSymbol b) (length$scaleSymbol a)) is_scales
is_scale_symbols=Map.fromList$map (\v->(scaleSymbol v,v)) is_scales
is_dim_keys=Map.fromList $map (\o->(dimKey o,Dim o)) $metricSystemDims ism
---------------------------------------------------------
-- search the database for a composed dimension that fits the expression
-- deriveDim "V/A" -> R
deriveDim::Algo->Maybe Dimension
deriveDim (Dim o)=Just o
deriveDim (Unit o)=Just $scaleDim o
deriveDim (Quant (_,u))=Just$scaleDim u
deriveDim e@(Op op o)
  | dInfo(D_UNITS,"deriveDim of "++show e)=undefined
  | null$fst b=Nothing
  | prior op < Geometric = Nothing
  | otherwise =
    (dim e>>(listToMaybe $filter (\o->dimDerived o==(fromJust$dim e)) $metricSystemDims ism)) <|>
    ((base e)>>(dim e)>>(Just nd))
  where
    (Just base')=(D_UNITS,"base:")←(base e)
    (Just dim')=(D_UNITS,"dim:")←(dim e)
    w=(D_UNITS,"xcalc weights:")←(exaustCalcAsLits(Op op $map (\o->Op Set o) $(map . map) fst $filter (not . null) $map weights o))
    s=if prior op ==Geometric
      then (D_UNITS,"geometric xcalc units:")←(map solvedAsLits $ membersOf (exaustCalcAsLits $ Op op $map (\o->Op Set (map Unit o)) $filter (not . null) $map scales o))
      else (D_UNITS,"exponetial xcalc units:")←(map solvedAsLits $ membersOf (exaustCalcAsLits $ Op op $(map (\o->Op Set (map Unit o)) $filter (not . null) $map scales o)++[o!!1]))
    wsc=(D_UNITS,"wsc:")←(zip (membersOf w) s)
    b=(D_UNITS,"wsc partition:")←(partition (\o->snd o==base') wsc)
    nd=(D_UNITS,"new dim:")←Dimension ism (clrColors$show base') (clrColors$show base') base' dim' ds bu
    bu=(D_UNITS,"mkScale:")←(mkScale (head$fst b) bu)
    ds=(D_UNITS,"other dim scales:")←(map snd $
      Data.List.Ordered.nubBy (\(a,_)(b,_)->a/=b) $
      map (\o->(scaleWeight o,o)) $
      sortBy (\a b->if (scaleWeight a)==(scaleWeight b) then compare (plex$Unit a) (plex$Unit b) else compare (scaleWeight a) (scaleWeight b)) $
      (bu:map (\o->mkScale o bu) (snd b)))
    mkScale (w,o) b=Scale nd (clrColors$show o) (clrColors$show o) w o b
deriveDim _ = Nothing

-- search the database for a composed unit that fits the expression
-- ex: V/A -> Ω
deriveUnit::Algo->Maybe Scale
deriveUnit o=units o>>(listToMaybe=<< (filterM (\i->(scaleWeight i==)<$>(weight o)) =<< (dimScales <$> deriveDim o)))

convForm x k
  | Utils.has (==Pref) k = repVars (Map.fromList[(Pref,x)]) k
  | otherwise = x/k

-- select proper scales to represent given values
-- 10000V -> 10KV
fitScale :: Algo -> Algo
fitScale (Quant (Bool v, _))=Bool v -- boolean values have no scale, but they can result from scales relation
fitScale (Quant (v, u@(Scale _ _ _ f _ _)))
  =(Quant (solvedAsLits (if Utils.has (==Pref) (fst fit) then repVars (Map.fromList[(Pref,v)]) (fst fit) else val/(fst fit)),snd fit))
  where
    val=solvedAsLits $ if Utils.has (==Pref) f then repVars (Map.fromList[(Pref,v)]) f else v*f
    fit=chooseScale val (weights (Unit u))
fitScale o=o

chooseScale :: Algo -> [(Algo, t)] -> (Algo, t)
chooseScale x [] = undefined -- dont come here
chooseScale _ [s] = s
chooseScale x s = _i s $filter (\(_,b)->b>=1)$map (\(k,v)->((k,v),solvedAsLits (convForm x k))) s
  where
_i s []=head $ sortBy (\(a,_) (b,_)->compare a b) s
_i s si=fst $ foldl1 (\a@(_,aa) b@(_,bb)->if aa<bb then a else b)$si

-- list of dimensions present at expression
dims::Algo->[Dimension]
dims (Dim d)=[d]
dims (Unit d)=[scaleDim d]
dims (Quant (_,u))=[scaleDim u]
dims (Op _ m)=concatMap dims m
dims _=[]

-- replace Units with respective diensions
dim :: Algo -> Maybe Algo
dim (Op Exp [a,b@(Nom _)])=solvedAsLits<$>(\x->Op Exp [x,b])<$>dim a
dim (Op Exp [a,_])=Nothing
dim (Op op m)
  | null d=Nothing
  | otherwise=Just $solvedAsLits$chkQuant $Op op d
  where d=map fromJust $filter ok $map dim m
dim x
  | null d=Nothing
  | otherwise = Just $Dim $head d
  where d=dims x

-- rewrite expression using base units
base :: Algo -> Maybe Algo
base (Op Exp [a,b@(Nom _)])=solvedAsLits<$>(\x->Op Exp [x,b])<$>base a
base (Op Exp [a,_])=Nothing
base (Op op m)
  | null d=Nothing
  | otherwise=Just $solvedAsLits$chkQuant $Op op d
  where d=map fromJust $filter ok $map base m
base (Dim d)
  | null scs=Nothing
  | otherwise=base $Unit $head scs
  where scs=dimScales d
base (Unit o)=Just $Unit $scaleBase o
base (Quant (_,o))=Just $Unit (scaleBase o)
base _ = Nothing

-- rewrite expression using only the units
units::Algo->Maybe Algo
units u@(Unit _)=Just u
units (Quant (_,u))=Just$Unit u
units (Op op m) = Just $ chkQuant $ Op op $map fromJust $ filter ok $map units m
units _ = Nothing

compo::Algo->Maybe Algo
compo u@(Unit o)
  | (dimDerived . scaleDim) o == Und = Just u
  | otherwise=(base . dimDerived . scaleDim) o
compo (Quant (_,o))
  | (dimDerived . scaleDim) o==Und = Just $Unit o
  | otherwise=(base . dimDerived . scaleDim) o
compo (Op op m)
  | null o=Nothing
  | otherwise=Just$chkQuant $Op op o
  where o=map fromJust $  filter isJust $map compo m

-- get convertion factor or formula to base unit
weight::Algo->Maybe Algo
weight (Unit s)=Just$ scaleWeight s
weight (Quant (_,u))=Just$ scaleWeight u
weight (Op op m) = Just $ solvedAsLits $ chkQuant $ Op op $ map (fromJust . weight . fromJust) $ filter ok $map units m
weight _ = Nothing

-- get all possible scales for expression
scales::Algo->[Scale]
scales (Dim d)=dimScales d
scales (Unit u)=dimScales$scaleDim u
scales (Quant (_,u))=dimScales$scaleDim u
scales o@(Op _ _)=map snd $ weights o
scales _=[] --[dimensionless]

-- get all possible scale weights for expression
weights::Algo->[(Algo,Scale)]
weights o@(Dim d)=map (\o->(scaleWeight o,o)) (scales o)
weights u@(Unit _)=map (\o->(scaleWeight o,o)) (scales u)
weights (Quant (_,u))=weights (Unit u)
weights (Op Resol m)=weights$last m
weights (Op Simpl m)=weights$last m
weights o@(Op op m)
  | isJust newDim = (map (\o->(scaleWeight o,o)) (scales $Dim $fromJust newDim))
  | otherwise=[]
  where newDim=deriveDim o
-- weights _ =[]
weights o=[(o,dimensionless)]

-- base conversion formula
toBaseExpr u=
  if Utils.has (==Pref) (scaleWeight u)
  then scaleWeight u
  else (Op Mul [Pref,scaleWeight u])

{-fromBaseExpr u= case evided Pref (toBaseExpr u) Pref of
  (Just e)->e
  otherwise->Und-}

--convert to base unit
toBase::Algo->Algo
toBase (Quant (q,u)) = solvedAsLits $repVars (Map.fromList [(Pref,q)]) (toBaseExpr u)
--fromBase (Quant (q,u)) = solvedAsLits $repVars (Map.fromList [(Pref,q)]) (fromBaseExpr u)

asLits::Algo->Algo
asLits (Unit o)=Lit $scaleSymbol o
asLits (Op op m)=Op op $map asLits m
asLits o=o

asUnits::Algo->Algo
asUnits e@(Lit o)
  | null ou=e
  | otherwise=Unit $head ou
  where ou=map fromJust $filter isJust $map (\(f,u)->if f o#=2 then Just u else Nothing) is_scale_matchers
asUnits (Op op m)=Op op $map asUnits m
asUnits o=o

solvedAsLits= asUnits . solved . asLits
exaustCalcAsLits= asUnits . exaustCalc . asLits
