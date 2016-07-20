module Intervals where

import Data.Maybe
import Control.Applicative
import qualified Data.Map as Map

import AlgData
--import AlgShow
--import Calc
import {-# SOURCE #-} Solver
import AlgParser
import {-# SOURCE #-} AlgSets
import {-# SOURCE #-} Rules
import Lib.Debug
import Utils
import AlgAux

negInf=Op Neg [Infinit]
posInf=Op Pos [Infinit]

wingOrd::RangeWing->RangeWing->Maybe Ordering
wingOrd (RangeWing ai ae) (RangeWing bi be)
  | is Equals ae be = Just$if ai==bi then EQ else (if ai then GT else LT)
  | is Less ae be = Just$LT
  | is Greater ae be = Just$GT
  | otherwise=Nothing

wingMinMax::Ordering->RangeWing->RangeWing->Maybe RangeWing
wingMinMax r a b
  | o == Nothing = Nothing
  | o == (Just r) = Just b
  | otherwise=Just a
  where o=wingOrd a b

wingMax::RangeWing->RangeWing->Maybe RangeWing
wingMax=wingMinMax LT
wingMin::RangeWing->RangeWing->Maybe RangeWing
wingMin=wingMinMax GT

is op a b = (varSolved $ (Op Equation [a,Op op [b]]))==Bool True

rangeUnion a@(Sets (Range al@(RangeWing ali alv) ah@(RangeWing ahi ahv))) b@(Sets (Range bl@(RangeWing bli blv) bh@(RangeWing bhi bhv)))
  | alv==blv&&ahv==bhv=Just $ Sets (Range (RangeWing (ali||bli) alv) (RangeWing (ahi||bhi) ahv) )
  | wingOrd al bl == (Just GT) =rangeUnion b a -- lets order them to simplify thing here
  | ahv == blv && not (ahi||bli) = Nothing
  | ahv/=blv&& wingOrd ah bl == (Just LT) = Nothing
  | isJust low && isJust high  = -- they should intersect here or be adjacent
    if wingExpr jl == wingExpr jh && (wingIncl jl /= wingIncl jh)
    then Just $Op Set [wingExpr jl]
    else Just $Sets (Range jl jh)
  | otherwise=Nothing
  where
    low=wingMin al bl
    high=wingMax ah bh
    (Just jl)=low
    (Just jh)=high
rangeUnion a@(Neighbor _ _) b = (`rangeUnion` b)=<<(toRange a)
rangeUnion a b@(Neighbor _ _) =  (rangeUnion a)=<<(toRange b)
rangeUnion _ _=Nothing

rangeInters a@(Sets (Range al@(RangeWing ali alv) ah@(RangeWing ahi ahv))) b@(Sets (Range bl@(RangeWing bli blv) bh@(RangeWing bhi bhv)))
  | dInfo (D_RANGES, "rangeInters "++show a++" ∩ "++show b)=undefined
  | alv==blv&&ahv==bhv = Just $ Sets (Range (RangeWing (ali&&bli) alv) (RangeWing (ahi&&bhi) ahv) )
  | isJust low && isJust high && wingOrd jl jh /= (Just GT) =
    if wingExpr jl == wingExpr jh
    then (Just $Op Set (if wingIncl jl && wingIncl jh then [wingExpr jl] else []))
    else Just $Sets (Range jl jh)
  | and (map isNom [alv,ahv,blv,bhv])= Just $Op Set [] -- all nominals => non intersecting
  | otherwise=Nothing -- cant say yet
  where
    low=wingMax al bl
    high=wingMin ah bh
    (Just jl)=low
    (Just jh)=high
rangeInters a@(Neighbor _ _) b = (`rangeInters` b)=<<toRange a
rangeInters a b@(Neighbor _ _) = rangeInters a=<<toRange b
rangeInters _ _=Nothing

toRange :: Algo -> Maybe Algo
toRange (Neighbor Equals v) = Just $ Sets $ Range (RangeWing True v) (RangeWing True v)
toRange (Neighbor Less v) = Just $ Sets $ Range (RangeWing False $ Op Neg [Infinit]) (RangeWing False v)
toRange (Neighbor LessOrEqual v) = Just $ Sets $ Range (RangeWing False $ Op Neg [Infinit]) (RangeWing True v)
toRange (Neighbor Greater v) = Just $ Sets $ Range (RangeWing False v) (RangeWing False $Op Pos [Infinit])
toRange (Neighbor GreaterOrEqual v) = Just $ Sets $ Range (RangeWing True v) (RangeWing False $Op Pos [Infinit])
toRange (Op Simpl _)=Nothing
toRange (Op Resol m)=toRange(last m)
--toRange o@(Op Equation [_,Op Equals _])=(D_RANGES,show o++" toRange Equation ")←Nothing
toRange r@(Sets (Range _ _))=(Just r)~>simplify
toRange o@(Op Equation (i:r@(Op _ _):_))=(D_RANGES,show o++" toRange inequation ")←(((\o->Op Equation [i,Op ElementOf [o]]) <$> _toRange r)~>simplify)
--toRange o@(Op Equation (_:r@(Op _ _):_))=(D_RANGES,show o++" toRange complex equiation ")←Nothing
{-toRange (Op Simpl [l,Op rl [v],Op rh [h]])
  | (rl==Greater || rl==GreaterOrEqual) && (rh==Greater||rh==GreaterOrEqual) =Just$Sets (Range (RangeWing (rh/=Greater) h) (RangeWing (rl/=Greater) l))
  | (rl==Less || rl==LessOrEqual) && (rh==Less||rh==LessOrEqual) =Just$Sets (Range (RangeWing (rl/=Less) l) (RangeWing (rh/=Less) h))
  | otherwise=Nothing-}
toRange o@(Op op m) = (algProc toRange o)~>simplify
{-  | null m'=Nothing
  | otherwise=(D_RANGES,show o++" toRange operator ")←(Just$chkQuant$Op op m')
  where m'=map fromJust $filter ok $map toRange m-}
toRange o=Nothing --Just o
_toRange :: Algo -> Maybe Algo
--_toRange (Op ElementOf [r@(Sets (Range _ _))])=Nothing --Just r
_toRange (Op Equals (v:[]))=Just $ Sets (Range (RangeWing True v) (RangeWing True v))
_toRange (Op Less (v:[]))=Just $ Sets (Range (RangeWing False (Op Neg [Infinit])) (RangeWing False v))
_toRange (Op LessOrEqual (v:[]))=Just $ Sets (Range (RangeWing False (Op Neg [Infinit])) (RangeWing True v))
_toRange (Op Greater (v:[]))=Just $ Sets (Range (RangeWing False v) (RangeWing False (Op Pos [Infinit])))
_toRange (Op GreaterOrEqual (v:[]))=Just $ Sets (Range (RangeWing True v) (RangeWing False (Op Pos [Infinit])))
_toRange (Op NotEqual (v:[]))
  =a>>b>>(Just $ Op Union [fromJust a,fromJust b])
  where
    a=_toRange (Op Less [v])
    b=_toRange (Op Greater [v])
_toRange _=Nothing

fromRange :: Algo -> Maybe Algo
--fromRange (Solver defs vars expr)=(Solver defs vars) <$> fromRange expr
fromRange (Op Resol m@(_:_))=fromRange (last m)
fromRange (Op Equation [l,Op ElementOf [Op Set [r]]])=Just $Op Equation [l,Op Equals [r]]
fromRange (Op Equation [l,Op ElementOf [Sets (Range lw rw)]])
  | wingExpr lw == wingExpr rw && (wingIncl lw || wingIncl rw) = Just $ Op Equation [l,Op Equals [wingExpr lw]]
  | otherwise = Nothing
fromRange (Op Equation [e,Op ElementOf [o]]) = repVars (Map.fromList[(Pref,e)]) <$> fromRange o
fromRange (Op Equation [e,Op _ [o]]) = Nothing
fromRange o@(Op op m)=algProc fromRange o
  -- | null m'=Nothing
  -- | otherwise=Just$chkQuant$Op op m'
  -- where m'=map fromJust $filter ok $map fromRange m
fromRange  (Sets (Range l@(RangeWing li lv) h@(RangeWing hi hv)))
  | lv==negInf && hv==posInf = Just $ Op Equation [Pref,Op ElementOf [_R]]
  | lv == hv = Just $ Op Equation [Pref,Op (if li||hi then Equals else NotEqual) [lv]]
  | lv==negInf = Just $ Op Equation [Pref,Op (if hi then LessOrEqual else Less) [hv]]
  | hv==posInf = Just $ Op Equation [Pref,Op (if li then GreaterOrEqual else Greater) [lv]]
  | otherwise
    =Just $ Op Simpl [lv,Op (if li then LessOrEqual else Less) [Pref],Op (if hi then LessOrEqual else Less) [hv]]
fromRange _=Nothing
