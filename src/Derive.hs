module Derive where

import AlgData
import AlgParser
import Utils
import AlgAux
import Lib.Debug

import Data.Maybe
import Data.Fixed
import Data.Ratio

derive::Algo->Algo->Maybe Algo
derive x (Op Func m@(_:p))
  |elem x p =Just $ Op DerivedFunc m
  |otherwise=Nothing
derive x (Op Neg [e])=(Just$Op Neg []) <+ derive x e
derive x (Op Sum m)
  | null (filter isJust p) = Nothing
  | otherwise=Just $ Op Sum $ algRebuild p m
  where p=map (derive x) m
derive x (Op Mul m)
  | null f = Nothing
  | f#>1=Just $ Op Sum $ map (Op Mul) $dmat p m
  | otherwise= Just $ Op Mul $ (D_ANY,"Mul:")←(map (\(a,b)->(a==0)?(b,a)) $ zip (algRebuild p m) m)
  where
    p=(D_ANY,"Mul derive p:")←(map (derive x) m)
    f=filter isJust p

derive x (Op Exp [b,e])
  | b==x = Just $ Op Mul [e,Op Exp [b,e-1]]
  | otherwise=Nothing
derive x e
  | e==x = Just 1
  | otherwise=Just 0

dmat::[Maybe n]->[n]->[[n]]
dmat a b =_dmat a [] b
  where
    _dmat [] _  _=[]
    _dmat _ _ []=[]
    _dmat (e:ee) o' (o:oo)=(if isJust e then [o'++[fromJust e]++oo] else [])++(_dmat ee (o'++[o]) oo)
