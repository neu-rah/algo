module PLD where

{-
Polinominal
Long
Divisio

not implemented yet!
this is only a scratch
-}

import Data.List
import Data.List.Ordered
import Data.Functor
import Control.Applicative

import AlgData
import AlgAux
import Utils
import Solver
import Lib.Debug
import Lib.Colors
import AlgNum

-- get dominant (member,degree)
dominant e@(Op op o)
  = maximumBy (\a b->compare (snd a) (snd b)) $zip lits (map (`degree` e) lits)
  where lits=literals e
dominant e@(Lit _)=(e,Nom 1)
dominant o=(o,Nom 0)

-- degree of dominant member
degree' o
  | null lits=Nom 0
  | otherwise=maximum $map (`degree` o) lits
  where lits=literals o

--canonize
canon (Op Mul o)=Op Mul (sortOn degree' (map canon o))
canon (Op op o)=
  if canComut op
  then Op op (reverse$sortOn degree' (map canon o))
  else Op op (map canon o)
canon o=o

pld a b
  | a == b = Just $ Nom 1
  | otherwise = pld' ca cb
  where
    ca=canon a
    cb=canon b

pld' e@(Op opa (a:b:[])) f@(Op opb (c:d:[]))
  | opa/=opb=Nothing
  | a==c = Just (Op Div [d,b])
  | b==d = Just (Op Div [a,c])
  | opa == Div = solved <$> (Just $ Op Mul [e,(Op Div [d,c])])
  | b==c = Just (Op Div [a,d])
  | a==d = Just (Op Div [b,c])
  | otherwise=Nothing
pld' o (Op Mul (a:b:[]))
  | o == a = Just b
  | o == b = Just a
  | otherwise=Nothing

pld' (Op Mul (a:b:[])) o
  | o == a = Just b
  | o == b = Just a
  | otherwise=Nothing

pld' (Op opa (a:aa)) (Op opb (b:bb))=undefined

{-pld' a b
  | fst da /= fst db = (D_PLD,show da++","++show db++" dominants mismatch ")←Nothing
  | otherwise = solve$Op Mul [Op Sub [snd da , snd db],fst da]
  where
    da=dominant a
    db=dominant b-}

pld' a b
  | a == b = Just $ Nom 1
  | otherwise=Nothing

_pld (Op opa []) _ q r = (q,r)
_pld n@(Op opa (a:ma)) d@(Op opb (b:mb)) q r
  | dInfo(D_ANY,show a++" / "++show b)=undefined
  | otherwise= (Op opa ((solved (a/b)):membersOf q'),r')
  where (q',r')=_pld (Op opa ma) (Op opb mb) q r

-- EOF --
