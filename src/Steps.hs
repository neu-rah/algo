{-# LANGUAGE CPP #-}
module Steps where

import AlgData
import AlgShow
import Utils
import AlgAux
import Lib.Debug
import Data.Maybe
import Control.Applicative

#define DEBUG

step::Algo->Algo->Maybe Algo
#ifdef DEBUG
step e r = case r' of
  (Just (Op Resol (Op Resol _:_))) -> error $"nested resolution "++show e++" => "++show r
  _ -> r'
  where r'= _step e r
#endif
#ifndef DEBUG
step = _step
#endif

_step::Algo->Algo->Maybe Algo
_step (Op Document _) o@(Op Document _)=Just o-- document are inner stepping
_step a@(Op Equiv _) b@(Op Equiv _)=Just $Op Resol [a,b]
_step a@(Op Equiv _) b@(Op Implic _)=Just $Op Resol [a,b]
_step a@(Op Implic _) b@(Op Equiv _)=Just $Op Resol [a,b]
_step a@(Op Implic _) b@(Op Implic _)=Just $Op Resol [a,b]
_step a@(Op Resol ma) b@(Op Resol m@(Op rop _:_))
  | elem rop resolSteps = Just $(D_STEPS,show a++"Resol+Resol")←Op Resol ([a]++m)
  | otherwise=Just $(D_STEPS,show a++"Resol -> complete Resol")←b
_step a@(Op Resol _) b@(Op Resol _)=error "does this exist" --Just $(D_ANY,"And stepping to complete Resol with a simmple start")←b -- must be complete resolution
--_step a@(Op Resol ma) b@(Op Resol mb)=(D_ANY,show a++" stepping Resol+Resol:")←(Just b) --(Just$Op Resol (ma++mb))-- solve can produce a sequence of valid steps
_step a@(Op Simpl ma) b@(Op Simpl (_:mb))=Just$ Op Simpl (ma++mb)--error ("not efficient, stepping Simpl to Simpl\n"++show a++"\n"++show b)
_step a@(Op Resol ma) b@(Op op _)
  | elem op resolSteps = (D_STEPS,show a++"<->"++show b++" stepping Resol:")←((Just a)<+(Just b))
  | otherwise= (D_STEPS,"_step Resol+Op ")←(Just$Op Resol (ma++[Op Equiv [b]])) --(resStepOp a b)
_step a@(Op Resol ma) b = Just$Op Resol (ma++[Op Equiv [b]])
_step a@(Op Simpl _) b@(Op op _)
  | elem op equatOps = (D_STEPS,show a++" stepping Simpl:")←((Just a)<+(Just b))
  | otherwise= (D_STEPS,"_step Simpl+Op")←((Just a)<+(Just$Op Equals [b]))
_step a@(Op And _) b@(Op Resol m@(Op op _:_))
  | elem op resolSteps = Just $ (D_STEPS,"And stepping to Resol ") ←(Op Resol ([a]++m))
  | otherwise = Just $(D_STEPS,"And stepping to complete Resol ")←b -- its a complete resolution
_step a@(Op And _) b@(Op Resol _)=error "does this exist" --Just $(D_ANY,"And stepping to complete Resol with a simmple start")←b -- must be complete resolution
_step a@(Op And _) b@(Op op _)
  | hasOp Equation a =(D_STEPS,show a++" -> "++show b++" stepping And (with equations):")←(resStepOp a b)
  | otherwise=(D_STEPS,show a++" stepping And:")←(defStep a b)
_step a@(Op And _) b
  | hasOp Equation a = (D_STEPS,show a++" stepping And equation:")←(Just $ Op Resol [a,Op Equiv [b]])
  | otherwise=(D_STEPS,show a++" stepping And:")←(Just $ Op Simpl [a,Op Equals [b]])
_step a@(Op System _) b@(Op op _)=(D_STEPS,show a++" stepping System:")←(resStepOp a b)
_step a@(Op Equation _) b@(Op Resol _)=(D_STEPS,show a++" stepping Equation to Resol:")←(Just b)
_step a@(Op Equation _) b@(Op op _)=(D_STEPS,show a++" stepping Equation Op:")←(resStepOp a b)
_step a@(Op Equation _) b =Just $ (D_STEPS,show a++" stepping Resol element:")←(Op Resol [a,Op Equiv [b]])
_step a@(Op opa _) b@(Op Resol m@(Op rop _:_))
  | elem rop resolSteps = Just $(D_STEPS,"stepping Op+Resol:")←(Op Resol ([a]++m))
  | otherwise=stepOp a b
_step a@(Op opa _) b@(Op Resol _)=error "does this exist"
_step a@(Op opa _) b@(Op opb mb)
  | elem opb resolSteps = Just $Op Resol ([a]++mb)
  | otherwise=stepOp a b
  --where b'=if elem opb resolSteps then b else Op Equiv [b]
_step a b@(Op Resol mb@((Op rop _):_))
  |elem rop resolOps = Just$Op Resol ([a]++mb)
  |otherwise=Just b --complete resolution
_step a b@(Op Resol _)=Just b
_step a b@(Op _ _)=stepOp a b
_step a b= (D_STEPS,"stepping:")←(defStep a b)

stepOp a b@(Op op _)
  | elem op equatOps = Just$(D_STEPS,show a++" -> "++show b++" stepping equatOps:")←(Op Simpl [a,b])
  | otherwise= (D_STEPS,show a++" -> "++show b++" stepping op:")←(defStep a b)

resStepOp a b@(Op op _)
  | elem op resolSteps = Just $ (D_STEPS,show a++" -> "++show b++" stepResOp:")←(Op Resol [a,b])
  | otherwise= Just $ (D_STEPS,show a++" -> "++show b++" stepResOp:")←(Op Resol [a,Op Equiv [b]])
resStepOp a b = Just $ (D_STEPS,show a++" -> "++show b++" stepResOp:")←(Op Resol [a,Op Equiv [b]])
defStep a b=Just $ (D_STEPS,"default _step:")←(Op Simpl [a,Op Equals [b]])

(<=>) :: Algo -> Maybe Algo -> Maybe Algo
a <=> (Just b) = step a b
_ <=> _ = Nothing

-- produce steps of a given operation
steps::(Algo->Maybe Algo)->Algo->Maybe Algo
steps f o = o <=> r
  where r = f o

{-steps f o@(Op op m)
  | dInfo (D_ANY,"_step "++show o) = undefined
  | not$ok res=(D_STEPS,show o++" stepping (no results) to ")←Nothing
  | op==Document=res
  | op==Resol=(D_STEPS,show o++" stepping Resol to ")←(if elem rop resolSteps
    then Just $ Op op $ m++[r]
    else Just $ Op op $ m++[Op (fromJust ((getOp $ last m) <|> Just Equiv)) [r]])
  | op==Simpl=(D_STEPS,show o++" stepping Simpl to ")←(if elem rop equatOps
    then Just $ Op op $ m++[r]
    else Just $ Op op $ m++[Op (fromJust ((getOp $ last m) <|> Just Equals)) [r]])
  | hasEq&&not resolStep=(D_STEPS,show o++" stepping Equation ~ to ")←(Just$Op Resol [o,Op Equiv [fromJust res]])
  | elem (resOp res) exprOps=(D_STEPS,show o++" stepping exprOps to ")←res --(Just$Op Simpl [o,Op Equals [fromJust res]])
  | op==Simpl||op==Resol
    = (D_STEPS,show o++" stepping Simp/Resol to ")←(if elem (nostep$fromJust res) (map   nostep m)
      then Nothing -- ignoring redundant _step !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      else Just$algAppend (fromJust res) o)
  | resolStep=(D_STEPS,show o++" stepping resolStep to ")←(Just$Op Resol [o,fromJust res])
  -- | otherwise=(D_STEPS,show o++" steppingt to ")←((Just$Op Simpl [o])<+(Just$Op Equals [])<+res)
  | otherwise=(D_STEPS,show o++" stepping otherwise to ")←res
  where
    res=f o
    rop=resOp res
    resolStep=elem rop resolSteps
    resOp (Just (Op rop _))=rop
    resOp _=op
    hasEq=hasOp Equation o
    (Just r)=res
old_steps _ _=Nothing
-}
-- EOF
