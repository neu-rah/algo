{-# LANGUAGE CPP #-}
module Lib.Debug where --(module Lib.Colors) where

import Lib.Colors

#define DEBUG

#ifdef DEBUG
import Debug.Trace

debugSections=[D_ANY]::[DebugSections]

algTrace :: (DebugSections, String) -> a -> a
{-# INLINE algTrace #-}
algTrace (sec,msg) value
  | elem sec debugSections=trace (redColor++show sec++"  »"++nColor++msg++" ") value
  | otherwise=value
dInfo::(DebugSections,String)->Bool
dInfo (sec,msg)
  | elem sec debugSections=trace ("==>"++redColor++show sec++"  »"++nColor++msg++" ") False
  | otherwise = False
#endif
#ifndef DEBUG
algTrace :: (DebugSections, String) -> a -> a
{-# INLINE algTrace #-}
algTrace _ value=value
dInfo::(DebugSections,String)->Bool
{-# INLINE dInfo #-}
dInfo (sec,m,msg)=False
#endif

data DebugSections
  = D_ANY | D_PLD | D_PARSER | D_SAMPLE
  | D_CALC | D_NOMS | D_CTX | D_UNITS
  | D_RULES | D_GROUP | D_MORPH | D_EVID | D_ASSIGN
  | D_SOLVER | D_SETS | D_RANGES | D_STEPS | D_NEIGH
  | D_CONT | D_FILE
  deriving (Show,Eq,Ord,Enum)

(←) :: Show a => (DebugSections, [Char]) -> a -> a
(←) (s,m) r=algTrace (s,(m++show r++" ")) r
