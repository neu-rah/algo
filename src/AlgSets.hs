module AlgSets where

import AlgData
--import AlgShow
import Utils
import AlgAux
import Evid
--import Lib.OrdSet
import Lib.Debug
import Lib.Colors
import Lib.Noms

--import Data.Ratio
import Data.Maybe
import qualified Data.Map as Map
import Control.Applicative

-- natural numbers check
isNatural::Algo->Maybe Algo
isNatural (Nom n) = Just $Bool (snd (properFraction n) == 0 && n>0)
isNatural _ = Nothing

isRational::Algo->Maybe Algo
isRational (Nom (NrRatio _)) = Just $Bool True
isRational (Nom (NrReal _)) = Just $Bool False
isRational _ = Nothing

--real numbers "check"
isReal::Algo->Maybe Algo
isReal _ = Just $Bool True


--class Set o where elem::Algo->o->Bool

--algebraic sets, defined as string, print function, contains function and compare function
algSets :: Map.Map [Char] Algo
algSets=Map.fromList $ map (\o@(Sets(AlgSet l _ _ _))->(l,o)) [_N,_R]

_N,_R::Algo
_N=Sets $AlgSet "N" (\_->yellowColor++"ℕ "++nColor) isNatural ordSet
_Q=Sets $AlgSet "Q" (\_->yellowColor++"ℚ "++nColor) isRational ordSet
_R=Sets $AlgSet "R" (\_->yellowColor++"ℝ "++nColor) isReal ordSet
--------------------------------------------------------------------------------
showSet :: (Show a1, Show a) => a -> a1 -> String
showSet e d = blueColor++"{"++show e++blueColor++":"++show d++blueColor++"}"++nColor

-- deal with things like:
-- Q = {a/b : a, b ∈ Z, b ≠ 0}
elemSet::Algo->Algo->Algo->Maybe Algo
elemSet e d o
  | dInfo(D_SETS,"elemSet e:"++show e++" d:"++show d++" o:"++show o)=undefined
  -- | and oks = Just $(D_SETS,"then:")←(Op And $map fromJust r)
  | ok r = Just rr
  | otherwise= Nothing
  where
    lit=(D_SETS,"literals: ")←(head$literals e)
    ele=(D_SETS,"lits,evids:")←(_evid lit e) --(zip lits $ map (\l->_evid l e) lits)
    r=(D_SETS,"evid repVars:")←(repVars (Map.fromList [(Pref,o)]) <$> ele)
    rr=(D_SETS,"rr=")←(repVars (Map.fromList [(lit,fromJust r)]) d)
    --r=(D_SETS,"evid repVars:")←(map (\(a,b)->(repVars (Map.fromList [(Pref,a)])) <$> b) ele)
    -- oks=(D_SETS,"Oks:")←(map ok r)
    -- rv=repVars

-- EOF --
