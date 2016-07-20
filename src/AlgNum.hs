module AlgNum where

import Data.Boolean

import AlgData
import {-# SOURCE #-} AlgParser
import Lib.Noms
import Lib.Debug
--import Data.String
--import GHC.Exts ( IsString(..) )

instance Num Algo where
  a+b=Op Sum [a,b]
  a*b=Op Mul [a,b]
  abs a= Op Abs [a]
  signum a=Op Sgn [a]
  fromInteger=Nom . fromInteger
  negate a=Op Neg [a]

instance Boolean Algo where
  true=Bool True
  false=Bool False
  notB b=Op Not [b]
  a &&* b=Op And [a,b]
  a ||* b=Op Or [a,b]

instance Fractional Algo where
  fromRational a=(Nom (NrRatio a))
  recip a=Op Div [Nom 1,a]

instance Floating Algo where
  pi=Nom $ NrReal pi
  exp a=Op Exp [a,2]
  log a=Op Log [a]
  sin a=Op Sin [a]
  cos a=Op Cos [a]
  asin a=Op ASin [a]
  atan a= Op ATg [a]
  acos a= Op ACos [a]
  sinh a= Op SinH [a]
  cosh a= Op CosH [a]
  asinh a= Op ASinH [a]
  atanh a= Op ATgH [a]
  acosh a= Op ACosH [a]

instance Real Algo where
  toRational (Nom r)=toRational r
  toRational _ = undefined

instance RealFrac Algo where
  properFraction (Nom n)= (\(p,q)->(p,Nom q)) $properFraction n
  properFraction o=(0,o)
  round (Nom n)=round n

-- in low level a==b -> False
-- in high level should be Just a=b
-- we make no distinction between assignment and comparision
-- all are assignments, but some asignments might reveal inconsistency, concluding to 'False'

--instance Eq Algo where
-- well, this derivation exists and we need it to work as is (low level)
-- therefor forbiding an higher implementation using this derivation
