-- the Algo number format
module Lib.Noms where

import Lib.Debug

import Data.Number.CReal
import Data.Ratio
--import Data.Char
--import Data.List
--import Debug.Trace
--import Data.List.Ordered
--import Math.ContinuedFraction
--import Data.Complex.Cyclotomic
--import Data.Maybe
--import Math.ContinuedFraction

data Nr
  = NrRatio Rational
  | NrReal CReal
  -- | Integer Integer
  -- | NrCyclo Cyclotomic
  deriving (Show)

-- continuous fraction step
{-cfs :: (RealFrac t1, Integral t, Integral a) => (a, t1) -> (t, t1)
cfs (i,r)
  | r==fromIntegral i= (0,0)
  | otherwise = (floor r',r')
  where r'=1/(r-fromIntegral i)

-- generate continuous fraction
ncf :: (RealFrac b1, Integral b) => b1 -> [b]
ncf x=map fst $takeWhile (\(_,r)->r/=0) $iterate cfs (floor x,x)

mkcf x=cf o oo where (o:oo)=ncf x

-- continuous fraction to number
cfn :: (Integral a, Fractional b) => [a] -> b
cfn (o:[])=fromIntegral o
cfn (o:oo@(_:_))=fromIntegral o+1/cfn oo

converge (o:oo)=convergents $cf o oo

l2t []=[]
l2t (a:[])=error "odd list"
l2t (a:b:l)=(a,b):l2t l

l3t []=[]
l3t (a:[])=error "list #%3/=0"
l3t (a:b:[])=error "list #%3/=0"
l3t (a:b:c:l)=(a,b,c):l3t l-}

instance Eq Nr where
  (==) (NrRatio a) (NrRatio b)=a==b
  (==) (NrReal a) (NrRatio b)=a==fromRational b
  (==) (NrRatio a) (NrReal b)=fromRational a==b
  (==) (NrReal a) (NrReal b)=a==b

instance Ord Nr where
  (<=) (NrRatio a) (NrRatio b) = a<=b
  (<=) (NrRatio a) (NrReal b) = fromRational a<=b
  (<=) (NrReal a) (NrRatio b) = a<=fromRational b
  (<=) (NrReal a) (NrReal b) = a<=b

instance Num Nr where
  (+) (NrRatio a) (NrRatio b)=NrRatio (a+b)
  (+) (NrReal a) (NrReal b)=NrReal (a+b)
  (+) (NrRatio a) (NrReal b)=NrReal (fromRational a+b)
  (+) (NrReal a) (NrRatio b)=NrReal (a+fromRational b)

  --(+) (NrRatio a) (NrCyclo b)=NrCyclo $ fromRational a+b
  --(+) (NrReal a) (NrCyclo b)= toReal b -- this toReal sucks!
  --(+) (NrCyclo a) (NrReal b)=NrCyclo (a+fromRational b)
  --(+) (NrCyclo a) (NrRatio b)=NrCyclo (a+fromRational b)

  (*) (NrRatio a) (NrRatio b)=NrRatio (a*b)
  (*) (NrReal a) (NrReal b)=NrReal (a*b)
  (*) (NrRatio a) (NrReal b)=NrReal (fromRational a*b)
  (*) (NrReal a) (NrRatio b)=NrReal (a*fromRational b)

  abs (NrRatio n) = NrRatio (abs n)
  abs (NrReal n) = NrReal (abs n)
  signum (NrRatio n) = NrRatio (signum n)
  signum (NrReal n) = NrReal (signum n)
  fromInteger i = NrRatio (fromInteger i)
  -- fromInteger i = NrReal (fromInteger i)
  negate (NrRatio n)=NrRatio (negate n)
  negate (NrReal n)=NrReal (negate n)

instance Fractional Nr where
  fromRational r=NrRatio r
  (/) (NrRatio a) (NrRatio b)=NrRatio (a/b)
  (/) (NrRatio a) (NrReal b)=NrReal (fromRational a/b)
  (/) (NrReal a) (NrRatio b)=NrReal (a/fromRational b)
  (/) (NrReal a) (NrReal b)=NrReal (a/b)

instance Real Nr where
  toRational (NrRatio r)=r
  toRational (NrReal r)=toRational r

instance RealFrac Nr where
  properFraction (NrReal n)= (\(p,q)->(p,NrReal q)) (properFraction n)
  properFraction (NrRatio n)=(\(p,q)->(p,NrRatio q)) (properFraction (fromRational n))
  round (NrReal n)=round n
  round (NrRatio n)=round n

instance Floating Nr where
  pi=NrReal pi

  exp (NrReal n)=NrReal $ exp n
  exp (NrRatio n)=NrReal $ exp (fromRational n)
  log (NrReal n)=NrReal $ log n
  log (NrRatio n)=NrReal $ log (fromRational n)
  sin (NrReal n)=NrReal $ sin n
  sin (NrRatio n)=NrReal $ sin (fromRational n)
  cos (NrReal n)=NrReal $ cos n
  cos (NrRatio n)=NrReal $ cos (fromRational n)
  asin (NrReal n)=NrReal $ asin n
  asin (NrRatio n)=NrReal $ asin (fromRational n)
  atan (NrReal n)=NrReal $ atan n
  atan (NrRatio n)=NrReal $ atan (fromRational n)
  acos (NrReal n)=NrReal $ acos n
  acos (NrRatio n)=NrReal $ acos (fromRational n)
  sinh (NrReal n)=NrReal $ sinh n
  sinh (NrRatio n)=NrReal $ sinh (fromRational n)
  cosh (NrReal n)=NrReal $ cosh n
  cosh (NrRatio n)=NrReal $ cosh (fromRational n)
  asinh (NrReal n)=NrReal $ asinh n
  asinh (NrRatio n)=NrReal $ asinh (fromRational n)
  atanh (NrReal n)=NrReal $ atanh n
  atanh (NrRatio n)=NrReal $ atanh (fromRational n)
  acosh (NrReal n)=NrReal $ acosh n
  acosh (NrRatio n)=NrReal $ acosh (fromRational n)

class AlgoNr a where
  isInt::a->Bool

instance AlgoNr Nr where
  isInt (NrRatio o)=denominator o==1
  isInt (NrReal o)= f==0 where (_,f)=properFraction o

-- EOF --
