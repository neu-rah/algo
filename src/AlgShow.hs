{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module AlgShow where

import Data.List
import Data.Ratio
import Data.Number.CReal
--import Data.Complex.Cyclotomic
import Data.Maybe
import Data.Numbers.Primes
import Lib.Noms
import Control.Applicative
import Data.Unique
import qualified Data.Map as Map

import AlgData
import Utils
import Lib.Debug
import Lib.Colors
import Lib.Noms

-- show structural info for debug purposes
info :: Algo -> [Char]
info (Op Equiv m) = "<=>"++"["++ (intercalate ", " $map info m) ++"]"
info (Op Implic m) = "=>"++"["++ (intercalate ", " $map info m) ++"]"
info (Op Less m) = "<"++"["++ (intercalate ", " $map info m) ++"]"
info (Op Greater m) = ">"++"["++ (intercalate ", " $map info m) ++"]"
info (Op LessOrEqual m) = "<="++"["++ (intercalate ", " $map info m) ++"]"
info (Op GreaterOrEqual m) = ">="++"["++ (intercalate ", " $map info m) ++"]"
info (Op op m)=clrColors$show op ++"["++ (intercalate ", " $map info m) ++"]"
info (Lit x)=x
info (Pref)="?"
info (Sets (SetExpr a b))=clrColors $ "AlgSet {"++info a++":"++info b++"}"
info (Sets s)=clrColors $ "Sets "++(show s)
info (Nom(NrRatio o))=show o
info (Nom(NrReal o))=showCReal decPlaces o
info (Quant (v, (Scale ms u n f _ s)))=info v++" "++n -- ++" ("++n++") "++show s -- ++"*"++show f++" ("++show ms++")"
info o=clrColors $ show o

-- delimiters for printing -------------------------------------------
delims :: Ops -> ([Char], [Char], [Char])
delims Not =("~","","")
delims And =(""," ∧ ","")
delims Or  =(""," ∨ ","")
delims Set =("{",",","}")
delims List =(" ",","," ")
delims Neg =("-","","")
delims Pos =("+","","")
delims PosOrNeg =("±","","")
delims Sum =("","+","")
delims Sub =("","-","")
delims Mul =("","·","")
delims Div =("","/","")
delims Exp =("","^","")
delims Log =("log(",",",")")
delims Root=("root(",",",")")
delims Floor=("⌊","","⌋")

delims Sin=("sin ","","")
delims Cos=("cos ","","")
delims ASin=("asin ","","")
delims ACos=("acos ","","")
delims Tg=("tg ","","")
delims ATg=("atg ","","")
delims SinH=("sinh ","","")
delims CosH=("cosh ","","")
delims ASinH=("asinh ","","")
delims ACosH=("acosh ","","")
delims ATgH=("atgh ","","")

delims ElementOf = (" ∈ ","","")
delims NotElementOf = (" ∉ ","","")
delims Equals        =("=",":","")
delims Greater       =(">",":","")
delims Less          =("<",":","")
delims GreaterOrEqual=("≥",":","")
delims LessOrEqual   =("≤",":","")
delims NotEqual   =("≠",":","")
delims Relates   =("↔ ",":","")
delims InvRelates   =("⇼ ",":","")

delims Equation =("","","")
delims Equiv    =(resolColor++"⇔ "++nColor,"","")
delims Implic   =(resolColor++"⇒ "++nColor,"","")
delims SuchThat =("",":","")
delims Simpl    =("","","")
delims Resol    =(""," ","")

delims Sentence    =(""," ","")
delims Params    =("",",","")

delims System   =("\t|","\n\t|","\n\n")
delims Document =("","\n","\n")

delims Union     = (""," ∪ ","")
delims Intersect = (""," ∩ ","")
delims Index = ("","@","")

delims op    =("("," "++show op++" ",")")

instance Show MetricSystem where show (MetricSystem ms ds)=ms++"\n"++ show ds
instance Show Dimension where show (Dimension _ desig e _ _ _ _)=e
instance Show Scale where show (Scale _ u _ _ _ _)=u
instance Show RangeWing where show (RangeWing c o)=show c++" "++show o

resolColor=yellowColor
numColor=greenColor
litColor=blueColor
opColor=whiteColor
entityColor=redColor++boldStyle
unitColor=redColor
dimColor=boldStyle++yellowColor
wordColor=whiteColor

instance Show AlgSets where
  show (LSeq o)=show o
  show (RSeq o)=show o
  show (SetExpr expr dom)=opColor++"{"++show expr++opColor++":"++show dom++opColor++"}"++nColor
  show o@(AlgSet _ toString _ _) = toString o
  show (Range (RangeWing li l) (RangeWing ri r)) =
    opColor++(if li then "[" else "]")++show l ++ opColor++ ";" ++ show r ++ opColor++(if ri then "]" else "[")++nColor

decPlaces=3
prettyFraction::CReal
prettyFraction=10^(decPlaces-1)
prettyFractionInt=floor prettyFraction

showRatio i -- Rational
  | denominator i == 1 = numColor++(show $ numerator i)++nColor
  | i>10000 = numColor++(show $ fromRational i)++nColor
  | denominator i>=prettyFractionInt = numColor++(show $ fromRational i)++nColor
  | otherwise = numColor++(show (numerator i)++"/"++(show $ denominator i))++nColor

toRatio::CReal->Maybe Rational
toRatio n
  | isInt p=Just $ (floor $ n*prettyFraction) % prettyFractionInt
  | otherwise=Nothing
  where p=NrReal (n*prettyFraction)

showFloat (NrReal n)=numColor++(showCReal decPlaces n)++nColor
showFloat (NrRatio n)=numColor++(showCReal decPlaces $ fromRational n)++nColor

instance Show Algo where
  show (Op Sentence (n:m))=o++showLitAsWord n++(concat$(map (\ð->case ð of
      (Punctuation p) -> wordColor++p++nColor
      (Lit l) -> s++wordColor++l++nColor
      _ -> s++(show ð)
    ) m))++c
    where
      (o,s,c)=delims Sentence
      showLitAsWord (Lit l)=wordColor++l++nColor
      showLitAsWord o=show o
  show (Solver defs vars books docs)="{"++show (Map.toList defs)++","++show (Map.toList vars)++"}\n"++show docs
  show (Neighbor op e)
    =numColor++"("++show (Op op [e])++numColor++")"++nColor
  show Und="Undefined"
  show (Nom (NrRatio n))
    | denominator n==1 =numColor++show (numerator n)++nColor
    | otherwise = numColor++show (numerator n)++"/"++show (denominator n)++nColor
  show (Nom nr@(NrReal n))
    | (f==1&&p==0) = numColor++"1"++nColor
    | f==0 = numColor++show p++nColor
    | ok r && (denominator (fromJust r)<prettyFractionInt)=show $Nom(NrRatio $fromJust r)
    | otherwise=showFloat nr --numColor++(showCReal decPlaces n)++nColor
    where
      (p,f)=properFraction n;
      r=toRatio n
  show (Lit s)=litColor++s++nColor
  --show (Word s)=wordColor++s++nColor
  show (Punctuation s)=wordColor++s++nColor
  show (Bool b)=entityColor++(show b)++nColor
  show Pref=resolColor++"?"++nColor
  show Ellipsis=resolColor++"..."++nColor
  show (Numeric i)=numColor++"#"++i++nColor
  show Infinit=entityColor++"∞"++nColor
  show Infinitesimal=entityColor++"ε"++nColor
  show (Unit s)=unitColor++show s++nColor
  show (Quant (q@(Op op _),u))
    | elem op signalOps =show q++show u
    | otherwise=opColor++"("++show q++opColor++")"++show u
  show (Quant ((Nom v),s))=numColor++(showFloat v)++unitColor++show s++nColor
  show (Quant (v,s))=show v++unitColor++show s++nColor
  show (Dim d)=dimColor++show d++nColor
  show (Sets o)=show o
  show (Op Set [])=entityColor++"∅ "++nColor
  show o@(Op Func (name:params))=opColor++(clrColors$show name)++"("++showOp (Op Params params)++opColor++")"++nColor
  show o@(Op InvFunc (name:params))=opColor++(clrColors$show name)++"⁻¹("++showOp (Op Params params)++opColor++")"++nColor
  show o@(Op DerivedFunc (name:params))=opColor++(clrColors$show name)++"'("++showOp (Op Params params)++opColor++")"++nColor
  show o@(Op Exp (a@(Op opa _):(Nom n):[]))=showOp o
  show o@(Op Exp (a:(Nom n):[]))
    -- =showOp o
    | n<10&&n>0=show a++numColor++[(fst (specialChars!!(round n)))]++nColor
    | n<0&&n>(-10)=show a++numColor++"⁻"++[(fst (specialChars!!(round (-n))))]++nColor
    | otherwise=showOp o
  show (Op Sum (m:mm))
    = o++show m++(concat $ map showSub mm)++c
    where
      (o,s,c)=delims Sum
      showSub o'@(Nom n)
        | n<0 =show o'
        | otherwise=opColor++s++nColor++show o'
      showSub o@(Quant (Nom n,_))
        | n<0 = show o
        | otherwise=opColor++s++nColor++show o
      showSub o@(Quant (Op sop _,_))
        | elem sop signalOps = show o
        | otherwise=opColor++s++nColor++show o
      showSub sub@(Op sop _)
        | elem sop signalOps = show sub
        | prior Sum >= prior sop && (not $ elem sop envOps)
          =opColor++s++"("++nColor++show sub++opColor++")"++nColor
        | otherwise = opColor++s++nColor++show sub
      showSub x=opColor++s++nColor++show x
  {-show (Op Equation (aop@(Op opa a):bop@(Op opb b):oo))
    |prior opa <= prior opb = "("++show aop++")"++show bop
    |otherwise=show aop ++ show bop-}
  show o@(Op _ _)=showOp o

showOp :: Algo -> [Char]
showOp (Op op m)
  | elem op exprOps = wss
  | elem op equatOps = case m of
      [Op sop _] -> if elem sop logicOps then wss else woss
      _ -> woss
  | otherwise=woss
  where
    color=if elem op signalOps && (m#=1) && (head m)==Infinit then entityColor else opColor
    (o,s,c)=delims op
    wss=color++o++nColor++(intercalate (opColor++s++nColor) (map showSub m))++opColor++c++nColor
    woss=color++o++nColor++(intercalate (opColor++s++nColor) (map show m))++opColor++c++nColor
    showSub s'@(Op sop _)=
      if prior op >= prior sop && (not $ (elem sop envOps||elem op envOps))
      then opColor++"("++nColor++show s'++opColor++")"++nColor
      else show s'
    showSub s'=show s'
showOp _ = undefined
-- EOF --
