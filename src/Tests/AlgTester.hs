module Tests.AlgTester where

import Data.List
import Control.Applicative

import AlgData
import Calc
import Rules
import AlgParser
import Evid
import Utils
import Solver
import Lib.Debug
import Lib.Colors
import Lib.ISUnits

loop :: (Num a, Monad m, Eq a) => m a1 -> a -> m a1
loop f 0=f
loop f n=do
  _<-f
  loop f (n-1)

test :: IO ()
test=do
  strTest
  objTest

objTest :: IO ()
objTest = putStr$ (intercalate "\n" $map (\(t,(e,r))->tester t e r)
  [
  (solveM emptyCtx, (Op System [_algo "x/a=0",_algo "k=1"],"\t|x/a=0\n\t|k=1\n\n \8660 \t|x=0\n\t|k=1\n\n"))
  ,(solveM emptyCtx,(Op Div [Op Mul [Unit volts,Unit amps],Unit volts],"(V·A)/V=W/V=A"))
  ,(evid x,(Op System [_algo "x+x=10-b",_algo "a=1",_algo "b=2a"],"\t|x+x=10-b\n\t|a=1\n\t|b=2\183a\n\n \8660 \t|2\183x=10-b\n\t|a=1\n\t|b=2\183a\n\n \8660 \t|x=(10-b)/2\n\t|a=1\n\t|b=2\183a\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "x+2=5-b",_algo "b=12"],"\t|x+2=5-b\n\t|b=12\n\n \8660 \t|x+2=5-12\n\t|b=12\n\n \8660 \t|x+2=5-12\n\t|b=12\n\n \8660 \t|x+2=-7\n\t|b=12\n\n \8660 \t|x=-7-2\n\t|b=12\n\n \8660 \t|x=-7-2\n\t|b=12\n\n \8660 \t|x=-7-2\n\t|b=12\n\n \8660 \t|x=-9\n\t|b=12\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "R=E/I",_algo "E=12",_algo "I=0.5"],"\t|R=E/I\n\t|E=12\n\t|I=1/2\n\n ⇔ \t|R=12/1/2\n\t|E=12\n\t|I=1/2\n\n ⇔ \t|R=24\n\t|E=12\n\t|I=1/2\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "R=E/I",_algo "E=5",_algo "R=180"],"\t|R=E/I\n\t|E=5\n\t|R=180\n\n ⇔ \t|180=5/I\n\t|E=5\n\t|R=180\n\n ⇔ \t|I=5/180\n\t|E=5\n\t|R=180\n\n ⇔ \t|I=1/36\n\t|E=5\n\t|R=180\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "f(x)=2·x", _algo "f(y)=98"],"\t|f(x)=2\183x\n\t|f(y)=98\n\n \8660 \t|f(x)=2\183x\n\t|2\183y=98\n\n \8660 \t|f(x)=2\183x\n\t|y=98/2\n\n \8660 \t|f(x)=2\183x\n\t|y=49\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "f⁻(x)=x/2", _algo "f(12)"],"\t|f\8315\185(x)=x/2\n\t|f(12)\n\n \8660 \t|f\8315\185(x)=x/2\n\t|12·2\n\n \8660 \t|f\8315\185(x)=x/2\n\t|24\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "f(n)=2n", _algo "f⁻(x)"],"\t|f(n)=2·n\n\t|f\8315\185(x)\n\n \8660 \t|f(n)=2·n\n\t|x/2\n\n"))
  ,(solveM emptyCtx,(Op System [_algo "f(n)=2n", _algo "f⁻(x)=x/2"],"\t|f(n)=2·n\n\t|f\8315\185(x)=x/2\n\n \8660 \t|n·2=2·n\n\t|x/2=x/2\n\n \8660 \t|True\n\t|True\n\n \8660 True"))
  ,(solveM emptyCtx,(Op System ["g(a,b)=a*b","f(x)=g(x,2)","f⁻(n)"],"\t|g(a,b)=a\183b\n\t|f(x)=g(x,2)\n\t|f\8315\185(n)\n\n \8660 \t|g(a,b)=a\183b\n\t|f(x)=g(x,2)\n\t|n/2\n\n"))
  ])++"\n------\n"

strTest :: IO ()
strTest = putStr$ (intercalate "\n" $map (\(t,(e:r:[]))->tester t (_algo e) r)
  [
    (((aresume 500 )<$>) .solveM emptyCtx,["5x+8=3x-6","5·x+8=3·x-6 ⇔ x=-7"]),
    (solveM emptyCtx,["root(16,2) ∈ ℕ ","root(16,2) ∈ ℕ  ⇔ 4 ∈ ℕ  ⇔ True"]),
    (solveM emptyCtx,["10ºC+1ºC","10.0ºC+1.0ºC=557.3K"]),
    (solveM emptyCtx,["(a=x)&(a=1)","a=x ∧ a=1 ⇔ 1=x ∧ a=1 ⇔ x=1 ∧ a=1"]),
    (solveM emptyCtx,["(1+inf)+b<2","1+\949+b<2 \8660 b>2-1-\949 \8660 b>2-1-\949 \8660 b>2-1-\949 \8660 b>1-\949 \8660 b\8805\&1"]),
    (solveM emptyCtx,["x·(2|3)","x·(2 ∨ 3)=(x·2 ∨ x·3)"]),
    (((aresume 500 )<$>) . solveM emptyCtx,["(a ∈ [0;1[) & (a+b=12)","a ∈ [0;1[ ∧ a+b=12 ⇔ a≥0 ∧ a<1 ∧ b≤12 ∧ b>11"]),
    (solveM emptyCtx,["x=2+1","x=2+1 ⇔ x=3"]),
    (solveM emptyCtx,["(a>=2)&(2a=4)","a≥2 ∧ 2·a=4 ⇔ a≥2 ∧ a=4/2 ⇔ 2≥2 ∧ a=2 ⇔ True ∧ a=2 ⇔ a=2"]),
    (solveM emptyCtx,["(a=1)&(a=2)","a=1 ∧ a=2 ⇔ False ∧ False ⇔ False"]),
    (evid x,["x*a=k","x·a=k ⇒ x=k/a:a≠0"]),
    (evid x,["x*a=0","x·a=0 ⇒ x=0/a:a≠0 ⇔ x=0:a≠0"]),
    (solveM emptyCtx,["10x+x","10·x+x=11·x"]),
    (solveM emptyCtx,["12V/A","12.0V/A=12.0Ω"]),
    (solveM emptyCtx,["](-Inf);2]∩]2;10[","]-∞;2] ∩ ]2;10[=∅ "]),
    (solveM emptyCtx,["5V/50mA","5.0V/50.0mA=100.0Ω"]),
    (Just . solved,["{a,b}/{c}","{a/c,b/c}"]),
    (solveM emptyCtx,["1A+500mA","1.0A+500.0mA=1.5A"]),
    (solveM emptyCtx,["3x>4x","3·x>4·x ⇔ 3·x-4·x>0 ⇔ 3·x-4·x>0 ⇔ -1·x>0 ⇔ -x>0 ⇔ x<-0 ⇔ x<0"]),
    (solveM emptyCtx,["10 ∈ {(2·n-1):(n∈ ℕ )}","10 ∈ {2·n-1:n ∈ ℕ } ⇔ 11/2 ∈ ℕ  ⇔ 11/2 ∈ ℕ  ⇔ False"]),
    (solveM emptyCtx,["3.2·ℕ  ∩ ℕ ","16/5·ℕ  ∩ ℕ =16·ℕ "]),
    (solveM emptyCtx,["3.2 ∈ {(a/b):(a,b ∈ ℕ) }","16/5 ∈ {a/b:a,b ∈ ℕ } ⇔ 16/5·b ∈ ℕ  ∧ b ∈ ℕ  ⇔ 16·ℕ ≠∅ "]),
    (solveM emptyCtx,["root(5,2) ∈ {(a/b):(a,b ∈ ℕ) }","root(5,2) ∈ {a/b:a,b ∈ ℕ } ⇔ 2.236 ∈ {a/b:a,b ∈ ℕ } ⇔ 2.236·b ∈ ℕ  ∧ b ∈ ℕ  ⇔ 2.236·ℕ  ∩ ℕ ≠∅ "]),
    (solveM emptyCtx,["3x+2x","3·x+2·x=5·x"]),
    (solveM emptyCtx,["a+a=(2a,(1=2))","a+a=2·a:1=2 ⇔ a+a=2·a:False"]),
    (solveM emptyCtx,["a=(b,True)","a=b:True ⇔ a=b"]),
    (solveM emptyCtx,["3.2 ∈ ℚ","16/5 ∈ ℚ  ⇔ True"]),
    (solveM emptyCtx,["3.2∈ {((2^n)/(2n+1)):(n∈ ℕ )}","16/5 ∈ {2^n/(2·n+1):n ∈ ℕ }"]),
    (solveM emptyCtx,["6 ∈ {(2n):(n ∈ ℕ) }","6 ∈ {2·n:n ∈ ℕ } ⇔ 3 ∈ ℕ  ⇔ True"]),
    (solveM emptyCtx,["(x·2) ∈ ({1,2,3}·x)","x·2 ∈ {1,2,3}·x ⇔ x·2 ∈ {1·x,2·x,3·x} ⇔ True"]),
    (solveM emptyCtx,["2<x","2<x \8660 x>2"]),
    (solveM emptyCtx,["2<=2","2≤2 ⇔ True"]),
    (calc,["x<>x", "False"]),
    (calc,["2+2", "4"]),
    (simplify,["x+x", "2·x"]),
    (calc,["1+2+3", "6"]),
    (simplify,["x+x+x", "2·x+x"]),
    (calc . last . membersOf,["a=2+2", "=4"]),
    (simplify . last . membersOf ,["a=x+x", "=2·x"]),
    (calc,["a=b=2+2", "4"]),
    (simplify,["a=b=x+x", "2·x"]),
    (calc,["a=2+2","a=4"]),
    (simplify,["a=x+x", "⇔ a=2·x"]),
    (calc,["(2+2=4)&x","4=4 ∧ x"]),
    (solveM emptyCtx,["(2+2=4)&x","2+2=4 ∧ x ⇔ 4=4 ∧ x ⇔ True ∧ x ⇔ x"]),
    (simplify,["x=a+a","⇔ x=2·a"]),
    (calc,["x=0+a","x=a"]),
    (calc,["(3·a+2)-x=0 <=>x=0+(3·a+2)","x=3·a+2"]),
    (solveM emptyCtx,["(3·a+2)-x=0 <=>x=0+(3·a+2)","3·a+2-x=0 ⇔ x=0+3·a+2 ⇔ x=3·a+2"]),
    (_evid (Lit "x"),["2x=0","⇔ x=0/2"]),
    (calc,["x/1=0 <=>x=0·1","x=0"]),
    (evid (Lit "x"),["x/1=0","x/1=0 ⇔ x=0"]),
    (solveM emptyCtx,["(a=2)&(a+a=4)","a=2 ∧ a+a=4 ⇔ a=2 ∧ 2·a=4 ⇔ a=2 ∧ a=4/2 ⇔ a=2 ∧ a=2 ⇔ a=2"]),-- TODO: should resume to True, no?
    (solveM emptyCtx,["(a=2)&(a+a=5)","a=2 ∧ a+a=5 ⇔ a=2 ∧ 2·a=5 ⇔ a=2 ∧ a=5/2 ⇔ False ∧ a=5/2 ⇔ False"]),
    --(solveM emptyCtx,["a+0","a+0=a"]),
    --(Just . evid x,["x+x=0","x+x=0 ⇔ (1+1)·x=0 ⇔ 2·x=0 ⇔ x=0/2 ⇔ x=0"]),
    --(solveM emptyCtx,["2+x=5","2+x=5 ⇔ x=5-2 ⇔ x=3"]),
    --(solveM emptyCtx,["x+x^2=0","x+x²=0 ⇔ x=(-1±root((1²-(4·1·0)),2))/(2·1) ⇔ x=(-1±root((1-0),2))/2 ⇔ x=(-1±root((1+0),2))/2 ⇔ x=(-1±root(1,2))/2 ⇔ x=(-1±1)/2 ⇔ x=(-1+1 ∨ -1-1)/2 ⇔ x=(0 ∨ -1-1)/2 ⇔ x=(0 ∨ -2)/2 ⇔ x=0/2 ∨ -2/2 ⇔ x=0 ∨ -(2/2) ⇔ x=0 ∨ -1 ⇔ x=0 ∨ -1 ⇔ x=0 ∨ x=-1"]),
    --((\o->verify =<< solve o), ["x+x^2=0","0+0²=0 ∧ -1+-1²=0 ⇔ 0+0=0 ∧ -1+1=0 ⇔ 0=0 ∧ 0=0 ⇔ True ∧ True ⇔ True"]),
    --(Just . evid (_algo "E"), ["R=E/I","R=E/I ⇔ E=R·I"]),
    (evid (_algo "I"), ["R=E/I","R=E/I ⇔ I=E/R"]),
    --(Just . evid (Lit "x"),["-12·x²·x=5-x","-12·x²·x=5-x ⇔ -12·x²·x-(5-x)=0 ⇔ -12·x²·x+x-5=0 ⇔ -12·x²·x+x-5=0 ⇔ x^(2+1)·-12+x-5=0 ⇔ x\179·-12+x-5=0"]),
    (solveM emptyCtx,["x=(-x)","x=-x ⇔ x-(-x)=0 ⇔ x-(-x)=0 ⇔ x+x=0 ⇔ 2·x=0 ⇔ x=0/2 ⇔ x=0"]),
    (solveM emptyCtx,["a·(a-2)=15","a·(a-2)=15 ⇔ a·a+a·-2=15 ⇔ a²+a·-2=15 ⇔ a²+-2·a+0-15=0 ⇔ a²+(-2·a-15)=0 ⇔ a²+-2·a-15=0 ⇔ a=(2±root((4--60),2))/2 ⇔ a=(2±root((4+60),2))/2 ⇔ a=(2±root(64,2))/2 ⇔ a=(2±8)/2 ⇔ a=(10 ∨ 2-8)/2 ⇔ a=(10 ∨ -6)/2 ⇔ a=(5 ∨ -6/2) ⇔ a=(5 ∨ -3) ⇔ a=(5 ∨ -3) ⇔ a=5 ∨ a=-3"]),
    (solveM emptyCtx,["True=False","True=False ⇔ False"]),
    (solveM emptyCtx,["x ∈ [1;x]","x ∈ [1;x] ⇔ True"]),
    (solveM emptyCtx,["x ∈ [1;x[","x ∈ [1;x[ ⇔ False"]),

    (solveM emptyCtx,["0=x+x²","0=x+x² ⇔ x=(-1±root((1-0),2))/2 ⇔ x=(-1±root((1+0),2))/2 ⇔ x=(-1±root(1,2))/2 ⇔ x=(-1±1)/2 ⇔ x=(0 ∨ -1-1)/2 ⇔ x=(0 ∨ -2)/2 ⇔ x=(0 ∨ -2/2) ⇔ x=(0 ∨ -1) ⇔ x=(0 ∨ -1) ⇔ x=0 ∨ x=-1"]),
    (solveM emptyCtx,["a-a²=0","a-a²=0 ⇔ a=(-1±root((1-0),2))/-2 ⇔ a=(-1±root((1+0),2))/-2 ⇔ a=(-1±root(1,2))/-2 ⇔ a=(-1±1)/-2 ⇔ a=(0 ∨ -1-1)/-2 ⇔ a=(0 ∨ -2)/-2 ⇔ a=(-0/2 ∨ 2/2) ⇔ a=(-0 ∨ 1) ⇔ a=(0 ∨ 1) ⇔ a=0 ∨ a=1"]),
    (solveM emptyCtx,["a²=(-a)","a²=-a ⇔ a²-(-a)=0 ⇔ a²-(-a)=0 ⇔ a²+a=0 ⇔ a=(-1±root((1-0),2))/2 ⇔ a=(-1±root((1+0),2))/2 ⇔ a=(-1±root(1,2))/2 ⇔ a=(-1±1)/2 ⇔ a=(0 ∨ -1-1)/2 ⇔ a=(0 ∨ -2)/2 ⇔ a=(0 ∨ -2/2) ⇔ a=(0 ∨ -1) ⇔ a=(0 ∨ -1) ⇔ a=0 ∨ a=-1"]),
    (solveM emptyCtx,["(x+2)^2=0","(x+2)^2=0 ⇔ x²+2·x·2+2²=0 ⇔ x²+4·x+4=0 ⇔ x=(-4±root((16-16),2))/2 ⇔ x=(-4±root((16-16),2))/2 ⇔ x=(-4±root(0,2))/2 ⇔ x=(-4±0)/2 ⇔ x=(-4 ∨ -4+0)/2 ⇔ x=(-4 ∨ -4)/2 ⇔ x=-4/2 ⇔ x=-2 ⇔ x=-2"]),
    ((\o->verify $ solve o),["a²=(-a)","0²=-0 ∧ -1²=--1 ⇔ 0=0 ∧ 1=1 ⇔ True ∧ True ⇔ True"]),
    (solveM emptyCtx,["a+{x}+b","a+{x}+b=a+{x+b}={a+(x+b)}={a+x+b}"]),
    (solveM emptyCtx,["{0,1,2}+1={3,2,1}","{0,1,2}+1={3,2,1} ⇔ {0+1,1+1,2+1}={3,2,1} ⇔ {1,2,3}={3,2,1} ⇔ True"]),
    (solveM emptyCtx,["(k/b)·(j/k)","(k/b)·(j/k)=j/b"])

  ])++"\n------\n"

tester t e r
  | r==show tr = "Ok "++show e++" -> "++show tr
  | not$ok tr=redColor++"  »Error "++nColor++show e++" -> Nothing!"
  | r==res="Ok "++show e++" -> "++show res'
  | otherwise=redColor++"  »Error "++nColor++show e++" -> \t"++r++"\n\t\tresult:\t"++(show res')
  where
    tr=t e
    (Just res')=tr
    res=clrColors $show res'

x,y,a,b,c,n::Algo
x=Lit "x"
y=Lit "y"
a=Lit "a"
b=Lit "b"
c=Lit "c"
n=Lit "n"
