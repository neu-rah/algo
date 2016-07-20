module Bench where

import AlgData
import Lib.Debug
import Rules

import qualified Data.Map as Map

{-
n ∈ {f(x):v ∈ X }
--------------------------------------------
10 ∈ {2·n:n ∈ ℕ }
n:10 f(x):2*n v:n X:ℕ

10=2*n <=> n=10/2

<=> 10/2 ∈ ℕ

------------------------------
10 ∈ {a/b : a,b ∈  ℕ}

n:10 f(x):a/b v:a,b X:ℕ

10=a/b <=> a=10b <=> b=a/10

10b ∈ ℕ & a/10 ∈ ℕ
-}

{-tst vars target@(Sets (SetExpr te td)) rule@(Sets (SetExpr re@(Op Func fd@(fn:[fp])) rd@(Op Equation [v,Op ElementOf d]))) strict
  =proc
  where
    proc=(D_ANY,"proc:")←(((Just . Map.union)=<<ls_chkRule vars te re strict)<*>(ls_chkRule vars td rd strict))
-}
