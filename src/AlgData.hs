{-# LANGUAGE GADTs #-}
module AlgData where

import Data.List
import Data.Number.CReal
--import Data.Complex.Cyclotomic
import qualified Data.Map as Map
--import Data.Unique
import Data.Monoid hiding (Sum)

import Lib.Noms
import Lib.Debug
import Lib.Colors

--data Sgn = Neu | Pos | Neg | PosOrNeg deriving (Show,Eq,Ord,Enum)
--data Ops = Equat | Logic | Art | Geo | Exp | Func deriving (Show,Eq,Ord,Enum)

--some sort of annotation on this elements had been nice... :(
data Algo
  = Und
  | Bool Bool
  | Nom Nr
  | Lit String
  -- | Word String -- this still is a good idea to clean up var scopes!
  | Punctuation String
  | Op Ops [Algo]
  | Sets AlgSets
  | Ellipsis
  | Pref -- preference, used on evidenciation
  | Numeric String-- used on rules system to drive numerical calculation
  | Unit Scale -- measure unit
  | Quant (Algo,Scale) -- value and unit (unit expression must include only Units)
  | Dim Dimension -- metric dimensions like distance, velocity, mass, etc...
  | Infinit
  | Infinitesimal
  | Neighbor {neighbourOp::Ops, neighbourExpr::Algo}-- relational operator and expression, this is an internal object
  | Solver {slvDefs::Ctx, slvVars::Ctx, slvBooks::Algo, slvDoc::Algo}
  deriving (Ord)

note=(,)

data RangeWing=RangeWing {wingIncl::Bool, wingExpr::Algo} deriving Eq

data AlgSets
  = AlgSet
      String -- set name as: ℕ ℤ ℚ ℝ
      (AlgSets->String) -- show it
      (Algo->Maybe Algo) -- contains
      (AlgSets->AlgSets->Ordering) -- provides cardinality to compare infinit sets
  | SetExpr Algo Algo -- as: {expression:domain} ex: { a/b : a,b ∈ ℕ }
  | Range RangeWing RangeWing
  | RSeq Algo -- recursive sequence TODO: NOT IMPLEMENTED
  | LSeq Algo -- linear Sequence TODO: NOT IMPLEMENTED

data MetricSystem = MetricSystem {
  metricSystemName::String,
  metricSystemDims::[Dimension]
  }
data Dimension = Dimension {
  dimSys::MetricSystem,
  dimName::String,
  dimKey::String, -- for parser
  dimSymbol::Algo,
  dimDerived::Algo,
  dimScales::[Scale],
  favScale::Scale
  }
data Scale = Scale {
  scaleDim::Dimension,
  scaleSymbol::String,--- used by parser
  scaleName::String,
  scaleWeight::Algo,
  scaleExpr::Algo,
  scaleBase::Scale
  }

instance Eq MetricSystem where (==) (MetricSystem a _)(MetricSystem b _) = a==b
instance Eq Dimension where (==) (Dimension am an _ _ _ _ _)(Dimension bm bn _ _ _ _ _) = am==bm && an==bn
instance Eq Scale where (==) (Scale am _ _ ab _ _)(Scale bm _ _ bb _ _) = am==bm && ab==bb
instance Ord MetricSystem where compare a b=compare (metricSystemName a) (metricSystemName b)
instance Ord Dimension where compare a b=compare (dimName a) (dimName b)
instance Ord Scale where
  compare a b
    | compare (scaleDim a) (scaleDim b) == EQ = compare (scaleName a) (scaleName b)
    | otherwise=compare (scaleDim a) (scaleDim b)

class StrictEq o where
  strictEq::o->o->Bool

instance Eq AlgSets where
  (==) (AlgSet a _ _ _) (AlgSet b _ _ _) = a==b
  (==) (Range l1 r1) (Range l2 r2) = l1==l2 && r1==r2
  (==) _ _ = False

instance Ord AlgSets where compare = ordSet

ordSet::AlgSets->AlgSets->Ordering
ordSet (AlgSet "N" _ _ _) (AlgSet "N" _ _ _) = EQ
ordSet (AlgSet "N" _ _ _) (AlgSet "R" _ _ _) = LT
ordSet (AlgSet "R" _ _ _) (AlgSet "N" _ _ _) = GT
ordSet (AlgSet "R" _ _ _) (AlgSet "R" _ _ _) = EQ
ordSet _ _ = undefined

instance StrictEq RangeWing where
  strictEq (RangeWing ai ae) (RangeWing bi be)=ai==bi&&strictEq ae be
instance StrictEq AlgSets where
  strictEq (AlgSet a _ _ _) (AlgSet b _ _ _) = a==b
  strictEq (Range l1 r1) (Range l2 r2) = strictEq l1 l2 && strictEq r1 r2
  strictEq _ _ = False

instance StrictEq Algo where
  strictEq (Op opa ma) (Op opb mb)=opa==opb &&(and$zipWith strictEq ma mb)
  strictEq Und Und=True
  strictEq (Bool a) (Bool b)=a==b
  strictEq (Nom a) (Nom b)=a==b
  strictEq (Lit a) (Lit b)=a==b
  strictEq Pref Pref = True
  strictEq (Sets a) (Sets b) = strictEq a b
  strictEq _ _ = False

instance Eq Algo where
  (==) Und Und=True
  (==) (Bool a) (Bool b)=a==b
  (==) (Nom a) (Nom b)=a==b
  (==) (Lit a) (Lit b)=a==b
  (==) Pref Pref = True
  (==) (Sets a) (Sets b) = a==b
  (==) (Numeric a) (Numeric b)=a==b
  (==) Infinit Infinit=True -- just at low lever for the sake of program logic
  (==) Ellipsis Ellipsis=True -- just at low lever for the sake of program logic

  (==) (Neighbor n1 v1) (Neighbor n2 v2) = n1==n2 && v1==v2
  (==) (Neighbor Equals v) (Op o [m]) = (Equals==o && v==m) || v==m
  (==) (Neighbor Equals v) b = v==b
  (==) (Op Neg [Nom a]) (Nom b) = a==(-b)
  (==) (Nom b) (Op Neg [Nom a]) = a==(-b)
  (==) (Op o [m]) (Neighbor Equals v) = (Equals==o && v==m) || v==m
  (==) a (Neighbor Equals v) = v==a
  (==) (Neighbor n v) (Op o [m]) = n==o && v==m
  (==) (Op o [m]) (Neighbor n v) = n==o && v==m
  (==) (Op Equals [m]) o = o==m
  (==) o (Op Equals [m]) = o==m

  (==) (Unit a) (Unit b)=a==b
  (==) (Dim a) (Dim b)=a==b
  (==) a@(Quant (qa,ua)) b@(Quant (qb,ub)) = ua==ub && qa==qb
  (==) (Op Equation (a:(Op ra ma@(ea:ca)):[])) (Op Equation (b:(Op rb mb@(eb:cb)):[]))
    | ra==rb && a == b && ma==mb = True
    | ra == Equals || ra == NotEqual || (ra == inverse rb)= a==eb && b==ea && ca==cb
    | otherwise = False
  (==) (Op opa ma) (Op opb mb)
    =opa==opb&&if canComut opa then (((ma\\mb)==[])&&((mb\\ma)==[])) else ma==mb
  (==) _ _ = False

data Ops
   = Identity | Sentence | SuchThat
   | Set | List | Not | Or | And
   | Neg | Pos | PosOrNeg
   | Sum | Sub | Mul | Div | Exp | Root | Log
   | Fact | Sgn | Abs | Floor |Round
   | Sin | Cos | ASin | ACos | Tg | ATg -- | CTg | ACTg
   | SinH | CosH | ASinH | ATgH | ACosH
   | Func | InvFunc | DerivedFunc
   | Index
   | Contains | Contained
   | Union | Intersect | Disjunct
   | Equation | Simpl | Resol
   | ElementOf | NotElementOf
   | Equals | Greater | Less
   | GreaterOrEqual | LessOrEqual | NotEqual
   | Relates | InvRelates
   | Equiv | Implic
   | System | Document
   | Params -- used in parser as a generic container
  deriving (Show,Eq,Ord)

data Prior
  = Documents | Sentences
  |  Process | Steps | SetOps
  | Logic | Arithmetic | Geometric | Exponential  | Relational
  | Function | Lists | Element
  deriving (Show,Eq,Ord,Enum)

prior :: Ops -> Prior
prior op
  | op==SuchThat=SetOps
  | op==Document=Documents
  | op==Sentence=Sentences
  | elem op setOps=Lists
  | op==Equation||elem op equatOps=Relational
  | elem op procOps=Process
  | elem op resolOps=Process
  | elem op resolSteps=Steps
  | elem op opSetOps=SetOps
  | elem op logicOps=Logic
  | elem op arithmeticOps=Arithmetic
  | elem op geometricOps=Geometric
  | elem op exponentialOps=Exponential
  | otherwise=Function

type Ctx=Map.Map Algo Algo

---------------------------------------
instance Monoid Algo where
  mempty=Und
  mappend Und Und=Und
  mappend Und x=x
  mappend x Und=x
  mappend (Op op1 m1) o@(Op op2 m2)=if op1==op2||op2==List then Op op1 (m1++m2) else Op op1 (m1++[o])
  mappend o (Op op m)=Op op (o:m)
  mappend (Op op m) o=Op op (m++[o])
  mappend a b=Op List [a,b]

sameAtom :: Algo -> Algo -> Bool
sameAtom Und Und=True
sameAtom (Bool _) (Bool _)=True
sameAtom (Nom _) (Nom _)=True
sameAtom (Lit _) (Lit _)=True
sameAtom (Op a ma) (Op b mb)=a==b&&(and $map (\(a',b')->sameAtom a' b') $zip ma mb)
sameAtom Pref Pref=True
sameAtom _ _ = False

nomVal:: Algo -> Nr
nomVal (Nom x)=x

------------------------
-- grouping operators --
-- ================== --

-- by priority
setOps,logicOps,sequenceOps,arithmeticOps,geometricOps,exponentialOps,functionOps::[Ops]
setOps =[List,Set,Params]
logicOps =[And,Or,Not]
sequenceOps=setOps++logicOps
arithmeticOps =[Sub,Sum,Neg,Pos,PosOrNeg]
geometricOps =[Mul,Div]
exponentialOps=[Exp,Root,Log,Fact]
functionOps=[Func,Neg,Pos]

-- by sample type
unaryCalc,partialCalc,binaryCalc::[Ops]
unaryCalc=[Not,Neg,Pos,Fact,Floor,Round] -- have unary sample
partialCalc=[Root,Log] -- can have omitted value
binaryCalc=[Or,And,Sum,Sub,Mul,Div,Exp,Root,Log] -- have binary sample

-- by number of elements
unaryOps,partialOps,listOps::[Ops]
unaryOps=[Not,Neg,Pos,Fact,PosOrNeg] -- (1,1)
partialOps=[Root,Log,Equals,Greater,Less,GreaterOrEqual,LessOrEqual,Equiv,Implic] -- (1,2)
listOps=[Set,Or,And,Sum,Sub,Mul,Div] -- (2,..)

-- Expr Operators, generate
xformOps,exprOps,equatOps,resolOps,resolSteps,procOps,parallelOps,paramsOps,envOps::[Ops]
xformOps=[Neg,Pos,PosOrNeg,Sum,Sub,Mul,Div,Exp,Root,Log,Fact,Func,InvFunc,DerivedFunc] -- can be applyed to equations as a convenience
exprOps=[List,Set,Not,Or,And,Neg,Pos,Sum,Sub,Mul,Div,Exp,Root,Log,Fact,Func,InvFunc,DerivedFunc]
equatOps=[Equals,Greater,Less,GreaterOrEqual,LessOrEqual,NotEqual,Relates,ElementOf,NotElementOf]
--exprOps=[List,Set,Not,Or,And,Neg,Pos,PosOrNeg,Sum,Sub,Mul,Div,Exp,Root,Log,Fact,Func,ElementOf]
--equatOps=[Equals,Greater,Less,GreaterOrEqual,LessOrEqual,Relates,ElementOf]
resolOps=[Equation,System,Document]
resolSteps=[Equiv,Implic]
procOps=[Resol,Simpl]
parallelOps=[Document,System]
paramsOps=[Root,Log,Set,Func,InvFunc,DerivedFunc,Sentence]
envOps=[List,Set,Func,InvFunc,DerivedFunc]
rawSequenceOps=[List,Set]
funcs=[Func,InvFunc,DerivedFunc]
opSetOps=[Union,Intersect,Contained,Contains]
binaryOps=[SuchThat]

-- comutative ops
comutOps::[Ops]
comutOps=[Set,Or,And,Sum,Mul]--,Equation]
-- equations can only comut if = or <> (<,>,>=,<=,∈,...) need special treatment on comut

signalOps::[Ops]
signalOps=[Neg,Pos,PosOrNeg]

canComut::Ops->Bool
canComut op= elem op comutOps

quant :: Num t => Ops -> (t, Int)
quant op
  | elem op unaryOps=(1,1)
  | elem op binaryOps=(2,2)
  | elem op partialOps=(1,2)
  | op==Set=(0,maxBound::Int)
  | otherwise=(2,maxBound::Int)

neutral :: Ops -> Maybe Algo
neutral Sum=Just$Nom 0
neutral Mul=Just$Nom 1
-- neutral Exp=Just$Nom 1
neutral Root=Just$Nom 1
neutral _=Nothing

inverse :: Ops -> Ops
inverse Sum=Sub
inverse Mul=Div
inverse Sub=Sum
inverse Div=Mul
inverse Exp=Root
inverse Neg=Neg
inverse Equiv=Equiv
inverse Func=InvFunc
inverse InvFunc=Func
inverse Greater=Less
inverse Less=Greater
inverse GreaterOrEqual=LessOrEqual
inverse LessOrEqual=GreaterOrEqual
inverse Equals=Equals
inverse System=System
inverse e=Identity --error $"Undefined inverse operation for "++show e

distOver::Prior->Prior->Bool
{-# INLINE distOver #-}
distOver Arithmetic Lists= True
distOver Geometric Lists= True
distOver Exponential Lists = True
distOver Arithmetic Logic= True
distOver Exponential Geometric = True
distOver Geometric Arithmetic = True
distOver _ _ = False

-- EOF --
