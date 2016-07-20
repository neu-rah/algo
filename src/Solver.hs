module Solver where

import AlgData
import Utils
import AlgAux
import Calc
import Rules
import Steps
import Context
--import Trans
import Evid
import Lib.Debug
import Neighbor
import Intervals
import AlgParser

import Data.Maybe
import Control.Applicative
import qualified Data.Map as Map

evids (Op Resol m)=evids $last m
evids (Op Equiv [o])=evids o
evids (Op Implic [o])=evids o
evids (Op Simpl m)=Nothing --evids $last m
evids (Lit _)=Nothing
evids e@(Op Equation _)
  | lits #=1=_evid (head lits) e
  | otherwise = Nothing --_evid (head lits) e -- ok just use one of them... for now
  where lits=literals e
evids _ = Nothing

(>·>) :: Maybe Algo -> (Algo -> Maybe Algo) -> Maybe Algo
(>·>) e o = e·>proc (steps o)

(>~>) :: Maybe Algo -> (Algo -> Maybe Algo) -> Maybe Algo
(>~>) e o = e~>proc (steps o)

(>··>) :: Maybe Algo -> [Algo -> Maybe Algo] -> Maybe Algo
(>··>) e o = e··>map (\i->proc (steps i)) o

(>~~>) :: Maybe Algo -> [Algo -> Maybe Algo] -> Maybe Algo
(>~~>) e o=e~~>map (\i->proc (steps i)) o

(>·|·>):: Maybe Algo -> [Algo -> Maybe Algo] -> Maybe Algo
(>·|·>) e s=run e (>··>) s

(>//>) e l=steps ((//>l) . Just) e

a<·<b=b>·>a
a<~<b=b>~>a
a<··<b=b>··>a
a<~~<b=b>~~>a
a<·|·<b=b>·|·>a

(<··>)::Algo->(Algo->Maybe Algo)->Maybe Algo
(<··>) o@(Op op m) f
  |null sok=Nothing
  |otherwise=Just$Op rop ((Op op (algRebuild (map (flt<$>) s) m)):rm)
  where
    s=map f m
    sok=filter ok s
    (Op rop rm)=foldl rs (Op Equiv []) s
    rs s@(Op sop c) (Just e@(Op op (o:oo)))
      | elem op resolSteps = Op (resolPrec sop op) (c++oo)
      | otherwise=s
    rs s _ =s
    flt (Op Implic (o:_))=o
    flt (Op Equiv (o:_))=o
    flt o=o

--generic  list of deltas over a list of integers
diff::[Int]->[Int]
diff (a:o@(b:oo)) = (abs(b-a):diff o)
diff _=[]

-- accumulative deltas with a ceilling
accumDiff::Int->[Int]->[Int]
accumDiff m (a:o@(b:oo)) = (abs(b-a):_accumDiff m (abs(b-a)) o)
  where
    _accumDiff m n (a:o@(b:oo))
      | (n+abs(b-a))<m = ( (n+abs(b-a)) : (_accumDiff m (n+abs(b-a)) o) )
      | otherwise = (n+abs(b-a):_accumDiff m 0 o)
    _accumDiff _ _ _=[]
accumDiff _ _=[]

-- condensates an operator (resolution) by skipping minor plex change steps
resume n r@(Op op m@(o:oo))=
  Op op ((o:(map snd $ filter ((>=n) . fst) $init$zip (diff$map plex m) oo))++[last m])

-- condensates an operator (resolution) with accumulative plex deltas
aresume n r@(Op op m@(o:oo))=
  Op op ((o:(map snd $ filter ((>=n) . fst) $init$zip (accumDiff n$map plex m) oo))++[last m])

enunciateOf :: Algo -> Algo
enunciateOf (Op Document m)=Op Document $map enunciateOf m
enunciateOf (Op Resol (o:_))=o
enunciateOf (Op Simpl (o:_))=o
enunciateOf e=e

-- verify a resolution
verify:: Algo->Maybe Algo
verify doc@(Op Document _) = solveM emptyCtx (repVars (getVars doc) $enunciateOf doc)
verify e@(Op Resol ((Op System _):_)) = solveM emptyCtx $repVars (getVars e) $enunciateOf e
  {-= solveM emptyCtx (repVars concl (head $ membersOf $ last $ membersOf $ chk)) -- exclude initial numeric definitions
  where
    concl=getVars e
    ops=map (\(a,b)->Op Equation [a,Op Equals [b]]) $Map.toList concl
    chk=solve $Op System $concat [ops,membersOf $head$membersOf e]-}

verify e@(Op Resol ((Op Equation _):_))
  = solveM concl (Op And tests)
  where
    concl=getVars e
    p=map (Map.fromList) $map (zip (Map.keys concl)) $prods $Map.elems $Map.map membersOf concl
    tests=map (\r->r (enunciateOf e)) (map repVars p)

verify (Op Equation (a:b:[]))
  -- | solved==(Just a)=Just$Bool False
  | ok solved=Just$Bool False
  | otherwise=Just$Bool $b==last m
  where
    solved=solve' emptyCtx a
    (Just (Op Simpl m))=solved

verify e=Nothing --error $"can not verify "++show e

--detecting an assignment (walker) should take an independent action to be used by this
flatWalk::(Algo->Algo)->Algo->Algo
flatWalk f (Op op m)=f$Op op $ map (flatWalk f) m
flatWalk f o = f o

shallowWalk :: (Algo -> Algo) -> Algo -> Algo
shallowWalk f (Op op m)=f$Op op $ map f m
shallowWalk f o = f o

solved::Algo->Algo
solved a = conclusion $ solve a

_solved::Ctx->Algo->Maybe Algo
_solved vars a
  | ok d=Just $ head $ membersOf $ last $membersOf $ fromJust d
  | otherwise=Nothing
  where d=_solve vars a

-- =============================================================================
-- solve expression and return the sequence steps, this can latter be sumarized
-- this is the successive request cycle of solve
solve::Algo->Algo
solve o=fromJust $ solveM emptyCtx o

solveM::Ctx->Algo->Maybe Algo
solveM _ doc@(Op Document _)
  = (solveM defs =<< (D_SOLVER,"rebuild doc:")←(rebuild (steps (solve' defs)) doc))<|> Just doc -- inner step composition
  where defs=getVars doc -- was getDefs but Documents compose in deff. way.. so getVars
solveM _ (Op Resol (Op Resol _:_))=error "solveM nested resolution"
solveM defs o =(solveM defs =<< ((D_SOLVER,show o++" solve':")←(steps (solve' defs) o)))<|> Just o-- outter step composition

-- contextualized solve, at this point new variables (coclusions) are checked
-- before procedding to solve step functions
solve'::Ctx->Algo->Maybe Algo
solve' vars o
  = ((D_SOLVER,show o++" solving:")←(_solve localVars o))
  <|> ((D_SOLVER,show o++" repDefs:")←(neighbourMove=<<(useCtx localVars o)))
  where
    localVars=(D_SOLVER,show o++" localVars:")←(getVars' vars o)
    --defVars=(D_SOLVER," defVars:")←(fromVars$defs)

-- a simpler "solved" to be used when resolving variable values concurrency
-- this simple version MUST not do variable expanssion/replacement
varSolved::Algo->Algo
varSolved  o = fromJust(((Just o)·>(_solve emptyCtx))<|>(Just o))

-- ******************** solving step functions
-- this functions should return a single step of solving.
-- usually without stepping operator, unless given by solving mechanisms
-- (calc, simplify, evid, etc..)
_solve::Ctx->Algo->Maybe Algo
-- TODO: solving with just the last member invalidates any redundancy check efforts!
-- so do NOT activate this!
-- activated for parallel ops because redundancy checks does not include them yet.
_solve vars e@(Op Resol m@(_:_))
  =case lm of
    (Op _ (Op System _:_)) -> (D_SOLVER,"System resolution:")←(_solve vars lm)
    (Op _ (Op And _:_)) -> (D_SOLVER,"Logic And resolution:")←(_solve vars lm)
    _ -> __solve vars e
  where lm=last m
_solve vars e@(Op Simpl m@(_:_))
  =case lm of
    (Op _ (Op System _:_)) -> (D_SOLVER,"System simplification:")←(_solve vars lm)
    (Op _ (Op And _:_)) -> (D_SOLVER,"Logic And simplification:")←(_solve vars lm)
    _ -> __solve vars e
  where lm=last m
_solve vars e = __solve vars e

__solve::Ctx->Algo->Maybe Algo
__solve vars e@(Op Equiv (o:oo))=_solveResolStep vars e
__solve vars e@(Op Implic (o:oo))=_solveResolStep vars e
__solve vars e@(Op System _)=_solveParallelOps vars e
__solve vars e@(Op And _)=_solveParallelOps vars e
__solve vars e@(Op Equation _)=(D_SOLVER,"solving equation "++show e++" to ")←((Just e)//>[calc,simplify,evids,useCtx vars])
__solve vars e=(Just e)//>[calc,simplify,evids,useCtx vars]

_solveParallelOps vars e=(e<··>_solve vars) <|> ((Just e)//>[calc,simplify,useCtx vars])
_solveResolStep vars e@(Op op (o:oo))=mkRes(r)<++|oo--TODO: also solve conditions oo
  where
    r=(D_SOLVER,show e++" _solveResolStep:")←(_solve vars o)
    mkRes res@(Just re@(Op op m))
      | elem op resolSteps = res
      | otherwise=Just $ Op Equiv [re]
    mkRes (Just e)=Just $ Op Equiv [e]
    mkRes _=Nothing

exaustCalc::Algo->Algo
exaustCalc o=fromJust$last$takeWhile ok $iterate (calc=<<) (Just o)
