{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}

module Rules where

--import GHC.Stack
import Data.Maybe
import Data.List
import qualified Data.Map as Map
--import Debug.Trace
import Control.Applicative
import {-# SOURCE #-} Solver
import {-# SOURCE #-} Evid

import AlgData
import AlgParser
import Calc
import AlgShow
import Utils
import Lib.Debug
import Lib.Colors
import AlgAux
import Intervals
import Context
import {-# SOURCE #-} AlgFile
-- ********************************************************************
-- The RULES system

consistentRule::Algo->Bool
consistentRule (Op op (r:[Op _ o]))
  | op == Resol || op == Equation = isNothing $ chkRule emptyCtx (last o) r False
  | otherwise=False
consistentRule _ = False

--simplRules
genSimplRules,canonRules :: [Algo]
(simplRules,canonRules)= (partition consistentRule genSimplRules)
genSimplRules=[
  "a*(1/b)=a/b"
  ,"(a&a)=a"
  ,"(a|a)=a"
  --,"-(#*x)=(-#)*x"
  --,"#a*x+#b*x=(#a+#b)*x"
  --"-(a+b)=(-a)+(-b)",
  --"-(a*b)=)(-a)*b",
  --"(x∈a)&(x∈b)=x∈(a∩b)",
  ,"0-a=(-a)"
  ,"a/b=0<=>a=0" -- inconsistent but usefull
  ,"(-(-a))=a", "-(a-b)=b-a","(+/-(+/-a))=(+/-a)"
  ,"(-1)*x=(-x)","x/(-1)=(-x)"
  --,"-b+a=a-b" --TODO: this thing messes up inverse function expansion when f(x)=x-1 then f⁻(x)=x-1 also!!!! WTF!
  ,"0/a=0"
  ,"a-a=0", "a/a=1"
  ,"a+a=2a","x*x=x^2"
  ,"a^1=a","a^0=1"

  ,"n^a*(1/n)=n^(a-1)"
  ,"n/n^a=n^(1-a)"

  ,"root(n,(-1))=n^(-1)"

  ,"a*?+b*?=((a+b)*?)"
  ,"a*x-b*x=((a-b)*x)"
  ,"(k/b)*(j/k)=j/b"
  ,"(a*x)/(b*x)=a/b" --inconsistent and annoyng rule
  ,"(x/a)/(x/b)=b/a" --annoyng rule, always match.. then filtered by nochange
  ,"(a/x)/(b/a)=(a²)/(b*x)"
  ,"a/b/c=a/(b*c)"

  ,"(+/-a)/b=(+/-(a/b))"
  ,"a+(+/-b)=((a+b)|(a-b))"
  ,"a*(+/-b)=(+/-(a*b))"
  ,"a/(+/-b)=(+/-(a/b))"
  ,"a/(-b)=(-(a/b))"
  ,"(-a)/b=(-(a/b))"
  ,"a=(b|c)<=>((a=b)|(a=c))"-- TODO: use Relates (<->) is not working ok
  ,"(b|c)/a=((b/a)|(c/a))"
  ,"a^b*a^c=a^(b+c)"
  ,"a^b/a^c=a^(b-c)"
  ,"a^b*a=a^(b+1)"
  ,"a^b/a=a^(b-1)"
  ,"a*x^2+b*x+c<->0<=>x<->(-b+∓(root((b^2-4*a*c),2)))/(2a)"
  ,"a*x^2+b*x+c=k<=>a*x^2+b*x+c+(-k)=0"
  ,"(x*ℕ∩ℕ)=((x*ℕ),(x∈ℕ))"
  --,Op Resol [Op System ["x ∈ X","x ∈ Y"],Op Equiv ["x ∈ (X∩Y)"]]
  ,"((x ∈ X) & (x ∈ Y)) <=> (x ∈ (X∩Y))"
  ,"((x ∈ X) & (x ∈ Y)) <=> (x ∈ (X∩Y))"
  ,"((x ∈ X) | (x ∈ Y)) <=> (x ∈ (X∪Y))"
  ,"(n ∈ {f(x):(v ∈ X)})<=>(v∈X)"
  ,"(((x*n)∈ℕ)&(n∈ℕ))<=>((x*ℕ∩ℕ)<>{})"
  ,"{(x^n/n):(n∈ℕ)}∩ℕ={(x^(x^i-i)):(i∈ℕ)}"
  ,"a<->(b,True)<=>a<->b"
  ,"a*x-x/b=(a*b*x-x)/b"
  ,"a*x+x/b=(a*b*x+x)/b"
  ,"x*(a|b)=(x*a|x*b)"
  ,"0+(-x)=(-x)"
  ,"cos⁻(-cos(x))=x+180"
  ,"x<n+inf<=>x<=n"
  ,"x<=n-inf<=>x<n"
  ,"x>n-inf<=>x>=n"
  ,"x>=n-inf<=>x>n"
  ]

combinations :: (Num a, Eq a) => a -> [t] -> [[t]]
{-# INLINE combinations #-}
combinations 0 _  = [ [] ]
combinations n xs = [ y:ys|y:xs'<-tails xs,ys<-combinations (n-1) xs']

-- rules system
simplify :: Algo -> Maybe Algo
simplify (Solver defs vars books doc)=(Solver defs vars books)<$>simplify doc
simplify o
  -- = proc <|> _simplify o canonRules True
  = (calc=<<(proc <|> scr))<|>proc
  -- = (calc=<<(proc <|> _simplify o canonRules True))<|>toRange o<|>proc
  -- =(exaustCalc=<<( proc <|> _simplify o canonRules True))<|>proc
  where
    scr'=_simplify o canonRules True
    scr=if null scr' then Nothing else head scr'
    proc'=filter isJust $ _simplify o simplRules False
    proc=if null proc' then Nothing else head proc'

--e=Op Simpl ["k",Op Equals ["2a"],Op Equals ["a+a"]]

chkRedundant (Just r) e
  = (D_RULES,"checking "++show r++" "++info r++" as redundant on "++show e++" ")←v
  where v=or $ map (chkRed r) $membersOf e
chkRed r o@(Op rop (e:_))=(elem rop (resolSteps++equatOps) && strictEq r e)|| strictEq r o
chkRed r o= strictEq r o

_simplify :: Algo -> [Algo] -> Bool -> [Maybe Algo]
_simplify (Op SuchThat [_,Bool False]) _ _=[] --Nothing
_simplify e@(Op Resol steps) rules strict
  | dInfo(D_RULES,show e++" simplify "++(show$last steps))=undefined
  | not (isAlgOp (last steps))= [] --Nothing
  | otherwise=filter (\ð->not$chkRedundant ð e) $res
  where
    (Op sop (r:c))=last steps
    res=filter isJust$_simplify r rules strict

_simplify o@(Op Simpl steps) rules strict
  =filter (\ð->isJust ð && (not$chkRedundant ð o)) $_simplify r rules strict
  where (Op sop (r:c))=last steps

_simplify (Op Equation (_:[(Op _ (_:[Bool False]))])) _ _=[]
_simplify o@(Op Equation (r:m:[])) rules strict
  = filter (\(Just ð)->not$strictEq o ð || strictEq o (fromJust(Just ð~>calc))) $filter isJust
  $ (map (\ð->Just$Op Equiv [Op Equation [fromJust ð,m]]) (filter ok $ _simplify r rules strict))
  ++ (map (\ð->Just$Op Equiv [Op Equation [r,fromJust ð]]) (filter ok $ _simplify m rules strict))
  ++ (filter ok $applyRules emptyCtx o rules strict)

_simplify target rules strict
  = filter (\(Just ð)->not$strictEq target ð || strictEq target (fromJust(Just ð~>calc)))
  $ filter ok $ applyRules emptyCtx target rules strict

tryGroups :: Ctx -> Algo -> Algo -> Bool -> Maybe Algo
tryGroups vars target@(Op op m) rule@(Op Equation rm@(e:(Op sop resm):[])) strict
  | (not $canComut op) && (ok morphed)
    = (D_RULES,"tryGroups ")←(tryGroups vars (algTrace(D_RULES,show target++"fitting "++show rule++" morphed to ") $fromJust morphed) rule strict) --Nothing -- TODO: can try partials?
  | (not $canComut op) =  Nothing --head$map ((\o->Op op [Op op o]) <$>) (map permutations m)-- TODO: comut members!
  | null tries=Nothing
  -- | TODO: add divergence! ... somewhere reducing to lowest complexity result
  | otherwise=algTrace (D_GROUP,"tryGroups on "++show target++" matching "++show rule++" rsulting in "++show final) final
  where
    perms=map (splitAt (length rm)) (permutations m)
    (groups,rem)=unzip perms
    ops=map (Op op) groups
    tries=nub $ filter (ok . fst) (zip (map (\o->_applyRule vars o rule strict) ops) rem)
    morphed=(D_MORPH,show target++" morphing to ")←morph vars target
    len=length $membersOf e
    final=Just (algInsert (fromJust$fst $ head tries) (Op op (snd $ head tries)))

applyRules::Ctx -> Algo->[Algo]->Bool->[Maybe Algo]
{-# INLINE applyRules #-}
applyRules vars target rules strict=(D_RULES,"applyRules:")←(map (\o->applyRule vars target o strict) rules)

-------------------------------------------------------------------------------
applyRule::Ctx -> Algo->Algo->Bool->Maybe Algo
--applyRule vars target@(Op _ t@(_:(Op op _):_)) rule@(Op Resol (Op Equation (a:(Op Relates r):rr):rrr))
applyRule vars target@(Op _ t@(_:(Op op _):_)) rule@(Op Resol ((Op Equation (a:(Op Relates r):rr)):( Op e ((Op Equation (ra:(Op Relates rrr):[])):[])):[])) strict
  | elem op equatOps =(D_RULES,"apply relational rule ")←(applyRule vars target nr strict)
  | otherwise= Nothing
  where
    nr=(D_RULES,show rrr++" rewriting relational rule to ")←(Op Resol ((Op Equation (a:(Op op r):rr)):( Op e ((Op Equation (ra:(Op op rrr):[])):[])):[])) -- rewrite the rule

applyRule vars target@(Op top _) rule@(Op Resol (match@(Op Equation m):steps)) strict
  | ok chk&&(target/=fromJust chk)
    = algTrace (D_RULES,"1º applyRule "++show rule++" to "++show target++" resulting in "++show chk) chk
  | otherwise= Nothing
  where
    chk=_applyRule vars target rule strict

applyRule vars target@(Op top _) rule@(Op Resol (m:steps)) strict
  | ok chk&&(target/=fromJust chk)
    = algTrace (D_RULES,"2º applyRule "++show rule++" to "++show target++" resulting in "++show chk) chk
  | otherwise= Nothing
  where
    chk=_applyRule vars target rule strict

applyRule vars target@(Sets (SetExpr te td)) rule@(Op Equation ((Sets (SetExpr re rd)):(Op Equals (res:[])):[]) ) strict
  =_applyRule vars target rule strict

--sets can generate a LOT of combinations in the rule system... let them be resolved by calc or ignored forever
--TODO: add special case when rule is also a set or list
--applyRule _ t@(Op Set _) r _ = Nothing
--applyRule _ t@(Op List _) r _ = Nothing

applyRule vars target@(Op top tm) rule@(Op Equation (m:r:[])) strict
  | dInfo (D_RULES,"applyRule "++show rule++" to "++show target) = undefined
  | ok chk && (not $ strictEq target (fromJust chk)) --target/=fromJust chk)
    =(D_RULES,"2º appplyRule "++show rule++" vars:"++show vars++" to "++show target++" resulting in "++show chk)
    ←chk
  | otherwise=(D_RULES,"resize? ")←
      (if (D_RULES,"target lenght > rule length ")←(length tm>(length $membersOf m))
      then tryGroups vars target rule strict
      else Nothing)
  where
    chk=(D_RULES,"chk: ")←(_applyRule vars target rule strict)
    swapNegs e@(Op Equation [Op Sum sm,Op Equals em])
      =(D_RULES,show target++" swapping to ")←Nothing
    swapNegs _=Nothing

applyRule _ _ _ _ = Nothing

replaceOp::Algo->Ops->Algo
{-# INLINE replaceOp #-}
replaceOp (Op _ m) op=(Op op m)
replaceOp x _=x

propagateRule :: Ctx -> Algo -> Algo -> Bool -> Maybe Algo
propagateRule vars target@(Op System m) rule strict
  | not (filter ok prop#>0) =Nothing
  | steps#=0 = Just$ Op Equiv [Op System proc]
  | steps#=1 = Just$ Op (fromJust$getOp$head steps) [Op System $ map stepLess proc]
  where
    prop=map (\o->applyRule vars o rule strict) m
    proc=flat System [] $ zipWith (\a b->if ok a then fromJust a else b) prop m
    steps= filter isStep proc
    isStep (Op op _)=elem op resolSteps
    isStep _ = False
    stepLess e@(Op o (m:[]))
      | isStep e = m
      | otherwise = e
    stepLess o = o

propagateRule vars target@(Op op m) rule strict
  | (filter ok prop)#>0 = Just$ Op op $ proc
  | otherwise=Nothing
  where
    prop=map (\o->applyRule vars o rule strict) m
    proc=flat op [] $ zipWith (\a b->if ok a then fromJust a else b) prop m

_applyRule::Ctx -> Algo->Algo->Bool->Maybe Algo -- ===========================================
_applyRule vars target@(Sets (SetExpr te td)) (Op Equation (rule@(Sets (SetExpr re rd)):res@(Op _ (_:[])):[]) ) strict
  | dInfo (D_RULES,"sets as rules, v:"++show v++" te:"++show te++" re:"++show re++" "++show v)=undefined
  | otherwise=(\o->useCtx o res) =<< v
  where v=_chkRule vars target rule strict

_applyRule vars target@(Op Resol steps) rule strict=applyRule vars (last steps) rule strict
_applyRule vars target@(Op Simpl steps) rule strict=applyRule vars (last steps) rule strict

_applyRule vars target@(Op top _) rule@(Op Resol (match:steps)) strict
  -- | top /= Equation = prop
  | otherwise=chk <|> prop
  where
    chk=__applyRule vars target rule strict
    prop=propagateRule vars target rule strict

_applyRule vars target@(Op top tm) rule@(Op Equation (m@(Op rop rm):r:[])) strict
  | length tm /= length rm =prop -- && not(rop==Func||rop==InvFunc)=prop
  | otherwise=chk <|> prop
  where
    chk=__applyRule vars target rule strict
    prop=propagateRule vars target rule strict

_applyRule v t r strict=__applyRule v t r strict

__applyRule::Ctx -> Algo->Algo->Bool->Maybe Algo
__applyRule vars target@(Op top _) (Op Resol (match:steps)) strict
  | dInfo(D_RULES,show vars ++ " __applyRule resol "++show match++" on "++show target)=undefined
  | isNothing proc=Nothing
  | otherwise = (D_RULES,"__applyRule resol "++show match++" on "++show target++" to:")←(Just rep)
  where
    proc=(D_RULES,"__applyRule proc:")←((chkRule) vars target match strict)
    rep = (D_RULES,"__applyRule rep:")←(repVars (fromJust proc) (last steps))

__applyRule vars target@(Op top _) rule@(Op Equation (match:(Op rop (r:rr)):[])) strict
  | dInfo(D_RULES,"__applyRule Equation "++show match++" on "++show target)=undefined
  | isJust proc && (rr==[] || chked)
    = (D_RULES,"__applyRule:"++show rule++" with vars:"++show vars++" over "++show target++" result:")
    ← (proc)
  | otherwise=Nothing
  where
    rep=chkRule vars target match strict
    proc=(\o->Just$repVars o r) =<< (rep)
    chked=chk((D_RULES,"\t"++show rr++" chk:")←(_solved (fromJust rep) (Op System rr)))
    chk (Just(Op System ((Bool True):[])))=True
    chk (Just(Bool True))=True
    chk _=False

__applyRule _ target@(Op top _) r _= error ("rules MUST be equations, actual "++show r)

__applyRule _ _ _ _= Nothing


--------------------------------------------------------------------------------
-- check operators =============================================================
liberalSizeTo::Algo->Int->Maybe Algo
liberalSizeTo o@(Op Div [m]) 2=Just$Op Div [m,1]
liberalSizeTo o@(Op Exp [m]) 2=Just$Op Exp [m,1]
liberalSizeTo o@(Op Root [m]) 2=Just$Op Exp [m,1]
liberalSizeTo o n=sizeTo o n

sizeTo::Algo->Int->Maybe Algo
sizeTo o@(Op op m) sz
  | (snd $quant op)<sz = Nothing
  | otherwise=final <* n
  where
    n=neutral op
    d= sz - length m
    final=Just $Op op (m ++ (replicate d (fromJust n)))
sizeTo _ _=Nothing

-- TODO: checkRule need to try groupping even on strict mode! 2016.Mar
chkRule:: Ctx -> Algo -> Algo -> Bool -> Maybe Ctx
{-# INLINE chkRule #-}
chkRule vars target rule strict
  | dInfo(D_RULES,"chkRule "++show target++"→ "++show rule)=undefined
  | null res=Nothing
  | otherwise=
    (D_RULES,show rule++" over "++show target++" chkRule with vars:"++show vars++" to:")
    ←head res
  where res=filter ok $map (\o->_chkRule vars target o strict) $ mutex rule

-- transform expression into equivalent of alternative type
morph::Ctx->Algo->Maybe Algo
morph vars o = (D_MORPH,show o++" Morphing to")←(_morph vars o)
_morph::Ctx->Algo->Maybe Algo
-- consider case of negative multiplication, passing the negation to the interior
-- however this is best done with target after neutral insertion...
_morph vars (Op Neg ((Op Mul gm@(_:_)):[]))
  =   (pref >> (Op Mul <$> (repFst (==np) (\_->fromJust pref) gm))) -- a negated preference is present?
  <|> (Op Mul <$> (repFst (\o->isNom o && (nomVal o)<0) (Nom . negate . nomVal) gm)) -- a negative number is present?
  <|> (Op Mul <$> (repFst isNom (\(Nom o)->Nom (-o)) gm)) -- any other number?
  <|> (Op Mul <$> (repFst (\o->(Just o)/=pref) ((Op Neg).(:[])) gm)) -- ok, just negate the first nom preference
  where
    pref=Map.lookup Pref vars
    np=Op Neg [fromJust pref]

_morph _ (Op Sub (o:oo))=Just$ Op Sum (o:(map (\e->Op Neg [e]) oo))
_morph _ (Op Div ((Nom _):(Nom _):[]))=Nothing
_morph _ (Op Div (_:_:[]))=Nothing
_morph _ (Op Div (o:oo))=Just$ Op Div [o,Op Mul oo]
_morph _ (Op Root (b:[]))=Just$Op Exp [b,Op Div [Nom 1,Nom 2]]
_morph _ (Op Root (b:i:[]))=Just$Op Exp [b,Op Div [Nom 1,i]]
_morph _ _ = Nothing

_grouping::Int->Algo->[Algo]
_grouping n o@(Op op m)
  | length m<n=[o]
  | otherwise=map (\(a,b)->Op op (a++[chkQuant$Op op b])) $ map (splitAt (n-1)) $ permutations m

trySeq:: (Algo->Maybe r) -> [Algo] -> Maybe r
trySeq _ []=Nothing
trySeq op (o:oo)=op o <|> trySeq op oo

_chkRule:: Ctx -> Algo -> Algo -> Bool -> Maybe Ctx
_chkRule vars target@(Op op m) rule@(Op _ rm) strict=
  (D_RULES,show target++" _chkRule "++show rule++" to:")
  ←(if canComut op then trySeq (\ð->ls_chkRule vars ð rule strict) (_grouping (length rm) target) else ls_chkRule vars target rule strict)
_chkRule vars target rule  strict=
  (D_RULES,show target++" _chkRule "++show rule++" to:")
  ←(ls_chkRule vars target rule strict)

chkStrictRule:: Ctx -> Algo -> Algo -> Maybe Ctx
chkStrictRule vars target rule = ls_chkRule vars target rule True

ls_chkRule:: Ctx -> Algo -> Algo -> Bool -> Maybe Ctx
ls_chkRule vars target@(Op Neg [n@(Op top t)]) rule@(Op rop r) strict
  | dInfo(D_RULES,"ls_chkRule "++show rule++" on "++show target)=undefined
  | ok dir= (D_RULES,show target++" matched to "++show rule++" to")←dir
  | rop==Neg = proc
  | not (ok proc)=Nothing
  | otherwise =
    (D_RULES,show target++" handle negation here to match "++show rule++" "++show proc++" sugested form "++show (Op Neg [xlat])++" generates infinite cycle!\n"++" xformed to "++show xlat)
        ← ((\ð->ls_chkRule vars ð rule strict)=<<(morph (fromJust proc) (Op Neg [xlat])))
  where
    dir=_chkRule' vars target rule False
    proc=_chkRule' vars n rule False
    pref=Map.lookup Pref vars
    xlat= repVars (fromJust proc) rule

ls_chkRule
  vars
  target@(Op Equation [n,Op ElementOf [tt@(Sets (SetExpr te td))]])
  rule@(Op Equation [n',Op ElementOf [rr@(Sets (SetExpr re (Op Equation [v,rd@(Op ElementOf d)]) ))]]) strict
  | dInfo(D_RULES,show vars ++" ls_chkRule ElementOf Set "++show rule++" on "++show target)=undefined
  | otherwise = (D_RULES,"ElementOf Sets def ")←vins
  where
    proc=(D_RULES,"proc:")←((Just .(Map.insert n' n)) =<<(ls_chkRule vars tt rr strict))
    vdef=(D_RULES,"vdef:")←((Map.lookup v) =<< proc)
    (Just vlits)=(D_RULES,"vlits:")←(literals<$>vdef)
    commonVars=(D_RULES,"commonVars:")←(intersect vlits (literals n'))
    n''=head$if null commonVars then vlits else commonVars
    newdef=(D_RULES,"commonVars:"++show commonVars++" newdef:")←((Just . (repVars (Map.fromList[(n'',n)])))=<< vdef)
    vins=(D_RULES,"vins")←(((Just . (Map.insert v)) =<<newdef)<*>proc)

-- sets {f(x):v ∈ X} ----------------------------------------------------------

ls_chkRule vars target@(Sets (SetExpr te td)) rule@(Sets (SetExpr re rd@(Op Equation [v,Op ElementOf d]))) strict
  =(D_RULES,show target++"<->"++show rule++" _chkRule between Sets ")
    ←(
      if vlits#>0
      then (if expansion#>1 then vins else Nothing)
      else proc
    )
  where
    proc=((Just . Map.union)=<<ls_chkRule vars te re strict)<*>(ls_chkRule vars td rd strict)
    vdef=(Map.lookup v) =<< proc
    (Just vlits)=literals<$>vdef
    expansion=takeWhile ok $iterate ((useCtx (fromJust proc))=<<) (algo "f⁻(n)")
    expanded=last$expansion
    -- TODO: check and eventually rename remaining rule variables to avoid colision!
    newdef=(Just . (repVars (Map.fromList[(head vlits,fromJust expanded)])))=<< vdef
    vins=((Just . (Map.insert v)) =<<newdef)<*>proc

{-
ls_chkRule vars target@(Sets (SetExpr te td)) rule@(Sets (SetExpr re@(Op Func fd@(fn:[fp])) rd@(Op Equation [v,Op ElementOf d]))) strict
  =(D_CTX,show target++"<->"++show rule++" _chkRule between Sets ")
    ←(
      if ok vdef && vlits#>0
      then (D_CTX,"ok vdef && vlits#>0:")←(if expansion#>0 then vins else Nothing)
      else (D_CTX,"proc:")←proc
    )
  where
    proc=(D_RULES,"proc:")←(((Just . Map.union)=<<ls_chkRule vars te re strict)<*>(ls_chkRule vars td rd strict))
    (Just jp)=proc
    vdef=(D_RULES,"vdef:")←((Map.lookup v) =<< proc)
    (Just vlits)=(D_RULES,"vlits:")←(literals<$>vdef)
    def=(D_RULES,show fd++" def:")←((\ð->Map.fromList[(Op Func fd,ð)])<$>(Map.lookup (Op Func fd) jp))
    np=(D_RULES,"np:")←(useCtx (fromJust def) (Op InvFunc fd))
    expansion=(D_RULES,"expansion:")
      ←(takeWhile ok $iterate ((useCtx (fromJust proc))=<<) np)
    expanded=(D_RULES,"expanded:")←(last$expansion)
    -- TODO: check and eventually rename remaining rule variables to avoid colision!
    newdef=(D_RULES,"newdef:")←((Just . (repVars (Map.fromList[(head vlits,fromJust expanded)])))=<< vdef)
    vins=(D_RULES,"vins:")←(((Just . (Map.insert v)) =<<newdef)<*>proc)
-}
{-ls_chkRule vars target@(Sets (SetExpr te td)) rule@(Sets (SetExpr re@(Op Func fd@(fn:[fp])) rd@(Op Equation [v,Op ElementOf d]))) strict
  | dInfo(D_CTX,"vars:"++show vars++" "++show rule++" Set  ls _chkRule over  "++show target)=undefined
  | otherwise=(D_CTX,show target++"<->"++show rule++" ls_chkRule between Sets ")
    ←(
      if ok vdef && vlits#>0
      then (if expansion#>1 then vins else Nothing)
      else proc
    )
  where
    proc=(D_RULES,"proc:")←(((Just . Map.union)=<<ls_chkRule vars te re strict)<*>(ls_chkRule vars td rd strict))
    vdef=(D_RULES,"vdef:")←((Map.lookup v) =<< proc)
    (Just vlits)=(D_RULES,"vlits:")←(literals<$>vdef)
    expansion=(D_RULES,"expansion:")←(takeWhile ok $iterate ((useCtx (fromJust proc))=<<) (algo "f⁻(n)"))
    expanded=(D_RULES,"expanded:")←(last$expansion)
    -- TODO: check and eventually rename remaining rule variables to avoid colision!
    newdef=(D_RULES,"newdef:")←((Just . (repVars (Map.fromList[(head vlits,fromJust expanded)])))=<< vdef)
    vins=(D_RULES,"vins:")←(((Just . (Map.insert v)) =<<newdef)<*>proc)
-}
ls_chkRule vars target@(Op Func t) rule@(Op Func r) strict
  =(D_RULES,"function as rule over function!")←(_chkRule' vars target rule False)

ls_chkRule vars target@(Op top t) rule@(Op Func (fn:p1:p)) strict
  | dInfo(D_RULES,show rule++" _chkRule function over operator "++show target)=undefined
  | null tv=Nothing -- functions must have variables
  | (intersect tv p)#>0 = undefined -- has common variables... need some care?
  | length p /= length tv =Just$Map.fromList[(rule,target)]
  | otherwise =(D_RULES,show rule++" function as rule! over "++show target++" to:" )
    ← (Just$ Map.insert rule target vars)
  where
    tv=(D_RULES,"\tliterals:")←literals target

ls_chkRule vars target@(Op top t) rule@(Op rop r)  strict=_chkRule' vars target rule strict

ls_chkRule vars target rule@(Op rop r) strict
  | ok rsz = chkRule vars (fromJust rsz) rule strict
  | otherwise=Nothing
  where rsz=maybeBool (not strict) >> (sizeTo (Op rop [target]) $ length r)

ls_chkRule vars e rule@(Lit _) strict
  | isJust var = if ((fromJust var)==e) then Just vars else Nothing
  | otherwise=Just (Map.insert rule e vars)
  where
    var=Map.lookup rule vars

ls_chkRule vars t@(Nom _) r@(Numeric _) _=Just $ Map.insert r t vars

ls_chkRule _ (Nom _) Pref _=Nothing

ls_chkRule vars e rule@(Pref) strict
  | isJust var = if (fromJust var)==e then Just vars else Nothing
  | otherwise=Just (Map.insert rule e vars)
  where var=Map.lookup rule vars

-- generic expressions
ls_chkRule vars test rule _ = if test==rule then Just vars else Nothing

--common code
_chkRule' :: Ctx -> Algo -> Algo -> Bool -> Maybe Ctx
_chkRule' vars target@(Op top t) rule@(Op rop r) strict
  -- | dInfo(D_RULES,"_chkRule' "++show target++" → "++show rule)=undefined
  | top/=rop && not (top==System&&rop==And)= ((\f->chkRule vars f rule strict) =<< fake)
  | length t > length r =Nothing -- grouping is higher lever (for now)
  | length t<length r =
    if ok rsz
    then chkRule vars (fromJust rsz) rule strict
    else Nothing
  | otherwise = proc
  where
    proc=(D_MORPH,show target++"_chkRule "++show rule++" chkRule:")←(chkRuleOp vars rop t r strict)
    rsz=(D_MORPH,show target++"_chkRule "++show rule++" rsz:")←((maybeBool (not strict))>>(sizeTo target$length r))
    morphed=maybeBool (not strict)>>(D_MORPH,show target++"_chkRule "++show rule++" morphed:")←(morph vars target)
    fake=(D_MORPH,show target++"_chkRule "++show rule++" fake:")←(
      if isJust morphed then morphed
      else
        if (prior top>=Arithmetic) && (prior top/=Function) && (not strict)
          then sizeTo (Op rop [target]) $length r
          else Nothing)

------------------------------------------------------------------------
-- check operator (target and rule) members
chkRuleOp :: Ctx -> Ops -> [Algo] -> [Algo] -> Bool -> Maybe Ctx
{-# INLINE chkRuleOp #-}
chkRuleOp vars _ [] [] _ = Just vars
chkRuleOp _ _ [] _ _ = error "Should not reach this 1"
chkRuleOp _ _ _ [] _ = error "Should not reach this 2"

-- if a rule literal variable appears multiple times then it can not match to the operator neutral!
-- otherwise some rules would just keep applying to themselves, ex: #a*x+#b*x=(#a+#b)*x
chkRuleOp vars op (t:tt) (r@(Lit _):rr) strict
  | ok (neutral op) && ok (Map.lookup r vars) && t == (fromJust$neutral op) = Nothing
  | otherwise=(\o -> chkRuleOp o op tt rr strict) =<< (ls_chkRule vars t r strict)
chkRuleOp vars op (t:tt) (r:rr) strict
  =(\o -> chkRuleOp o op tt rr strict) =<< (ls_chkRule vars t r strict)

maybeBool :: Bool -> Maybe Bool
{-# INLINE maybeBool #-}
maybeBool b
  | b = Just b
  | otherwise= Nothing

-- EOF --
