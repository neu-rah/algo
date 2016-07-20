{-# LANGUAGE CPP #-}

module Utils where

import AlgData
import Lib.Debug
import {-# SOURCE #-} AlgShow

import Data.Maybe
import Data.List
--import Data.Map (Map)
--import Debug.Trace
import Data.List.Ordered (sortOn)
import Text.Regex
import Data.Number.CReal
import Control.Applicative
import qualified Data.Map as Map
import Control.Exception.Base (assert)

-- Utils -----------------------------
(?|) :: Maybe t -> t -> t
{-# INLINE (?|) #-}
(?|) (Just a) _=a
(?|) Nothing b=b
(?) :: Bool -> (t, t) -> t
{-# INLINE (?) #-}
test ? (a,b)=if test then a else b

trd(_,_,o)=o

ok :: Maybe a -> Bool
{-# INLINE ok#-}
ok=isJust

(¢)(Op _ m)=head m
(¢) o = o

(þ)(Op _ m)=last m
(þ) o = o

-- check list minimal elements
(#>) :: [a] -> Int -> Bool
{-# INLINE (#>) #-}
list #> 0=not $null list
(_:_:_) #> 1 =True
(_:_:_:_) #> 2 = True
(_:_:_:_:_) #> 3 = True
list #> n=not (null $ drop n list)

-- check list cardinal
(#=) :: [a] -> Int -> Bool
{-# INLINE (#=) #-}
(#=) [] 0=True
(#=) [] _=False
(#=) (_:[]) 1=True
(#=) (_:[]) _=False
(#=) (_:_:[]) 2=True
(#=) (_:_:[]) _=False
(#=) (_:_:_:[]) 3=True
(#=) (_:_:_:[]) _=False
(#=) l n=(n-1)==(fst$last$zip [0..n] l)

(#>=) [] 0=True
(#>=) [] _=False
(#>=) l n=(fst$last$zip [1..n] l)>=n

isNom :: Algo -> Bool
{-# INLINE isNom #-}
isNom (Nom _)=True
isNom (Neighbor _ (Nom _))=True
isNom _ = False

emptyCtx :: Map.Map k a
{-# INLINE emptyCtx #-}
emptyCtx=Map.empty

hasOp::Ops->Algo->Bool
{-# INLINE hasOp #-}
hasOp o (Op op m)=(o==op)||(or$map (hasOp o) m)
hasOp _ _=False

-- get list of members or list with self for non-operators
membersOf::Algo->[Algo]
{-# INLINE  membersOf #-}
membersOf (Op _ m)=m
membersOf x = [x]

-- check expression type on a list of types
memberOf::Algo->[Ops]->Bool
{-# INLINE memberOf #-}
memberOf (Op op _) ops=elem op ops
memberOf _ _=False

(€) :: Algo -> [Ops] -> Bool
{-# INLINE  (€) #-}
(€)=memberOf

literals::Algo->[Algo]
literals e=Map.keys $literals' emptyCtx e

literals'::Ctx->Algo->Ctx
literals' ctx (Neighbor _ e)=literals' ctx e
literals' ctx (Op Resol m)=literals' ctx $last m
literals' ctx (Op Simpl m)=literals' ctx $last m
literals' ctx (Op Equation (o@(Op InvFunc _):[Op Equals [v]]))=Map.insert o v ctx
literals' ctx (Op Equation (o@(Op Func _):[Op Equals [v]]))=Map.insert o v ctx
literals' ctx o@(Op InvFunc (_:oo)) =
  if null lits then ctx else Map.union (Map.insert o Und ctx) lits
  where lits=literals' ctx (Op Params oo)
literals' ctx o@(Op Func (_:oo)) =
  if null lits then ctx else Map.union (Map.insert o Und ctx) lits
  where lits=literals' ctx (Op Params oo)
literals' ctx (Op op (o:oo))= (\x->literals' x (Op op oo)) $! (literals' ctx o)--foldl' literals' ctx m
literals' ctx o@(Dim _)=Map.insert o Und ctx
literals' ctx o@(Lit _)=Map.insert o Und ctx
literals' ctx _=ctx

isLit (Lit _)=True
isLit _ = False

has::(Algo->Bool)->Algo->Bool
{-# INLINE has #-}
has p o@(Op _ m)=(p o)||(or $ map (has p) m)
has p o=p o

mkop :: [Algo] -> Maybe Algo
{-# INLINE mkop #-}
mkop []=Nothing --error $"should not reach!"++show e++"\n"++info e
mkop (o:[])=Just o
mkop l@(_:_:_)=Just $ Op Or l

--------------------------------------------------------------------------
-- insert or append elements to operator but join them if equals and canComut
-- TODO: try to avoid this
algInsert::Algo->Algo->Algo
algInsert e@(Op opi mi) b@(Op op m)
  | fromIntegral(length m)>=(snd $quant op) = error $"Insert: operator overloaded "++(show op)++" "++(show opi)
  | (opi==op) && (canComut op) = Op op (mi++m)
  | otherwise=Op op (e:m)

algInsert e (Op op m)
  | fromIntegral(length m)>=(snd $quant op) = error $"Insert: operator overloaded "++(show op)
  | otherwise=Op op (e:m)

algInsert _ _ = undefined

algAppend :: Algo -> Algo -> Algo
algAppend e@(Op opi mi) (Op op m)
  | fromIntegral(length m)>=(snd $quant op) = error $"Append: operator overloaded "++(show opi)++" "++(show op)
  | (opi==op) && (canComut op) = Op op (m++mi)
  | otherwise=Op op (m++[e])

algAppend e (Op op m)
  | fromIntegral(length m)>=(snd $quant op) = error $"Append: operator overloaded "++(show op)
  | otherwise=Op op (m++[e])

algAppend _ _ = undefined

-- strips out stepping operators and return its contents
nosteps::Algo->[Algo]
nosteps e@(Op sop m)=if elem sop resolSteps then m else [e]
nosteps o=[o]

--this will also throw away the conditions along with the step
nostep::Algo->Algo
nostep e@(Op sop sm)=if elem sop resolSteps then head sm else e
nostep o=o

flatOp::Algo->Algo
{-# INLINE flatOp #-}
flatOp (Op op m)=Op op (flat op [] (map flatOp m))
flatOp x=x

flat::Ops->[Algo]->[Algo]->[Algo]
{-# INLINE  flat #-}
flat _ a []=a
flat op ma mb@(o:oo)
  | not(canComut op)=ma++mb
  | isOp op o=flat op (ma++(membersOf o)) oo
  | otherwise=flat op (ma++[o]) oo

isOp :: Ops -> Algo -> Bool
{-# INLINE  isOp #-}
isOp a (Op b _) = a==b
isOp _ _ = False

priority :: Algo -> Prior
{-# INLINE  priority #-}
priority (Op o _)=prior o
priority _=Element

specialChars::[(Char,String)]
specialChars=[
   ('⁰',"^0")
  ,('¹',"^1")
  ,('²',"^2")
  ,('³',"^3")
  ,('⁴',"^4")
  ,('⁵',"^5")
  ,('⁶',"^6")
  ,('⁷',"^7")
  ,('⁸',"^8")
  ,('⁹',"^9")
  ]

------------------------------------------------------------
-- carthesian produc base
cartProd :: [a] -> [Tpls a] -> [Tpls a]
{-# INLINE cartProd #-}
cartProd xs ys = [Tpl(x,y) | x <- xs, y <- ys]

-- flaten nested tupples to a list
data Tpls a=Til|Tpl (a,Tpls a) deriving(Show)

flaTpl :: Tpls t -> [t]
{-# INLINE flaTpl #-}
flaTpl Til=[]
flaTpl (Tpl(a,b))=a:(flaTpl b)

-- cartesian product between lists
prods::[[a]]->[[a]]
{-# INLINE prods #-}
prods=(map flaTpl) . (foldr cartProd [Til])

-- list all expression permutating members
algPerms::Algo->[Algo]
{-# INLINE  algPerms #-}
algPerms (Op op m)=map (Op op) $ permutations m
algPerms e=[e]

-- list all variants of an expression (permuting associative elements)
mutex::Algo->[Algo]
{-# INLINE  mutex #-}
mutex e@(Op Equation (o:[Op rop (r:rr)]))
  | rop==Equals || rop==NotEqual = [e,Op Equation [r,Op rop (o:rr)]]
  | otherwise=[e]
mutex (Op op m)
  | canComut op = nubBy strictEq$concat$map algPerms $map (Op op) $prods$map mutex m
  | otherwise = nubBy strictEq$map (Op op) $prods$map mutex m
mutex x=[x]

isUnd :: Algo -> Bool
{-# INLINE  isUnd #-}
isUnd Und=True
isUnd _=False

invmap :: Ord k => Map.Map a k -> Map.Map k [a]
{-# INLINE  invmap #-}
invmap m=Map.fromListWith (++) [(v,[k])|(k,v)<-Map.toList m]

clrColors :: String -> String
{-# INLINE  clrColors #-}
clrColors str=subRegex (mkRegex "\x1b\\[[^m]*m") str ""

-- monadic booleans?
justTrue :: Maybe Bool -> Maybe Bool
{-# INLINE justTrue #-}
justTrue o@(Just True)=o
justTrue _=Nothing
justFalse :: Maybe Bool -> Maybe Bool
{-# INLINE justFalse #-}
justFalse o@(Just False)=o
justFalse _=Nothing

getOp::Algo->Maybe Ops
getOp (Op op _)=Just op
getOp _=Nothing

repFst :: (a -> Bool) -> (a -> a) -> [a] -> Maybe [a]
repFst predicate xform items= rep' items
  where
    rep' (o:oo)
      | predicate o = Just ((xform o) : oo)
      | otherwise =(:) <$> (Just o) <*> rep' oo
    rep' [] = Nothing

exaust::(Algo->Maybe Algo)->Algo->Algo
exaust f o
  | ok r=exaust f jr
  | otherwise=o
  where r=f o;(Just jr)=r

lm=last . membersOf
hm=head . membersOf

chkQuant :: Algo -> Algo
{-# INLINE chkQuant #-}
chkQuant ao@(Op op members)
  | null members && (length members < mn) = error $"Empty operator found! "++show op
  | {-mn==1 ||-} (length members < mn) = head members
  | otherwise=ao
  where (mn,_) = quant op
chkQuant o=o

-- apply function to members
-- returning Just the processed expression
-- or Nothing if no result from members
algProc::(Algo->Maybe Algo)->Algo->Maybe Algo
algProc f (Op op m)
  | chk #>0 = Just $ Op op res
  | otherwise = Nothing
  where
    proc=map (\o->(Just o,f o)) m
    chk=[o | (_,o)<-proc , isJust o]
    res=map (\(mm,pp)->fromJust (pp<|>mm)) proc
algProc f o=f o

-- exaust procedure application and return list of step results
procSteps::(Eq (f a), Monad f, Alternative f) => (a -> f a) -> a -> [f a]
procSteps f o=takeWhile (not . (empty ==))$iterate (f=<<) (return o)

-- return only the last result or empty
proc::(Monad f, Eq (f a), Alternative f) => (a -> f a) -> a -> f a
proc f o
  | t#>1=last t
  | otherwise=empty
  where t=procSteps f o

-- exaust a procedure f on o and return result or empty
(·>) :: (Monad m, Eq (m a), Alternative m) => m a -> (a -> m a) -> m a
(·>) o f = o>>=((proc f))

-- exaust a procedure f on o and return result or original
(~>) :: (Monad f, Eq (f a), Alternative f) => f a -> (a -> f a) -> f a
(~>) a b=(a·>b) <|>a

-- apply a list of procedures
(··>) :: (Monad m, Eq (m a), Alternative m) => m a -> [a -> m a] -> m a
(··>) e []=e
(··>) e (o:oo)=r>>r··>oo<|>r where r=e·>o

(~~>) :: (Monad f, Eq (f a), Alternative f) => f a -> [a -> f a] -> f a
(~~>) e []=e
(~~>) e (o:oo)=(e~>o)~~>oo

a<·b=b·>a
a<~b=b~>a
a<··b=b··>a
a<~~b=b~~>a

-- repeating given sequence
run :: a1 -> (a1 -> [t] -> a) -> [t] -> a
run e f o=f e$concat$repeat o

(·|·>):: (Monad m, Eq (m a), Alternative m) => m a -> [a -> m a] -> m a
(·|·>) e s=run e (··>) s

-- apply list of procedures until first succeeds or empty
(//>) :: (Monad m, Eq (m a), Alternative m) => m a -> [a -> m a] -> m a
(//>) e []=empty
(//>) e (o:oo)=r<|>(e//>oo) where r=o=<<e

a<·|·b=a·|·>b
a<//b=b//>a

tryRun::(Eq (f a), Monad f, Alternative f) => f a -> (f a -> [a -> f a] -> f a) -> [a -> f a] -> f a
tryRun e f o=(r>>f r o)<|>r where r=e//>o

algElement::Algo->Bool
algElement (Op _ _)=False
algElement _ = True

-- EOF --
