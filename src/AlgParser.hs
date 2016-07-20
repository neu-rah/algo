{-# Language RankNTypes #-}
{-# Language TypeSynonymInstances #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module AlgParser where

import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Token
import Text.Parsec.Expr
import Text.Parsec.Language
import GHC.Stack

import Data.Maybe
import Data.List.Split (onSublist,split)
import qualified Data.Map as Map
import Data.Number.CReal
import Data.Ratio
import Text.Show.Functions
import Text.Regex
import Control.Monad
import Control.Applicative ((<$>),(<*>),(*>))
--import Control.Exception
import Data.Unique
import Control.Monad.Trans
import Data.String
import Data.List

import AlgData
import Utils
import AlgShow
--import AlgSets
import Lib.Noms
import Lib.Debug
import Lib.Colors
import Lib.ISUnits

import {-# SOURCE #-} AlgSets

º::[Char] -> Maybe Algo
º=algo

getParams (Op Params m)=m
getParams o=[o]

-- Lexer
-- def=javaStyle
def = emptyDef { identStart  = letter
               , identLetter = alphaNum
               , opStart     = oneOf "+-*/=<>&|^;∪∩º\n"
               , opLetter    = oneOf "+-*/=<>&|^;∪∩º"
               , reservedNames=["ℕ","ℝ","ℚ"]
               , reservedOpNames=["{}","sin","cos","True","False","º"]
               }

lexer :: TokenParser ()
lexer = makeTokenParser def

-- The parser ===============================================
getNom::Either Integer Double -> Algo
getNom e = case e of
  (Left i) -> Nom $fromIntegral i
  (Right n) -> Nom $NrReal $fromRational$toRational n --(fromRational $ toRational n) -- $ toRational n

(<++>) a b = (++) <$> a <*> b
(<:>) a b = (:) <$> a <*> b

number :: Parser String
number = many1 digit

plus :: Parser String
plus = char '+' *> number

minus :: Parser String
minus = char '-' <:> number

int :: Parser String
int = plus <|> minus <|> number

nr :: Parser CReal
nr = fmap rd $ int <++> decimal <++> exponent
  where
    rd       = read :: String -> CReal
    decimal  = option "" $ char '.' <:> number
    exponent = option "" $ oneOf "eE" <:> int

parseNumber :: Parser Algo
parseNumber = do
  cr<-nr
  v <- try (identifier lexer) <|> ((symbol lexer)"")
  let r=toRatio cr
  let n=(Nom (if ok r then NrRatio $fromJust r else NrReal cr))
  let s=Map.lookup v is_scale_symbols -- check IS scale units
  return $ if isJust s then Quant (n, (fromJust s)) else  chkMul n v
  where
    chkMul a b=if b=="" then a else Op Mul [a,Lit b]

parseIdentifier :: Parser Algo
parseIdentifier = do
  i <- identifier lexer
  let isDim=Map.lookup i is_dim_keys -- check IS scale units
  --let isScale=map ((\(l,u)->(Lit (head l),u)) . fromJust) $filter isJust $map (\(f,u)->if f i#=2 then Just (f i,u) else Nothing) is_scale_matchers
  let isScale=Map.lookup i is_scale_symbols
  return $
    if isJust isDim
    then fromJust$isDim
    else
      if isJust isScale
      then Unit (fromJust isScale)
      else Lit i

parsePunctuator = do
  i <- try ((symbol lexer)".") -- <|> ((symbol lexer)":")
  return (Punctuation i)

chkSentenceOrUnit a b@(Lit b')
  | dInfo(D_PARSER,show a++" chkSentenceOrUnit "++show b)=undefined
  | isJust ss=(D_PARSER,"Quant:")←(Quant (a,fromJust ss))
  | otherwise=(D_PARSER,"sentence:")←(Op Sentence [a, b])
  where ss=Map.lookup b' is_scale_symbols
chkSentenceOrUnit a b=(D_PARSER,"other sentence:")←(Op Sentence [a,b])

--lit2word (Lit s)=Word s
--lit2word o = o

binOp::Ops->Algo->Algo->Algo
--  binOp Sentence (Op List oo) o=binOp Sentence (Op Sentence $ map lit2word oo) o
binOp Sentence (Op Params oo) o=binOp Sentence (Op Sentence $ intersperse (Punctuation ",") oo) o
binOp Sentence a@(Op Sentence ma) (Op Params pp) =Op Sentence $ma++(intersperse (Punctuation ",") pp)
binOp Sentence a (Op Params pp) =(D_PARSER,"Sentence a Params ")←(Op Sentence $[a]++(intersperse (Punctuation ",") pp))
binOp Sentence a b@(Unit s)=Quant (a,s)
binOp Sentence a@(Lit _) b=(D_PARSER,"Sentence Lit "++show a++" "++show b++" ")←(chkSentenceOrUnit a b)
binOp Sentence a@(Op Sentence ma) b@(Lit _) =(D_PARSER,"Sentence (Sentence a) b")←(Op Sentence $ma++[b])
binOp Sentence a b=(D_PARSER,"Sentence "++show a++" "++show b++"")←(chkSentenceOrUnit a b)

binOp SuchThat (Op Equation [e,Op r oo]) o=Op Equation [e,Op r (oo++[o])]

binOp Params a@(Op Params ma) b
  =(D_PARSER,"1º Params binOp "++show a++" "++show b++" ") ←(Op Params $ma++[b])

binOp Params a@(Op opa ma) b@(Op Equation mb)
  =(D_PARSER,show opa++" 2º Params binOp")←(Op System [a,b])
binOp op a@(Op opa ma) b@(Op Params mb@(bh:bb))=
  (D_PARSER,show op++" binOp1 "++show a++" "++show b) ←
    (if op==opa && ((snd$quant op)<((length ma)+(length mb)))
    then (D_PARSER," same op, loading ")← (Op op (ma++mb))
    else (D_PARSER," diff op, loading ")← (Op Params ((Op op [a,bh]):bb)))
    -- (Op op ([a]++mb))

binOp op a b@(Op Params (b1:mb))=
  (D_PARSER,show op++" binOp2 "++show a++" "++show b) ←
    (if (elem op paramsOps)
    then Op op ([a]++(b1:mb))
    else Op Params ([Op op [a,b1]]++mb))

binOp Div (Op Div m) o = Op Div (m++[o])
binOp op a@(Op opa ma) b
  -- | prior opa<prior op =
  |  op==Exp && (prior opa==Geometric) =(D_PARSER,show a++" "++show op++" "++show b++" prior rearrange:")←(Op opa (init ma++[Op op [last ma,b]]))
  | otherwise = (D_PARSER,show op++" binOp3 "++show a++"→ ") ← (if op==opa && canComut op then Op op (ma++[b]) else Op op [a,b])

binOp op a b = (D_PARSER,show op++" binOp4 "++show a++" "++show b++" ")←(Op op [a,b])

unOp::Ops->Algo->Algo
unOp op (Op Params m)=  Op op m
unOp op o=  Op op [o]

stepOp::Ops->Algo->Algo->Algo
stepOp op a@(Op Simpl m) b = Op Simpl (m++[Op op [b]])
stepOp op a@(Op Equation m) b = Op Simpl (m++[Op op [b]])
stepOp op a b@(Op System p)=Op Equation [a,Op op p]
stepOp op a b@(Op Params p)=Op Equation [a,Op op p]
stepOp op a b=Op Equation [a,Op op [b]]

parseExpression :: Parser Algo
parseExpression = (flip buildExpressionParser) parseTerm [
   [
     Prefix (reservedOp lexer "-" >> return (unOp Neg))
     , Prefix (reservedOp lexer "⁻" >> return (unOp Neg))
     , Prefix (reservedOp lexer "+" >> return (unOp Pos))
     , Prefix (reservedOp lexer "∓" >> return (unOp PosOrNeg))
     , Prefix (reservedOp lexer "+/-" >> return (unOp PosOrNeg))
     , Prefix (reservedOp lexer "root" >> return (unOp Root))
     , Prefix (reservedOp lexer "log" >> return (unOp Log))
   ]

 , [
     Infix (reservedOp lexer "^" >> return (binOp Exp)) AssocLeft
   , Infix (reservedOp lexer "⁻" >> return (binOp InvFunc)) AssocLeft
   , Infix (reservedOp lexer "'" >> return (binOp DerivedFunc)) AssocLeft
   , Infix (reservedOp lexer "@" >> return (binOp Index)) AssocLeft
   ]
 , [ Infix (reservedOp lexer "*" >> return (binOp Mul)) AssocLeft
   , Infix (reservedOp lexer "·" >> return (binOp Mul)) AssocLeft
   , Infix (reservedOp lexer "/" >> return (binOp Div)) AssocLeft
   ]
 , [ Infix (reservedOp lexer "+" >> return (binOp Sum)) AssocLeft
   , Infix (reservedOp lexer "-" >> return (binOp Sub)) AssocLeft
   , Infix (reservedOp lexer "∓" >> return (\a b->binOp Sum a (Op PosOrNeg [b]))) AssocLeft
   , Infix (reservedOp lexer "," >> return (binOp Params)) AssocLeft
   --, Infix (reservedOp lexer ":" >> return (binOp Params)) AssocLeft
   ]
 , [ Infix (reservedOp lexer "<=" >> return (stepOp LessOrEqual)) AssocLeft
   , Infix (reservedOp lexer ">=" >> return (stepOp GreaterOrEqual)) AssocLeft
   , Infix (reservedOp lexer "<>" >> return (stepOp NotEqual)) AssocLeft
   , Infix (reservedOp lexer "<->" >> return (stepOp Relates)) AssocLeft
   , Infix (reservedOp lexer ">-<" >> return (stepOp InvRelates)) AssocLeft
   , Infix (reservedOp lexer "=" >> return (stepOp Equals)) AssocLeft
   , Infix (reservedOp lexer ">" >> return (stepOp Greater)) AssocLeft
   , Infix (reservedOp lexer "<" >> return (stepOp Less)) AssocLeft
   , Infix (reservedOp lexer "∈" >> return (stepOp ElementOf)) AssocLeft
   , Infix (reservedOp lexer "∉" >> return (stepOp NotElementOf)) AssocLeft
   ]
 , [ Infix (reservedOp lexer "∪" >> return (binOp Union)) AssocLeft
   , Infix (reservedOp lexer "∩" >> return (binOp Intersect)) AssocLeft
   , Infix (reservedOp lexer ":" >> return (binOp SuchThat)) AssocLeft
   , Infix (reservedOp lexer "\n" >> return (binOp Document)) AssocLeft
   , Infix (reservedOp lexer "" >> return (binOp Sentence)) AssocLeft
   ]
 , [ Infix (reservedOp lexer "&" >> return (binOp And)) AssocLeft
   , Infix (reservedOp lexer "|" >> return (binOp Or)) AssocLeft
   ]
 ]

parseLeftWing :: Parser RangeWing
parseLeftWing = do
   i <- try ((symbol lexer) "[") <|> ((symbol lexer)"]")
   v <- parseTerm
   return $ RangeWing (i=="[") v

parseRightWing :: Parser RangeWing
parseRightWing = do
 v <- parseTerm
 i <- try ((symbol lexer) "[") <|> ((symbol lexer)"]")
 return $ RangeWing (i=="]") v

parseRange lexer e= do
  a <- parseLeftWing
  s <- ((symbol lexer) ";")
  b <- parseRightWing
  return $ Sets (Range a b)

parseFloor lexer e= do
  _ <- ((symbol lexer) "⌊")
  expr <- parseTerm
  _ <- ((symbol lexer) "⌋")
  return $ Op Floor [expr]

parseSet lexer e= do
  i <- braces lexer e
  return $ (D_PARSER,show i++" braces to ")
    ← case i of
      (Op SuchThat [expr,dom])->Sets $ SetExpr expr dom
      (Op Equation [Op Or [expr,vars],rel])->Sets $ SetExpr expr (Op Equation [vars,rel])
      _->(Op Set $getParams i)

parseFunc lexer e=do
  i <- identifier lexer
  s <- ((symbol lexer)"(")
  p <- parseExpression --parseTerm
  _ <- ((symbol lexer) ")")
  return $ (D_PARSER,"i="++show i++" parsing function!")←(if s=="(" then (Op Func (Lit i:getParams p)) else Und)

parseNumeric lexer e = do
  _<-symbol lexer "#"
  i<-many alphaNum
  return (Numeric i)

parseTerm :: Parser Algo
parseTerm
        -- = try (parseInvFunc lexer parseExpression)
        = try (parseFunc lexer parseExpression)
        <|>parens lexer parseExpression
        <|> (reserved lexer "?"  >> return Pref)
        <|> parseNumeric lexer parseExpression
        <|> (reserved lexer "{}"  >> return (Op Set []))
        <|> try (parseFloor lexer parseExpression)
        <|> try (parseSet lexer parseExpression)
        -- <|> try (parseSetDef lexer parseExpression)
        <|> parseRange lexer parseExpression
        <|> (reserved lexer "Inf"  >> return Infinit)
        <|> (reserved lexer "inf"  >> return Infinitesimal)
        <|> (reserved lexer "..."  >> return Ellipsis)
        <|> (reserved lexer "ℕ"  >> return (_N))
        <|> (reserved lexer "ℚ"  >> return (_Q))
        <|> (reserved lexer "ℝ"  >> return (_R))
        <|> (reserved lexer "True"  >> return (Bool True))
        <|> (reserved lexer "False" >> return (Bool False))
        <|> parseIdentifier
        <|> parseNumber
        <|> parsePunctuator
        --where i=(liftIO newUnique)>>=(return . Numeric)

parseInput :: Parser Algo
parseInput = do
    whiteSpace lexer
    ex <- parseExpression
    eof
    return ex

mapNth :: Integral a => (t -> [t]) -> a -> [t] -> [[t]]
mapNth _ _ [] = []
mapNth f n (o:oo) = map (\(e,i)->if mod i n==0 then f e else [e]) [(e,i)|(e,i)<-zip (o:oo) [1..]]

parseResol :: String -> Maybe Algo
parseResol s
    | (implics#=1) && (implic#=1)=parseAlgoExpr s -- $ head implics
  | otherwise=Just parsed
  where
    equivs=split (onSublist "<=>") s
    implic=split (onSublist "=>") s
    implics=foldr (++) [] $ (split (onSublist "=>")$head equivs) :(mapNth (split (onSublist "=>")) 2 $ tail equivs)
    parsed=resolFromList$if equivs#=1 then implic else implics

stepsFromList :: [String] -> [Algo]
stepsFromList []=[]
stepsFromList [_]=error "bad list"
stepsFromList (o:oo)
  | ok h = Op op [fromJust h]:(stepsFromList$tail oo)
  | otherwise = stepsFromList$tail oo
  where
    h=parseAlgoExpr$head oo
    op=case o of
      "<=>" -> Equiv
      "=>"-> Implic
      otherwise -> error "no reach! steps can only be => or <=> (as parsed!)"

resolFromList::[String]->Algo
resolFromList (o:oo)
  -- =Op Resol ((parseAlgoExpr o):(stepsFromList oo))
  |ok e= Op Resol ((fromJust e):(stepsFromList oo))
  |otherwise=Op Resol $ stepsFromList oo
  where e=parseAlgoExpr o

parseAlgoExpr :: String -> Maybe Algo
parseAlgoExpr i=case parse parseInput "AlgParser" i of
  Right e -> Just e
  Left e -> Nothing --errorWithStackTrace ("parse error... "++i++"\n"++show e)

format::Algo->Algo
format op@(Op Simpl m)
  | and (map relatLogic mid) = flatOp$formatRelLogic m
  | otherwise = op
  where
    mid=init$tail$m
    relatLogic:: Algo -> Bool
    relatLogic (Op r [Op l _]) = elem r equatOps && elem l logicOps
    relatLogic _ = False
    formatRelLogic:: [Algo]->Algo
    formatRelLogic [o] = o
    formatRelLogic (a:(Op r [Op l [b,c]]):oo) = Op l [Op Equation [a,Op r [b]] , formatRelLogic (c:oo)]
    formatRelLogic o = Op Equation o
format e@(Op Div [Nom a,Nom b])
  | b == 0 = e
  | otherwise =Nom (a/b)
format (Op Params o) = Op List (map format o)
format (Op Neg ((Nom n):[]))=Nom (-n)
format (Op Sub (o:oo))=format (Op Sum (o:(map (\o->Op Neg [format o]) oo)))
format (Op op m)=flatOp (Op op $map format m)
format x=x

xlatOps::String->String
xlatOps= xlatEquiv . xlatOr . xlatAnd . xlatEmpty
  where
    xlatEquiv str=subRegex (mkRegex "⇔") str "<=>"
    xlatOr=map xlat
      where
        xlat '∨' = '|'
        xlat c = c
    xlatAnd=map xlat
      where
        xlat '∧'='&'
        xlat c=c
    xlatEmpty str=subRegex (mkRegex "∅") str "{}"

specialCharsMap :: Map.Map Char String
specialCharsMap=Map.fromList specialChars
expand c
  | ok sc=fromJust sc
  | otherwise=[c]
  where sc=Map.lookup c specialCharsMap

algo::[Char]->Maybe Algo
algo s=format<$>(parseResol $concatMap expand$ xlatOps s)

_algo :: [Char] -> Algo
_algo s
  | isJust r=format$fromJust r
  | otherwise = errorWithStackTrace $"parse error at: "++s
  where
    expanded=concatMap expand
    r=parseResol $expanded $ xlatOps s

instance Show (Parser Algo) where
  showsPrec _ _ = \s->"«Algo parser "++s++"»"


instance Read Algo where readsPrec d s =[(_algo s,"")]
instance IsString Algo where fromString=_algo

-- EOF --
