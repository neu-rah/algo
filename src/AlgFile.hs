module AlgFile where

import AlgData
import AlgAux
import AlgParser
import Utils
import Evid
import Context
import Solver
import Lib.Debug

import Control.Applicative
import Control.Exception.Base
import System.IO
import Data.Maybe

emptyDoc=Op Document []

resDoc :: Algo -> Either String Algo -> String -> Either String Algo
resDoc b (Right o) l=docInput b o l
resDoc b (Left o) l=Right $ Op Document []

load :: FilePath -> IO Algo
load fn=loadAlgo emptyDoc  emptyDoc fn

_load fn=do
  catch (readFile fn)
      (\e -> do let err = show (e :: IOException)
                hPutStr stderr ("Warning: Couldn't open " ++ fn ++ ": " ++ err)
                return "")

-- read a list of expressions (one per line)
-- no solving is attempted
readAlgo :: FilePath -> IO [Algo]
readAlgo fn=do
  let doc=Op Document []
  ld<-_load fn
  let l=lines ld
  let loaded=map (_algo) l
  return loaded

loadAlgo :: Algo->Algo -> FilePath -> IO Algo
loadAlgo books doc fn=do
  ld<-_load fn
  let l=lines ld
  let loaded=foldl (resDoc books) (Right doc) l
  rdoc<-res loaded
  return rdoc
  where
  e=Op Document []
  res::Either String Algo -> IO Algo
  res (Right o)=return o
  res (Left s)=do
    putStrLn s
    return $ Op Document []

docInput::Algo->Algo->String->Either String Algo
docInput books doc@(Op Document m) eq
  | ok mproc = docPut books doc proc
  | otherwise= Left "parse error, ignoring input"
  where
    mproc=algo (xlatOps$clrColors eq)
    (Just proc)=mproc

docPut::Algo->Algo->Algo->Either String Algo
docPut books doc@(Op Document m) (Op Equation [l@(Lit _),Op Equals [Pref]])=Right (fromJust ((docEvidChk doc l) <|> (Just doc)))
docPut books@(Op Document bkDefs) doc@(Op Document m) proc
  | dInfo(D_FILE,"books:"++show books++" docPut:"++show doc++" proc:"++show proc)=undefined
  | not (null b) =(D_ANY,"from books")←(docPut (Op Document nb) (Op Document (m++b)) proc)
  | has (==Pref) proc = Left ("Preference ("++show Pref++") not allowed as input, ignoring")
  | algElement proc = if isLit proc && (has (==proc) doc || has (==proc) books)
      then Right (fromJust ((docEvidChk doc proc) <|> (Just doc)))
      else Left "Unknown element at top level, ignoring"
  | otherwise= Right slv
  where
    vars=getAssigns emptyCtx doc
    nd=Op Document (m++[proc])
    slv=solve nd;
    b'=map (_solve vars) bkDefs
    b=map fromJust $ filter ok $ b'
    nb=map fromJust $filter isJust $zipWith (\a b->if isJust a then Nothing else Just b) b' bkDefs

docEvidChk::Algo->Algo->Maybe Algo
docEvidChk doc p@(Lit _) = evid p doc
docEvidChk doc _ = Nothing
