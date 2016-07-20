module Trans where

import AlgData
import AlgAux
import Utils
import Context
import Lib.Debug

import qualified Data.Map as Map
import Data.Maybe
import Control.Applicative

{-getVarsList :: Algo -> [(Algo,Algo)]
getVarsList (Op Resol m)=getDefsList $last m
getVarsList o=getDefsList o

getDefs::Algo->Ctx
getDefs=Map.fromList . getDefsList
getDefsList :: Algo -> [(Algo,Algo)]
getDefsList (Op Equation ( e@(Lit _) : [Op Equals (v:_)] ) ) = [(e,v)]
getDefsList (Op Resol m)=getDefsList $head m
getDefsList (Op System m) = concatMap getVarsList m
getDefsList (Op And m) = concatMap getDefsList m
getDefsList (Op Or m) = concatMap getDefsList m
getDefsList (Op op m)
  | elem op resolSteps = getDefsList $head m
  | otherwise = []
getDefsList _ = []
-}
trans:: Algo -> Maybe Algo
trans o@(Op Document m)
  | ok vars = Just $ Op Document $ algRebuild r m
  | otherwise=Nothing
  where
    vars=chkAssign emptyCtx o
    (Just v)=vars
    r=map (useCtx v) m

trans o=(D_CTX,"trans "++show o++": ")←((`useVars` o)=<<vars) --useCtx vars vars o
  where vars=chkAssign emptyCtx o

useVars::Ctx->Algo->Maybe Algo
useVars vars o@(Op Resol m)=useVars vars (last m)
useVars vars o@(Op Simpl m)=useVars vars (last m)
useVars vars (Op Equation [l@(Lit _),v@(Op rop (r:c))])
  | at == (Just Und) || at == (Just r) || (not $ ok at)= (D_CTX,"useVars Equation:") ← (Just$Op Equation [l]) <+ useVars vars v
  | plex (fromJust at)<=plex r = (Just$Op Equation []) <+ at <+ Just v
  | otherwise = Nothing
  where at=Map.lookup l vars

useVars vars e@(Op op m)
  | filter isJust mr #>0 = Just $ Op op $ algRebuild mr m
  | otherwise=Nothing
  where mr=map (useVars vars) m

useVars vars e@(Lit _)
  | Map.null vars || at==(Just Und)=Nothing
  | otherwise = at
  where at=Map.lookup e vars

useVars _ _ = Nothing
