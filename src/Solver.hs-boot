module Solver where

import AlgData

solved::Algo->Algo
varSolved::Algo->Algo
solve::Algo->Algo
--solve'::Algo->Maybe Algo
_solve::Ctx->Algo->Maybe Algo
_solved::Ctx->Algo->Maybe Algo
exaustCalc::Algo->Algo
{-
(>·>) :: Maybe Algo -> (Algo -> Maybe Algo) -> Maybe Algo
(>~>) :: Maybe Algo -> (Algo -> Maybe Algo) -> Maybe Algo
(>··>) :: Maybe Algo -> [Algo -> Maybe Algo] -> Maybe Algo
(>~~>) :: Maybe Algo -> [Algo -> Maybe Algo] -> Maybe Algo
(>·|·>):: Maybe Algo -> [Algo -> Maybe Algo] -> Maybe Algo
-}
