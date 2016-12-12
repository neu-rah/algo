{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Maybe
import Data.Either
import Data.List
import Data.List.Split
import Data.Ratio
import Debug.Trace
import Control.Applicative
import System.Console.ANSI
import qualified Data.Map as Map
import Data.List
import Data.List.Split
import Data.Char
import Data.Number.CReal
import Data.Fixed
import Data.Numbers.Primes
import Math.ContinuedFraction
import Data.String
import Data.Unique
import Control.Monad.Trans
import qualified Text.Parsec as Parsec
import Data.Either.Extra
import Control.Monad
import Data.Monoid hiding (Sum)
import Data.Foldable hiding (elem,concat)
import Text.Regex
import Data.Fixed
--import Data.Boolean
--import Data.Distributive
--import Data.Parallel

import AlgData
import Utils
import AlgShow
import AlgAux
import AlgParser
import Calc
import Rules
import Evid
import Solver
import Tests.AlgTester
import AlgNum
import AlgSets
import Lib.Noms
import Lib.Debug
import Lib.Colors
import Lib.ISUnits
import Intervals
import Context
import Sample
import Trans
import Derive
import Steps
import Neighbor
import Bench
import Continued
import AlgFile
import PLD

import Paths_algo (version,getDataFileName)
import Data.Version (showVersion)
--import System.IO (hFlush,stdout,hSetEcho)
import Control.Exception
import Data.Typeable
import System.IO
--import System.Console.Haskeline

rules=readAlgo("docs/SimplificationRules.algo")


docMain=do
  _<-clearScreen
  _<-setCursorPosition 0 0
  putStrLn ("Algo " ++ showVersion version)
  putStrLn "Rui Azevedo <ruihfazevedo@gmail.com>"
  putStrLn $"Enter "++boldStyle++"help"++noStyle++" for a list of commands."
  electric<-getDataFileName "docs/electric.algo"
  books<-loadAlgo (Op Document []) (Op Document []) electric
  -- let bookdefs=getAssigns
  repl books Und

main
  =putStrLn
  $show
  $ applyRule emptyCtx (Op Sum [Lit "a",Lit "a"]) (Op Equation [Op Sum [Lit "a",Lit "a"],Op Equals [Op Mul [Nom 2,Lit "a"]]]) False
  -- $ applyRule emptyCtx "a+a" "a+a=2a" False
  -- $solve "2+2"

--prompt=redColor++"λ"++whiteColor++">"++nColor
prompt=boldStyle++redColor++"α"++whiteColor++"·>"++noStyle++nColor

replLoad :: Algo->Algo -> [FilePath] -> IO Algo
replLoad books doc (_:params)=do
  if null params || (params#=2&&params!!0=="")
  then do
    putStrLn "provide filename"
    return doc
  else do
    putStr $ "LOAD! "
    putStrLn $ show (params!!0)
    foldlM (loadAlgo books) doc params

replCmds=["load","book"]::[String]

repl :: Algo->Algo -> IO ()
repl books doc@(Op Document _)=do
  putStr prompt
  hFlush stdout
  eq<-getLine
  repl_core books doc eq
repl books Und=repl books$Op Document []
repl books o=repl books$Op Document [o]

repl_core :: Algo->Algo->String -> IO ()
repl_core books doc@(Op Document m) eq=do
  case eq of
    "" -> repl books doc
    "help" -> do
      putStrLn "book «file» - load file into bookshelf"
      putStrLn "books - Show books content"
      putStrLn "clear - Clears the current document!"
      putStrLn "doc - Show current document"
      putStrLn "exit - Exit this shell"
      putStrLn "load «file» - load file as current document"
      putStrLn "test - Run included test (development only)"
      putStrLn "vars - List document vars"
      putStrLn "verify - Verify the current document"
      repl books doc
    "electric" -> do
      electric<- getDataFileName "docs/electric.algo"
      loaded<-loadAlgo books doc electric
      repl books loaded
    "calc" -> repl books $ fromJust ((calc doc)<|>Just doc)
    "solve" -> repl books $ solve doc
    "simplify" -> repl books $ fromJust ((simplify doc)<|>Just doc)
    "trans" -> repl books $ fromJust ((trans doc)<|>Just doc)
    "info" -> do
      putStrLn $ info doc
      repl books doc
    "clear" -> do
      putStrLn "document cleaned."
      repl books $ Op Document []
    "doc" -> do
      putStrLn $ show doc
      repl books doc
    "books" -> do
      putStrLn $ show books
      repl books doc
    "vars" -> do
      putStrLn $ show $ getAssigns emptyCtx doc
      repl books doc
    "verify"->do
      let v=verify doc
      putStrLn $ if ok v then show $ fromJust v else "can't verify document"
      repl books doc
    "test"->do
      test
      repl books doc
    "exit"->return ()
    _ -> do
      let cmdLine=matchRegex (mkRegex $ "^\\s*("++(intercalate "|" replCmds)++")\\s*(.*)\\s*$") eq
      if isJust cmdLine
      then do
        let cmd=fromJust cmdLine
        case cmd!!0 of
          "load"->do
            d <- replLoad books doc cmd
            repl books d
          "book"->do
            d<-(replLoad (Op Document []) books cmd)
            repl d doc
      else do
        let r=docInput books doc eq
        case r of
          (Right rd)->do
            _<-clearScreen
            _<-setCursorPosition 0 0
            putStrLn "== Algo solve -------------------------------------------------------"
            putStrLn $ show rd
            repl books rd
          (Left err)->do
            putStrLn "== Algo input error --------------------------------------------------"
            putStrLn err
            putStrLn eq
            repl books doc
--repl_core _ _=error "reple MUST use a document."

-- EOF --
