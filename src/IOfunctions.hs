{-# LANGUAGE OverloadedStrings #-}

module IOfunctions where

import Parser
import Prover
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment
import System.IO
import System.Exit
import Control.Exception hiding (try)
import Control.Monad

readArgs :: Ord a => IO (Formula a -> Proof, FilePath)
readArgs = do
    progName <- getProgName
    args <- getArgs
    undefined
    {-case args of
        [] -> die $ "Usage: " ++ progName ++ " [dnf|dcf] <file path>"
        [fileName] -> do
            TIO.putStrLn "Uses standard translation to disjunctive normal form"
            return (prove . connectionClauses . dnf . mapInts . nnf, fileName)
        [flag, fileName] -> do
            case flag of
                "dnf" -> return (prove . connectionClauses . dnf . mapInts . nnf, fileName)
                "dcf" -> return (prove . connectionClauses. dcfTranslation . mapInts . nnf, fileName)
                _ -> do die $ "Invalid argument: " ++ flag; error ""-}

readFile' :: FilePath -> IO Text
readFile' path = onException (TIO.readFile path) $ die "The file does not exist"

readFormula :: FilePath -> IO (Text, Formula Text)
readFormula path = do
    contents <- readFile' path
    case parse parseFormula path contents of
        Left err -> do putStrLn (show err); die "unexpected parse error"; error ""
        Right formula -> return  formula
