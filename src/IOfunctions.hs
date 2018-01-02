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

readArgs :: IO (Formula Text -> Proof, FilePath)
readArgs = do
    progName <- getProgName
    args <- getArgs
    case args of
        [fileName] -> do
            TIO.putStrLn "Using default non exhaustive search"
            return (prover, fileName)
        [arg, fileName] -> do
            case arg of
                "e" -> return (exhaustiveProver', fileName)
                "exhaustive" -> return (exhaustiveProver', fileName)
                _ -> die $ "Usage: " ++ progName ++ "[e|exhaustive] <file path>"
        _ -> die $ "Usage: " ++ progName ++ "[e|exhaustive] <file path>"

readFile' :: FilePath -> IO Text
readFile' path = onException (TIO.readFile path) $ die "The file does not exist"

readFormula :: FilePath -> IO (Text, Formula Text)
readFormula path = do
    contents <- readFile' path
    case parse parseFormula path contents of
        Left err -> do putStrLn (show err); die "unexpected parse error"; error ""
        Right formula -> return  formula

exhaustiveProver' :: Ord a => Formula a -> Proof
exhaustiveProver' f
    | prover f == Valid = Valid
    | otherwise = exhaustiveProver f
