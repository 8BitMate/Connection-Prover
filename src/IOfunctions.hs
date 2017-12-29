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

readArgs :: IO FilePath
readArgs = do
    progName <- getProgName
    args <- getArgs
    case args of
        [fileName] -> do
            return fileName
        _ -> die $ "Usage: " ++ progName ++ " <file path>"

readFile' :: FilePath -> IO Text
readFile' path = onException (TIO.readFile path) $ die "The file does not exist"

readFormula :: FilePath -> IO (Text, Formula Text)
readFormula path = do
    contents <- readFile' path
    case parse parseFormula path contents of
        Left err -> do putStrLn (show err); die "unexpected parse error"; error ""
        Right formula -> return  formula
