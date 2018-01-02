{-# LANGUAGE OverloadedStrings #-}

module Main where

import Parser
import Prover
import IOfunctions
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

main :: IO ()
main = do
    (prover, fileName) <- readArgs
    (name, formula) <- readFormula fileName
    TIO.putStrLn $ "The name of the formula is " `T.append` name
    print formula
    TIO.putStrLn ""
    let result = prover formula
    case result of
        Valid -> TIO.putStrLn "The formula is valid"
        _ -> TIO.putStrLn "The formula is not valid"
