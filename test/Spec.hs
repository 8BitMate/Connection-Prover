{-# LANGUAGE OverloadedStrings #-}

module Main where

import Prover
import IOfunctions
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment
import System.IO
import System.Directory
import Control.Monad

main :: IO ()
main = do
    setCurrentDirectory "prop1_problems"
    propFiles <- fmap reverse $ listDirectory "."
    print propFiles
    propNameFomulaPairs <- mapM readFormula propFiles
    setCurrentDirectory "../fof1_problems"
    fofFiles <- fmap reverse $ listDirectory "."
    print fofFiles
    fofNameFomulaPairs <- mapM readFormula fofFiles
    TIO.putStrLn "----Now testing with propositional formulas----\n"
    propProofs <- checkProofs propNameFomulaPairs prover
    print propProofs
    TIO.putStrLn "\n----Now testing with first order formulas----\n"
    fofProofs <- checkProofs fofNameFomulaPairs prover
    print fofProofs

checkProofs :: [(Text, Formula Text)] -> (Formula Text -> Proof) -> IO [Proof]
checkProofs nameFomulaPairs prover =
    mapM (\(name, formula) -> do
        TIO.putStrLn $ "The name of the formula is " `T.append` name
        print formula
        case prover formula of
            Valid -> do putStrLn $ show name ++ " is valid"
                        return Valid
            _ -> do putStrLn $ show name ++ " is not valid"
                    return Invalid) nameFomulaPairs
