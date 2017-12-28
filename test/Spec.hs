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
    files <- listDirectory "."
    nameFomulaPairs <- mapM readFormula files
    TIO.putStrLn "----Now testing with dnf----\n"
    dnfProofs <- checkProofs nameFomulaPairs dnfProver
    putStrLn "\n----dnfProofs----"
    print dnfProofs

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

dnfProver :: Formula Text -> Proof
dnfProver = prove . connectionClauses . dnf . herbrandtisize . mapInts . nnf
