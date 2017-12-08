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
    TIO.putStrLn "----Now testing with dcf----\n"
    dcfProofs <- checkProofs nameFomulaPairs dcfProver
    putStrLn "\n----dnfProofs----"
    print dnfProofs
    putStrLn "\n----dcfProofs----"
    print dcfProofs
    if (dnfProofs == dcfProofs)
        then TIO.putStrLn "The provers prove the same thing"
        else TIO.putStrLn "The provers prove different things"

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
dnfProver = undefined -- prove . connectionClauses . dnf . mapInts . nnf

dcfProver :: Formula Text -> Proof
dcfProver = undefined -- prove . connectionClauses. dcfTranslation . mapInts . nnf
