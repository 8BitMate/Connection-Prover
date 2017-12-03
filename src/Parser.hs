{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Prover
import qualified Text.Megaparsec as MP
import Text.Megaparsec hiding (parse)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Data.Void
import Data.Text (Text)
import qualified Data.Text as T
import Data.Foldable (foldl')

type Parser = Parsec Void Text

parseFormula :: Parser (Text, Formula Text)
parseFormula = do
    fof >> parens body

body :: Parser (Text, Formula Text)
body = do
    name <- word <* comma
    conjecture >> comma
    f <- formula
    return (name, f)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

atomExp :: Parser (Formula Text)
atomExp = do
    var <- word
    return (Atom var) <?> "atom expression"

notExp :: Parser (Formula Text)
notExp = do
    maybeNot <- optional lnot
    case maybeNot of
        Nothing -> do
            f <- atomicExp
            return f <?> "not expresion"
        _ -> do
            f <- notExp
            return (Not f) <?> "not expresion"

innerFormula :: Parser (Formula Text)
innerFormula = parens formula <?> "inner formula"

atomicExp :: Parser (Formula Text)
atomicExp = try atomExp <|> innerFormula <?> "atomic expression"

andExp :: Parser (Formula Text)
andExp = do
    first <- notExp
    rest <- many (land >> notExp)
    return (foldl' And first rest) <?> "and expression"

orExp :: Parser (Formula Text)
orExp = do
    first <- andExp
    rest <- many (lor >> andExp)
    return (foldl' Or first rest) <?> "or expression"

formula :: Parser (Formula Text)
formula = do
    first <- orExp
    rest <- many (arrow >> orExp)
    return (foldr Implies first rest) <?> "formula"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comma :: Parser Text
comma = symbol ","

lnot :: Parser Text
lnot = symbol "~"

land :: Parser Text
land = symbol "&"

lor :: Parser Text
lor = symbol "|"

arrow :: Parser Text --logical implication
arrow = symbol "->"

word :: Parser Text
word = fmap T.pack $ lexeme . some $ (alphaNumChar <|> char '_')

fof :: Parser Text --Start of input file
fof = symbol "fof"

conjecture :: Parser Text
conjecture = symbol "conjecture"

parse :: Parser a -> String -> Text -> Either (ParseError Char Void) a
parse = MP.parse
