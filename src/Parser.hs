{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Prover
import qualified Text.Megaparsec as MP
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import Data.Void
import Data.Text (Text)
import qualified Data.Text as T
import Data.Foldable (foldl')

type Parser = Parsec Void Text

expr :: Parser (Formula Text)
expr = makeExprParser term table <?> "expression"

term = parens expr <|> atomExp <?> "term"

table = [ [prefix "~" Not],
          [binaryL "&" And],
          [binaryL "|" Or],
          [binaryR "->" Implies] ]

binaryL name f = InfixL (f <$ symbol name)
binaryR name f = InfixR (f <$ symbol name)
prefix name f = Prefix $ foldr1 (.) <$> some (f <$ symbol name)


parseFormula :: Parser (Text, Formula Text)
parseFormula = do
    fof >> parens body

body :: Parser (Text, Formula Text)
body = do
    name <- word <* comma
    conjecture >> comma
    f <- expr
    return (name, f)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

atomExp :: Parser (Formula Text)
atomExp = do
    var <- word
    return (Atom var) <?> "atom expression"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comma :: Parser Text
comma = symbol ","

word :: Parser Text
word = fmap T.pack $ lexeme . some $ (alphaNumChar <|> char '_')

fof :: Parser Text --Start of input file
fof = symbol "fof"

conjecture :: Parser Text
conjecture = symbol "conjecture"

parse :: Parser a -> String -> Text -> Either (ParseError Char Void) a
parse = MP.parse
