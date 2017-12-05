{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Prover
import qualified Text.Megaparsec as MP
import Text.Megaparsec hiding (parse)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Expr
import Text.Megaparsec.Char
import Data.Void
import Data.Text (Text)
import qualified Data.Text as T
import Data.Foldable (foldl')

type Parser = Parsec Void Text

expr :: Parser (Formula Text)
expr = makeExprParser term table <?> "expression"

term = forall <|> exists <|> parens expr <|> predicate <?> "term"

table = [ [prefix "~" Not],
          [binaryL "&" And],
          [binaryL "|" Or],
          [binaryR "->" Implies] ]

binaryL name f = InfixL (f <$ symbol name)
binaryR name f = InfixR (f <$ symbol name)
prefix name f = Prefix $ foldr1 (.) <$> some (f <$ symbol name)

exists :: Parser (Formula Text)
exists = do
    symbol "?"
    var <- brackets word
    symbol ":"
    formula <- (lookAhead (symbol "~") >> expr) <|> term
    return $ Exists var formula

forall :: Parser (Formula Text)
forall = do
    symbol "!"
    var <- brackets word
    symbol ":"
    formula <- (lookAhead (symbol "~") >> expr) <|> term
    return $ Forall var formula

predicate :: Parser (Formula Text)
predicate = do
    p <- word
    vars <- option [] (parens $ sepBy1 word comma)
    case vars of
        [] -> return $ Atom p
        _ ->  return $ Pred p vars

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

parseFormula :: Parser (Text, Formula Text)
parseFormula = do
    fof >> parens body

body :: Parser (Text, Formula Text)
body = do
    name <- word <* comma
    conjecture >> comma
    f <- expr
    return (name, f)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

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
