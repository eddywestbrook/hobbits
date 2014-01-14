{-# LANGUAGE TemplateHaskell #-}

-----------------------------------
-- a parser for Haskell patterns --
-- (don't ask...)                --
-----------------------------------

module PattParser (
  parsePatt, parseVar
) where

import Text.ParserCombinators.Parsec
import Language.Haskell.TH
import Data.Char


varStartChars = ['a'..'z']
ctorStartChars = ['A'..'Z']

identChars = varStartChars ++ ctorStartChars ++ ['0'..'9'] ++ "'_"

varParser :: GenParser Char st String
varParser =
    do char1 <- oneOf varStartChars
       char_rest <- many (oneOf identChars)
       return (char1 : char_rest)

ctorParser :: GenParser Char st String
ctorParser =
    do char1 <- oneOf ctorStartChars
       char_rest <- many (oneOf identChars)
       return (char1 : char_rest)

stringParser :: GenParser Char st String
stringParser =
    do char '"'
       res <- stringContentsParser
       return res

stringContentsParser =
    many (noneOf "\\\"") >>= \prefix ->
        (char '"' >> return prefix)
        <|>
        (char '\\' >> do c <- anyChar
                         rest <- stringContentsParser
                         return $ prefix ++ [c] ++ rest)

charParser :: GenParser Char st Char
charParser =
    do char '\''
       c <- ((char '\\' >> anyChar) <|> anyChar)
       char '\''
       return c

digitsToInt digits = helper digits 0
    where helper [] accum = accum
          helper (digit:digits) accum =
              helper digits (accum * 10 + (digitToInt digit))

intToRational :: Int -> Rational
intToRational = fromIntegral

digitsToFrac digits = helper digits
    where helper [] = 0.0
          helper (digit:digits) = ((helper digits) + (intToRational $ digitToInt digit)) / 10

numParser :: GenParser Char st Lit
numParser =
    do base_digits <- many1 (oneOf ['0'..'9'])
       ((do char '.'
            frac_digits <- many1 (oneOf ['0'..'9'])
            return (RationalL $ (intToRational $ digitsToInt base_digits) + digitsToFrac frac_digits))
        <|> return (IntegerL $ fromIntegral $ digitsToInt base_digits))

litParser :: GenParser Char st Lit
litParser = (charParser >>= return . CharL) <|>
            (stringParser >>= return . StringL) <|>
            numParser

commaSepParser :: GenParser Char st [Pat]
commaSepParser =
    do first <- pattParser
       rest <- (char ',' >> commaSepParser) <|> (return [])
       return (first:rest)


tokenParser :: GenParser Char st Pat
tokenParser =
    -- literals
    (litParser >>= return . LitP) <|>

    -- wildcards
    (char '_' >> return WildP) <|>

    -- vars
    (varParser >>= return . VarP . mkName) <|>

    -- tuples; NOTE: we parse any parenthesized expression as a tuple,
    -- and remove the TupP constructor when there are no commas
    (do char '('
        tup <- commaSepParser
        char ')'
        return (case tup of
                  [] -> ConP '() []
                  [patt] -> patt
                  _ -> TupP tup)) <|>

    -- constructor applications
    (do ctor <- ctorParser
        args <- many (try pattParser)
        return $ ConP (mkName ctor) args) <|>

    -- lists
    (do char '['
        elems <- commaSepParser
        char ']'
        return $ ListP elems)



wsParser :: GenParser Char st ()
wsParser = many (oneOf " \t\n\r") >> return ()

pattParser :: GenParser Char st Pat
pattParser = do wsParser
                res <- tokenParser
                wsParser
                return res

varOnlyParser :: GenParser Char st String
varOnlyParser = do wsParser
                   res <- varParser
                   wsParser
                   eof
                   return res


----------------------------------------
-- Finally, the external interface... --
----------------------------------------

parsePatt str = case parse pattParser "" str of
                  Left err -> error $ show err
                  Right patt -> patt

parseVar str = case parse varOnlyParser "" str of
                 Left err -> error $ show err
                 Right str -> str
