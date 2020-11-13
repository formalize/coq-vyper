module LexerUtils where

import Numeric (readInt)
import qualified Token
import qualified Data.Map
import Data.Maybe (fromMaybe)
import Data.Char (chr)

----------------------------------------------------
-- reading binary literals

binaryDigitToInt :: Char -> Int
binaryDigitToInt '0' = 0
binaryDigitToInt '1' = 1

isBinaryDigit :: Char -> Bool
isBinaryDigit '0' = True
isBinaryDigit '1' = True
isBinaryDigit _ = False

readBinaryS :: ReadS Integer
readBinaryS = readInt 2 isBinaryDigit binaryDigitToInt

readBinaryNoPrefix :: String -> Integer
readBinaryNoPrefix s = 
    case readBinaryS s of
        [(i, "")] -> i
        _ -> error "error parsing a binary literal: extra characters"

readBinary :: String -> Integer
readBinary s =
    case s of
        '0' : 'b' : t -> readBinaryNoPrefix t
        '0' : 'B' : t -> readBinaryNoPrefix t
        _ -> error "error parsing a binary literal: no 0b/0B prefix"

----------------------------------------------------
-- recognizing keywords

keywordMap = Data.Map.fromList [ ("and"     , Token.And)
                               , ("as"      , Token.As)
                               , ("assert"  , Token.Assert)
                               , ("break"   , Token.Break)
                               , ("const"   , Token.Const)
                               , ("continue", Token.Continue)
                               , ("contract", Token.Contract)
                               , ("count"   , Token.Count)
                               , ("def"     , Token.Def)
                               , ("elif"    , Token.Elif)
                               , ("else"    , Token.Else)
                               , ("emit"    , Token.Emit)
                               , ("event"   , Token.Event)
                               , ("for"     , Token.For)
                               , ("from"    , Token.From)
                               , ("idx"     , Token.Idx)
                               , ("if"      , Token.If)
                               , ("in"      , Token.In)
                               , ("import"  , Token.Import)
                               , ("map"     , Token.Map)
                               , ("not"     , Token.Not)
                               , ("or"      , Token.Or)
                               , ("pass"    , Token.Pass)
                               , ("pub"     , Token.Pub)
                               , ("raise"   , Token.Raise)
                               , ("return"  , Token.Return)
                               , ("revert"  , Token.Return)
                               , ("type"    , Token.Type)
                               , ("while"   , Token.While)
                               ]

recognizeOneKeyword :: Token.Token -> Token.Token
recognizeOneKeyword x@(Token.Name s) = fromMaybe x (Data.Map.lookup s keywordMap)
recognizeOneKeyword x = x

recognizeKeywords = map (\(pos, tok) -> (pos, recognizeOneKeyword tok))

----------------------------------------------------
-- processing escapes

escapeMap = Data.Map.fromList [ ('\n', '\n')
                              , ('\\', '\\')
                              , ('\"', '\"')
                              , ('\'', '\'')
                              , ('a', '\a')
                              , ('b', '\b')
                              , ('f', '\f')
                              , ('n', '\n')
                              , ('r', '\r')
                              , ('t', '\t')
                              , ('v', '\v')
                              ]

processStringLiteral :: String -> String
processStringLiteral ('\"':rest) = process rest
    where process "\"" = ""
          process ('\\':'x':a:b:rest) = chr (read ['0', 'x', a, b] :: Int) : process rest
          
          process ('\\':a:b:c:rest) | '0' <= a && a <= '7' &&
                                      '0' <= b && b <= '7' &&
                                      '0' <= c && c <= '7' =
              chr (read ['0', 'o', a, b, c] :: Int) : process rest
          process ('\\':a:b:rest) | '0' <= a && a <= '7' &&
                                    '0' <= b && b <= '7' =
              chr (read ['0', 'o', a, b] :: Int) : process rest
          process ('\\':a:rest) | '0' <= a && a <= '7' =
              chr (read ['0', 'o', a] :: Int) : process rest
          process ('\\':e:rest) = case Data.Map.lookup e escapeMap of
                                    Just c -> c : process rest
                                    Nothing -> error $ "unknown escape char: " ++ [e]
          process (h:t) = h : process t

----------------------------------------------------
-- indents

-- indent
