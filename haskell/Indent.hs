module Indent (addIndentsAndNewlines) where

import Token
import Lexer

doDedents :: [Int] -> Int -> ([Int], [Token.Token])
doDedents [] newIndent = error "no indent level to fall back on (the file starts indented?)"
doDedents oldIndentStack@(oldIndent : restIndents) newIndent
  | oldIndent == newIndent = (oldIndentStack, [])
  | oldIndent < newIndent  = error "inconsistent indent level"
  | otherwise = let (newIndentStack, dedents) = doDedents restIndents newIndent in
                (newIndentStack, Token.Dedent : dedents)

doIndent :: [Int] -> Int -> ([Int], [Token.Token])
doIndent [] newIndent = ([newIndent], [])
doIndent oldIndentStack@(oldIndent : restIndents) newIndent =
    if oldIndent < newIndent
        then (newIndent : oldIndentStack, [Token.Indent])
        else doDedents oldIndentStack newIndent

procEof _ [] = []
procEof _ [_] = []
procEof line (h : t) = (AlexPn 0 (line + 1) 1, Token.Dedent) : procEof line t

proc :: Int -> [Int] -> [(AlexPosn, Token.Token)] -> [(AlexPosn, Token.Token)]
proc line indentStack [] = (AlexPn 0 (line + 1) 1, Token.Newline) : procEof line indentStack
proc lastLine indentStack (first@(pos@(AlexPn _ line column), tok) : rest) =
    if lastLine == line
        then first : proc line indentStack rest
        else let (newIndentStack, prefix) = doIndent indentStack column in
             let indented = map ((,) pos) prefix ++ first : proc line newIndentStack rest in
             if lastLine /= 0
                 then (pos, Token.Newline) : indented
                 else indented


addIndentsAndNewlines :: [(AlexPosn, Token.Token)] -> [(AlexPosn, Token.Token)]
addIndentsAndNewlines = proc 0 []
