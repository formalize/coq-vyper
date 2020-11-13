{
module Lexer where

import LexerUtils
import qualified Token
}

%wrapper "posn"

$oct = [0-7]
$dec = [0-9]
$hex = [0-9A-Fa-f]

-- Not planning to support Unicode identifiers because many different Unicode letters look identical,
-- and having those as an option is very bad for demonstrating that a contract code is not malicious.
$letter = [_A-Za-z]

@escape = \\ ( [\n\\\"\'abfnrtv] | $oct{1,3} | x $dec{2} )    -- here's an extra " to calm down editors
@string_item_no_quote = @escape | [^\\\"]                     -- here's an extra " to calm down editors
@string_item_no_apost = @escape | [^\\\']

:-

$white;
"#" .*;

$letter ($letter | $dec)*             { \ p s -> (p, Token.Name s) }

$dec ("_" | $dec)* 
    | 0[xX] $hex ("_" | $hex)*  
    | 0[oO] $oct ("_" | $oct)*        { \ p s -> (p, Token.Number $ read       $ filter (/= '_') s) }
0[bB][01][_01]*                       { \ p s -> (p, Token.Number $ readBinary $ filter (/= '_') s) }

\" @string_item_no_quote* \"          { \ p s -> (p, Token.String $ processStringLiteral s) }   -- here's an extra " to calm down editors
\' @string_item_no_apost* \'          { \ p s -> (p, Token.String $ processStringLiteral s) }

"("   { \ p _ -> (p, Token.OpenParen) }
")"   { \ p _ -> (p, Token.CloseParen) }
":"   { \ p _ -> (p, Token.Colon) }
","   { \ p _ -> (p, Token.Comma) }

"+"   { \ p _ -> (p, Token.Plus) }
"-"   { \ p _ -> (p, Token.Minus) }
"*"   { \ p _ -> (p, Token.Star) }
"**"  { \ p _ -> (p, Token.DoubleStar) }
"//"  { \ p _ -> (p, Token.IntDiv) }
"%"   { \ p _ -> (p, Token.Mod) }
"&"   { \ p _ -> (p, Token.BitAnd) }
"~"   { \ p _ -> (p, Token.BitNot) }
"|"   { \ p _ -> (p, Token.BitOr) }
"^"   { \ p _ -> (p, Token.BitXor) }
"<<"  { \ p _ -> (p, Token.LeftShift) }
">>"  { \ p _ -> (p, Token.RightShift) }

"="   { \ p _ -> (p, Token.Assign) }
"+="  { \ p _ -> (p, Token.AssignAdd) }
"-="  { \ p _ -> (p, Token.AssignSub) }
"*="  { \ p _ -> (p, Token.AssignMul) }
"**=" { \ p _ -> (p, Token.AssignPow) }
"//=" { \ p _ -> (p, Token.AssignIntDiv) }
"&="  { \ p _ -> (p, Token.AssignBitAnd) }
"|="  { \ p _ -> (p, Token.AssignBitOr) }
"^="  { \ p _ -> (p, Token.AssignBitXor) }
"<<=" { \ p _ -> (p, Token.AssignLeftShift) }
">>=" { \ p _ -> (p, Token.AssignRightShift) }

"<"   { \ p _ -> (p, Token.Lt) }
">"   { \ p _ -> (p, Token.Gt) }
"<="  { \ p _ -> (p, Token.Le) }
">="  { \ p _ -> (p, Token.Ge) }
"=="  { \ p _ -> (p, Token.Eq) }
"!="  { \ p _ -> (p, Token.Ne) }

{
tokenize = recognizeKeywords . alexScanTokens
 -- vim: set ft=haskell:
}
