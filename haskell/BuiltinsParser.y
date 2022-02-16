{
module BuiltinsParser where

import PatchedExtracted hiding (map, div, Int)
import qualified Token
import qualified Data.Text
import Data.Text.Encoding (encodeUtf8)
import qualified Data.ByteString
}

%name parse
%tokentype { Token.Token }
%error { parseError }

%token
    name   { Token.Name $$ }
    newline { Token.Newline }

    '('  { Token.OpenParen }
    ')'  { Token.CloseParen }
    ','  { Token.Comma }
    "->"  { Token.Arrow }

%%

All : Proto     { [$1] }
    | Proto All { $1 : $2 }
    | newline All { $2 }

Proto : name Args "->" Types newline { Build_proto_ast $1 $2 $4 } 
      | name Args            newline { Build_proto_ast $1 $2 [] }

Args : '(' ')'       { [] }
     | '(' Types ')' { $2 }

Types : name           { [$1] }
      | name ',' Types { $1 : $3 }

{
parseError :: [Token.Token] -> a
parseError ts = error $ "Parse error: " ++ show (take 10 ts)
}

-- vim: set ft=haskell:
