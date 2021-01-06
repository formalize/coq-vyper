{
module Parser where

import PatchedExtracted hiding (map, div)
import qualified Token
import CoqBridge (zOfInteger)
import qualified Data.Text
import Data.Text.Encoding (encodeUtf8)
import qualified Data.ByteString
import Data.Word (Word8)
import Data.Bits
}

%name parse
%tokentype { Token.Token }
%error { parseError }

%token
    name   { Token.Name $$ }
    number { Token.Number $$ }
    string { Token.String $$ }
    newline { Token.Newline }
    indent { Token.Indent }
    dedent { Token.Dedent }

    '('  { Token.OpenParen }
    ')'  { Token.CloseParen }
    ':'  { Token.Colon }
    ','  { Token.Comma }
    '.'  { Token.Dot }

    '+'  { Token.Plus }
    '-'  { Token.Minus }
    '*'  { Token.Star }
    "**" { Token.DoubleStar }
    "//" { Token.IntDiv }
    '%'  { Token.Mod }
    '&'  { Token.BitAnd }
    '~'  { Token.BitNot }
    '|'  { Token.BitOr }
    '^'  { Token.BitXor }
    "<<" { Token.LeftShift }
    ">>" { Token.RightShift }

    "=="  { Token.Eq }
    "!="  { Token.Ne }
    '<'   { Token.Lt }
    '>'   { Token.Gt }
    "<="  { Token.Le }
    ">="  { Token.Ge }

    '='   { Token.Assign }
    "+="  { Token.AssignAdd }
    "-="  { Token.AssignSub }
    "*="  { Token.AssignMul }
    "**=" { Token.AssignPow }
    "%="  { Token.AssignMod }
    "//=" { Token.AssignIntDiv }
    "&="  { Token.AssignBitAnd }
    "|="  { Token.AssignBitOr }
    "^="  { Token.AssignBitXor }
    "<<=" { Token.AssignLeftShift }
    ">>=" { Token.AssignRightShift }
    
    "and"      { Token.And }
    "assert"   { Token.Assert }
    "break"    { Token.Break }
    "continue" { Token.Continue }
    "count"    { Token.Count }
    "def"      { Token.Def }
    "elif"     { Token.Elif }
    "else"     { Token.Else }
    "for"      { Token.For }
    "if"       { Token.If }
    "in"       { Token.In }
    "not"      { Token.Not }
    "or"       { Token.Or }
    "pass"     { Token.Pass }
    "raise"    { Token.Raise }
    "range"    { Token.Range }
    "return"   { Token.Return }
    "revert"   { Token.Revert }
    "self"     { Token.Self }
    "uint256"  { Token.UInt256 }
%%

All : Decl      { \c -> [$1 c] }
    | Decl All  { \c -> ($1 c) : ($2 c) }


Atom : name               { \_ -> LocalVar $1 }
     | "self" '.' name    { \_ -> StorageVar $3 } 
     | string             { \c -> Const (checkedUInt256OfString c $1) }
     | number             { \c -> Const (checkedUInt256OfInteger c $1) }


Call : name '(' ExprList ')' { \c -> PrivateOrBuiltinCall $1 ($3 c) }
     | name '(' ')'          { \_ -> PrivateOrBuiltinCall $1 [] }

Primary : Atom         { $1 }
        | Call         { $1 }
        | '(' Expr ')' { $2 }  -- surprisingly I can't find this rule in the official Python grammar (either as a primary or as an atom)

Power : Primary "**" Factor { \c -> BinOp Pow ($1 c) ($3 c) }
      | Primary             { $1 }

Factor -- '+' Factor                      { \c }
       : '-' Factor                      { \c -> UnOp Neg ($2 c) }
       | '~' Factor                      { \c -> UnOp BitwiseNot ($2 c) }
       | Power                           { $1 }

Term : Term '*' Factor                   { \c -> BinOp Mul ($1 c) ($3 c) }
     | Term "//" Factor                  { \c -> BinOp Quot ($1 c) ($3 c) }
     | Term '%' Factor                   { \c -> BinOp Mod ($1 c) ($3 c) }
     | Factor                            { $1 }

Sum : Sum '+' Term                       { \c -> BinOp Add ($1 c) ($3 c) }
    | Sum '-' Term                       { \c -> BinOp Sub ($1 c) ($3 c) }
    | Term                               { $1 }

ShiftExpr : ShiftExpr "<<" Sum           { \c -> BinOp ShiftLeft  ($1 c) ($3 c) }
          | ShiftExpr ">>" Sum           { \c -> BinOp ShiftRight ($1 c) ($3 c) }
          | Sum                          { $1 }

BitwiseAnd : BitwiseAnd '&' ShiftExpr    { \c -> BinOp BitwiseAnd ($1 c) ($3 c) }
           | ShiftExpr                   { $1 }

BitwiseXor : BitwiseXor '^' BitwiseAnd   { \c -> BinOp BitwiseXor ($1 c) ($3 c) }
           | BitwiseAnd                  { $1 }

BitwiseOr : BitwiseOr '|' BitwiseXor     { \c -> BinOp BitwiseOr ($1 c) ($3 c) }
          | BitwiseXor                   { $1 }

CompOp : '<'  { binopLt }
       | '>'  { binopGt }
       | "<=" { binopLe }
       | ">=" { binopGe }
       | "==" { binopEq }
       | "!=" { binopNe }

-- currently not supporting chain comparisons
Comparison : BitwiseOr CompOp BitwiseOr   { \c -> BinOp $2 ($1 c) ($3 c) }
           | BitwiseOr                    { $1 }

Negation : "not" Negation   { \c -> UnOp LogicalNot ($2 c) }
         | Comparison       { $1 }

Conjunction : Conjunction "and" Negation { \c -> LogicalAnd ($1 c) ($3 c) }
            | Negation                   { $1 }

Disjunction : Disjunction "or" Conjunction { \c -> LogicalOr ($1 c) ($3 c) }
            | Conjunction                  { $1 }

Expr : Disjunction "if" Disjunction "else" Expr { \c -> IfThenElse ($3 c) ($1 c) ($5 c) }
     | Disjunction                              { $1 }

ExprList : Expr ',' ExprList { \c -> ($1 c) : ($3 c) }
         | Expr              { \c -> [$1 c] }

ArgNames : name               { [$1] }
         | name ',' ArgNames  { $1 : $3 }

Args : '(' ')'          { [] }
     | '(' ArgNames ')' { $2 }

Assignable : "self" '.' name { AssignableStorageVar $3 }
           | name            { AssignableLocalVar $1 }

BinopAssign : "+="  { Add }
            | "-="  { Sub }
            | "*="  { Mul }
            | "//=" { Quot }  -- we don't have floats yet, so no /
            | "%="  { Mod }
            | "**=" { Pow }
            | "<<=" { ShiftLeft }
            | ">>=" { ShiftRight }
            | "|="  { BitwiseOr }
            | "&="  { BitwiseAnd }
            | "^="  { BitwiseXor }            

SmallStmt : "pass"                      { \_ -> Pass }
          | "break"                     { \_ -> Break }
          | "continue"                  { \_ -> Continue }
          | "return"                    { \_ -> Return Nothing }
          | "return" Expr               { \c -> Return (Just ($2 c)) }
          | "revert"                    { \_ -> Revert }
          | "raise" Expr                { \c -> Raise ($2 c) }
          | "assert" Expr               { \c -> Assert ($2 c) Nothing }
          | "assert" Expr ',' Expr      { \c -> Assert ($2 c) (Just ($4 c)) }
          | Assignable '=' Expr         { \c -> Assign $1 ($3 c) }
          | Assignable BinopAssign Expr { \c -> BinOpAssign $1 $2 ($3 c) }
          | Expr                        { \c -> ExprStmt ($1 c) }

-- We don't consider LocalVarDecl a small statement
-- because it's sort of let-in compound in disguise.
-- During compilation, it actually becomes compound.
LocalVarDecl : name ':' "uint256"           { \_ -> LocalVarDecl $1 Nothing }
             | name ':' "uint256" '=' Expr  { \c -> LocalVarDecl $1 (Just ($5 c)) }

AfterIf : Expr ':' newline Block    { \c -> IfElseStmt ($1 c) ($4 c) Nothing }
        | Expr ':' newline Block "elif" AfterIf 
                { \c -> IfElseStmt ($1 c) ($4 c) (Just [($6 c)]) }
        | Expr ':' newline Block "else" ':' newline Block 
                { \c -> IfElseStmt ($1 c) ($4 c) (Just ($8 c)) }

IfElseStmt : "if" AfterIf  { $2 }

FixedRangeLoop : "for" name "in" "range" '(' number ')' ':' newline Block
            --     1    2    3      4     5    6     7   8     9     10
                    { \c -> FixedRangeLoop $2 Nothing (checkedUInt256OfInteger c $6) ($10 c) }
               | "for" name "in" "range" '(' number ',' number ')' ':' newline Block
            --     1    2    3      4     5     6    7    8     9  10    11     12
                    { \c -> FixedRangeLoop $2 (Just (checkedUInt256OfInteger c $6)) (checkedUInt256OfInteger c $8) ($12 c) }

FixedCountLoop : "for" name "in" "count" '(' Expr ',' number ')' ':' newline Block
            --     1    2    3      4     5   6    7    8     9  10    11     12
                    { \c -> FixedCountLoop $2 ($6 c) (checkedUInt256OfInteger c $8) ($12 c) }
 

Stmt : SmallStmt newline    { \c -> SmallStmt ($1 c) }
     | LocalVarDecl newline { $1 }
     | IfElseStmt           { $1 }
     | FixedRangeLoop       { $1 }
     | FixedCountLoop       { $1 }

Stmts : Stmt        { \c -> [$1 c] }
      | Stmt Stmts  { \c -> ($1 c) : ($2 c) }

Block : indent Stmts dedent { $2 }

FunDecl : "def" name Args ':' newline Block { \c -> FunDecl $2 $3 ($6 c) }
VarDecl : name ':' "uint256" newline { \_ -> StorageVarDecl $1 }

Decl : VarDecl { $1 }
     | FunDecl { $1 }

--------------------------------------------------------
{
parseError :: [Token.Token] -> a
parseError ts = error $ "Parse error: " ++ show (take 10 ts)

checkedUInt256OfInteger :: VyperConfig -> Integer -> Uint256
checkedUInt256OfInteger c n =
    let z = zOfInteger n in
    let result = uint256_of_Z c z in
    let z' = z_of_uint256 c result in
    if z_eqb z z'
        then result
        else error "constant too large for uint256"

byteListOfString :: String -> [Word8]
byteListOfString = Data.ByteString.unpack . encodeUtf8 . Data.Text.pack

integerOfByteList :: [Word8] -> Integer
integerOfByteList a = f 0 a
    where f n []  = n
          f n (h:t) = f ((n `Data.Bits.shiftL` 8) .|. toInteger h) t

checkedUInt256OfString :: VyperConfig -> String -> Uint256
checkedUInt256OfString c =
    checkedUInt256OfInteger c . integerOfByteList . byteListOfString


}
-- vim: set ft=haskell:
