module Token where

data Token = Name String  -- used to be named Ident but it's too similar to Indent
           | Number Integer
           | String String

           | OpenParen
           | CloseParen
           | Colon
           | Comma
           | Dot

           | Plus  -- unary or binary
           | Minus -- unary or binary
           | Star  -- usually multiplication, but also possibly in *args
           | DoubleStar -- usually power, but also possibly in **kwargs
           | IntDiv -- //
           | Mod    -- %
           | BitAnd -- &
           | BitNot -- ~
           | BitOr  -- |
           | BitXor -- ^
           | LeftShift  -- <<
           | RightShift -- >>

           | Arrow -- ->

           | Assign -- =
           | AssignAdd -- +=
           | AssignSub -- -=
           | AssignMul -- *=
           | AssignMod -- %=
           | AssignPow -- **=
           | AssignIntDiv -- //=
           | AssignBitAnd -- &=
           | AssignBitOr  -- |=
           | AssignBitXor -- ^=
           | AssignLeftShift  -- <<=
           | AssignRightShift -- >>=

           | Lt
           | Gt
           | Le
           | Ge
           | Eq
           | Ne

           | Indent
           | Dedent
           | Newline

           -- keywords (must all be listed in LexerUtils.keywordMap):
           | And
           | As
           | Assert
           | Break
           | Const
           | Continue
           | Contract
           | Count  -- for i in count(..., ...)
           | Def
           | Elif
           | Else
           | Emit
           | Event
           | For
           | From
           | Idx
           | If
           | In
           | Import
           | Map
           | Not
           | Or
           | Pass
           | Pub
           | Raise -- I don't see it in the Fe grammar currently but that can't be right
           | Range -- for i in range(..., ...)
           | Return
           | Revert
           | Self
           | Type
           | UInt256 -- I've decided to make it a keyword for now
           | While
        deriving (Eq, Show)
