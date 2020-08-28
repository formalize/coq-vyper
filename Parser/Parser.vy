%{
Require Import String.
From Vyper Require Import L20.AST. 
%}

%token NUM VAR_NAME

%start<AST.expr> expr

%%

expr:
| num = NUM
  { AST.expr.Const num }
| var = VAR_NAME
  { AST.expr.LocalVar var } 

