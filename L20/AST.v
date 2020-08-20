From Coq Require Import String List.

From Vyper Require Import Config FSet.
From Vyper Require L10.AST L10.Interpret.

Section AST.

Context {C: VyperConfig}.

Inductive expr
:= Const (val: uint256)
 | LocalVar (name: string) (* x *)
 | StorageVar (name: string) (* self.x *)
 | UnOp (op: L10.AST.unop) (a: expr)
 | BinOp (op: L10.AST.binop) (a b: expr)
 | IfThenElse (cond yes no: expr)
 | LogicalAnd (a b: expr)
 | LogicalOr (a b: expr)
 | PrivateCall (name: string) (args: list expr)
 | BuiltinCall (name: string) (args: list expr).

(** "Small statement" is a term used in Python grammar, also in rust-vyper grammar.
    Here we don't count local variable declarations as small statements.
 *)
Inductive small_stmt
:= Pass
 | Abort (ab: L10.Interpret.abort)
 | Return (result: expr)
 | Raise (error: expr)
 | Assign (lhs: L10.AST.assignable) (rhs: expr)
 | ExprStmt (e: expr).

(** Lists of statements are obsolete as they make recursion too tricky.
    Now the statements can be chained together by [Semicolon];
    also [LocalVarDecl] has an explicit scope.
 *)
Inductive stmt
:= SmallStmt (s: small_stmt)
 | LocalVarDecl (name: string) (init: expr) (scope: stmt)
 | IfElseStmt (cond: expr) (yes: stmt) (no: stmt)
 | Loop (var: string) (start: expr) (count: uint256) (body: stmt)
 | Semicolon (a b: stmt).

Inductive decl
:= (* ImportDecl
      EventDecl
      InterfaceDecl
      StructDecl *)
  StorageVarDecl (name: string)
| FunDecl (name: string) (args: list string) (body: stmt).

Definition decl_name (d: decl)
: string
:= match d with
   | StorageVarDecl name | FunDecl name _ _ => name
   end.

End AST.