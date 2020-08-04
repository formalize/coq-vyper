From Coq Require Import String List.

Require Import Config FSet.

Inductive unop
:= BitwiseNot
 | Neg.

Inductive binop
:= LogicalOr
 | LogicalAnd
 | Lt
 | Le
 | Gt
 | Ge
 | Eq
 | Ne
 | In
 | NotIn
 | Is
 | IsNot
 | BitwiseOr
 | BitwiseAnd
 | BitwiseXor
 | ShiftLeft
 | ShiftRight
 | Add
 | Sub
 | Mul
 | Div
 | Quot
 | Mod
 | Pow.

Inductive assignable
:= AssignableLocalVar (name: string)
 | AssignableStorageVar (name: string).

Section AST.

Context {C: VyperConfig}.

Inductive expr
:= Const (val: uint256)
 | LocalVar (name: string) (* x *)
 | StorageVar (name: string) (* self.x *)
 | UnOp (op: unop) (a: expr)
 | BinOp (op: binop) (a b: expr)
(* | IfThenElse (cond yes no: expr) *)
 | PrivateOrBuiltinCall (name: string) (args: list expr).

(** "Small statement" is a term used in Python grammar, also in rust-vyper grammar.
    Here we don't count local variable declarations as small statements.
 *)
Inductive small_stmt
:= Pass
 | Break
 | Continue
 | Return (result: option expr)
 | Revert
 | Raise (error: expr)
 | Assert (cond: expr) (error: option expr)
(* | Log *)
 | Assign (lhs: assignable) (rhs: expr)
 | BinOpAssign (lhs: assignable) (op: binop) (rhs: expr)
 | ExprStmt (e: expr).


Inductive stmt
:= SmallStmt (s: small_stmt)
 | LocalVarDecl (name: string) (init: option expr)
 | IfElseStmt (cond: expr) (yes: list stmt) (no: option (list stmt))
 | FixedRangeLoop (var: string) (start: option uint256) (stop: uint256) (body: list stmt)
 | FixedCountLoop (var: string) (start: string) (count: uint256) (body: list stmt).

Inductive decl
:= (* ImportDecl
      EventDecl
      InterfaceDecl
      StructDecl *)
  StorageVarDecl (name: string)
| FunDecl (name: string) (args: list string) (body: expr). (* body: list stmt *)

Definition decl_name (d: decl)
: string
:= match d with
   | StorageVarDecl name | FunDecl name _ _ => name
   end.

End AST.