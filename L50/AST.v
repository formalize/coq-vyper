From Coq Require Import String.
From Vyper Require Import Config.
From Vyper.L50 Require Import Types.

Inductive expr {C: VyperConfig}
:= FunCall (name: string) (args: list expr) 
 | LocVar (name: string)
 | Const (t: yul_type) (val: yul_value t).

Definition typename: Type := yul_type * string.

Inductive stmt {C: VyperConfig}
:= BlockStmt (s: block)
 | VarDecl (vars: list typename) (init: option expr)
 | Assign (lhs: list string) (rhs: expr)
 | If (cond: expr) (body: block)
 | Expr (e: expr)
 | Switch (e: expr) (cases: list case) (default: option block)
 | For (init: block) (cond: expr) (after body: block)
 | Break
 | Continue
 | Leave
with case  {C: VyperConfig} := Case (t: yul_type) (val: yul_value t) (body: block)
with block {C: VyperConfig} := Block (body: list stmt).

Record fun_decl {C: VyperConfig} := {
  fd_name: string;
  fd_inputs: list typename;
  fd_outputs: list typename;
  fd_body: block;
}.

Definition program {C: VyperConfig}: Type := string_map fun_decl * block.


Definition is_var_decl {C: VyperConfig} (s: stmt)
:= match s with
   | VarDecl _ _ => true
   | _ => false
   end.

Program Definition var_decl_unpack {C: VyperConfig} (s: stmt) (IsVarDecl: is_var_decl s = true)
: list typename * option expr
:= match s with
   | VarDecl vars init => (vars, init)
   | _ => False_rect _ _
   end.
Next Obligation.
destruct s; cbn in IsVarDecl; try discriminate.
exact (H vars init eq_refl).
Qed.