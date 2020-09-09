From Coq Require Import String Arith.
From Vyper Require Import Config L10.AST NaryFun.
From Vyper Require UInt256.

Inductive abort {C: VyperConfig}
:= AbortError (msg: string)
 | AbortException (data: uint256)
 | AbortBreak
 | AbortContinue
 | AbortReturnFromContract
 | AbortRevert.

Inductive expr_result {C: VyperConfig} (type: Type)
:= ExprSuccess (value: type)
 | ExprAbort (a: abort).
Arguments ExprSuccess {C type}.
Arguments ExprAbort {C type}.

Inductive stmt_result {C: VyperConfig} (return_type: Type)
:= StmtSuccess
 | StmtAbort (a: abort)
 | StmtReturnFromFunction (value: return_type).
Arguments StmtSuccess {C _}.
Arguments StmtAbort {C _}.
Arguments StmtReturnFromFunction {C _}.


Section Base.
Context {C: VyperConfig}.


Definition expr_error {type: Type} (msg: string) := @ExprAbort C type (AbortError msg).

(*************************************************************************************************)

Definition interpret_unop (op: unop) (a: uint256)
: expr_result uint256
:= match UInt256.interpret_unop op a with
   | Some result => ExprSuccess result
   | None => expr_error "arithmetic error"
   end.

Definition interpret_binop (op: binop) (a b: uint256)
: expr_result uint256
:= match UInt256.interpret_binop op a b with
   | Some result => ExprSuccess result
   | None => expr_error "arithmetic error"
   end.

(*************************************************************************************************)

Definition map_lookup {Value} (m: string_map Value) := let _ := string_map_impl in Map.lookup m.
Definition map_insert {Value} (m: string_map Value) := let _ := string_map_impl in Map.insert m.
Definition map_remove {Value} (m: string_map Value) := let _ := string_map_impl in Map.remove m.

Definition builtin := { arity: nat
                      & world_state -> nary_fun uint256 arity (world_state * expr_result uint256) 
                      }.

Definition call_builtin {arity: nat}
                        (args: list uint256)
                        (ArityOk: (arity =? List.length args)%nat = true)
                        (callable: nary_fun uint256 arity (world_state * expr_result uint256))
: world_state * expr_result uint256
:= fst (nary_call callable args (Nat.eq_le_incl _ _ (proj1 (Nat.eqb_eq _ _) ArityOk))).

End Base.