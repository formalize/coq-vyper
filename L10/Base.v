From Coq Require Import String Arith ZArith HexString.
From Vyper Require Import Config L10.AST NaryFun.
From Vyper Require UInt256.

Definition Z_of_string (s: string)
:= Z.of_N
     (List.fold_left (fun x y => N.lor (N.shiftl x 8) y)
       (List.map Ascii.N_of_ascii (list_ascii_of_string s))
       0%N).

Example hex_arithmetic_error:
  HexString.of_Z (Z_of_string "arithmetic error") = "0x61726974686d65746963206572726f72"%string.
Proof.                                             (*  a r i t h m e t i c   e r r o r *)
trivial.
Qed.


(* 210119: removed AbortError because the compiled code has to reproduce it with pure uint256s *)
Inductive abort {C: VyperConfig}
:= AbortException (data: uint256)
 | AbortBreak
 | AbortContinue
 | AbortReturnFromContract
 | AbortRevert.

Definition string_of_abort {C: VyperConfig} (a: abort)
:= (match a with
    | AbortException n => "exception(" ++ HexString.of_Z (Z_of_uint256 n) ++ ")"
    | AbortBreak => "break"
    | AbortContinue => "continue"
    | AbortReturnFromContract => "return_from_contract"
    | AbortRevert => "revert"
    end)%string.

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


Definition expr_error {type: Type} (msg: string) 
:= @ExprAbort C type (AbortException (uint256_of_Z (Z_of_string msg))).

Definition stmt_error {type: Type} (msg: string) 
:= @StmtAbort C type (AbortException (uint256_of_Z (Z_of_string msg))).

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