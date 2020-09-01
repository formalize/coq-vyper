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

Definition do_assign {return_type: Type} 
                     (world: world_state) (loc: string_map uint256)
                     (lhs: assignable)
                     (computed_rhs: expr_result uint256)
: world_state * string_map uint256 * stmt_result return_type
:= let _ := string_map_impl in
   match computed_rhs with
   | ExprAbort ab => (world, loc, StmtAbort ab)
   | ExprSuccess a =>
       match lhs with
       | AssignableLocalVar name =>
           match Map.lookup loc name with
           | None => (world, loc, StmtAbort (AbortError "undeclared local variable"))
           | Some _ => (world, Map.insert loc name a, StmtSuccess)
           end
       | AssignableStorageVar name =>
           match storage_lookup world name with
           | None => (world, loc, StmtAbort (AbortError "undeclared global variable"))
           | Some _ => (storage_insert world name a, loc, StmtSuccess)
           end
       end
   end.

Definition do_binop_assign {return_type: Type} 
                           (world: world_state) (loc: string_map uint256)
                           (lhs: assignable)
                           (op: binop)
                           (computed_rhs: expr_result uint256)
: world_state * string_map uint256 * stmt_result return_type
:= let _ := string_map_impl in
   match computed_rhs with
   | ExprAbort ab => (world, loc, StmtAbort ab)
   | ExprSuccess a =>
       match lhs with
       | AssignableLocalVar name =>
           match Map.lookup loc name with
           | None => (world, loc, StmtAbort (AbortError "undeclared local variable"))
           | Some old_val =>
                match interpret_binop op old_val a with
                | ExprSuccess new_val => (world, Map.insert loc name new_val, StmtSuccess)
                | ExprAbort ab => (world, loc, StmtAbort ab)
                end
           end
       | AssignableStorageVar name =>
           match storage_lookup world name with
           | None => (world, loc, StmtAbort (AbortError "undeclared global variable"))
           | Some old_val =>
                match interpret_binop op old_val a with
                | ExprSuccess new_val => (storage_insert world name new_val, loc, StmtSuccess)
                | ExprAbort ab => (world, loc, StmtAbort ab)
                end
           end
       end
   end.

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