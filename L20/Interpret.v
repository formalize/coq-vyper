From Coq Require Import String Arith NArith ZArith.
From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import Base.
From Vyper.L20 Require Import AST Callset Descend Expr Stmt.
From Vyper Require FSet Map L10.UInt256 L10.Interpret.

Local Open Scope list_scope.
Local Open Scope string_scope.

Section Interpret.

Context {C: VyperConfig}.

Local Lemma interpret_call_helper {this_decl: decl}
                                  {fun_name: string}
                                  {arg_names: list string}
                                  {body: stmt}
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let _ := string_set_impl in FSet.is_subset (stmt_callset body) (decl_callset this_decl) = true.
Proof.
subst this_decl. unfold decl_callset. apply FSet.is_subset_refl.
Qed.

(*************************************************************************************************)

Definition map_lookup {Value} (m: string_map Value) := let _ := string_map_impl in Map.lookup m.
Definition map_insert {Value} (m: string_map Value) := let _ := string_map_impl in Map.insert m.
Definition map_remove {Value} (m: string_map Value) := let _ := string_map_impl in Map.remove m.

Fixpoint interpret_call {call_depth_bound: nat}
                        {cd: calldag}
                        (builtins: string -> option builtin)
                        (fc: fun_ctx cd call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256)
{struct call_depth_bound}
: world_state * expr_result uint256
:= match call_depth_bound as call_depth_bound' return _ = call_depth_bound' -> _ with
   | O => fun Ebound => False_rect _ (Nat.nlt_0_r (fun_depth fc)
                                                  (eq_ind _ _
                                                          (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))
                                                          _ Ebound))
   | S new_call_depth_bound => fun Ebound =>
        match fun_decl fc as d return _ = d -> _ with
        | FunDecl _ arg_names body => fun E =>
            match L10.Interpret.bind_args arg_names arg_values with
            | inl err => (world, expr_error err)
            | inr loc =>
                let '(world', loc', result) := interpret_stmt Ebound fc (interpret_call builtins)
                                                              builtins world loc body 
                                                              (interpret_call_helper E)
                in (world', match result with
                            | StmtSuccess => ExprSuccess zero256
                            | StmtReturnFromFunction x => ExprSuccess x
                            | StmtAbort AbortBreak
                            | StmtAbort AbortContinue => expr_error "break and continue not allowed"
                            | StmtAbort a => ExprAbort a
                            end)
            end
        | _ => fun _ => (world, expr_error "declaration not found")
        end eq_refl
   end eq_refl.

(** This is a simplified interface to interpret_call that takes care of creating a function context. *)
Definition interpret (builtins: string -> option builtin)
                     (cd: calldag)
                     (function_name: string)
                     (world: world_state)
                     (arg_values: list uint256)
: world_state * expr_result uint256
:= match make_fun_ctx_and_bound cd function_name with
   | None => (world, expr_error "declaration not found")
   | Some (existT _ bound fc) => interpret_call builtins fc world arg_values
   end.

End Interpret.