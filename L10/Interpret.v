From Coq Require Import String Arith NArith ZArith Eqdep_dec.
From Vyper Require Import Config.
From Vyper.L10 Require Import AST Base Callset Descend Expr Stmt.
From Vyper Require FSet Map UInt256.

Local Open Scope list_scope.
Local Open Scope string_scope.

Section Interpret.
Context {C: VyperConfig}.

Local Lemma interpret_call_helper {this_decl: decl}
                                  {fun_name: string}
                                  {arg_names: list string}
                                  {body: list stmt}
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let _ := string_set_impl in FSet.is_subset (stmt_list_callset body) (decl_callset this_decl) = true.
Proof.
subst this_decl. unfold decl_callset. apply FSet.is_subset_refl.
Qed.


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
          match bind_args arg_names arg_values with
          | inl err => (world, expr_error err)
          | inr loc =>
              let '(world', loc', result) := interpret_stmt_list Ebound fc (interpret_call builtins)
                                                                 builtins world loc body
                                                                 (interpret_call_helper E)
              in (world', match result with
                          | StmtSuccess => ExprSuccess zero256
                          | StmtReturnFromFunction x => ExprSuccess x
                          | StmtAbort a => ExprAbort a
                          end)
          end
      | _ => fun _ => (world, expr_error "a declaration is found but it's not a function")
      end eq_refl
  end eq_refl.

Local Lemma make_fun_ctx_helper {cd: calldag}
                          {name: string}
                          {d : decl}
                          (Ed : cd_declmap cd name = Some d)
                          (Edepth : cd_depthmap cd name = None):
  False.
Proof.
assert (W := cd_depthmap_ok cd name).
rewrite Ed in W. rewrite Edepth in W. exact W.
Qed.

Definition make_fun_ctx_and_bound (cd: calldag)
                                  (name: string)
: option { bound: nat & fun_ctx cd bound }
:= match cd_declmap cd name as maybe_d return _ = maybe_d -> _ with
   | None => fun _ => None
   | Some d => fun Ed =>
      match cd_depthmap cd name as depth' return _ = depth' -> _ with
      | None => fun Edepth => False_rect _ (make_fun_ctx_helper Ed Edepth)
      | Some depth => fun Edepth => Some (existT _
                                                 (S depth)
                                                 {| fun_name := name
                                                  ; fun_decl := d
                                                  ; fun_decl_ok := Ed
                                                  ; fun_depth := depth
                                                  ; fun_depth_ok := Edepth
                                                  ; fun_bound_ok := proj2 (Nat.ltb_lt _ _)
                                                                          (Nat.lt_succ_diag_r _)
                                                 |})
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

(*

Lemma interpret_stmt_fun_ctx_irrel {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                   (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                   {cd: calldag}
                                   {fc1 fc2: fun_ctx cd bigger_call_depth_bound}
                                   (FcOk: fun_name fc1 = fun_name fc2)
                                   (do_call: forall
                                                 (fc': fun_ctx cd smaller_call_depth_bound)
                                                 (world: world_state)
                                                 (arg_values: list uint256),
                                               world_state * expr_result uint256)
                                   (builtins: string -> option builtin)
                                   (world: world_state)
                                   (loc: string_map uint256)
                                   (s: stmt)
                                   (NotLocVar: is_local_var_decl s = false)
                                   (CallOk1: let _ := string_set_impl in 
                                                FSet.is_subset (stmt_callset s)
                                                               (decl_callset (fun_decl fc1))
                                                = true)
                                   (CallOk2: let _ := string_set_impl in 
                                                FSet.is_subset (stmt_callset s)
                                                               (decl_callset (fun_decl fc2))
                                                = true):
  interpret_stmt Ebound fc1 do_call builtins world loc s NotLocVar CallOk1
   =
  interpret_stmt Ebound fc2 do_call builtins world loc s NotLocVar CallOk2.
Proof.
*)

End Interpret.