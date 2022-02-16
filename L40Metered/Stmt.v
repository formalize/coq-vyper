From Coq Require Import String Arith ZArith PropExtensionality Lia.

From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require Import AST Descend Callset Descend Expr Stmt.
From Vyper.L40Metered Require Import Interpret Expr.

Lemma small_stmt_metering_ok
           {C: VyperConfig}
           {bigger_call_depth_bound smaller_call_depth_bound: nat}
           (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
           {cd: calldag}
           (fc: fun_ctx cd bigger_call_depth_bound)
           (do_call: forall
                         (fc': fun_ctx cd smaller_call_depth_bound)
                         (world: world_state)
                         (arg_values: list uint256),
                       world_state * expr_result uint256)
           (do_call_metered: forall
                               (decl: L40.AST.decl)
                               (world: world_state)
                               (arg_values: list uint256),
                             world_state * option (expr_result uint256))
           (DoCallOk: forall (fc': fun_ctx cd smaller_call_depth_bound)
                             (world: world_state)
                             (arg_values: list uint256),
                        let '(world', result) := do_call fc' world arg_values in
                          do_call_metered (fun_decl fc') world arg_values
                           =
                          (world', Some result))
           (builtins: string -> option builtin)
           (world: world_state)
           (loc: memory)
           (loops: list loop_ctx)
           (ss: small_stmt)
           (CallOk: let _ := string_set_impl in 
                      FSet.is_subset (small_stmt_callset ss)
                                     (decl_callset (fun_decl fc))
                      = true):
  let '(world', result) := interpret_small_stmt Ebound fc do_call builtins
                                                world loc loops ss CallOk
   in interpret_small_stmt_metered (cd_decls cd) do_call_metered builtins
                                   world loc loops ss
       =
      (world', Some result).
Proof.
destruct ss.
{ (* abort *) easy. }
{ (* return *)
  cbn.
  assert (M := expr_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                builtins world loc loops e
                                (callset_descend_return eq_refl CallOk)).
  destruct interpret_expr as (world', result).
  rewrite M.
  now destruct result.
}
{ (* raise *)
  cbn.
  assert (M := expr_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                builtins world loc loops e
                                (callset_descend_raise eq_refl CallOk)).
  destruct interpret_expr as (world', result).
  rewrite M.
  now destruct result.
}
{ (* assign *)
  cbn.
  assert (M := expr_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                builtins world loc loops rhs
                                (callset_descend_assign_rhs eq_refl CallOk)).
  destruct interpret_expr as (world', result).
  rewrite M.
  now destruct result.
}
(* ExprStmt *)
cbn.
assert (M := expr_metering_ok Ebound fc do_call do_call_metered DoCallOk
                              builtins world loc loops e
                              (callset_descend_expr_stmt eq_refl CallOk)).
destruct interpret_expr as (world', result).
rewrite M.
now destruct result.
Qed.

Local Lemma weak_block_metering_ok
           {C: VyperConfig}
           {bigger_call_depth_bound smaller_call_depth_bound: nat}
           (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
           {cd: calldag}
           (fc: fun_ctx cd bigger_call_depth_bound)
           (do_call: forall
                         (fc': fun_ctx cd smaller_call_depth_bound)
                         (world: world_state)
                         (arg_values: list uint256),
                       world_state * expr_result uint256)
           (do_call_metered: forall
                               (decl: L40.AST.decl)
                               (world: world_state)
                               (arg_values: list uint256),
                             world_state * option (expr_result uint256))
           (DoCallOk: forall (fc': fun_ctx cd smaller_call_depth_bound)
                             (world: world_state)
                             (arg_values: list uint256),
                        let '(world', result) := do_call fc' world arg_values in
                          do_call_metered (fun_decl fc') world arg_values
                           =
                          (world', Some result))
           (builtins: string -> option builtin)
           (b: block)
           (StmtOk: (* this condition is what makes this lemma weak,
                       later we can prove a stronger lemma without this *)
              match b with
              | Block body =>
                 List.Forall
                   (fun s : stmt =>
                    forall (CallOk : FSet.is_subset (stmt_callset s) (decl_callset (fun_decl fc)) = true) 
                      (world : world_state) (loc : memory) (loops : list loop_ctx),
                    let '(world', result) := interpret_stmt Ebound fc do_call builtins
                                                            world loc loops s CallOk
                    in
                     interpret_stmt_metered (cd_decls cd) do_call_metered builtins
                                                           world loc loops s 
                      =
                    (world', Some result))
                   body
              end)
           (world: world_state)
           (loc: memory)
           (loops: list loop_ctx)
           (CallOk: let _ := string_set_impl in 
                      FSet.is_subset (block_callset b)
                                     (decl_callset (fun_decl fc))
                      = true):
  let '(world', result) := interpret_block Ebound fc do_call builtins
                                           world loc loops b CallOk
   in interpret_block_metered (cd_decls cd) do_call_metered builtins
                              world loc loops b
       =
      (world', Some result).
Proof.
destruct b as [body]. cbn.
remember (callset_descend_block eq_refl CallOk) as COk. clear HeqCOk CallOk.
revert world loc COk. induction body. { easy. }
intros. cbn.
assert (HeadOk := List.Forall_inv StmtOk (callset_descend_stmts_head eq_refl COk)
                                  world loc loops).
cbn in HeadOk.
fold (interpret_stmt Ebound fc do_call builtins world loc loops a).
destruct interpret_stmt as ((world', loc'), result).
rewrite HeadOk.
destruct result; trivial.
apply (IHbody (List.Forall_inv_tail StmtOk) world' loc'
              (callset_descend_stmts_tail eq_refl COk)).
Qed.

Lemma stmt_metering_ok
           {C: VyperConfig}
           {bigger_call_depth_bound smaller_call_depth_bound: nat}
           (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
           {cd: calldag}
           (fc: fun_ctx cd bigger_call_depth_bound)
           (do_call: forall
                         (fc': fun_ctx cd smaller_call_depth_bound)
                         (world: world_state)
                         (arg_values: list uint256),
                       world_state * expr_result uint256)
           (do_call_metered: forall
                               (decl: L40.AST.decl)
                               (world: world_state)
                               (arg_values: list uint256),
                             world_state * option (expr_result uint256))
           (DoCallOk: forall (fc': fun_ctx cd smaller_call_depth_bound)
                             (world: world_state)
                             (arg_values: list uint256),
                        let '(world', result) := do_call fc' world arg_values in
                          do_call_metered (fun_decl fc') world arg_values
                           =
                          (world', Some result))
           (builtins: string -> option builtin)
           (world: world_state)
           (loc: memory)
           (loops: list loop_ctx)
           (s: stmt)
           (CallOk: let _ := string_set_impl in 
                      FSet.is_subset (stmt_callset s)
                                     (decl_callset (fun_decl fc))
                      = true):
  let '(world', result) := interpret_stmt Ebound fc do_call builtins
                                                world loc loops s CallOk
   in interpret_stmt_metered (cd_decls cd) do_call_metered builtins
                                   world loc loops s
       =
      (world', Some result).
Proof.
revert world loc loops.
induction s using stmt_ind'; intros.
{ (* small *)
  apply small_stmt_metering_ok.
  apply DoCallOk.
}
{ (* switch without default *)
  cbn.
  assert (M := expr_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                builtins world loc loops e
                                (callset_descend_switch_expr eq_refl CallOk)).
  destruct interpret_expr as (world', result).
  rewrite M. clear M.
  destruct result as [value|]. 2:reflexivity.
  remember (callset_descend_cases eq_refl CallOk) as COk. clear HeqCOk CallOk.
  cbn in COk. revert COk.
  induction cases as [|h]. { easy. }
  intro COk.
  destruct h as [h_guard].
  fold (interpret_block Ebound fc do_call builtins).
  destruct (Z_of_uint256 value =? Z_of_uint256 h_guard)%Z.
  { (* match found *)
    assert (Hh := List.Forall_inv H). cbn in Hh.
    apply (weak_block_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                         builtins body Hh world' loc loops
                                         (callset_descend_cases_head eq_refl COk)).
  }
  (* no match *)
  apply (IHcases (List.Forall_inv_tail H) (callset_descend_cases_tail eq_refl COk)).
}
{
  (* switch with default *)
  cbn.
  assert (M := expr_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                builtins world loc loops e
                                (callset_descend_switch_expr eq_refl CallOk)).
  destruct interpret_expr as (world', result).
  rewrite M. clear M.
  destruct result as [value|]. 2:reflexivity.
  remember (callset_descend_cases eq_refl CallOk) as COk. clear HeqCOk.
  remember (callset_descend_cases_default eq_refl CallOk) as DOk. clear HeqDOk CallOk.
  cbn in COk. revert COk.
  induction cases as [|h].
  {
    intro Foo.
    apply (weak_block_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                  builtins (Block default) H0 world' loc loops
                                  DOk).
  }
  intro COk.
  destruct h as [h_guard].
  fold (interpret_block Ebound fc do_call builtins).
  destruct (Z_of_uint256 value =? Z_of_uint256 h_guard)%Z.
  { (* match found *)
    assert (Hh := List.Forall_inv H). cbn in Hh.
    apply (weak_block_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                         builtins body Hh world' loc loops
                                         (callset_descend_cases_head eq_refl COk)).
  }
  (* no match *)
  apply (IHcases (List.Forall_inv_tail H) (callset_descend_cases_tail eq_refl COk)).
}
(* loop *)
remember (Block body) as loop_body.
cbn. fold (interpret_block Ebound fc do_call builtins).
subst loop_body.
remember (Z.to_nat (Z_of_uint256 count)) as n. clear Heqn.
remember (OpenArray.get loc var) as offset. clear Heqoffset.
revert world loc.
induction n. { trivial. }
intros.
assert (W := let _ := memory_impl in
             weak_block_metering_ok Ebound fc do_call do_call_metered DoCallOk
                                    builtins (Block body) H world loc
                                    ({|
                                       loop_offset := offset;
                                       loop_count := count;
                                       loop_countdown := n
                                    |} :: loops)
                                    (callset_descend_loop_body eq_refl CallOk)).
destruct interpret_block as ((world', loc'), result). rewrite W. clear W.
destruct result. 3:trivial.
{ apply IHn. }
destruct a; trivial.
apply IHn.
Qed.

Lemma block_metering_ok
           {C: VyperConfig}
           {bigger_call_depth_bound smaller_call_depth_bound: nat}
           (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
           {cd: calldag}
           (fc: fun_ctx cd bigger_call_depth_bound)
           (do_call: forall
                         (fc': fun_ctx cd smaller_call_depth_bound)
                         (world: world_state)
                         (arg_values: list uint256),
                       world_state * expr_result uint256)
           (do_call_metered: forall
                               (decl: L40.AST.decl)
                               (world: world_state)
                               (arg_values: list uint256),
                             world_state * option (expr_result uint256))
           (DoCallOk: forall (fc': fun_ctx cd smaller_call_depth_bound)
                             (world: world_state)
                             (arg_values: list uint256),
                        let '(world', result) := do_call fc' world arg_values in
                          do_call_metered (fun_decl fc') world arg_values
                           =
                          (world', Some result))
           (builtins: string -> option builtin)
           (world: world_state)
           (loc: memory)
           (loops: list loop_ctx)
           (b: block)
           (CallOk: let _ := string_set_impl in 
                      FSet.is_subset (block_callset b)
                                     (decl_callset (fun_decl fc))
                      = true):
  let '(world_and_loc', result) := interpret_block Ebound fc do_call builtins
                                           world loc loops b CallOk
   in interpret_block_metered (cd_decls cd) do_call_metered builtins
                              world loc loops b
       =
      (world_and_loc', Some result).
Proof.
refine (weak_block_metering_ok Ebound fc do_call do_call_metered DoCallOk
                               builtins b _ world loc loops CallOk).
clear CallOk world loc loops.
destruct b as [body].
rewrite List.Forall_forall.
intros s H CallOk world loc loops. clear H.
apply (stmt_metering_ok Ebound fc do_call do_call_metered DoCallOk
                        builtins world loc loops).
Qed.

(****************************************************************************)
(* DEPRECATED *)
Lemma small_stmt_respects_var_cap
           {C: VyperConfig}
           {bigger_call_depth_bound smaller_call_depth_bound: nat}
           (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
           {cd: calldag}
           (fc: fun_ctx cd bigger_call_depth_bound)
           (do_call: forall
                         (fc': fun_ctx cd smaller_call_depth_bound)
                         (world: world_state)
                         (arg_values: list uint256),
                       world_state * expr_result uint256)
           (do_call_metered: forall
                               (decl: L40.AST.decl)
                               (world: world_state)
                               (arg_values: list uint256),
                             world_state * option (expr_result uint256))
           (DoCallOk: forall (fc': fun_ctx cd smaller_call_depth_bound)
                             (world: world_state)
                             (arg_values: list uint256),
                        let '(world', result) := do_call fc' world arg_values in
                          do_call_metered (fun_decl fc') world arg_values
                           =
                          (world', Some result))
           (builtins: string -> option builtin)
           (world: world_state)
           (loc: memory)
           (loops: list loop_ctx)
           (ss: small_stmt)
           (CallOk: let _ := string_set_impl in 
                      FSet.is_subset (small_stmt_callset ss)
                                     (decl_callset (fun_decl fc))
                      = true):
  let '(world, loc', result) :=
      interpret_small_stmt_metered (cd_decls cd) do_call_metered builtins
                                   world loc loops ss
  in forall k,
       (var_cap_small_stmt ss <= k)%N
        ->
       let _ := memory_impl in
       OpenArray.get loc k = OpenArray.get loc' k.
Proof.
remember (interpret_small_stmt_metered (cd_decls cd) do_call_metered builtins world loc loops ss) as output.
destruct output as ((world', loc'), result).
intros k L. cbn.
destruct ss; cbn in L; cbn in Heqoutput.
{ (* abort *) inversion Heqoutput. now subst. }
{ (* return *)
  destruct interpret_expr_metered as (w, r).
  destruct r as [r|]; [destruct r as [|r]|]; inversion Heqoutput; now subst.
}
{ (* raise *)
  destruct interpret_expr_metered as (w, r).
  destruct r as [r|]; [destruct r as [|r]|]; inversion Heqoutput; now subst.
}
{ (* assign *)
  destruct interpret_expr_metered as (w, r).
  destruct r as [r|]; [destruct r as [|r]|]; inversion Heqoutput; subst; try easy.
  rewrite OpenArray.put_ok.
  assert (B: (lhs <> k)%N) by lia.
  apply N.eqb_neq in B. now rewrite B.
}
(* expr *)
destruct interpret_expr_metered as (w, r).
destruct r as [r|]; [destruct r as [|r]|]; inversion Heqoutput; now subst.
Qed.
