From Coq Require Import String ZArith Eqdep_dec.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L10.Expr L20.AST L10.Interpret L20.Interpret.

From Vyper.From10To20 Require Import Translate Callset FunCtx Expr.

(* This tactic applies interpret_translated_expr wherever possible. *)
Local Ltac expr :=
  let e20 := fresh "e20" in
  let e10 := fresh "e10" in
  let E := fresh "E" in
  remember (L20.Expr.interpret_expr _ _ _ _ _ _ _ _) as e20;
  remember (L10.Expr.interpret_expr _ _ _ _ _ _ _ _) as e10;
  assert (E: e20 = e10) by (subst; now apply interpret_translated_expr);
  rewrite E; clear E; subst e10; subst e20.


Lemma interpret_translated_small_stmt {C: VyperConfig}
                                {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                {cd: L10.Descend.calldag}
                                (builtins: string -> option builtin)
                                (fc: fun_ctx cd bigger_call_depth_bound)
                                {cd2: L20.Descend.calldag}
                                (ok: cd2 = translate_calldag cd)
                                {do_call_10: forall
                                      (fc': fun_ctx cd smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                {do_call_20: forall
                                      (fc': fun_ctx cd2 smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                (DoCallOk: forall fc' world arg_values,
                                             do_call_20 (translate_fun_ctx fc' ok) world arg_values
                                              =
                                             do_call_10 fc' world arg_values)
                                (world: world_state)
                                (loc: string_map uint256)
                                {ss10: L10.AST.small_stmt}
                                {s20: L20.AST.stmt}
                                (StmtOk: s20 = let is_private_call := fun name: string =>
                                                  match cd_declmap cd name with
                                                  | Some _ => true
                                                  | _ => false
                                                  end
                                               in translate_small_stmt is_private_call ss10)
                                (CallOk20: let _ := string_set_impl in 
                                   FSet.is_subset (L20.Callset.stmt_callset s20)
                                                  (L20.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk10: let _ := string_set_impl in 
                                   FSet.is_subset (L10.Callset.small_stmt_callset ss10)
                                                  (L10.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
   L20.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok) do_call_20 builtins
                           world loc s20 CallOk20
    =
   L10.Stmt.interpret_small_stmt Ebound fc do_call_10 builtins
                                 world loc ss10 CallOk10.
Proof.
induction ss10.
{ (* pass *) now subst. }
{ (* break *) now subst. }
{ (* continue *) now subst. }
{ (* return *)
  subst. cbn.
  destruct result. 2:{ easy. }
  cbn. now expr.
}
{ (* revert *) now subst. }
{ (* raise *)
  subst. cbn. expr.
  now L10.Expr.destruct_let_pair.
}
{ (* assert *)
  subst. cbn. expr.
  L10.Expr.destruct_let_pair.
  destruct e. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z). 2:{ trivial. }
  destruct error. 2: { easy. }
  (* there's an error message *)
  expr.
  L10.Expr.destruct_let_pair.
  match goal with
  |- _ = match ?e with | ExprSuccess _ => _ | ExprAbort _ => _ end => now destruct e
  end.
}
{ (* assign *)
  subst. cbn. expr.
  L10.Expr.destruct_let_pair.
  unfold L10.Stmt.do_assign. unfold L20.Stmt.do_assign.
  destruct e. 2:{ trivial. } 
  destruct lhs. { trivial. }
  now rewrite storage_var_is_declared_ok.
}
{ (* binop assign *)
  subst. cbn.
  destruct lhs; cbn.
  { (* local var *)
    unfold map_lookup.
    remember (Map.lookup loc name) as m.
    destruct m.
    {
      expr.
      destruct L10.Expr.interpret_expr.
      unfold L20.Stmt.do_assign.
      destruct e. 2:{ trivial. }
      rewrite<- Heqm. trivial.
    }
    unfold expr_error. trivial.
  }
  (* global var *)
  rewrite storage_var_is_declared_ok.
  unfold L20.Stmt.do_assign.
  remember (L10.Expr.storage_var_is_declared _ _) as is_declared.
  destruct is_declared. 2:easy.
  expr.
  destruct L10.Expr.interpret_expr.
  destruct e. 2:{ trivial. }
  rewrite storage_var_is_declared_ok.
  rewrite<- Heqis_declared.
  trivial.
}
(* expr *)
subst. cbn. expr.
now L10.Expr.destruct_let_pair.
Qed.

(*



Theorem interpret_translated_call {C: VyperConfig}
                                  (builtins: string -> option L10.Interpret.builtin)
                                  {cd: L10.Interpret.calldag}
                                  {call_depth_bound: nat}
                                  (fc: L10.Interpret.fun_ctx cd call_depth_bound)
                                  {cd2: L20.Interpret.calldag}
                                  (ok: cd2 = translate_calldag cd)
                                  (world: world_state)
                                  (arg_values: list uint256):
  L20.Interpret.interpret_call builtins (translate_fun_ctx fc ok) world arg_values
   =
  L10.Interpret.interpret_call builtins fc world arg_values.
Proof.
induction call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (L10.Interpret.fun_bound_ok _ _ fc)). }
pose (is_private_call := fun name: string =>
          match L10.Interpret.cd_declmap _ _ cd name with
          | Some _ => true
          | _ => false
          end).
assert(F: L20.Interpret.fun_decl _ _ (translate_fun_ctx fc ok)
           = 
          translate_decl is_private_call (L10.Interpret.fun_decl _ _ fc)).
{
  clear IHcall_depth_bound.
  unfold translate_fun_ctx in *. cbn in *.
  unfold cached_translated_decl in *.
  remember (translate_fun_ctx_fun_decl_helper fc ok) as foo. clear Heqfoo.
  remember (Interpret.cd_declmap cd2 (L10.Interpret.fun_name cd (S call_depth_bound) fc)) as d.
  destruct d. 2:{ contradiction. }
  subst. cbn in Heqd.
  remember (L10.Interpret.cd_declmap L10.AST.decl L10.Callset.decl_callset cd
                                     (L10.Interpret.fun_name cd (S call_depth_bound) fc)) as x.
  destruct x. 2:{ discriminate. }
  inversion Heqd. unfold is_private_call.
  f_equal. inversion Heqx.
  assert (D := L10.Interpret.fun_decl_ok _ _ fc).
  rewrite D in *. inversion H1. (* XXX *)
  trivial.
}
unfold L20.Interpret.interpret_call.
unfold L10.Interpret.interpret_call.
rewrite F.






  intro H. clear H.
  
  
  
remember  as d10.


unfold translate_fun_ctx. unfold cached_translated_decl.
remember (L10.Interpret.fun_name _ _ fc) as fun_name.

unfold translate_fun_ctx.





Theorem translate_ok {C: VyperConfig}
                     (builtins: string -> option L10.Interpret.builtin)
                     (cd: L10.Interpret.calldag)
                     (fun_name: string)
                     (world: world_state)
                     (arg_values: list uint256):
  L20.Interpret.interpret builtins (translate_calldag cd) fun_name world arg_values
   =
  L10.Interpret.interpret builtins cd fun_name world arg_values.
Proof.
unfold L10.Interpret.interpret. unfold L20.Interpret.interpret.
remember (L10.Interpret.cd_declmap cd fun_name) as d. 
unfold translate_calldag.
unfold L20.Interpret.make_fun_ctx_and_bound. cbn.
revert translate_dag_helper.
destruct d.
*)
