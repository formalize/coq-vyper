From Coq Require Import String ZArith Eqdep_dec.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L20.AST L10.Interpret L20.Interpret.

From Vyper.From10To20 Require Import Translate Callset FunCtx.

Lemma storage_var_is_declared_ok {C: VyperConfig}
                                 (cd: L10.Descend.calldag)
                                 (name: string):
  L20.Expr.storage_var_is_declared (translate_calldag cd) name
   =
  L10.Expr.storage_var_is_declared cd name.
Proof.
unfold L20.Expr.storage_var_is_declared. unfold L10.Expr.storage_var_is_declared.
cbn. destruct cd_declmap; trivial.
now destruct d.
Qed.

Lemma interpret_translated_expr {C: VyperConfig}
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
                                {e10: L10.AST.expr}
                                {e20: L20.AST.expr}
                                (ExprOk: e20 = translate_expr 
                                                 (fun name: string =>
                                                   match cd_declmap cd name with
                                                   | Some _ => true
                                                   | _ => false
                                                   end)
                                                e10)
                                (CallOk20: let _ := string_set_impl in 
                                   FSet.is_subset (L20.Callset.expr_callset e20)
                                                  (L20.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk10: let _ := string_set_impl in 
                                   FSet.is_subset (L10.Callset.expr_callset e10)
                                                  (L10.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
   L20.Expr.interpret_expr Ebound (translate_fun_ctx fc ok) do_call_20 builtins
                                world loc e20 CallOk20
    =
   L10.Expr.interpret_expr Ebound fc do_call_10 builtins
                                world loc e10 CallOk10.
Proof.
revert e20 ExprOk CallOk20 world loc. induction e10 using L10.AST.expr_ind'; intros.
{ (* Const *) now subst. }
{ (* LocalVar *) now subst. }
{ (* StorageVar *)
  subst. cbn.
  rewrite storage_var_is_declared_ok.
  now destruct L10.Expr.storage_var_is_declared.
}
{ (* UnOp *)
  subst. cbn.
  rewrite (IHe10 (L10.Callset.callset_descend_unop eq_refl CallOk10)); trivial.
}
{ (* BinOp *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_binop_left eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_binop_left eq_refl CallOk10)) as (world_a, result_a).
  destruct result_a. 2:{ trivial. }
  rewrite (IHe10_2 (L10.Callset.callset_descend_binop_right eq_refl CallOk10)); trivial.
}
{ (* IfThenElse *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_if_cond eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_if_cond eq_refl CallOk10)) as (world_cond, result_cond).
  destruct result_cond. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z).
  { (* else *) rewrite (IHe10_3 (L10.Callset.callset_descend_if_else eq_refl CallOk10)); trivial. }
  (* then *)   rewrite (IHe10_2 (L10.Callset.callset_descend_if_then eq_refl CallOk10)); trivial.
}
{ (* LogicalAnd *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_and_left eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_and_left eq_refl CallOk10)) as (world_a, result_a).
  destruct result_a. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z). { trivial. }
  rewrite (IHe10_2 (L10.Callset.callset_descend_and_right eq_refl CallOk10)); trivial.
}
{ (* LogicalOr *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_or_left eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_or_left eq_refl CallOk10)) as (world_a, result_a).
  destruct result_a. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z). 2:{ trivial. }
  rewrite (IHe10_2 (L10.Callset.callset_descend_or_right eq_refl CallOk10)); trivial.
}
(* call *)
subst. cbn.
cbn in CallOk20.
remember (cd_declmap cd name) as d.
destruct d; cbn;
  remember (fix interpret_expr_list 
                        (w: world_state) (loc: string_map uint256) 
                        (exprs : list L20.AST.expr)
                        (CallOk : FSet.is_subset (Callset.expr_list_callset exprs)
                                    (L20.Callset.decl_callset (cached_translated_decl fc eq_refl))
                                  = true)
                        := _)
    as interpret_expr_list_20;
  remember (fix translate_expr_list (l: list L10.AST.expr): list L20.AST.expr := _)
    as translate_expr_list;
  remember (fix interpret_expr_list
                        (w: world_state) (loc: string_map uint256) 
                        (exprs : list L10.AST.expr)
                        (CallOk : FSet.is_subset (L10.Callset.expr_list_callset exprs)
                                    (L10.Callset.decl_callset
                                       (fun_decl fc)) =
                                  true)
                        := _)
    as interpret_expr_list_10.
{ (* PrivateCall *)
  assert (L: interpret_expr_list_20 world loc (translate_expr_list args)
               (L20.Callset.callset_descend_args eq_refl CallOk20)
              =
             interpret_expr_list_10 world loc args 
               (L10.Callset.callset_descend_args eq_refl CallOk10)).
  {
    remember (L20.Callset.callset_descend_args eq_refl CallOk20) as CallsOk20.
    remember (L10.Callset.callset_descend_args eq_refl CallOk10) as CallsOk10.
    clear CallOk10 HeqCallsOk10 CallOk20 HeqCallsOk20.
    revert world loc. induction args. { now subst. }
    intros. cbn in *.
    assert (CallsOk10' := CallsOk10).
    rewrite FSet.union_subset_and in CallsOk10'.
    rewrite Bool.andb_true_iff in CallsOk10'.
    destruct CallsOk10' as (HeadCallOk, TailCallsOk).
    subst. cbn.
    rewrite (List.Forall_inv H HeadCallOk) by trivial.
    match goal with
    |- (let (_, _) := ?l in _) = let (_, _) := ?r in _ =>
       remember l as lhs_head_result;
       remember r as rhs_head_result
    end.
    assert (R: lhs_head_result = rhs_head_result).
    { subst. f_equal. apply Eqdep_dec.eq_proofs_unicity. decide equality. }
    rewrite<- R.
    clear Heqlhs_head_result Heqrhs_head_result R rhs_head_result.
    destruct lhs_head_result as (world', result_h).
    destruct result_h. 2:{ trivial. }
    now rewrite (IHargs (List.Forall_inv_tail H)
                        (L20.Callset.callset_descend_tail eq_refl CallsOk20)
                        (L10.Callset.callset_descend_tail eq_refl CallsOk10) world' loc).
  }
  rewrite L.
  clear L Heqinterpret_expr_list_10 Heqinterpret_expr_list_20 H.
  destruct (interpret_expr_list_10 world loc args (L10.Callset.callset_descend_args eq_refl CallOk10))
    as (world', result_args).
  destruct result_args. 2:{ trivial. }
  match goal with
  |- _ = match ?x with Some _ => _ | None => _ end =>
          remember x as maybe_ctx10
  end.
  clear interpret_expr_list_10 interpret_expr_list_20 world.
  assert (D: L20.Descend.fun_ctx_descend (translate_fun_ctx fc eq_refl) CallOk20 eq_refl eq_refl
              =
             match maybe_ctx10 with
             | Some ctx => Some (translate_fun_ctx ctx eq_refl)
             | None => None
             end).
  {
    (* This follows fun_ctx_descend_irrel. *)
    unfold L10.Descend.fun_ctx_descend in Heqmaybe_ctx10.
    unfold L20.Descend.fun_ctx_descend.
    assert (InnerOk: forall (d1: L10.AST.decl)
                            (Edecl1: cd_declmap cd name = Some d1)
                            (d2: L20.AST.decl)
                            (Edecl2: cd_declmap (translate_calldag cd) name = Some d2),
                   L20.Descend.fun_ctx_descend_inner (translate_fun_ctx fc eq_refl) CallOk20 
                                                     eq_refl eq_refl Edecl2
                    =
                   match L10.Descend.fun_ctx_descend_inner fc CallOk10 eq_refl eq_refl Edecl1 with
                   | Some ctx10 => Some (translate_fun_ctx ctx10 eq_refl)
                   | None => None
                   end).
    {
      intros.
      unfold L10.Descend.fun_ctx_descend_inner.
      unfold L20.Descend.fun_ctx_descend_inner.
      remember (fun (depth: nat) (Edepth: cd_depthmap (translate_calldag cd) name = Some depth) =>
          Some
            {|
            fun_name := name;
            fun_depth := depth;
            fun_depth_ok := Edepth;
            fun_decl := d2;
            fun_decl_ok := Edecl2;
            fun_bound_ok := L20.Descend.call_descend'
                              (translate_fun_ctx fc eq_refl) CallOk20 eq_refl eq_refl
                              Edecl2 Edepth |})
        as some_branch_l.
      remember (fun (Edepth: cd_depthmap (translate_calldag cd) name = None) =>
        False_rect (option (fun_ctx (translate_calldag cd) smaller_call_depth_bound))
          (Descend.fun_ctx_descend_helper Edecl2 Edepth))
        as none_branch_l.
      remember (fun (depth: nat) (Edepth: cd_depthmap cd name = Some depth) =>
        Some
          {|
          fun_name := name;
          fun_depth := depth;
          fun_depth_ok := Edepth;
          fun_decl := d1;
          fun_decl_ok := Edecl1;
          fun_bound_ok := L10.Descend.call_descend' fc CallOk10 eq_refl eq_refl Edecl1 Edepth |})
        as some_branch_r.
      remember (fun Edepth : cd_depthmap cd name = None =>
                  False_rect (option (fun_ctx cd smaller_call_depth_bound))
                             (L10.Descend.fun_ctx_descend_helper Edecl1 Edepth))
        as none_branch_r.
      assert (NoneOkL: forall (Edepth: cd_depthmap (translate_calldag cd) name = None),
                         none_branch_l Edepth = None).
      { intro. exfalso. exact (Descend.fun_ctx_descend_helper Edecl2 Edepth). }
      assert (NoneOkR: forall (Edepth: cd_depthmap cd name = None),
                         none_branch_r Edepth = None).
      { intro. exfalso. exact (L10.Descend.fun_ctx_descend_helper Edecl1 Edepth). }
      clear Heqnone_branch_l Heqnone_branch_r.
      revert none_branch_l none_branch_r NoneOkL NoneOkR.
      assert (SomeBranchOk: forall (depth: nat)
                                   (Edepth1: cd_depthmap cd name = Some depth)
                                   (Edepth2: cd_depthmap (translate_calldag cd) name = Some depth),
                     some_branch_l depth Edepth2 
                      =
                     match some_branch_r depth Edepth1 with
                     | Some ctx10 => Some (translate_fun_ctx ctx10 eq_refl)
                     | None => None
                     end).
      {
        intros. subst. unfold translate_fun_ctx. cbn.
        f_equal.
        assert (D: d2 = cached_translated_decl
                {|
                fun_name := name;
                fun_depth := depth;
                fun_depth_ok := Edepth1;
                fun_decl := d1;
                fun_decl_ok := Edecl1;
                fun_bound_ok := L10.Descend.call_descend' fc CallOk10 eq_refl eq_refl Edecl1 Edepth1 |}
                eq_refl).
        {
          unfold cached_translated_decl. cbn.
          remember (FunCtx.translate_fun_ctx_fun_decl_helper _ eq_refl) as Bad. clear HeqBad.
          cbn in Bad. revert Bad.
          rewrite Edecl1.
          intro Bad. clear Bad.
          unfold translate_calldag in Edecl2. cbn in Edecl2. rewrite Edecl1 in Edecl2.
          symmetry in Edecl2. inversion Edecl2. trivial.
        }
        subst. f_equal; apply PropExtensionality.proof_irrelevance.
      } (* SomeBranchOk *)
      clear Heqsome_branch_l Heqsome_branch_r Heqmaybe_ctx10 translate_expr_list Heqtranslate_expr_list
            CallOk10 CallOk20 Edecl1 Edecl2 d1 d2 maybe_ctx10 world' loc args value DoCallOk
            do_call_10 do_call_20.
      assert (R: cd_depthmap (translate_calldag cd) name = cd_depthmap cd name). { trivial. }
      revert some_branch_l some_branch_r SomeBranchOk.
      rewrite R. clear R.
      destruct (cd_depthmap cd name); intros. { apply SomeBranchOk. }
      rewrite (NoneOkL eq_refl).
      rewrite (NoneOkR eq_refl).
      trivial.
    } (* InnerOk *)
    remember L20.Descend.fun_ctx_descend_inner as inner20. clear Heqinner20.
    remember L10.Descend.fun_ctx_descend_inner as inner10. clear Heqinner10.
    subst.
    revert inner10 inner20 InnerOk.
    remember (cd_declmap cd name) as maybe_d1.
    remember (cd_declmap (translate_calldag cd) name) as maybe_d2.
    destruct maybe_d1; destruct maybe_d2; intros. 4:{ trivial. }
    { apply InnerOk. }
    1-2: exfalso; clear inner10 inner20 InnerOk.
    1-2: unfold translate_calldag in Heqmaybe_d2; cbn in Heqmaybe_d2; 
           rewrite<- Heqmaybe_d1 in Heqmaybe_d2; discriminate.
  } (* D *)
  rewrite D.
  assert (DNone := L10.Descend.fun_ctx_descend_none fc CallOk10 eq_refl eq_refl).
  destruct maybe_ctx10.
  { apply DoCallOk. }
  exfalso. rewrite<- Heqmaybe_ctx10 in DNone.
  rewrite<- Heqd in DNone.
  assert (Bad: Some d = None) by tauto.
  discriminate.
}
(* BuiltinCall *)
  assert (L: interpret_expr_list_20 world loc (translate_expr_list args)
               (L20.Callset.callset_descend_builtin_args eq_refl CallOk20)
              =
             interpret_expr_list_10 world loc args 
               (L10.Callset.callset_descend_args eq_refl CallOk10)).
  {
    remember (L20.Callset.callset_descend_builtin_args eq_refl CallOk20) as CallsOk20.
    remember (L10.Callset.callset_descend_args eq_refl CallOk10) as CallsOk10.
    clear CallOk10 HeqCallsOk10 CallOk20 HeqCallsOk20.
    revert world loc. induction args. { now subst. }
    intros. cbn in *.
    assert (CallsOk10' := CallsOk10).
    rewrite FSet.union_subset_and in CallsOk10'.
    rewrite Bool.andb_true_iff in CallsOk10'.
    destruct CallsOk10' as (HeadCallOk, TailCallsOk).
    subst. cbn.
    rewrite (List.Forall_inv H HeadCallOk) by trivial.
    match goal with
    |- (let (_, _) := ?l in _) = let (_, _) := ?r in _ =>
       remember l as lhs_head_result;
       remember r as rhs_head_result
    end.
    assert (R: lhs_head_result = rhs_head_result).
    { subst. f_equal. apply Eqdep_dec.eq_proofs_unicity. decide equality. }
    rewrite<- R.
    clear Heqlhs_head_result Heqrhs_head_result R rhs_head_result.
    destruct lhs_head_result as (world', result_h).
    destruct result_h. 2:{ trivial. }
    now rewrite (IHargs (List.Forall_inv_tail H)
                        (L20.Callset.callset_descend_tail eq_refl CallsOk20)
                        (L10.Callset.callset_descend_tail eq_refl CallsOk10) world' loc).
  }
  rewrite L.
  clear L Heqinterpret_expr_list_10 Heqinterpret_expr_list_20 H.
  destruct (interpret_expr_list_10 world loc args (L10.Callset.callset_descend_args eq_refl CallOk10))
    as (world', result_args).
  destruct result_args. 2:{ trivial. }
  assert (DNone := L10.Descend.fun_ctx_descend_none fc CallOk10 eq_refl eq_refl).
  symmetry in Heqd.
  apply DNone in Heqd.
  rewrite Heqd.
  trivial.
Qed.
