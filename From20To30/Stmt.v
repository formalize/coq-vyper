From Coq Require Import String ZArith NArith Eqdep_dec Lia.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L20.AST L30.AST L20.Interpret L30.Interpret.

From Vyper.From20To30 Require Import Translate Callset FunCtx Expr.

Definition VarmapInj {C: VyperConfig}
                     (varmap: string_map N)
:= let _ := string_map_impl in
   forall x y,
     match Map.lookup varmap x with
     | Some u =>
         match Map.lookup varmap y with
         | Some v => u = v -> x = y
         | None => True
         end
     | None => True
     end.

Lemma interpret_translated_small_stmt {C: VyperConfig}
                        {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        {cd20: L20.Descend.calldag}
                        (builtins: string -> option builtin)
                        (fc: fun_ctx cd20 bigger_call_depth_bound)
                        {cd30: L30.Descend.calldag}
                        (ok: translate_calldag cd20 = inr cd30)
                        {do_call_20: forall
                              (fc': fun_ctx cd20 smaller_call_depth_bound)
                              (world: world_state)
                              (arg_values: list uint256),
                            world_state * expr_result uint256}
                        {do_call_30: forall
                              (fc': fun_ctx cd30 smaller_call_depth_bound)
                              (world: world_state)
                              (arg_values: list uint256),
                            world_state * expr_result uint256}
                        (DoCallOk: forall fc' world arg_values,
                                     do_call_30 (translate_fun_ctx fc' ok) world arg_values
                                      =
                                     do_call_20 fc' world arg_values)
                        (world: world_state)
                        (locmap: string_map uint256)
                        (locmem: memory)
                        {ss20: L20.AST.small_stmt}
                        {s30: L30.AST.stmt}
                        (varmap: string_map N)
                        (VI: VarmapInj varmap)
                        (offset: N)
                        (Agree: VarsAgree varmap locmap locmem)
                        (Bound: VarsBound varmap offset)
                        (StmtOk: translate_small_stmt varmap offset ss20 = inr s30)
                        (CallOk30: let _ := string_set_impl in 
                           FSet.is_subset (L30.Callset.stmt_callset s30)
                                          (L30.Callset.decl_callset
                                             (fun_decl
                                               (translate_fun_ctx fc ok)))
                           = true)
                        (CallOk20: let _ := string_set_impl in 
                           FSet.is_subset (L20.Callset.small_stmt_callset ss20)
                                          (L20.Callset.decl_callset
                                            (fun_decl fc))
                           = true):
   let _ := string_map_impl in
   let _ := memory_impl in
   let '(world30, mem30, result30) := L30.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok)
                                                              do_call_30 builtins
                                                              world locmem s30 CallOk30
   in let '(world20, new_loc, result20) := L20.Stmt.interpret_small_stmt Ebound fc do_call_20 builtins
                                                                world locmap ss20 CallOk20
   in result30 = result20
       /\
      world30 = world20
       /\
      VarsAgree varmap new_loc mem30.
Proof.
destruct ss20; cbn in StmtOk.
{ (* pass *)
  inversion StmtOk. subst s30. cbn.
  split. { trivial. }
  split. { trivial. }
  exact Agree.
}
{ (* abort *) inversion StmtOk. now subst s30. }
{ (* return *)
  remember (translate_expr varmap offset (N.succ offset) result) as e30.
  destruct e30. { discriminate. }
  inversion StmtOk. subst s30. cbn.
  assert (T := interpret_translated_expr Ebound builtins fc ok DoCallOk world locmap locmem
                                         varmap offset (N.succ offset) Agree Bound
                                         (N.lt_succ_diag_r offset)
                                         (eq_sym Heqe30)
                                         (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                                         (L20.Callset.callset_descend_return eq_refl CallOk20)).
  cbn in T.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Expr.interpret_expr as (world20, result20).
  destruct result20, result30; try easy.
  {
    f_equal.
    split. { f_equal. tauto. }
    split. { tauto. }
    destruct T as (T_world, (T_mem, (T_agree, T_dst))).
    exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                   offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
  }
  split. { tauto. }
  split. { tauto. }
  destruct T as (T_world, (T_mem, T_result)).
  exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                               offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
}
{ (* raise *)
  remember (translate_expr varmap offset (N.succ offset) error) as e30.
  destruct e30. { discriminate. }
  inversion StmtOk. subst s30. cbn.
  assert (T := interpret_translated_expr Ebound builtins fc ok DoCallOk world locmap locmem
                                         varmap offset (N.succ offset) Agree Bound
                                         (N.lt_succ_diag_r offset)
                                         (eq_sym Heqe30)
                                         (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                                         (L20.Callset.callset_descend_raise eq_refl CallOk20)).
  cbn in T.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Expr.interpret_expr as (world20, result20).
  destruct result20, result30; try easy.
  {
    split. { f_equal. f_equal. tauto. }
    split. { tauto. }
    destruct T as (T_world, (T_mem, T_result)).
    exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                               offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
  }
  destruct T as (T_world, (T_mem, T_result)).
  split. { f_equal. f_equal. now inversion T_result. }
  split. { trivial. }
  exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                             offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
}
{ (* assign *)
  destruct lhs.
  {
    (* local *)
    assert (B := Bound name). unfold map_lookup in *.
    remember (Map.lookup varmap name) as m.
    destruct m. 2:{ discriminate. }
    remember (translate_expr varmap offset (N.succ offset) rhs) as e30.
    destruct e30. { discriminate. }
    inversion StmtOk. clear StmtOk. subst s30.
    cbn.
    assert (T := interpret_translated_expr Ebound builtins fc ok DoCallOk world locmap locmem
                                           varmap offset (N.succ offset) Agree Bound
                                           (N.lt_succ_diag_r _)
                                           (eq_sym Heqe30)
                                           (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                                           (L20.Callset.callset_descend_assign_rhs eq_refl CallOk20)).
    cbn in T.
    destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
    destruct L20.Expr.interpret_expr as (world20, result20).
    destruct result20, result30; try easy.
    2:{
      cbn.
      destruct T as (T_world, (T_mem, T_result)).
      repeat (split; trivial).
      exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                     offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
    }
    unfold L20.Stmt.do_assign.
    assert (A := Agree name).
    destruct (Map.lookup locmap name). 2:{ now rewrite<- Heqm in A. }
    split. { trivial. }
    split. { tauto. }
    destruct T as (T_world, (T_mem, (T_result, T_dst))).
    intro x.
    assert (V := vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                         offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem x).
    assert (VIx := VI name x).
    rewrite Map.insert_ok.
    destruct (string_dec name x).
    {
      subst x.
      destruct (Map.lookup varmap name). 2:{ easy. }
      rewrite OpenArray.put_ok.
      inversion Heqm. subst n0.
      replace (n =? n)%N with true. 2:{ symmetry. apply N.eqb_eq. trivial. }
      exact T_dst.
    }
    destruct (Map.lookup locmap x). 2:now destruct (Map.lookup varmap x).
    remember (Map.lookup varmap x) as v.
    destruct v. 2:exact V.
    rewrite OpenArray.put_ok.
    rewrite<- Heqm in VIx.
    replace (n =? n1)%N with false. { exact V. }
    symmetry. apply N.eqb_neq. tauto.
  } (* local var *)
  (* global var *)
  cbn.
  assert (B := Bound name). unfold map_lookup in *.
  remember (translate_expr varmap offset (N.succ offset) rhs) as e30.
  destruct e30. { discriminate. }
  inversion StmtOk. clear StmtOk. subst s30.
  cbn.
  assert (T := interpret_translated_expr Ebound builtins fc ok DoCallOk world locmap locmem
                                         varmap offset (N.succ offset) Agree Bound
                                         (N.lt_succ_diag_r _)
                                         (eq_sym Heqe30)
                                         (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                                         (L20.Callset.callset_descend_assign_rhs eq_refl CallOk20)).
  cbn in T.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Expr.interpret_expr as (world20, result20).
  destruct result20, result30; try easy.
  2:{
    destruct T as (T_world, (T_mem, T_result)).
    repeat (split; trivial).
    exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                   offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
  }
  unfold L20.Stmt.do_assign.
  assert (A := Agree name).
  unfold L20.Expr.storage_var_is_declared.
  assert (D := translate_fun_ctx_declmap ok name).
  destruct T as (T_world, (T_mem, (T_result, T_dst))).
  destruct (cd_declmap cd20 name), (cd_declmap cd30 name); try easy.
  2:{
    split. { trivial. }
    split. { trivial. }
    exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                               offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
  }
  destruct d; cbn in D; inversion D; subst.
  {
    split. { trivial. }
    split. { now f_equal. }
    exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                   offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
  }
  destruct (make_varmap args). { discriminate. }
  destruct translate_stmt. { discriminate. }
  inversion D; subst.
  split. { trivial. }
  split. { trivial. }
  exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                             offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
}
(* expr *)
cbn.
unfold map_lookup in *.
assert (T := interpret_translated_expr Ebound builtins fc ok DoCallOk world locmap locmem
                                       varmap offset (N.succ offset) Agree Bound
                                       (N.lt_succ_diag_r _)
                                       StmtOk
                                       CallOk30
                                       (L20.Callset.callset_descend_expr_stmt eq_refl CallOk20)).
cbn in T.
destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
destruct L20.Expr.interpret_expr as (world20, result20).
destruct T as (T_world, (T_mem, T_result)).
destruct result20, result30; try easy;
split; trivial;
split; trivial;
exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                             offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
Qed.

Lemma interpret_translated_stmt {C: VyperConfig}
                        {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        {cd20: L20.Descend.calldag}
                        (builtins: string -> option builtin)
                        (fc: fun_ctx cd20 bigger_call_depth_bound)
                        {cd30: L30.Descend.calldag}
                        (ok: translate_calldag cd20 = inr cd30)
                        {do_call_20: forall
                              (fc': fun_ctx cd20 smaller_call_depth_bound)
                              (world: world_state)
                              (arg_values: list uint256),
                            world_state * expr_result uint256}
                        {do_call_30: forall
                              (fc': fun_ctx cd30 smaller_call_depth_bound)
                              (world: world_state)
                              (arg_values: list uint256),
                            world_state * expr_result uint256}
                        (DoCallOk: forall fc' world arg_values,
                                     do_call_30 (translate_fun_ctx fc' ok) world arg_values
                                      =
                                     do_call_20 fc' world arg_values)
                        (world: world_state)
                        (locmap: string_map uint256)
                        (locmem: memory)
                        {s20: L20.AST.stmt}
                        {s30: L30.AST.stmt}
                        (varmap: string_map N)
                        (VI: VarmapInj varmap)
                        (offset: N)
                        (Agree: VarsAgree varmap locmap locmem)
                        (Bound: VarsBound varmap offset)
                        (StmtOk: translate_stmt varmap offset s20 = inr s30)
                        (CallOk30: let _ := string_set_impl in 
                           FSet.is_subset (L30.Callset.stmt_callset s30)
                                          (L30.Callset.decl_callset
                                             (fun_decl
                                               (translate_fun_ctx fc ok)))
                           = true)
                        (CallOk20: let _ := string_set_impl in 
                           FSet.is_subset (L20.Callset.stmt_callset s20)
                                          (L20.Callset.decl_callset
                                            (fun_decl fc))
                           = true):
   let _ := string_map_impl in
   let _ := memory_impl in
   let '(world30, mem30, result30) := L30.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok)
                                                              do_call_30 builtins
                                                              world locmem s30 CallOk30
   in let '(world20, new_loc, result20) := L20.Stmt.interpret_stmt Ebound fc do_call_20 builtins
                                                                   world locmap s20 CallOk20
   in result30 = result20
       /\
      world30 = world20
       /\
      VarsAgree varmap new_loc mem30.
Proof.
revert world offset varmap s30 StmtOk locmem locmap VI Agree Bound CallOk30 CallOk20.
induction s20; intros.
{ (* small *)
  apply (interpret_translated_small_stmt Ebound builtins fc ok DoCallOk world locmap locmem
                                         varmap VI offset Agree Bound
                                         StmtOk
                                         CallOk30
                                         (L20.Callset.callset_descend_small_stmt eq_refl CallOk20)).
}
{ (* LocalVarDecl *)
  clear s m.
  cbn. cbn in StmtOk.
  assert (A := Agree name). unfold map_lookup in *.
  remember (Map.lookup varmap name) as varmap_name.
  destruct (Map.lookup locmap name), varmap_name; try easy.
  clear A.
  remember (translate_expr varmap offset (N.succ offset) init) as init30.
  destruct init30. { discriminate. }
  remember (translate_stmt (map_insert varmap name offset) (N.succ offset) s20) as body30.
  destruct body30. { discriminate. }
  inversion StmtOk. subst s30. clear StmtOk.
  assert (T := interpret_translated_expr Ebound builtins fc ok DoCallOk world locmap locmem
                                         varmap offset (N.succ offset) Agree Bound
                                         (N.lt_succ_diag_r _)
                                         (eq_sym Heqinit30)
                                         (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                                         (L20.Callset.callset_descend_var_init eq_refl CallOk20)).
  cbn in T. cbn.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Expr.interpret_expr as (world20, result20).
  destruct T as (T_world, (T_mem, T_result)).
  destruct result20, result30; try easy.
  2:{ (* init failed *)
    repeat (split; trivial).
    exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                   offset (N.succ offset) Bound (N.lt_succ_diag_r _) T_mem).
  }
  (* init succeeded *)

  assert (VI': VarmapInj (map_insert varmap name offset)).
  {
    unfold VarmapInj. intros x y.
    unfold map_insert. repeat rewrite Map.insert_ok.
    assert (VIxy := VI x y).
    destruct (string_dec name x).
    {
      subst x.
      destruct (string_dec name y). { easy. }
      assert (By := Bound y).
      destruct (Map.lookup varmap y). 2:{ trivial. }
      intro E. subst.
      apply N.lt_irrefl in By.
      contradiction.
    }
    destruct (string_dec name y).
    { (* this is a mirror of the previous branch with x and y swapped *)
      subst y.
      assert (Bx := Bound x).
      destruct (Map.lookup varmap x). 2:{ trivial. }
      intro E. subst.
      apply N.lt_irrefl in Bx.
      contradiction.
    }
    apply VIxy.
  } (* VI' *)

  assert (Agree': VarsAgree (map_insert varmap name offset) (map_insert locmap name value) mem30).
  {
    intro x.
    unfold map_insert. repeat rewrite Map.insert_ok.
    destruct (string_dec name x). { now subst. }
    apply (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree offset (N.succ offset) Bound
           (N.lt_succ_diag_r offset) T_mem x).
  }

  assert (Bound': VarsBound (map_insert varmap name offset) (N.succ offset)).
  {
    intro x.
    unfold map_insert.
    rewrite Map.insert_ok.
    destruct (string_dec name x). { apply N.lt_succ_diag_r. }
    assert (B := Bound x).
    destruct (Map.lookup varmap x). 2:{ trivial. }
    apply N.lt_lt_succ_r. exact B.
  }

  assert (IH := IHs20 world30 (N.succ offset) (map_insert varmap name offset) _ (eq_sym Heqbody30)
                      mem30 (map_insert locmap name value)
                      VI' Agree' Bound'
                      (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30)
                      (L20.Callset.callset_descend_var_scope eq_refl CallOk20)).

  assert (R:
        (@Callset.callset_descend_semicolon_right C s s0 (@AST.Semicolon C s s0)
           (@Callset.decl_callset C
              (@fun_decl C (@AST.decl C) (@Callset.decl_callset C) cd30 bigger_call_depth_bound
                 (@translate_fun_ctx C bigger_call_depth_bound cd20 fc cd30 ok)))
           (@eq_refl (@AST.stmt C) (@AST.Semicolon C s s0)) CallOk30)
         =
       (@Callset.callset_descend_semicolon_right C s s0 (@AST.Semicolon C s s0)
           (@Callset.decl_callset C (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
           (@eq_refl (@AST.stmt C) (@AST.Semicolon C s s0)) CallOk30)).
  { apply PropExtensionality.proof_irrelevance. }
  rewrite R in IH. clear R.
  destruct L30.Stmt.interpret_stmt as ((world30', mem30'), result30').
  subst world30.
  destruct (L20.Stmt.interpret_stmt Ebound fc do_call_20 builtins world20
            (map_insert locmap name value) s20
            (Callset.callset_descend_var_scope eq_refl CallOk20)) as ((world20', loc20'), result20').
  destruct IH as (IH_result, (IH_world, IH_agree)).
  split. { trivial. }
  split. { assumption. }
  (* goal: VarsAgree varmap (map_remove loc20' name) mem30' *)
  intro x. unfold map_remove.
  rewrite Map.remove_ok.
  assert (A := IH_agree x). unfold map_insert in A.
  repeat rewrite Map.insert_ok in A.
  destruct (string_dec name x).
  { subst x. now rewrite<- Heqvarmap_name. }
  exact A.
}
{ (* IfElseStmt *)
  cbn in StmtOk.
  remember (translate_expr varmap offset (N.succ offset) cond) as cond30.
  destruct cond30. { discriminate. }
  remember (translate_stmt varmap offset s20_1) as then30.
  destruct then30. { discriminate. }
  remember (translate_stmt varmap offset s20_2) as else30.
  destruct else30. { discriminate. }
  inversion StmtOk. subst s30. cbn.
  clear s m.
  assert (Hcond := interpret_translated_expr
                            Ebound builtins fc ok DoCallOk world locmap locmem _ _
                            (N.succ offset) Agree Bound
                            (N.lt_succ_diag_r _) (eq_sym Heqcond30)
                            (Callset.callset_descend_semicolon_left eq_refl CallOk30)
                            (L20.Callset.callset_descend_stmt_if_cond eq_refl CallOk20)).
  cbn in Hcond.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Expr.interpret_expr as (world20, result20).
  destruct Hcond as (Cond_world, (Cond_mem, Cond_result)).
  destruct result20, result30; try easy.
  2:{ (* error in condition *)
    split. { trivial. }
    split. { assumption. }
    apply (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree offset (N.succ offset) Bound
                                   (N.lt_succ_diag_r offset) Cond_mem).
  }
  destruct Cond_result as (Cond_result, Cond_value).
  subst value.
  (* condition computed *)
  destruct (Z_of_uint256 (OpenArray.get mem30 offset) =? 0)%Z.
  { (* else *)
    subst world30.
    assert (IH := IHs20_2 world20 offset varmap _ (eq_sym Heqelse30) mem30 locmap VI
                          (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                                   _ _ Bound (N.lt_succ_diag_r offset) Cond_mem)
                          Bound
                          (L30.Callset.callset_descend_stmt_if_else eq_refl
                            (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30))
                          (L20.Callset.callset_descend_stmt_if_else eq_refl CallOk20)).
    cbn in IH.
    destruct L30.Stmt.interpret_stmt as ((world30', mem30'), result30').
    destruct (L20.Stmt.interpret_stmt Ebound fc do_call_20 builtins world20 locmap s20_2
                (L20.Callset.callset_descend_stmt_if_else eq_refl CallOk20)) as (world20', result20').
    now destruct result20', result30'.
  }
  (* then *)
  subst world30.
  assert (IH := IHs20_1 world20 offset varmap _ (eq_sym Heqthen30) mem30 locmap VI
                        (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                                 _ _ Bound (N.lt_succ_diag_r offset) Cond_mem)
                        Bound
                        (L30.Callset.callset_descend_stmt_if_then eq_refl
                          (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30))
                        (L20.Callset.callset_descend_stmt_if_then eq_refl CallOk20)).
  cbn in IH.
  destruct L30.Stmt.interpret_stmt as ((world30', mem30'), result30').
  destruct (L20.Stmt.interpret_stmt Ebound fc do_call_20 builtins world20 locmap s20_2
              (L20.Callset.callset_descend_stmt_if_else eq_refl CallOk20)) as (world20', result20').
  now destruct result20', result30'.
}
2:{ (* Semicolon *)
  cbn in StmtOk.
  remember (translate_stmt varmap offset s20_1) as t1.
  remember (translate_stmt varmap offset s20_2) as t2.
  destruct t1. { discriminate. }
  destruct t2. { discriminate. }
  inversion StmtOk. subst s30. cbn.

  assert (IH_1 := IHs20_1 world offset varmap _ (eq_sym Heqt1) locmem locmap VI Agree Bound
                          (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                          (L20.Callset.callset_descend_semicolon_left eq_refl CallOk20)).
  cbn in IH_1.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct (L20.Stmt.interpret_stmt Ebound fc do_call_20 builtins world locmap s20_1
             (L20.Callset.callset_descend_semicolon_left eq_refl CallOk20))
     as ((world20, mem20), result20).
  destruct result20, result30; try easy.
  cbn in IH_1. destruct IH_1 as (IH1_result, (IH1_world, IH1_agree)).
  clear IH1_result. subst world30.

  assert (IH_2 := IHs20_2 world20 offset varmap _ (eq_sym Heqt2) mem30 mem20 VI 
                          IH1_agree
                          Bound
                          (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30)
                          (L20.Callset.callset_descend_semicolon_right eq_refl CallOk20)).
  cbn in IH_2.
  destruct L30.Stmt.interpret_stmt as ((world30', mem30'), result30').
  destruct (L20.Stmt.interpret_stmt Ebound fc do_call_20 builtins world20 mem20 s20_2
             (L20.Callset.callset_descend_semicolon_right eq_refl CallOk20))
     as ((world20', mem20'), result20').
  now destruct result20', result30'.
} (* Semicolon *)
(* -------------------------------------------------------------------------------------------------*)
(* Loop *)
cbn in StmtOk.
remember (map_lookup varmap var) as lookup_var.
destruct lookup_var. { discriminate. }
remember (Z_of_uint256 count =? 0)%Z as count_is_0.
destruct count_is_0. { discriminate. }
remember (translate_expr varmap offset (N.succ offset) start) as start30.
destruct start30. { discriminate. }
remember (translate_stmt (map_insert varmap var offset) (N.succ offset) s20) as body30.
destruct body30. { discriminate. }
inversion StmtOk. subst s30. cbn. clear StmtOk.
assert (Hstart := interpret_translated_expr
                          Ebound builtins fc ok DoCallOk world locmap locmem _ _
                          (N.succ offset) Agree Bound
                          (N.lt_succ_diag_r _) (eq_sym Heqstart30)
                          (Callset.callset_descend_semicolon_left eq_refl CallOk30)
                          (L20.Callset.callset_descend_loop_start eq_refl CallOk20)).
cbn in Hstart.
destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
destruct L20.Expr.interpret_expr as (world20, result20).
assert (Q: map_lookup locmap var = None).
{
  assert (A := Agree var).
  unfold map_lookup in *.
  rewrite<- Heqlookup_var in A.
  now destruct (Map.lookup locmap var).
}
rewrite Q. rewrite<- Heqcount_is_0.
destruct result20, result30; try easy.
2:{ (* start computation failed *)
  destruct Hstart as (Start_world, (Start_mem, Start_result)).
  repeat (split; trivial).
  apply (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree offset (N.succ offset) Bound
                               (N.lt_succ_diag_r offset) Start_mem).
}
destruct Hstart as (Start_world, (Start_mem, (Start_result, Start_dst))).
clear Start_result. subst world30. subst value.
remember (Z_of_uint256 (uint256_of_Z (Z_of_uint256 (OpenArray.get mem30 offset) + Z_of_uint256 count - 1)) =?
           Z_of_uint256 (OpenArray.get mem30 offset) + Z_of_uint256 count - 1)%Z
  as no_overflow.
destruct no_overflow.
2:{
  repeat (split; trivial).
  apply (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree offset (N.succ offset) Bound
                                 (N.lt_succ_diag_r offset) Start_mem).
}

(* start computed, now the loop itself *)
remember (Z.to_nat (Z_of_uint256 count)) as countdown. (* n in From10To20 *)
remember (Z_of_uint256 (OpenArray.get mem30 offset)) as cursor.

(* preparing induction *)
remember (Z_of_uint256 (OpenArray.get mem30 offset) + Z_of_uint256 count - 1)%Z as cap.
(* In From10To20 this happens within the induction for some reason *)
assert (CapRange: (0 <= cap < 2 ^ 256)%Z).
{
  symmetry in Heqno_overflow. rewrite Z.eqb_eq in Heqno_overflow.
  rewrite uint256_ok in Heqno_overflow.
  rewrite Z.mod_small_iff in Heqno_overflow by apply two_to_256_ne_0.
  subst cursor cap.
  enough (~ (2 ^ 256 < (Z_of_uint256 (OpenArray.get mem30 offset) + Z_of_uint256 count - 1)%Z <= 0)%Z). 
  { tauto. }
  intro Y.
  assert (Bad := proj2 (Z.ltb_lt _ _) (Z.lt_le_trans _ _ _ (proj1 Y) (proj2 Y))).
  cbn in Bad. discriminate.
}

(* Here Heqcap is the main loop equation: [

      cap = Z_of_uint256 value + Z_of_uint256 count - 1

  ] where cap is constant, value goes up and count goes down.
However, in our interpretation of the count loop we allow overflow
during the last iteration, for example [

    for i in count(2^256 - 2, 2):
      ...

] is the same as [

    for i in [2^256 - 2, 2^256 - 1]:
      ...
] and therefore legit (except that the latter syntax is currently 
not supported). Therefore the main loop equation must be weakened to this: *)
assert (WeakMainLoopEq: 
          cap = (cursor + Z_of_uint256 count - 1)%Z
           \/
          Z_of_uint256 count = 0%Z).
{ left. subst cursor. exact Heqcap. }
clear Heqcap.

assert (Agree': VarsAgree varmap (map_remove locmap var) mem30).
{
  intro x.
  unfold map_remove.
  rewrite Map.remove_ok.
  destruct string_dec.
  { subst x. unfold map_lookup in Heqlookup_var. rewrite<- Heqlookup_var. trivial. }
  exact (vars_agree_if_mem_agree varmap locmap locmem mem30 Agree
                                 _ _ Bound (N.lt_succ_diag_r offset) Start_mem x).
}

clear Start_mem. (* we don't have a way to carry that through induction; Agree' is what we have instead *)
clear Agree Q Heqcursor Heqno_overflow Heqcount_is_0.
revert count locmap world20 mem30 cursor Agree' WeakMainLoopEq
       CallOk30 CallOk20 Heqcountdown.
induction countdown; intros. (* ----------- induction -------------*)
{ repeat (split; trivial). }
(* the following has plenty of dup from LocalVarDecl: *)
assert (BodyInj: VarmapInj (map_insert varmap var offset)).
{
  unfold VarmapInj. intros x y.
  unfold map_insert. repeat rewrite Map.insert_ok.
  assert (VIxy := VI x y).
  destruct (string_dec var x).
  {
    subst x.
    destruct (string_dec var y). { easy. }
    assert (By := Bound y).
    destruct (Map.lookup varmap y). 2:{ trivial. }
    intro E. subst.
    apply N.lt_irrefl in By.
    contradiction.
  }
  destruct (string_dec var y).
  { (* this is a mirror of the previous branch with x and y swapped *)
    subst y.
    assert (Bx := Bound x).
    destruct (Map.lookup varmap x). 2:{ trivial. }
    intro E. subst.
    apply N.lt_irrefl in Bx.
    contradiction.
  }
  apply VIxy.
}
assert (BodyAgree: VarsAgree (map_insert varmap var offset) 
                             (map_insert locmap var (uint256_of_Z cursor))
                             (OpenArray.put mem30 offset (uint256_of_Z cursor))).
{
  intro x.
  unfold map_insert. repeat rewrite Map.insert_ok.
  assert (A := Agree' x).
  unfold map_remove in A. rewrite Map.remove_ok in A.
  destruct (string_dec var x). { now rewrite OpenArray.put_same. }
  assert (B := Bound x).
  destruct (Map.lookup locmap x), (Map.lookup varmap x); try easy.
  rewrite OpenArray.put_ok.
  enough (F: (offset =? n0)%N = false) by now rewrite F.
  rewrite N.eqb_neq.
  intro H. rewrite<- H in B.
  exact (N.lt_irrefl offset B).
}

assert (BodyBound: VarsBound (map_insert varmap var offset) (N.succ offset)).
{
  intro x.
  unfold map_insert.
  rewrite Map.insert_ok.
  destruct (string_dec var x). { apply N.lt_succ_diag_r. }
  assert (B := Bound x).
  destruct (Map.lookup varmap x). 2:{ trivial. }
  apply N.lt_lt_succ_r. exact B.
}

assert (BodyOk := IHs20 world20 (N.succ offset) (map_insert varmap var offset) _ (eq_sym Heqbody30)
                        (OpenArray.put mem30 offset (uint256_of_Z cursor))
                        (map_insert locmap var (uint256_of_Z cursor))
                        BodyInj BodyAgree BodyBound
                        (Callset.callset_descend_loop_body eq_refl
                          (Callset.callset_descend_semicolon_right eq_refl CallOk30))
                        (L20.Callset.callset_descend_loop_body eq_refl CallOk20)).
cbn in BodyOk.
destruct L30.Stmt.interpret_stmt as ((world30', mem30'), result30').
destruct L20.Stmt.interpret_stmt as ((world20', mem20'), result20').
destruct BodyOk as (Body_result, (Body_world, Body_agree)).
subst result30' world30'.
assert (PostBodyAgree: VarsAgree varmap (map_remove mem20' var) mem30').
{
  intro x. assert (A := Body_agree x). unfold map_remove.
  rewrite Map.remove_ok.
  unfold map_insert in A. repeat rewrite Map.insert_ok in A.
  destruct (string_dec var x). 2:apply A.
  subst x. unfold map_lookup in Heqlookup_var. now rewrite<- Heqlookup_var.
}

(* checking that the counter doesn't go below 0 *)
pose (count' := uint256_of_Z (Z.pred (Z_of_uint256 count))).
assert (CountOk: countdown = Z.to_nat (Z_of_uint256 count')).
{
  unfold count'. rewrite uint256_ok.
  assert (R := uint256_range count).
  remember (Z_of_uint256 count) as z. clear Heqz.
  assert (W: z = Z.succ (Z.of_nat countdown)).
  {
    rewrite<- Nat2Z.inj_succ. rewrite Heqcountdown.
    symmetry. apply Z2Nat.id. tauto.
  }
  subst z. rewrite Z.pred_succ.
  replace (Z.of_nat countdown mod 2 ^ 256)%Z with (Z.of_nat countdown).
  { symmetry. apply Nat2Z.id. }
  symmetry. apply Z.mod_small.
  split.
  { (* 0 <= countdown *) apply Nat2Z.is_nonneg. }
  exact (Z.lt_trans _ _ _ (Z.lt_succ_diag_r (Z.of_nat countdown)) (proj2 R)).
}

(* strengthening WeakMainLoopEq *)
assert (MainLoopEq: cap = (cursor + Z_of_uint256 count - 1)%Z).
{
  enough (Z_of_uint256 count <> 0%Z). { tauto. }
  intro J. rewrite J in *.
  cbn in Heqcountdown. discriminate.
}

assert (NextLoopEq: cap = (Z.succ cursor + Z_of_uint256 count' - 1)%Z).
{
  rewrite MainLoopEq.
  enough (Z_of_uint256 count = Z_of_uint256 count' + 1)%Z by lia.
  subst countdown.
  assert (R := uint256_range count).
  assert (R' := uint256_range count').
  lia.
}

assert (WeakNextLoopEq: (cap = Z.succ cursor + Z_of_uint256 count' - 1 \/ Z_of_uint256 count' = 0)%Z).
{ left. apply NextLoopEq. }

assert (IH := IHcountdown count' mem20' world20' mem30' (Z.succ cursor)
                          PostBodyAgree WeakNextLoopEq CallOk30 CallOk20 CountOk).

assert (FixCall30:
            (@Callset.callset_descend_loop_body C (@AST.Loop C offset count' s1) s1 offset count'
               (@Callset.decl_callset C
                  (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
               (@eq_refl (@AST.stmt C) (@AST.Loop C offset count' s1))
               (@Callset.callset_descend_semicolon_right C s0 (@AST.Loop C offset count' s1)
                  (@AST.Semicolon C s0 (@AST.Loop C offset count' s1))
                  (@Callset.decl_callset C
                     (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
                  (@eq_refl (@AST.stmt C) (@AST.Semicolon C s0 (@AST.Loop C offset count' s1)))
                  CallOk30))
              =
            (@Callset.callset_descend_loop_body C (@AST.Loop C offset count s1) s1 offset count
          (@Callset.decl_callset C
             (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
          (@eq_refl (@AST.stmt C) (@AST.Loop C offset count s1))
          (@Callset.callset_descend_semicolon_right C s0 (@AST.Loop C offset count s1)
             (@AST.Semicolon C s0 (@AST.Loop C offset count s1))
             (@Callset.decl_callset C
                (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
             (@eq_refl (@AST.stmt C) (@AST.Semicolon C s0 (@AST.Loop C offset count s1))) CallOk30))).
{ apply PropExtensionality.proof_irrelevance. }
rewrite FixCall30 in IH. clear FixCall30.

assert (FixCall20:
          (@L20.Callset.callset_descend_loop_body C (@L20.AST.Loop C var start count' s20) s20
             var start count'
             (@L20.Callset.decl_callset C
                (@fun_decl C (@L20.AST.decl C) (@L20.Callset.decl_callset C) cd20
                   bigger_call_depth_bound fc))
             (@eq_refl (@L20.AST.stmt C) (@L20.AST.Loop C var start count' s20)) CallOk20)
            =
          (@L20.Callset.callset_descend_loop_body C (@L20.AST.Loop C var start count s20) s20
                var start count
                (@L20.Callset.decl_callset C
                   (@fun_decl C (@L20.AST.decl C) (@L20.Callset.decl_callset C) cd20
                      bigger_call_depth_bound fc))
                (@eq_refl (@L20.AST.stmt C) (@L20.AST.Loop C var start count s20)) CallOk20)).
{ apply PropExtensionality.proof_irrelevance. }
rewrite FixCall20 in IH. clear FixCall20.

destruct result20'; try easy.
now destruct a.
Qed.
