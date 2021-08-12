From Coq Require Import String ZArith NArith Lia PropExtensionality.


From Vyper Require Import Config Builtins Calldag Logic2.
From Vyper.L10 Require Import Base.
From Vyper.L30 Require AST Callset Interpret.
From Vyper.L40 Require AST Callset Interpret.
From Vyper.From30To40 Require Import FunCtx Translate.

(** XXX this is not necessary *)
Lemma var_range_callset {C: VyperConfig} (args_offset args_count: N):
  let _ := string_set_impl in
  FSet.is_empty
    (L40.Callset.expr_list_callset (var_range args_offset args_count))
   = true.
Proof.
cbn.
rewrite var_range_via_nat.
unfold var_range_nat.
remember (N.to_nat args_count) as n.
clear Heqn.
revert args_offset.
induction n; intros. { cbn. rewrite FSet.is_empty_to_list. apply FSet.empty_to_list. }
cbn. rewrite FSet.is_empty_true_iff.
intro x. rewrite FSet.union_ok. rewrite FSet.empty_ok. rewrite Bool.orb_false_l. 
assert (IH := IHn (N.succ args_offset)). rewrite FSet.is_empty_true_iff in IH.
assert (R: forall t,
             (fix var_range' (countdown : nat) : list AST.expr :=
               match countdown with
               | 0 => nil
               | S k => (AST.LocalVar (N.of_nat (N.to_nat args_offset + S n - 1 - k)) :: var_range' k)%list
               end) t
            =
            (fix var_range' (countdown : nat) : list AST.expr :=
              match countdown with
              | 0 => nil
              | S k =>
                  (AST.LocalVar (N.of_nat (N.to_nat (N.succ args_offset) + n - 1 - k)) :: var_range' k)%list
              end) t).
{
  induction t. { trivial. }
  f_equal. { f_equal. lia. }
  apply IHt.
}
rewrite R. clear R. apply IH.
Qed.

(** Interpreting [var_range] always succeeds and results in a view of the local memory
    that can also be obtained directly by [OpenArray.view].
 *)
Lemma interpret_var_range
          {C: VyperConfig}
          {smaller_call_depth_bound: nat}
          (B: builtin_names_config)
          {cd30: L30.Descend.calldag}
          {cd40: L40.Descend.calldag}
          (CalldagOk: translate_calldag B cd30 = inr cd40)
          (fc30: fun_ctx cd30 (S smaller_call_depth_bound))
          (FcNotVar: forall x,
                       fun_decl fc30 <> AST.StorageVarDecl x)
          (do_call_40: forall
                (fc': fun_ctx cd40 smaller_call_depth_bound)
                (world: world_state)
                (arg_values: list uint256),
              world_state * expr_result uint256)
          (builtins: string -> option builtin)
          (world: world_state)
          (loc: memory)
          (loopinfo: list L40.Expr.loop_ctx)
          (args_offset args_count: N)
          CallOk:
      let _ := memory_impl in
      let fix interpret_expr_list
                (world0 : world_state) (loc0 : memory) (e : list AST.expr)
                (CallOk : FSet.is_subset (Callset.expr_list_callset e)
                            (Callset.decl_callset (cached_translated_decl fc30 B CalldagOk FcNotVar)) =
                          true) {struct e} : world_state * expr_result (list uint256) :=
                match e as e' return (e = e' -> world_state * expr_result (list uint256)) with
                | nil => fun _ : e = nil => (world0, ExprSuccess nil)
                | (h :: t)%list =>
                    fun E : e = (h :: t)%list =>
                    let (world', result_t) :=
                      interpret_expr_list world0 loc0 t (Callset.callset_descend_tail E CallOk) in
                    match result_t with
                    | ExprSuccess values_t =>
                        let (world'', result_h) :=
                          L40.Expr.interpret_expr eq_refl (translate_fun_ctx fc30 B CalldagOk FcNotVar)
                            do_call_40 builtins world' loc0 loopinfo h
                            (Callset.callset_descend_head E CallOk) in
                        (world'',
                        match result_h with
                        | ExprSuccess value_h => ExprSuccess (value_h :: values_t)%list
                        | ExprAbort ab => ExprAbort ab
                        end)
                    | ExprAbort ab => (world', ExprAbort ab)
                    end
                end eq_refl
      in
        interpret_expr_list world loc 
                            (var_range args_offset args_count)
                            CallOk
         =
        (world, ExprSuccess (OpenArray.view loc args_offset args_count)).
Proof.
intros.
revert CallOk. rewrite var_range_via_nat. intro CallOk.
assert (V' := OpenArray.view_ok loc args_offset args_count).
assert (L := OpenArray.view_len loc args_offset args_count).
remember (OpenArray.view loc args_offset args_count) as v. clear Heqv.
(* a variant of V' with nats: *)
assert (V:
  forall k: nat, (k < (N.to_nat args_count)%N) -> 
    List.nth_error v k = Some (OpenArray.get loc (args_offset + (N.of_nat k)))).
{
  intros k H.
  rewrite<- (V' (N.of_nat k)). { now rewrite Nat2N.id. }
  rewrite<- N.compare_lt_iff.
  rewrite<- (N2Nat.id args_count).
  rewrite<- Nat2N.inj_compare.
  rewrite Nat.compare_lt_iff.
  exact H.
}
clear V'.
rewrite<- L in V.
remember (N.to_nat args_count) as n.
revert CallOk.
replace args_count with (N.of_nat n) in *. 2:{ subst. apply N2Nat.id. }
clear args_count Heqn.
intros. unfold var_range_nat.

revert args_offset v V L CallOk.
enough (T: forall  (t: nat) (args_offset: N) (v: list uint256),
            (forall k : nat,
               k < Datatypes.length v ->
                 List.nth_error v k
                  =
                 Some (OpenArray.get loc (args_offset + N.of_nat (k + n - t)))) ->
            Datatypes.length v = t ->
            t <= n ->
            forall CallOk,
              interpret_expr_list world loc
                ((fix var_range' (countdown : nat) : list AST.expr :=
                    match countdown with
                    | 0 => nil
                    | S k => (AST.LocalVar (N.of_nat (N.to_nat args_offset + n - 1 - k)) 
                             :: var_range' k)%list
                    end) t) CallOk = (world, ExprSuccess v)).
{
  intros.
  assert (W: forall k: nat,
               k < Datatypes.length v ->
               List.nth_error v k = Some (OpenArray.get loc (args_offset + N.of_nat (k + n - n)))).
  { intros. rewrite Nat.add_sub. now apply V. }
  apply (T n args_offset v W L (Nat.le_refl n)).
}
induction t. { intros. cbn. now destruct v. }
intros args_offset v V' L' Bound CallOk. cbn.
destruct v as [|h]. { discriminate. }
assert (L: Datatypes.length v = t) by now inversion L'.
assert (V: forall k: nat,
             k < Datatypes.length v ->
             List.nth_error v k = Some (OpenArray.get loc (args_offset + N.of_nat (k + n - t)))).
{
  intro k. assert (W := V' (S k)). cbn in W.
  intro Bk. rewrite W by lia.
  f_equal.
}
assert (Bt: t <= n) by lia.
rewrite (IHt args_offset v V L Bt).
repeat f_equal.
assert (W := V' 0 (Nat.lt_0_succ _)).
cbn in W.
inversion W. subst. f_equal. lia.
Qed.

Lemma interpret_translated_small_stmt
    {C: VyperConfig}
    {bigger_call_depth_bound smaller_call_depth_bound: nat}
    (B: builtin_names_config)
    (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
    {cd30: L30.Descend.calldag}
    {cd40: L40.Descend.calldag}
    (CalldagOk: translate_calldag B cd30 = inr cd40)
    (fc30: fun_ctx cd30 bigger_call_depth_bound)
    (FcNotVar: forall x,
                 fun_decl fc30 <> AST.StorageVarDecl x)
    {do_call_30: forall
          (fc': fun_ctx cd30 smaller_call_depth_bound)
          (world: world_state)
          (arg_values: list uint256),
        world_state * expr_result uint256}
    {do_call_40: forall
          (fc': fun_ctx cd40 smaller_call_depth_bound)
          (world: world_state)
          (arg_values: list uint256),
        world_state * expr_result uint256}
    (DoCallOk:
       forall fc'
              (NotVar: forall x, fun_decl fc' <> AST.StorageVarDecl x)
              world arg_values,
         do_call_40 (translate_fun_ctx fc' B CalldagOk NotVar) world arg_values
          =
         do_call_30 fc' world arg_values)
    {ss30: L30.AST.small_stmt}
    {l40: list L40.AST.stmt}
    (ok: translate_small_stmt B (cd_decls cd30) ss30 = inr l40)
    (builtins: string -> option builtin)
    (SloadOk: BuiltinsSupportSload B builtins)
    (SstoreOk: BuiltinsSupportSstore B builtins)
    (world: world_state)
    (loc: memory)
    (CallOk30: let _ := string_set_impl in 
               FSet.is_subset (L30.Callset.small_stmt_callset ss30)
                              (L30.Callset.decl_callset (fun_decl fc30))
               = true)
    (CallOk40: let _ := string_set_impl in 
               FSet.is_subset (L40.Callset.stmt_list_callset l40)
                              (L40.Callset.decl_callset
                                (fun_decl
                                  (translate_fun_ctx fc30 B CalldagOk FcNotVar)))
               = true)
    (loopinfo: list L40.Expr.loop_ctx):
  L30.Stmt.interpret_small_stmt Ebound fc30 do_call_30 builtins world loc ss30 CallOk30
   =
  L40.Stmt.interpret_block Ebound (translate_fun_ctx fc30 B CalldagOk FcNotVar)
                                  do_call_40 builtins world loc loopinfo
                                  (L40.AST.Block l40) CallOk40.
Proof.
destruct ss30; cbn in ok; try discriminate; inversion ok; subst; try easy.
{ (* sload *)
  unfold BuiltinsSupportSload in SloadOk. cbn.
  unfold cd_declmap. unfold map_lookup in *.
  destruct (Map.lookup (cd_decls cd30) name) as [d|]. 2:discriminate.
  destruct d. 2:discriminate.
  cbn.
  remember (builtin_name_sload B) as sload_name.
  cbn.
  remember (builtins sload_name) as sload_builtin.
  destruct sload_builtin as [(sload_arity, sload)|]. 2:contradiction.
  destruct sload_arity. { contradiction. }
  destruct sload_arity. 2: contradiction.
  inversion ok; subst l40. cbn.
  assert (K := SloadOk world name).
  remember (sload world (string_hash name)) as sload_result.
  destruct sload_result as (world', result).
  destruct result. 2:contradiction.
  destruct K as (W, V).
  rewrite<- Heqsload_builtin. cbn.
  subst world' value.
  now rewrite<- Heqsload_result.
}
{ (* sstore *)
  unfold BuiltinsSupportSstore in SstoreOk. cbn.
  unfold cd_declmap. unfold map_lookup in *.
  destruct (Map.lookup (cd_decls cd30) name) as [d|]. 2:discriminate.
  destruct d. 2:discriminate.
  cbn.
  remember (builtin_name_sstore B) as sstore_name.
  cbn.
  remember (builtins sstore_name) as sstore_builtin.
  destruct sstore_builtin as [(sstore_arity, sstore)|]. 2:contradiction.
  destruct sstore_arity. { contradiction. }
  destruct sstore_arity. { contradiction. }
  destruct sstore_arity. 2: contradiction.
  inversion ok; subst l40. cbn.
  assert (K := let _ := memory_impl in SstoreOk world name (OpenArray.get loc src)).
  remember (sstore world (string_hash name) _) as sstore_result.
  destruct sstore_result as (world', result).
  destruct result. 2:contradiction.
  rewrite<- Heqsstore_builtin. cbn.
  subst.
  now rewrite<- Heqsstore_result.
}
{ (* PrivateCall *)
  remember (map_lookup (cd_decls cd30) name) as lookup_result.
  destruct lookup_result as [d|]. 2:discriminate.
  destruct d. 1:discriminate.
  unfold L30.Descend.fun_ctx_descend.
  unfold L40.Descend.fun_ctx_descend.
  assert (D := translate_fun_ctx_declmap B CalldagOk name).
  inversion ok; subst; clear ok.
  unfold Translate.var_range in *. cbn.
  remember (Callset.callset_descend_assign_rhs eq_refl
              (Callset.callset_descend_small_stmt eq_refl
                 (Callset.callset_descend_stmts_head eq_refl
                    (Callset.callset_descend_block eq_refl _))))
    as CallOkRHS40.
  unfold L30.Descend.fun_ctx_descend.
  unfold L40.Descend.fun_ctx_descend.
  unfold cd_declmap in *. unfold map_lookup in *.
  remember (fix interpret_expr_list
                  (world0 : world_state) (loc0 : memory) (e : list AST.expr)
                  (CallOk : FSet.is_subset (Callset.expr_list_callset e)
                              (Callset.decl_callset (cached_translated_decl fc30 B CalldagOk FcNotVar)) =
                            true) {struct e} : world_state * expr_result (list uint256) := _)
    as interpret_expr_list.
  remember (fun d (Edecl : Map.lookup (cd_decls cd30) name = Some d) =>
      L30.Descend.fun_ctx_descend_inner fc30 CallOk30
        eq_refl eq_refl Edecl)
    as good_branch_30.
  remember (fun d (Edecl : Map.lookup (cd_decls cd40) name = Some d) =>
              Descend.fun_ctx_descend_inner (translate_fun_ctx fc30 B CalldagOk FcNotVar) CallOkRHS40
                                            eq_refl eq_refl Edecl)
    as good_branch_40.
  remember (fix var_range' (countdown : nat) : list AST.expr :=
               match countdown with
               | 0 => nil
               | S k =>
                   (AST.LocalVar (args_offset + args_count - 1 - N.of_nat k) :: var_range' k)%list
               end)
    as var_range.
  (* Coq has problems typing this in a bigger expression *)
  remember (fun y (Ey: Map.lookup (cd_decls cd40) name = Some y) =>
                         match good_branch_40 y Ey with
                         | Some new_fc =>
                            let (world', result_args) :=
                              interpret_expr_list world loc (var_range (N.to_nat args_count))
                                (Callset.callset_descend_args eq_refl CallOkRHS40) in
                            match result_args with
                            | ExprSuccess arg_values => do_call_40 new_fc world' arg_values
                            | ExprAbort ab => (world', ExprAbort ab)
                            end
                         | None => (world, expr_error "can't resolve function name")
                         end)
    as compute40.
  enough (W:
    forall x (Ex: Map.lookup (cd_decls cd30) name = Some x)
           y (Ey: Map.lookup (cd_decls cd40) name = Some y),
      let _ := memory_impl in
      match good_branch_30 x Ex with
      | Some new_fc =>
          let (world', call_result) := do_call_30 new_fc world (OpenArray.view loc args_offset args_count) in
          match call_result with
          | ExprSuccess result => (world', OpenArray.put loc dst result, StmtSuccess)
          | ExprAbort ab => (world', loc, StmtAbort ab)
          end
      | None => (world, loc, stmt_error "can't resolve function name")
      end =
      match
        (let '(world', result) := compute40 y Ey in
         match result with
         | ExprSuccess value => (world', OpenArray.put loc dst value, StmtSuccess)
         | ExprAbort ab => (world', loc, StmtAbort ab)
         end)
      return world_state * memory * stmt_result uint256
      with
      | (world', loc', StmtSuccess) => (world', loc', StmtSuccess)
      | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
          (world', loc', result)
      end).
  {
    clear Heqgood_branch_30.
    clear Heqgood_branch_40.
    destruct (Map.lookup (cd_decls cd30) name) as [d30|],
             (Map.lookup (cd_decls cd40) name) as [d40|]; cbn;
      try destruct d30; try destruct d40; try easy.
    subst compute40.
    apply W.
  }
  (* following InnerOk from From20To30/Expr.v *)
  intros x Ex y Ey. cbn.
  subst good_branch_30 compute40 good_branch_40.
  cbn.
  rewrite Ex in D. rewrite Ey in D.
  remember (match
                       match
                         Descend.fun_ctx_descend_inner (translate_fun_ctx fc30 B CalldagOk FcNotVar) CallOkRHS40 eq_refl eq_refl Ey
                       with
                       | Some new_fc =>
                           let (world', result_args) :=
                             interpret_expr_list world loc (var_range (N.to_nat args_count))
                               (Callset.callset_descend_args eq_refl CallOkRHS40) in
                           match result_args with
                           | ExprSuccess arg_values => do_call_40 new_fc world' arg_values
                           | ExprAbort ab => (world', ExprAbort ab)
                           end
                       | None => (world, expr_error "can't resolve function name")
                       end
                     with
                     | (world', ExprSuccess value) => (world', OpenArray.put loc dst value, StmtSuccess)
                     | (world', ExprAbort ab) => (world', loc, StmtAbort ab)
                     end) as rhs.
  (* this silliness is happening because we translate from
     stmt_result to expr_result and back *)
  replace ((let (p, result) := rhs in
             let (world', loc') := p in
             match result with
             | StmtSuccess => (world', loc', StmtSuccess)
             | _ => (world', loc', result)
             end))
    with rhs
    by now destruct rhs as ((world', loc'), result), result.
  subst rhs.
  unfold L30.Descend.fun_ctx_descend_inner.
  unfold L40.Descend.fun_ctx_descend_inner.
  remember (fun (depth: nat) (Edepth: cd_depthmap cd30 name = Some depth) =>
      Some
        {|
          fun_name := name;
          fun_depth := depth;
          fun_depth_ok := Edepth;
          fun_decl := x;
          fun_decl_ok := Ex;
          fun_bound_ok := _
        |})
    as some_branch_l.
  remember (fun Edepth : cd_depthmap cd30 name = None =>
              False_rect (option (fun_ctx cd30 smaller_call_depth_bound))
                         (L30.Descend.fun_ctx_descend_helper Ex Edepth))
    as none_branch_l.
  remember (fun (depth: nat) (Edepth: cd_depthmap cd40 name = Some depth) =>
    Some
      {|
        fun_name := name;
        fun_depth := depth;
        fun_depth_ok := Edepth;
        fun_decl := y;
        fun_decl_ok := Ey;
        fun_bound_ok := _
      |})
    as some_branch_r.
  remember (fun Edepth : cd_depthmap cd40 name = None =>
                False_rect (option (fun_ctx cd40 smaller_call_depth_bound))
                  (L40.Descend.fun_ctx_descend_helper Ey Edepth))
    as none_branch_r.
  assert (NoneOkL: forall (Edepth: cd_depthmap cd30 name = None),
                     none_branch_l Edepth = None).
  { intro. exfalso. exact (L30.Descend.fun_ctx_descend_helper Ex Edepth). }
  assert (NoneOkR: forall (Edepth: cd_depthmap cd40 name = None),
                     none_branch_r Edepth = None).
  { intro. exfalso. exact (L40.Descend.fun_ctx_descend_helper Ey Edepth). }
  clear Heqnone_branch_l Heqnone_branch_r.
  enough (SomeBranchOk:
      forall (depth: nat)
             (Edepth30: cd_depthmap cd30 name = Some depth)
             (Edepth40: cd_depthmap cd40 name = Some depth),
       let _ := memory_impl in
        match some_branch_l depth Edepth30
        return (world_state * memory * stmt_result uint256)
        with
        | Some new_fc =>
            let (world', call_result) := do_call_30 new_fc world (OpenArray.view loc args_offset args_count) in
            match call_result with
            | ExprSuccess result => (world', OpenArray.put loc dst result, StmtSuccess)
            | ExprAbort ab => (world', loc, StmtAbort ab)
            end
        | None => (world, loc, stmt_error "can't resolve function name")
        end =
        let (world', e) :=
           match some_branch_r depth Edepth40 with
           | Some new_fc =>
               let (world', result_args) :=
                 interpret_expr_list world loc (var_range (N.to_nat args_count))
                   (Callset.callset_descend_args eq_refl CallOkRHS40) in
               match result_args with
               | ExprSuccess arg_values => do_call_40 new_fc world' arg_values
               | ExprAbort ab => (world', ExprAbort ab)
               end
           | None => (world, expr_error "can't resolve function name")
           end in
         match e with
         | ExprSuccess value => (world', OpenArray.put loc dst value, StmtSuccess)
         | ExprAbort ab => (world', loc, StmtAbort ab)
         end).
  {
    revert none_branch_l none_branch_r NoneOkL NoneOkR.
    clear Heqsome_branch_l Heqsome_branch_r
          CallOk30 CallOk40 HeqCallOkRHS40 Ex Ey x y D DoCallOk.
    revert some_branch_l some_branch_r SomeBranchOk.
    rewrite (translate_fun_ctx_depthmap B CalldagOk name).
    destruct (cd_depthmap cd30 name); intros. { apply SomeBranchOk. }
    rewrite (NoneOkL eq_refl).
    rewrite (NoneOkR eq_refl).
    trivial.
  }
  intros. subst some_branch_l some_branch_r.
  unfold translate_fun_ctx. cbn.
  subst interpret_expr_list var_range.
  assert (R := interpret_var_range B CalldagOk fc30 FcNotVar do_call_40 builtins world loc loopinfo
                                   args_offset args_count
                                   (Callset.callset_descend_args eq_refl CallOkRHS40)).
  unfold var_range. unfold var_range in R. rewrite R. clear R.
  assert (FcNotVar': forall str: string,
                       fun_decl
                         {|
                           fun_name := name;
                           fun_depth := depth;
                           fun_depth_ok := Edepth30;
                           fun_decl := x;
                           fun_decl_ok := Ex;
                           fun_bound_ok := L30.Descend.call_descend' fc30 CallOk30 eq_refl eq_refl Ex Edepth30
                         |} <> AST.StorageVarDecl str).
  {
    cbn. intros str H. subst x.
    destruct y as (y_name, y_nargs, y_body).
    now destruct y_body.
  }
  rewrite<- (DoCallOk _ FcNotVar').
  remember (L30.Descend.call_descend' _ _ _ _ _ _) as DescendOk30.
  remember (L40.Descend.call_descend' _ _ _ _ _ _) as DescendOk40.
  assert (EDescend: DescendOk30 = DescendOk40)
    by apply proof_irrelevance.
  clear HeqDescendOk30 HeqDescendOk40.
  subst DescendOk40.
  enough (E: translate_fun_ctx
                {|
                  fun_name := name;
                  fun_depth := depth;
                  fun_depth_ok := Edepth30;
                  fun_decl := x;
                  fun_decl_ok := Ex;
                  fun_bound_ok := DescendOk30
                |} B CalldagOk FcNotVar'
               =
               {|
                 fun_name := name;
                 fun_depth := depth;
                 fun_depth_ok := Edepth40;
                 fun_decl := y;
                 fun_decl_ok := Ey;
                 fun_bound_ok := DescendOk30
               |})
    by now rewrite E.
  unfold translate_fun_ctx. cbn.
  enough (E: y = cached_translated_decl
              {|
                fun_name := name;
                fun_depth := depth;
                fun_depth_ok := Edepth30;
                fun_decl := x;
                fun_decl_ok := Ex;
                fun_bound_ok := DescendOk30
              |} B CalldagOk FcNotVar').
  {
    subst.
    assert (R: eq_trans (translate_fun_ctx_depthmap B CalldagOk name) Edepth30 = Edepth40)
      by apply proof_irrelevance. rewrite R. clear R.
    assert (R: Ey = FunCtx.translate_fun_ctx_decl_ok
                {|
                  fun_name := name;
                  fun_depth := depth;
                  fun_depth_ok := Edepth30;
                  fun_decl := x;
                  fun_decl_ok := Ex;
                  fun_bound_ok := DescendOk30
                |} B CalldagOk FcNotVar')
      by apply proof_irrelevance.
    now subst.
  }
  unfold cached_translated_decl. cbn.
  unfold cd_declmap.
  remember (fun E : Map.lookup (cd_decls cd40) name = None =>
              False_rect AST.decl _) as none_branch. clear Heqnone_branch.
  destruct (Map.lookup (cd_decls cd40) name).
  { now inversion Ey. }
  discriminate.
}
(* builtin *)
cbn.
rewrite interpret_var_range.
destruct (builtins name) as [(arity, builtin)|]. 2:easy.
remember (fun Earity : (arity =? Datatypes.length (OpenArray.view loc args_offset args_count)) = true =>
            let '(world', call_result) :=
              call_builtin (OpenArray.view loc args_offset args_count) Earity (builtin world) in
            match call_result return world_state * memory * stmt_result uint256 with
            | ExprSuccess result => (world', OpenArray.put loc dst result, StmtSuccess)
            | ExprAbort ab => (world', loc, StmtAbort ab)
            end)
  as good_branch_l.
remember (fun Earity : (arity =? Datatypes.length (OpenArray.view loc args_offset args_count)) = true =>
            call_builtin (OpenArray.view loc args_offset args_count) Earity (builtin world))
  as good_branch_r.
enough (W: forall (Earity: arity =? Datatypes.length (OpenArray.view loc args_offset args_count) = true),
             let _ := memory_impl in
             good_branch_l Earity =
              match
                (let '(world', result) := good_branch_r Earity in
                 match result return world_state * memory * stmt_result uint256 with
                 | ExprSuccess value => (world', OpenArray.put loc dst value, StmtSuccess)
                 | ExprAbort ab => (world', loc, StmtAbort ab)
                 end)
              with
              | (world', loc', StmtSuccess) => (world', loc', StmtSuccess)
              | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
                  (world', loc', result)
              end).
{
  clear Heqgood_branch_l. clear Heqgood_branch_r.
  now destruct (arity =? Datatypes.length (OpenArray.view loc args_offset args_count)).
}
intro Earity. cbn. subst.
destruct (call_builtin (OpenArray.view loc args_offset args_count) Earity (builtin world))
  as (new_world, result).
now destruct result.
Qed.

(******************************************************************************************)

Lemma interpret_translated_stmt
    {C: VyperConfig}
    {bigger_call_depth_bound smaller_call_depth_bound: nat}
    (B: builtin_names_config)
    (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
    {cd30: L30.Descend.calldag}
    {cd40: L40.Descend.calldag}
    (CalldagOk: translate_calldag B cd30 = inr cd40)
    (fc30: fun_ctx cd30 bigger_call_depth_bound)
    (FcNotVar: forall x,
                 fun_decl fc30 <> AST.StorageVarDecl x)
    {do_call_30: forall
          (fc': fun_ctx cd30 smaller_call_depth_bound)
          (world: world_state)
          (arg_values: list uint256),
        world_state * expr_result uint256}
    {do_call_40: forall
          (fc': fun_ctx cd40 smaller_call_depth_bound)
          (world: world_state)
          (arg_values: list uint256),
        world_state * expr_result uint256}
    (DoCallOk:
       forall fc'
              (NotVar: forall x, fun_decl fc' <> AST.StorageVarDecl x)
              world arg_values,
         do_call_40 (translate_fun_ctx fc' B CalldagOk NotVar) world arg_values
          =
         do_call_30 fc' world arg_values)
    {s30: L30.AST.stmt}
    {l40: list L40.AST.stmt}
    (ok: translate_stmt B (cd_decls cd30) s30 = inr l40)
    (builtins: string -> option builtin)
    (SloadOk: BuiltinsSupportSload B builtins)
    (SstoreOk: BuiltinsSupportSstore B builtins)
    (BuiltinsOk: BuiltinsSupportUInt256 B builtins) (* because we need lt() in the loop *)
    (world: world_state)
    (loc: memory)
    (CallOk30: let _ := string_set_impl in 
               FSet.is_subset (L30.Callset.stmt_callset s30)
                              (L30.Callset.decl_callset (fun_decl fc30))
               = true)
    (CallOk40: let _ := string_set_impl in 
               FSet.is_subset (L40.Callset.stmt_list_callset l40)
                              (L40.Callset.decl_callset
                                (fun_decl
                                  (translate_fun_ctx fc30 B CalldagOk FcNotVar)))
               = true)
    (loopinfo: list L40.Expr.loop_ctx):
  L30.Stmt.interpret_stmt Ebound fc30 do_call_30 builtins world loc s30 CallOk30
   =
  L40.Stmt.interpret_block Ebound (translate_fun_ctx fc30 B CalldagOk FcNotVar)
                                  do_call_40 builtins world loc loopinfo
                                  (L40.AST.Block l40) CallOk40.
Proof.
revert l40 ok world loc CallOk30 CallOk40 loopinfo. induction s30; intros.
{ (* small *)
  apply (interpret_translated_small_stmt B Ebound CalldagOk fc30 FcNotVar DoCallOk
                                         ok builtins SloadOk SstoreOk).
}
{ (* if *)
  match goal with
  |- ?l = ?r => remember r as rhs
  end.
  cbn. cbn in ok.
  remember (translate_stmt B (cd_decls cd30) s30_1) as l40_1.
  destruct l40_1 as [|l40_1]. { discriminate. } symmetry in Heql40_1.
  remember (translate_stmt B (cd_decls cd30) s30_2) as l40_2.
  destruct l40_2 as [|l40_2]. { discriminate. } symmetry in Heql40_2.
  assert (IHs30_1' := IHs30_1 l40_1 eq_refl). clear IHs30_1. rename IHs30_1' into IHs30_1.
  assert (IHs30_2' := IHs30_2 l40_2 eq_refl). clear IHs30_2. rename IHs30_2' into IHs30_2.
  inversion ok; subst l40; clear ok.

  remember (Z_of_uint256 (OpenArray.get loc cond_src) =? 0)%Z as cond_is_0.
  destruct cond_is_0; subst; cbn;
    replace (Z_of_uint256 zero256) with 0%Z by (unfold zero256; now rewrite uint256_ok);
    rewrite<- Heqcond_is_0.
  {
    assert (CallOk40' := (@Callset.callset_descend_block C l40_2 (@AST.Block C l40_2)
         (@Callset.decl_callset C
            (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk FcNotVar))
         (@eq_refl (@AST.block C) (@AST.Block C l40_2))
         (@Callset.callset_descend_cases_head C (@AST.Case C (@zero256 C) (@AST.Block C l40_2))
            (@nil (@AST.case C)) (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
            (@Callset.decl_callset C
               (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk FcNotVar))
            (@eq_refl (list (@AST.case C))
               (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))%list)
            (@Callset.callset_descend_cases C
               (@AST.Switch C (@AST.LocalVar C cond_src)
                  (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                  (@Some (@AST.block C) (@AST.Block C l40_1))) (@AST.LocalVar C cond_src)
               (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
               (@Some (@AST.block C) (@AST.Block C l40_1))
               (@Callset.decl_callset C
                  (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk
                     FcNotVar))
               (@eq_refl (@AST.stmt C)
                  (@AST.Switch C (@AST.LocalVar C cond_src)
                     (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                     (@Some (@AST.block C) (@AST.Block C l40_1))))
               (@Callset.callset_descend_stmts_head C
                  (@AST.Switch C (@AST.LocalVar C cond_src)
                     (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                     (@Some (@AST.block C) (@AST.Block C l40_1))) (@nil (@AST.stmt C))
                  (@AST.Switch C (@AST.LocalVar C cond_src)
                     (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                     (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))
                  (@Callset.decl_callset C
                     (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk
                        FcNotVar))
                  (@eq_refl (list (@AST.stmt C))
                     (@AST.Switch C (@AST.LocalVar C cond_src)
                        (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                        (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))%list)
                  (@Callset.callset_descend_block C
                     (@AST.Switch C (@AST.LocalVar C cond_src)
                        (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                        (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))
                     (@AST.Block C
                        (@AST.Switch C (@AST.LocalVar C cond_src)
                           (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                           (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C)))
                     (@Callset.decl_callset C
                        (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk
                           FcNotVar))
                     (@eq_refl (@AST.block C)
                        (@AST.Block C
                           (@AST.Switch C (@AST.LocalVar C cond_src)
                              (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                              (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))))
                     CallOk40)))))).
    rewrite IHs30_2 with (CallOk40 := CallOk40') (loopinfo := loopinfo).
    cbn.
    assert (X: forall x: world_state * memory * stmt_result uint256,
              match x with
              | (world', loc', StmtSuccess) => (world', loc', StmtSuccess)
              | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) => (world', loc', result)
              end = x).
    {
      intro x. destruct x as ((world', loc'), result). now destruct result.
    }
    rewrite X. clear X. f_equal. apply proof_irrelevance.
  }
  assert (CallOk40' := (@Callset.callset_descend_block C l40_1 (@AST.Block C l40_1)
       (@Callset.decl_callset C
          (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk FcNotVar))
       (@eq_refl (@AST.block C) (@AST.Block C l40_1))
       (@Callset.callset_descend_cases_default C
          (@AST.Switch C (@AST.LocalVar C cond_src) (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
             (@Some (@AST.block C) (@AST.Block C l40_1))) (@AST.LocalVar C cond_src)
          (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C)) (@AST.Block C l40_1)
          (@Callset.decl_callset C
             (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk FcNotVar))
          (@eq_refl (@AST.stmt C)
             (@AST.Switch C (@AST.LocalVar C cond_src)
                (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                (@Some (@AST.block C) (@AST.Block C l40_1))))
          (@Callset.callset_descend_stmts_head C
             (@AST.Switch C (@AST.LocalVar C cond_src)
                (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                (@Some (@AST.block C) (@AST.Block C l40_1))) (@nil (@AST.stmt C))
             (@AST.Switch C (@AST.LocalVar C cond_src)
                (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))
             (@Callset.decl_callset C
                (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk FcNotVar))
             (@eq_refl (list (@AST.stmt C))
                (@AST.Switch C (@AST.LocalVar C cond_src)
                   (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                   (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))%list)
             (@Callset.callset_descend_block C
                (@AST.Switch C (@AST.LocalVar C cond_src)
                   (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                   (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C))
                (@AST.Block C
                   (@AST.Switch C (@AST.LocalVar C cond_src)
                      (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                      (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C)))
                (@Callset.decl_callset C
                   (@cached_translated_decl C (S smaller_call_depth_bound) cd30 fc30 cd40 B CalldagOk FcNotVar))
                (@eq_refl (@AST.block C)
                   (@AST.Block C
                      (@AST.Switch C (@AST.LocalVar C cond_src)
                         (@AST.Case C (@zero256 C) (@AST.Block C l40_2) :: @nil (@AST.case C))
                         (@Some (@AST.block C) (@AST.Block C l40_1)) :: @nil (@AST.stmt C)))) CallOk40))))).
  rewrite IHs30_1 with (CallOk40 := CallOk40') (loopinfo := loopinfo).
  cbn.
  (* XXX dup with the previous branch *)
  assert (X: forall x: world_state * memory * stmt_result uint256,
            match x with
            | (world', loc', StmtSuccess) => (world', loc', StmtSuccess)
            | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) => (world', loc', result)
            end = x).
  {
    intro x. destruct x as ((world', loc'), result). now destruct result.
  }
  rewrite X. clear X. f_equal. apply proof_irrelevance.
}
2:{ (* Semicolon *)
  cbn. cbn in ok.
  remember (fix interpret_stmt_list
   (world0 : world_state) (loc0 : memory) (loops : list Expr.loop_ctx) (l : list AST.stmt)
   (Ok : FSet.is_subset (Callset.stmt_list_callset l)
           (Callset.decl_callset (cached_translated_decl fc30 B CalldagOk FcNotVar)) = true) {struct l} :
     world_state * memory * stmt_result uint256 := _) as interpret_stmt_list.
  remember (translate_stmt B (cd_decls cd30) s30_1) as l40_1.
  destruct l40_1 as [|l40_1]. { discriminate. } symmetry in Heql40_1.
  remember (translate_stmt B (cd_decls cd30) s30_2) as l40_2.
  destruct l40_2 as [|l40_2]. { discriminate. } symmetry in Heql40_2.
  assert (IHs30_1' := IHs30_1 l40_1 eq_refl). clear IHs30_1. rename IHs30_1' into IHs30_1.
  assert (IHs30_2' := IHs30_2 l40_2 eq_refl). clear IHs30_2. rename IHs30_2' into IHs30_2.
  inversion ok; subst l40; clear ok.
  rewrite IHs30_1 with (loopinfo := loopinfo)
                       (CallOk40 := L40.Callset.callset_descend_stmts_app_left eq_refl
                                      (Callset.callset_descend_block eq_refl CallOk40)).
  cbn. rewrite<- Heqinterpret_stmt_list.
  assert (A: forall Ok1 Ok2 Ok3,
    interpret_stmt_list world loc loopinfo (l40_1 ++ l40_2)%list Ok1
     =
    match interpret_stmt_list world loc loopinfo l40_1 Ok2
    with
    | (world', loc', StmtSuccess) =>
        interpret_stmt_list world' loc' loopinfo l40_2 Ok3
    | (world', loc', StmtAbort _ as result_a) | (world', loc', StmtReturnFromFunction _ as result_a) =>
        (world', loc', result_a)
    end).
  {
    clear Heql40_1 IHs30_1 Heql40_2 IHs30_2 CallOk40.
    revert world loc.
    induction l40_1 as [|h]; intros.
    {
      cbn in *.
      assert (NilOk: forall OkNil,
                       interpret_stmt_list world loc loopinfo nil OkNil
                        =
                       (world, loc, StmtSuccess))
        by now rewrite Heqinterpret_stmt_list.
      rewrite NilOk.
      repeat f_equal; apply proof_irrelevance.
    }
    assert (Ok1': let _ := string_set_impl in
                 FSet.is_subset (Callset.stmt_list_callset (h :: (l40_1 ++ l40_2)))
                  (Callset.decl_callset (cached_translated_decl fc30 B CalldagOk FcNotVar)) = true)
      by now rewrite List.app_comm_cons with (A := L40.AST.stmt).
    replace (interpret_stmt_list world loc loopinfo ((h :: l40_1) ++ l40_2)%list Ok1)
       with (interpret_stmt_list world loc loopinfo (h :: l40_1 ++ l40_2)%list Ok1').
    2:{
      revert Ok1 Ok1'. rewrite List.app_comm_cons with (A := L40.AST.stmt).
      intros. repeat f_equal. apply proof_irrelevance.
    }
    rewrite Heqinterpret_stmt_list. cbn. rewrite<- Heqinterpret_stmt_list.
    match goal with
    |- context G [match ?interp bigger_call_depth_bound smaller_call_depth_bound Ebound cd40
                                (translate_fun_ctx fc30 B CalldagOk FcNotVar)
                                do_call_40 builtins world loc loopinfo h
                                ?ok
                  with _ => _ end] =>
        remember interp as interpret_stmt; remember ok as OkH
    end.
    match goal with
    |- context G [match interpret_stmt bigger_call_depth_bound smaller_call_depth_bound Ebound cd40
                                       (translate_fun_ctx fc30 B CalldagOk FcNotVar)
                                       do_call_40 builtins world loc loopinfo h
                                       (L40.Callset.callset_descend_stmts_head eq_refl ?ok)
                  with _ => _ end] =>
        remember (L40.Callset.callset_descend_stmts_head eq_refl ok) as OkH'
    end.
    replace OkH' with OkH by apply proof_irrelevance.
    destruct interpret_stmt as ((world', loc'), result).
    now destruct result.
  }
  match goal with
  |- _ = interpret_stmt_list world loc loopinfo (l40_1 ++ l40_2)%list ?ok =>
      rewrite (A ok (L40.Callset.callset_descend_stmts_app_left eq_refl ok)
                    (L40.Callset.callset_descend_stmts_app_right eq_refl ok))
  end.
  match goal with
  |- context G [interpret_stmt_list world loc loopinfo l40_1 ?ok] =>
      remember ok as ok1
  end.
  match goal with
  |- context G [interpret_stmt_list world loc loopinfo l40_1
                  (Callset.callset_descend_stmts_app_left _ ?ok)] =>
      remember ok as ok2
  end.
  assert (ok1 = Callset.callset_descend_stmts_app_left eq_refl ok2)
    by apply proof_irrelevance.
  subst ok1.
  assert (R: Callset.callset_descend_block eq_refl (Callset.callset_descend_stmts_app_left eq_refl ok2)
              =
             Callset.callset_descend_stmts_app_left eq_refl ok2)
    by apply proof_irrelevance.
  rewrite R.
  destruct interpret_stmt_list as ((world', loc'), result).
  destruct result; trivial.
  rewrite IHs30_2 with (loopinfo := loopinfo)
                       (CallOk40 := L40.Callset.callset_descend_stmts_app_right eq_refl
                                      (Callset.callset_descend_block eq_refl CallOk40)).
  cbn. rewrite<- Heqinterpret_stmt_list.
  repeat f_equal. apply proof_irrelevance.
}
(* loop *)
(* weird: cbn and simpl hang up on ok *)
assert (CountNZ: Z_of_uint256 count <> 0%Z). (* translate_stmt raises an error if count = 0 *)
{
  unfold translate_stmt in ok.
  intro CountZ.
  rewrite<- Z.eqb_eq in CountZ.
  rewrite CountZ in ok.
  discriminate.
}
remember (translate_stmt B (cd_decls cd30) s30) as body40.
unfold translate_stmt in ok. rewrite (proj2 (Z.eqb_neq _ _) CountNZ) in ok. fold translate_stmt in ok.
rewrite<- Heqbody40 in ok.
destruct body40 as [|body40]. { discriminate. }
fold translate_stmt in Heqbody40.
(* weird: inversion ok doesn't work, simple inversion doesn't work either *)
assert (InvertInr: forall A B (x y: B) (H: @inr A B x = inr y),
                     x = y).
{ intros. now inversion H. }
apply InvertInr in ok. clear InvertInr. (* why is it so hard for inversion? *)
subst l40.
(* cbn still hangs up *)
unfold L40.Stmt.interpret_block.
unfold BuiltinsSupportUInt256 in BuiltinsOk.
assert (LtOk: BuiltinsSupportBinop builtins (builtin_name_uint256_lt B) UInt256.uint256_lt)
  by tauto.
assert (AddOk: BuiltinsSupportBinop builtins (builtin_name_uint256_add B)
                 CheckedArith.uint256_add)
  by tauto. (* used later for adding the counter to the offset *)
clear BuiltinsOk.
(* following CheckArith/Stmt here but that was about L30 so not using it directly *)
remember (L40.Expr.interpret_expr _ _ _ _ _ _ _ _ _) as lt_result.
unfold L40.Expr.interpret_expr in Heqlt_result.

(* following do_binop from CheckArith/Stmt.v except we have a language with exprs now *)
unfold BuiltinsSupportBinop in LtOk.
destruct (builtins (builtin_name_uint256_lt B)) as [lt|]; try contradiction.
assert (A := builtin_is_binop_arity _ _ LtOk).
destruct lt as (lt_arity, lt).
cbn in A.
subst lt_arity.
unfold Datatypes.length in Heqlt_result.
rewrite if_yes with (E := Nat.eqb_refl 2) in Heqlt_result.
rewrite (builtin_is_binop_ok _ _ LtOk) in Heqlt_result.
subst lt_result. clear lt LtOk.
unfold UInt256.uint256_lt.
rewrite uint256_ok.
rewrite Z.mod_small by (assert (Range := uint256_range count); lia).
remember (2 ^ 256 - Z_of_uint256 count <? Z_of_uint256 (OpenArray.get loc var))%Z
  as loop_is_bad.
destruct loop_is_bad.
{ (* loop overflows *)
  replace (Z_of_uint256 one256 =? Z_of_uint256 zero256)%Z with false
    by (unfold one256, zero256; now repeat rewrite uint256_ok).
  cbn.
  replace (Z_of_uint256 count =? 0)%Z with false
    by (symmetry; now rewrite Z.eqb_neq).
  enough (H: let _ := memory_impl in
          (Z_of_uint256 (uint256_of_Z (Z_of_uint256 (OpenArray.get loc var) + Z_of_uint256 count - 1)) 
            =?
           Z_of_uint256 (OpenArray.get loc var) + Z_of_uint256 count - 1)%Z 
            = false)
    by now rewrite H.
  clear IHs30 CallOk30 CallOk40 Heqbody40.
  cbn.
  rewrite uint256_ok.
  rewrite Z.eqb_neq.
  symmetry in Heqloop_is_bad. rewrite Z.ltb_lt in Heqloop_is_bad.
  match goal with
  |- ?l <> ?r => enough (H: (l < 2^256 <= r)%Z) by lia
  end.
  split. 2:lia.
  now apply Z.mod_pos_bound.
}
(* no overflow *)
symmetry in Heqloop_is_bad.
rewrite Z.ltb_ge in Heqloop_is_bad.
rename Heqloop_is_bad into NoOverflow.
rewrite Z.eqb_refl.
match goal with
|- ?l = ?r => remember r as rhs
end.
cbn.
replace (Z_of_uint256 count =? 0)%Z with false
  by (symmetry; now rewrite Z.eqb_neq).
replace ((Z_of_uint256 (uint256_of_Z (Z_of_uint256 (OpenArray.get loc var) + Z_of_uint256 count - 1)) 
          =?
         Z_of_uint256 (OpenArray.get loc var) + Z_of_uint256 count - 1)%Z)
  with true.
2:{
  symmetry.
  rewrite Z.eqb_eq.
  rewrite uint256_ok.
  apply Z.mod_small.
  assert (R1 := let _ := memory_impl in uint256_range (OpenArray.get loc var)). cbn in R1.
  assert (R2 := uint256_range count).
  lia.
}
subst rhs.
assert (R: forall x: world_state * memory * stmt_result uint256,
          match x with
          | (world', loc', StmtSuccess) => (world', loc', StmtSuccess)
          | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
                (world', loc', result)
          end = x)
  by (destruct x as ((world', loc'), result); now destruct result).
rewrite R. rewrite R.
clear R.

(* following CheckArith/Stmt here *)
remember (let _ := memory_impl in
          Z_of_uint256 (OpenArray.get loc var) + Z_of_uint256 count - 1)%Z as last.
assert (LastRange: (0 <= last < 2 ^ 256)%Z).
{
  cbn in Heqlast.
  subst.
  assert (R1 := let _ := memory_impl in uint256_range (OpenArray.get loc var)). cbn in R1.
  assert (R2 := uint256_range count).
  lia.
}

(* L30 loop machinery: *)
remember (Z.to_nat (Z_of_uint256 count)) as countdown.
remember (Z_of_uint256 (OpenArray.get loc var)) as cursor.

assert (MainLoopEq: last = (cursor + Z_of_uint256 count - 1)%Z)
  by (subst cursor; exact Heqlast).

(* L40 loop machinery: *)

remember (OpenArray.get loc var) as this_loop_offset. (* unchanged during induction *)
remember count as this_loop_count.                    (*           --//--           *)
rewrite Heqthis_loop_count in MainLoopEq, Heqcountdown.
rewrite Heqthis_loop_offset in Heqcursor.

assert (MainLoopFixedEq: (last = Z_of_uint256 this_loop_offset + Z_of_uint256 this_loop_count - 1)%Z)
  by now subst.

assert (CountUpper: (Z_of_uint256 count <= Z_of_uint256 this_loop_count)%Z)
  by (subst; apply Z.le_refl).

clear Heqlast Heqcursor NoOverflow CountNZ Heqthis_loop_count Heqthis_loop_offset.
revert count world loc cursor MainLoopEq CallOk30 CallOk40 Heqcountdown CountUpper.

induction countdown. { trivial. }
intros.
remember (L40.Stmt.interpret_small_stmt _ _ _ _ world loc _ _ _) as iter_init.
cbn in Heqiter_init.
(* Now we need to do for add() the same things we did above for lt(). *)
unfold BuiltinsSupportBinop in AddOk.
destruct (builtins (builtin_name_uint256_add B)) as [sum|]; try contradiction.
assert (A := builtin_is_binop_arity _ _ AddOk).
destruct sum as (sum_arity, sum).
cbn in A.
subst sum_arity.
unfold Datatypes.length in Heqiter_init.
rewrite if_yes with (E := Nat.eqb_refl 2) in Heqiter_init.
rewrite (builtin_is_binop_ok _ _ AddOk) in Heqiter_init.
subst iter_init. clear sum AddOk.
unfold CheckedArith.uint256_add.

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

assert (CursorOk: cursor =
           (Z_of_uint256 this_loop_offset +
            Z_of_uint256 (uint256_of_Z (Z_of_uint256 this_loop_count - 1 - Z.of_nat countdown)))%Z).
{
  rewrite uint256_ok.
  rewrite Z.mod_small
    by (assert (R := uint256_range this_loop_count); lia).
  lia.
}
rewrite<- CursorOk. (* now the L40 loop uses the same cursor as the L30 loop (for this iteration *)
remember (OpenArray.put loc var (uint256_of_Z cursor))
  as current_loc.
remember ({|
       Expr.loop_offset := this_loop_offset;
       Expr.loop_count := this_loop_count;
       Expr.loop_countdown := countdown
     |} :: loopinfo)%list
  as current_loopinfo.
match goal with
|- context G [ ?i_stmt_list world current_loc current_loopinfo body40 ?callok ] =>
    remember i_stmt_list as do_stmt_list; remember callok as IterCallOk40
end.
rewrite (IHs30 body40 eq_refl) with (CallOk40 := IterCallOk40) (loopinfo := current_loopinfo).

assert (R: Stmt.interpret_block Ebound (translate_fun_ctx fc30 B CalldagOk FcNotVar) do_call_40 builtins world
            current_loc current_loopinfo (AST.Block body40) IterCallOk40
           =
          do_stmt_list world current_loc current_loopinfo body40 IterCallOk40).
{
  cbn.
  rewrite Heqdo_stmt_list.
  assert (E: @Callset.callset_descend_block C body40 (@AST.Block C body40)
               (@Callset.decl_callset C
                  (@cached_translated_decl C bigger_call_depth_bound cd30 fc30 cd40 B CalldagOk FcNotVar))
               (@eq_refl (@AST.block C) (@AST.Block C body40)) IterCallOk40
               =
              IterCallOk40)
    by apply proof_irrelevance.
  rewrite E.
  trivial.
}
rewrite R. clear R.

assert (NextLoopEq: last = (Z.succ cursor + Z_of_uint256 count' - 1)%Z).
{
  subst count'.
  rewrite uint256_ok.
  rewrite Z.mod_small. { lia. }
  assert (R := uint256_range count).
  lia.
}
assert (NextCountUpper: (Z_of_uint256 count' <= Z_of_uint256 this_loop_count)%Z)
  by lia.
subst IterCallOk40.
destruct do_stmt_list as ((world', loc'), result). (* finally we do the iteration *)
destruct result; trivial.
{
  apply (IHcountdown count' world' loc' (Z.succ cursor) NextLoopEq
                   CallOk30 CallOk40 CountOk NextCountUpper).
}
destruct a; trivial.
apply (IHcountdown count' world' loc' (Z.succ cursor) NextLoopEq
                 CallOk30 CallOk40 CountOk NextCountUpper).
Qed.
