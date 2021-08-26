From Coq Require Import String Arith ZArith PropExtensionality.

From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require Import AST Descend Expr Callset Descend.
From Vyper.L40Metered Require Import Interpret.

(** The expression interpreter is in L40Metered.Interpret.
    This is the proof that both interpreters of L40 work the same on expressions.
 *)

Lemma expr_metering_ok {C: VyperConfig}
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
                       (e: expr)
                       (CallOk: let _ := string_set_impl in 
                                  FSet.is_subset (expr_callset e)
                                                 (decl_callset (fun_decl fc))
                                  = true):
  let '(world', result) := interpret_expr Ebound fc do_call builtins world loc loops e CallOk in
    interpret_expr_metered (cd_decls cd) do_call_metered builtins world loc loops e
     =
    (world', Some result).
Proof.
revert world loc loops. induction e using expr_ind'; try easy; intros; cbn.
{ (* PrivateCall *)
  unfold fun_ctx_descend.
  unfold cd_declmap.
  unfold map_lookup.
  refine (match Map.lookup (cd_decls cd) name as z return _ = z -> _ with
          | Some d => fun E => _
          | None => fun NotFound => _
          end eq_refl).
  2:{
    remember (fun d (Edecl : Map.lookup (cd_decls cd) name = Some d) =>
               Descend.fun_ctx_descend_inner fc CallOk Ebound eq_refl Edecl) as branch_not_taken.
    clear Heqbranch_not_taken.
    revert branch_not_taken.
    now rewrite NotFound.
  }
  replace (match
             Map.lookup (cd_decls cd) name as maybe_decl
             return (Map.lookup (cd_decls cd) name = maybe_decl -> option (fun_ctx cd smaller_call_depth_bound))
           with
           | Some d0 =>
               fun Edecl : Map.lookup (cd_decls cd) name = Some d0 =>
               Descend.fun_ctx_descend_inner fc CallOk Ebound eq_refl Edecl
           | None => fun _ : Map.lookup (cd_decls cd) name = None => None
           end eq_refl) with (Descend.fun_ctx_descend_inner fc CallOk Ebound eq_refl E).
  2:{
    remember (@Descend.fun_ctx_descend_inner C bigger_call_depth_bound smaller_call_depth_bound cd
               (@PrivateCall C name args) fc CallOk Ebound name args
               (@eq_refl (@expr C) (@PrivateCall C name args))) as foo.
    clear Heqfoo.
    unfold cd_declmap in foo.
    destruct (Map.lookup (cd_decls cd) name). 2:discriminate.
    inversion E; subst.
    f_equal.
    apply proof_irrelevance.
  }
  unfold Descend.fun_ctx_descend_inner.
  assert (DepthmapOk := cd_depthmap_ok cd name).
  rewrite E in DepthmapOk.
  refine (match cd_depthmap cd name as z return _ = z -> _ with
          | Some depth => fun Edepth => _
          | None => fun NotFound => _
          end eq_refl).
  2: now rewrite NotFound in DepthmapOk.
  rewrite Edepth in DepthmapOk.
  rewrite FSet.for_all_ok in DepthmapOk.
  replace (match
             cd_depthmap cd name as maybe_depth
             return (cd_depthmap cd name = maybe_depth -> option (fun_ctx cd smaller_call_depth_bound))
           with
           | Some depth0 =>
               fun Edepth0 : cd_depthmap cd name = Some depth0 =>
               Some
                 {|
                   fun_name := name;
                   fun_depth := depth0;
                   fun_depth_ok := Edepth0;
                   fun_decl := d;
                   fun_decl_ok := E;
                   fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth0
                 |}
           | None => _
           end eq_refl)
  with (Some
           {|
             fun_name := name;
             fun_depth := depth;
             fun_depth_ok := Edepth;
             fun_decl := d;
             fun_decl_ok := E;
             fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth
           |}).
  2:{
    remember (fun Edepth0 : cd_depthmap cd name = None =>
                False_rect (option (fun_ctx cd smaller_call_depth_bound)) (Descend.fun_ctx_descend_helper E Edepth0))
      as bad. clear Heqbad.
    remember (fun depth0 (Edepth0 : cd_depthmap cd name = Some depth0) =>
    Some
      {|
        fun_name := name;
        fun_depth := depth0;
        fun_depth_ok := Edepth0;
        fun_decl := d;
        fun_decl_ok := E;
        fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth0
      |}) as f.
    replace (Some
              {|
                fun_name := name;
                fun_depth := depth;
                fun_depth_ok := Edepth;
                fun_decl := d;
                fun_decl_ok := E;
                fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth
              |})
    with (f depth Edepth)
    by now subst.
    clear Heqf.
    destruct (cd_depthmap cd name). 2:discriminate.
    inversion Edepth. subst.
    f_equal.
    apply proof_irrelevance.
  }

  remember (fix interpret_expr_list
      (world0 : world_state) (loc0 : memory) (e : list expr)
      (CallOk0 : FSet.is_subset (expr_list_callset e) (decl_callset (fun_decl fc)) = true) {struct e} :
        world_state * expr_result (list uint256) := _) as interpret_expr_list.
  remember (fix interpret_expr_list (world0 : world_state) (loc0 : memory) (e : list expr) {struct e} :
            world_state * option (expr_result (list uint256)) := _) as interpret_expr_list_metered.

  assert (ArgsOk: forall w l COk,
                  let '(w', result) := interpret_expr_list w l args COk
                  in interpret_expr_list_metered w l args = (w', Some result)).
  {
    induction args. { now subst. }
    rewrite Heqinterpret_expr_list. rewrite Heqinterpret_expr_list_metered.
    cbn.
    rewrite<- Heqinterpret_expr_list. rewrite<- Heqinterpret_expr_list_metered.
    clear Heqinterpret_expr_list Heqinterpret_expr_list_metered.
    intros.
    assert (CallOk': let _ := string_set_impl in
                     FSet.is_subset (expr_callset (PrivateCall name args))
                                    (decl_callset (fun_decl fc))
                      = true).
    {
      cbn. cbn in CallOk.
      rewrite FSet.add_subset_and.
      rewrite FSet.add_subset_and in CallOk.
      rewrite Bool.andb_true_iff.
      rewrite Bool.andb_true_iff in CallOk.
      destruct CallOk as (CallOk, HasFun).
      split. 2:assumption. clear HasFun.
      rewrite FSet.union_subset_and in CallOk.
      rewrite Bool.andb_true_iff in CallOk.
      tauto.
    }  
    assert (IH := IHargs CallOk' (List.Forall_inv_tail H) w l (callset_descend_tail eq_refl COk)).
    clear IHargs.
    destruct (interpret_expr_list w l args (callset_descend_tail eq_refl COk)) as (world', result).
    rewrite IH. clear IH.
    destruct result. 2:trivial.
    assert (HeadOk := List.Forall_inv H (callset_descend_head eq_refl COk) world' l loops).
    cbn in HeadOk. clear H.
    destruct (interpret_expr Ebound fc do_call builtins world' l loops a (callset_descend_head eq_refl COk))
      as (ww, ll).
    rewrite HeadOk.
    now destruct ll.
  }

  assert (DoCallMeteredFinishes:
            forall (fc' : fun_ctx cd smaller_call_depth_bound) (w: world_state)
                   (arg_values : list uint256),
              snd (do_call_metered (fun_decl fc') w arg_values) <> None).
  {
    intros.
    assert (D := DoCallOk fc' w arg_values).
    destruct (do_call fc' w arg_values).
    intro HH.
    rewrite D in HH.
    inversion HH.
  }
  assert (DFinishes: forall (w: world_state)
                            (arg_values : list uint256),
            snd (do_call_metered d w arg_values) <> None).
  {
    apply (DoCallMeteredFinishes {|
                   fun_name := name;
                   fun_depth := depth;
                   fun_depth_ok := Edepth;
                   fun_decl := d;
                   fun_decl_ok := E;
                   fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth
                 |}).
  }
  assert (DoCallRewrite: forall (w: world_state)
                                (arg_values : list uint256),
           do_call {|
                   fun_name := name;
                   fun_depth := depth;
                   fun_depth_ok := Edepth;
                   fun_decl := d;
                   fun_decl_ok := E;
                   fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth
                 |} w arg_values
            =
           match snd (do_call_metered d w arg_values) as z return _ = z -> _ with
           | Some result => fun _ => (fst (do_call_metered d w arg_values), result)
           | None => fun Bad => False_rect _ (DFinishes _ _ Bad)
           end eq_refl).
  {
    intros.
    remember {|
                   fun_name := name;
                   fun_depth := depth;
                   fun_depth_ok := Edepth;
                   fun_decl := d;
                   fun_decl_ok := E;
                   fun_bound_ok := Descend.call_descend' fc CallOk Ebound eq_refl E Edepth
             |} as fc'.
    assert (D := DoCallOk fc' w arg_values).
    destruct (do_call fc' w arg_values) as (w', r').
    remember (fun Bad : snd (do_call_metered d w arg_values) = None =>
                False_rect (world_state * expr_result uint256) (DFinishes w arg_values Bad))
      as foo. clear Heqfoo.
    remember (snd (do_call_metered d w arg_values)) as s.
    destruct s.
    {
      subst fc'. cbn in D.
      rewrite D in *.
      cbn in *.
      f_equal.
      now inversion Heqs.
    }
    subst fc'. cbn in D.
    rewrite D in *.
    cbn in Heqs.
    discriminate.
  }
  clear H Heqinterpret_expr_list Heqinterpret_expr_list_metered.
  assert (A := ArgsOk world loc (callset_descend_args eq_refl CallOk)). clear ArgsOk.
  destruct (interpret_expr_list world loc args (callset_descend_args eq_refl CallOk))
    as (world', result_args).
  rewrite A.
  unfold cd_declmap in *.
  destruct result_args. 2:{ now rewrite E. }
  rewrite DoCallRewrite. clear DoCallRewrite.
  rewrite E.
  assert (Ok := DFinishes world' value).
  remember (fun Bad : snd (do_call_metered d world' value) = None =>
             False_rect (world_state * expr_result uint256) (DFinishes world' value Bad))
    as bad. clear Heqbad.
  remember (snd (do_call_metered d world' value)) as x. destruct x.
  { rewrite Heqx. now destruct (do_call_metered d world' value). }
  symmetry in Heqx. contradiction.
}
(* BuiltinCall *)
remember (fix interpret_expr_list
    (world0 : world_state) (loc0 : memory) (e : list expr)
    (CallOk0 : FSet.is_subset (expr_list_callset e) (decl_callset (fun_decl fc)) = true) {struct e} :
      world_state * expr_result (list uint256) := _) as interpret_expr_list.
remember (fix interpret_expr_list (world0 : world_state) (loc0 : memory) (e : list expr) {struct e} :
          world_state * option (expr_result (list uint256)) := _) as interpret_expr_list_metered.
assert (ArgsOk: forall w l COk,
                let '(w', result) := interpret_expr_list w l args COk
                in interpret_expr_list_metered w l args = (w', Some result)).
{
  induction args. { now subst. }
  rewrite Heqinterpret_expr_list. rewrite Heqinterpret_expr_list_metered.
  cbn.
  rewrite<- Heqinterpret_expr_list. rewrite<- Heqinterpret_expr_list_metered.
  clear Heqinterpret_expr_list Heqinterpret_expr_list_metered.
  intros.
  assert (CallOk': let _ := string_set_impl in
                   FSet.is_subset (expr_callset (BuiltinCall name args))
                                  (decl_callset (fun_decl fc))
                    = true).
  {
    cbn. cbn in CallOk.
    rewrite FSet.union_subset_and in CallOk.
    rewrite Bool.andb_true_iff in CallOk.
    tauto.
  }
  assert (IH := IHargs CallOk' (List.Forall_inv_tail H) w l (callset_descend_tail eq_refl COk)).
  clear IHargs.
  destruct (interpret_expr_list w l args (callset_descend_tail eq_refl COk)) as (world', result).
  rewrite IH. clear IH.
  destruct result. 2:trivial.
  assert (HeadOk := List.Forall_inv H (callset_descend_head eq_refl COk) world' l loops).
  cbn in HeadOk. clear H.
  destruct (interpret_expr Ebound fc do_call builtins world' l loops a (callset_descend_head eq_refl COk))
    as (ww, ll).
  rewrite HeadOk.
  now destruct ll.
}
clear H Heqinterpret_expr_list Heqinterpret_expr_list_metered.
assert (A := ArgsOk world loc (callset_descend_builtin_args eq_refl CallOk)). clear ArgsOk.
destruct (interpret_expr_list world loc args (callset_descend_builtin_args eq_refl CallOk))
  as (world', result_args).
rewrite A. clear A.
destruct result_args. 2:reflexivity.
destruct (builtins name). 2:reflexivity.
destruct b as (arity, b).
remember (fun Earity : (arity =? Datatypes.length value) = true => call_builtin value Earity (b world'))
  as good_branch_1.
remember (fun Earity : (arity =? Datatypes.length value) = true =>
   let '(world'', result0) := call_builtin value Earity (b world') in (world'', Some result0))
  as good_branch_2.
enough (Q: forall E, let '(w, result) := good_branch_1 E in
           good_branch_2 E = (w, Some result)).
{
  clear Heqgood_branch_1 Heqgood_branch_2.
  destruct (arity =? Datatypes.length value).
  { apply Q. }
  trivial.
}
subst. intro E. now destruct (call_builtin value E (b world')) as (w, result).
Qed.