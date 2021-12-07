From Coq Require Import String NArith ZArith DecimalString List Lia.

From Vyper Require Import Config.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require AST.
From Vyper.L50 Require AST.
From Vyper.L50 Require Import Types Expr.

From Vyper.L40Metered Require Import Interpret.

From Vyper.From40To50 Require Import Translate Proto.

Definition LocalVarsAgree {C: VyperConfig} (m: memory) (loc: string_map dynamic_value) (cap: N)
: Prop
:= let _ := memory_impl in
   forall k: N, (k < cap)%N ->
     map_lookup loc (make_var_name "var" k)
      =
     Some (existT _ U256 (yul_uint256 (OpenArray.get m k))).

Lemma local_vars_agree_weaken {C: VyperConfig} {m: memory} {loc: string_map dynamic_value}
                              {old_cap: N} {new_cap: N}
                              (Bound: (new_cap <= old_cap)%N)
                              (Ok: LocalVarsAgree m loc old_cap):
  LocalVarsAgree m loc new_cap.
Proof.
unfold LocalVarsAgree in *.
intros k KN.
assert (KO: (k < old_cap)%N) by lia.
apply (Ok k KO).
Qed.

Lemma local_vars_agree_weaken_left {C: VyperConfig} {m: memory} {loc: string_map dynamic_value}
                                   {a b: N}
                                   (Ok: LocalVarsAgree m loc (N.max a b)):
  LocalVarsAgree m loc a.
Proof.
refine (local_vars_agree_weaken _ Ok).
lia.
Qed.

Lemma local_vars_agree_weaken_right {C: VyperConfig} {m: memory} {loc: string_map dynamic_value}
                                    {a b: N}
                                    (Ok: LocalVarsAgree m loc (N.max a b)):
  LocalVarsAgree m loc b.
Proof.
refine (local_vars_agree_weaken _ Ok).
lia.
Qed.

(* L50 might have no value where L40 sees zero. *)
Definition ExprResultsAgree {C: VyperConfig}
                            (e40: expr_result uint256)
                            (e50: expr_result (list dynamic_value))
                            (n: N)
:= match e40, e50 with
   | ExprAbort a40, ExprAbort a50               =>  a40 = a50
   | ExprSuccess v40, ExprSuccess nil           =>  Z_of_uint256 v40 = 0%Z /\ n = 0%N
   | ExprSuccess v40, ExprSuccess (v50 :: nil)  =>  v40 = uint256_of_dynamic_value v50 /\ n = 1%N
   | _, _ => False
   end.

Definition ResultsAgree {C: VyperConfig}
                        (result40: world_state * option (expr_result uint256))
                        (result50: world_state * option (expr_result (list dynamic_value)))
                        (n: N)
:= let '(w40, r40) := result40 in
   let '(w50, r50) := result50 in
   w40 = w50
    /\
   match r40, r50 with
   | Some e40, Some e50 => ExprResultsAgree e40 e50 n
   | None, None => True
   | _, _ => False
   end.

Definition ValueListsAgree {C: VyperConfig}
                           (result40: world_state * option (expr_result (list uint256)))
                           (result50: world_state * option (expr_result (list dynamic_value)))
:= let '(w40, r40) := result40 in
   let '(w50, r50) := result50 in
   w40 = w50
    /\
   match r40, r50 with
   | Some (ExprAbort a40), Some (ExprAbort a50) =>
        a40 = a50
   | Some (ExprSuccess e40), Some (ExprSuccess e50) =>
        e40 = map uint256_of_dynamic_value e50
   | None, None => True
   | _, _ => False
   end.


(* loopinfo:
      (..., $$offset1, $$offset0)
 *)
Definition LoopOffsetsAgree {C: VyperConfig}
                            (loop_info: list L40.Expr.loop_ctx)
                            (loc: string_map dynamic_value)
:= let nesting_depth := length loop_info in
   forall k: nat,
     k < nesting_depth
      ->
     match nth_error (map L40.Expr.loop_offset loop_info) (nesting_depth - 1 - k) with
     | None => False
     | Some x => map_lookup loc (make_var_name "offset" (N.of_nat k)) = Some (existT _ U256 (yul_uint256 x))
     end.

Definition get_cursor {C: VyperConfig} (loop: L40.Expr.loop_ctx)
: uint256
:= uint256_of_Z (Z_of_uint256 (L40.Expr.loop_count loop) - 1 - Z.of_nat (L40.Expr.loop_countdown loop)).

Definition LoopCursorsAgree {C: VyperConfig}
                           (loop_info: list L40.Expr.loop_ctx)
                           (loc: string_map dynamic_value)
:= let nesting_depth := length loop_info in
   forall k: nat,
     k < nesting_depth
      ->
     match nth_error (map get_cursor loop_info) (nesting_depth - 1 - k) with
     | None => False
     | Some x => map_lookup loc (make_var_name "cursor" (N.of_nat k)) = Some (existT _ U256 (yul_uint256 x))
     end.

Definition ProtosAgree {C: VyperConfig}
                       (protos: string -> option proto)
                       (builtins: string -> option L50.Builtins.yul_builtin)
:= forall name,
     match protos name, builtins name with
     | None, None => True
     | Some p, Some b => p_inputs p = L50.Builtins.b_input_types b 
                          /\
                         p_outputs p = L50.Builtins.b_output_types b
     | _, _ => False
     end.

(*
Lemma interpret_translated_expr {C: VyperConfig}
                                {B: builtin_names_config}
                                {protos: string_map proto}
                                {e40: L40.AST.expr}
                                {e50: L50.AST.expr}
                                {n: N}
                                {loop_depth: N}
                                (Ok: translate_expr protos e40 loop_depth = inr (e50, n))
                                (call40: forall
                                              (decl: L40.AST.decl)
                                              (world: world_state)
                                              (arg_values: list uint256),
                                            world_state * option (expr_result uint256))
                                (call50: forall
                                              (decl: L50.AST.fun_decl)
                                              (world: world_state)
                                              (arg_values: list dynamic_value),
                                            world_state * option (expr_result (list dynamic_value)))
                                (CallsOk: forall (decl40: L40.AST.decl)
                                                 (decl50: L50.AST.fun_decl)
                                                 (Ok: translate_fun_decl B protos decl40 = inr decl50)
                                                 (world: world_state)
                                                 (args40: list uint256)
                                                 (args50: list dynamic_value)
                                                 (ArgsOk: args40 = map uint256_of_dynamic_value args50),
                                             ResultsAgree (call40 decl40 world args40)
                                                          (call50 decl50 world args50) 1%N)
                                (decls40: string_map L40.AST.decl)
                                (decls50: string_map L50.AST.fun_decl)
                                (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
                                (builtins40: string -> option builtin)
                                (builtins50: string -> option L50.Builtins.yul_builtin)
                                (BuiltinsSafe: forall x,
                                                 builtins50 ("$" ++ x)%string = None)
                                (ProtosOk: ProtosAgree (map_lookup protos) builtins50)
                                (world: world_state)
                                (loc40: memory)
                                (loc50: string_map dynamic_value)
                                (LocalVarsOk: LocalVarsAgree loc40 loc50 (L40.AST.var_cap_expr e40))
                                (loop_info: list L40.Expr.loop_ctx)
                                (LoopDepthOk: length loop_info = N.to_nat loop_depth)
                                (OffsetsOk: LoopOffsetsAgree loop_info loc50)
                                (CursorsOk: LoopCursorsAgree loop_info loc50):
  ResultsAgree
    (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e40)
    (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e50) n.
Proof.
revert e50 Ok world.
induction e40 using L40.AST.expr_ind'; intros; cbn in Ok; inversion Ok; subst; cbn; cbn in LocalVarsOk.
{ (* const *) easy. }
{ (* local var *)
  assert (L := LocalVarsOk name (N.lt_succ_diag_r name)).
  cbn in L. unfold map_lookup in L. now rewrite L.
}
{ (* offset *)
  clear H0.
  remember (loop_depth =? 0)%N as loop_depth_is_0.
  destruct loop_depth_is_0. { discriminate. }
  inversion Ok; subst; cbn; cbn in LocalVarsOk.
  unfold LoopOffsetsAgree in OffsetsOk.
  assert (L: length loop_info <> 0).
  {
    rewrite LoopDepthOk.
    intro H.
    replace 0 with (N.to_nat 0%N) in H by trivial.
    apply N2Nat.inj in H.
    subst.
    discriminate.
  }
  assert (J := OffsetsOk (Nat.pred (length loop_info)) (Nat.lt_pred_l _ L)).
  replace (length loop_info - 1 - Nat.pred (length loop_info)) with 0 in J by lia.
  destruct loop_info as [|loop]. { contradiction. }
  cbn in J. unfold map_lookup in J.
  replace (N.pred loop_depth) with (N.of_nat (length loop_info)) by (cbn in LoopDepthOk; lia).
  now rewrite J.
}
{ (* cursor *) (* dup from offset *)
  clear H0.
  remember (loop_depth =? 0)%N as loop_depth_is_0.
  destruct loop_depth_is_0. { discriminate. }
  inversion Ok; subst; cbn; cbn in LocalVarsOk.
  unfold LoopCursorsAgree in CursorsOk.
  assert (L: length loop_info <> 0).
  {
    rewrite LoopDepthOk.
    intro H.
    replace 0 with (N.to_nat 0%N) in H by trivial.
    apply N2Nat.inj in H.
    subst.
    discriminate.
  }
  assert (J := CursorsOk (Nat.pred (length loop_info)) (Nat.lt_pred_l _ L)).
  replace (length loop_info - 1 - Nat.pred (length loop_info)) with 0 in J by lia.
  destruct loop_info as [|loop]. { contradiction. }
  cbn in J. unfold map_lookup in J.
  replace (N.pred loop_depth) with (N.of_nat (length loop_info)) by (cbn in LoopDepthOk; lia).
  now rewrite J.
}
{ (* PrivateCall *)
  assert (F := translate_fun_decls_ok DeclsOk name).
  remember (fix translate_expr_list (C : VyperConfig) (l : list L40.AST.expr) (loop_depth : N) {struct l} :
         string + list AST.expr := _) as translate_expr_list.
  remember (translate_expr_list C args loop_depth) as maybe_args'.
  destruct maybe_args' as [err | args']. { discriminate. }
  inversion Ok. subst e50 n. cbn.

  (* looking up the same function in both maps *)
  cbn in BuiltinsSafe.
  rewrite BuiltinsSafe.
  destruct (map_lookup decls40 name) as [d40|].
  2:{ cbn in F. now destruct (map_lookup decls50). }
  cbn in F. destruct (map_lookup decls50) as [d50|]. 2:contradiction.

  (* args *)
  remember (fix interpret_expr_list (world0 : world_state) (loc : memory) (e : list L40.AST.expr):
              world_state * option (expr_result (list uint256)) := _) as interpret_list_40.
  remember (fix interpret_expr_list (world0 : world_state) (loc : string_map dynamic_value) (args0 : list AST.expr) :
              world_state * option (expr_result (list dynamic_value)) := _) as interpret_list_50.
  assert (V: ValueListsAgree (interpret_list_40 world loc40 args)
                             (interpret_list_50 world loc50 args')).
  {
    symmetry in Heqmaybe_args'.
    clear Ok H1.
    revert args' Heqmaybe_args' world H.
    rewrite Heqtranslate_expr_list.
    induction args; intros; cbn; cbn in Heqmaybe_args'.
    { inversion Heqmaybe_args'. now subst. }
    remember (translate_expr protos a loop_depth) as maybe_a'.
    destruct maybe_a' as [|(h', n)]. { discriminate. }
    (* arg must eval to 1 value only *)
    remember (n =? 1)%N as n_is_1. destruct n_is_1. 2:discriminate.
    symmetry in Heqn_is_1. apply N.eqb_eq in Heqn_is_1. subst n.
    rewrite<- Heqtranslate_expr_list in Heqmaybe_args'.
    remember (translate_expr_list C args loop_depth) as maybe_args_t'.
    destruct maybe_args_t' as [|t']. { discriminate. }
    inversion Heqmaybe_args'. subst args'. clear Heqmaybe_args'.
    rewrite Heqtranslate_expr_list in Heqmaybe_args_t'.
    assert (TailOk := IHargs (local_vars_agree_weaken_right LocalVarsOk)
                             t' (eq_sym Heqmaybe_args_t') world
                             (Forall_inv_tail H)).
    rewrite Heqinterpret_list_40. cbn. rewrite<- Heqinterpret_list_40.
    rewrite Heqinterpret_list_50. cbn. rewrite<- Heqinterpret_list_50.
    destruct (interpret_list_40 world loc40 args) as (world', result40).
    destruct (interpret_list_50 world loc50 t') as (world50, result50).
    (* figure out what the arg tail evaluates to *)
    unfold ValueListsAgree. unfold ValueListsAgree in TailOk.
    destruct TailOk as (W, R). subst world50.
    destruct result40 as [result40|]. 2:{ now destruct result50. }
    destruct result40 as [values40 | abort40].
    2:{
      destruct result50 as [result50|]. 2:{ contradiction. }
      destruct result50 as [values50 | abort50]. { contradiction. }
      now subst.
    }
    destruct result50 as [result50|]. 2:{ contradiction. }
    destruct result50 as [values50 | abort50]. 2:{ contradiction. }
    (* arg tail evaluated successfully, let's see what the head does *)
    assert (HeadOk := Forall_inv H (local_vars_agree_weaken_left LocalVarsOk)
                                 h' (eq_sym Heqmaybe_a') world').
    unfold ResultsAgree in HeadOk.
    destruct (interpret_expr_metered decls40 call40 builtins40 world' loc40 loop_info a) as (w40, r40).
    destruct (interpret_expr builtins50 (map_lookup decls50) call50 world' loc50 h') as (w50, r50).
    destruct HeadOk as (W, HeadOk).
    split. { exact W. }
    destruct r40 as [r40 |], r50 as [r50 |]; try easy.
    unfold ExprResultsAgree in HeadOk.
    destruct r40 as [v40 | a40], r50 as [v50 | a50]; try easy.
    unfold cons_eval_results.
    destruct v50. { destruct HeadOk. discriminate. }
    destruct v50. 2:{ contradiction. }
    destruct HeadOk as (HeadOk, _).
    cbn.
    now f_equal.
  }
  (* do the call *)
  destruct (interpret_list_40 world loc40 args) as (w40, r40).
  destruct (interpret_list_50 world loc50 args') as (w50, r50).
  unfold ValueListsAgree in V. destruct V as (W, V).
  destruct r40 as [[v40|a40] | ], r50 as [[v50|a50] | ]; try easy.
  subst w50.
  exact (CallsOk d40 d50 F w40 v40 v50 V).
}
(* builtin call *)
remember (fix translate_expr_list (C : VyperConfig) (l : list L40.AST.expr) (loop_depth : N) {struct l} :
       string + list AST.expr := _) as translate_expr_list.
remember (translate_expr_list C args loop_depth) as maybe_args'.
destruct maybe_args' as [err | args']. { discriminate. }
remember (Map.lookup protos name) as maybe_proto.
destruct maybe_proto as [proto|]. 2:discriminate.
inversion Ok. subst e50 n. cbn.
remember (fix interpret_expr_list (world0 : world_state) (loc : memory) (e : list L40.AST.expr):
            world_state * option (expr_result (list uint256)) := _) as interpret_list_40.
remember (fix interpret_expr_list (world0 : world_state) (loc : string_map dynamic_value) (args0 : list AST.expr) {struct
                args0} : world_state * option (expr_result (list dynamic_value)) := _) as interpret_list_50.
assert (P := ProtosOk name). unfold map_lookup in P. rewrite<- Heqmaybe_proto in P.
*)