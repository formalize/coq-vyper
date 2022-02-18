From Coq Require Import String ZArith NArith Lia PropExtensionality.

From Vyper Require Import Config Calldag Logic2 Range.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L40 Require AST.
From Vyper.L50 Require AST Call.
From Vyper.L50 Require Import Types Builtins DynError.
From Vyper.L10 Require Import Base.

From Vyper.L40Metered Require Import Interpret.

From Vyper.From40To50 Require Import Translate Proto Mangle Expr Stmt.


Local Definition OnlyVars {C: VyperConfig}
                          (loc: string_map dynamic_value)
: Prop
:= forall (name: string)
          (H: map_lookup loc name <> None),
   exists k, make_var_name "var" k = name.

Local Lemma only_vars_empty {C: VyperConfig}:
  let _ := string_map_impl in OnlyVars Map.empty.
Proof.
cbn. intros name H.
exfalso.
exact (H (Map.empty_lookup name)).
Qed.

(*
Local Lemma var_finder_empty {C: VyperConfig}:
  let _ := string_map_impl in VarFinder Map.empty 0%N.
*)

Local Lemma only_vars_insert {C: VyperConfig}
                              (loc: string_map dynamic_value)
                              (key: N)
                              (value: dynamic_value)
                              (F: OnlyVars loc):
  OnlyVars (map_insert loc (make_var_name "var" key) value).
Proof.
intros name H.
unfold map_lookup in H. unfold map_insert in H. rewrite Map.insert_ok in H.
destruct string_dec as [E|NE].
{ exists key. exact E. }
exact (F name H).
Qed.

(*
Local Lemma var_finder_insert {C: VyperConfig}
                              (loc: string_map dynamic_value)
                              (bound key: N)
                              (value: dynamic_value)
                              (F: VarFinder loc bound):
  VarFinder (map_insert loc (make_var_name "var" key) value) (N.max bound (N.succ key)).
Proof.
intros name H.
unfold map_lookup in H. unfold map_insert in H. rewrite Map.insert_ok in H.
destruct string_dec as [E|NE].
{ exists key.  split. { lia. } exact E. }
destruct (F name H) as (f, OkF).
exists f. split. { lia. } tauto.
Qed.
*)

Local Definition bind_args {C: VyperConfig}
                           (args: list uint256)
                           (arity start: N)
                           (loc: string_map dynamic_value)
:= LocalVars.bind_vars_to_values 
     (List.map (fun n : N => (U256, make_var_name "var" n)) (range start arity))
     (List.map (fun x : uint256 => existT _ U256 (yul_uint256 x))
         args) loc.

Definition ArgsAgree {C: VyperConfig}
                     (args: list uint256)
                     (loc: string_map dynamic_value)
:= OnlyVars loc
    /\
   forall k,
     option_map (fun x : uint256 => existT _ U256 (yul_uint256 x))
                (List.nth_error args (N.to_nat k))
      =
     map_lookup loc (make_var_name "var" k).

Lemma args_agree_nil {C: VyperConfig}:
  let _ := string_map_impl in
  ArgsAgree nil Map.empty.
Proof.
split. { apply only_vars_empty. }
unfold map_lookup. intro k. rewrite Map.empty_lookup.
rewrite (proj2 (List.nth_error_None _ _)). { easy. }
cbn. lia.
Qed.

Definition bind_args_ok {C: VyperConfig}
                        (args prefix: list uint256)
                        (arity: N)
                        (loc: string_map dynamic_value)
                        (F: ArgsAgree prefix loc):
  let b := bind_args args arity (N.of_nat (List.length prefix)) loc in
  match (List.length args ?= N.to_nat arity) with
  | Lt => b = inl DE_TooFewValues
  | Gt => b = inl DE_TooManyValues
  | Eq => match b with
          | inl _ => False
          | inr result => ArgsAgree (prefix ++ args) result
          end
  end.
Proof.
unfold ArgsAgree in *.
remember (N.to_nat arity) as n.
unfold bind_args. rewrite range_via_nat.
remember (make_var_name "var") as var_name.
revert prefix arity Heqn args loc F. induction n; intros; rewrite<- Heqn.
{
  destruct args as [|h]; cbn. 2:trivial.
  rewrite List.app_nil_r. exact F.
}
destruct args as [|h]; cbn. { trivial. }
assert (OkN: n = N.to_nat (N.pred arity)) by lia.
repeat rewrite Nat2N.id.
assert (X: forall x, x + S n - 1 - n = x) by lia. repeat rewrite X. clear X.
assert (M: map_lookup loc (var_name (N.of_nat (Datatypes.length prefix))) = None).
{
  rewrite<- (proj2 F).
  enough (A: List.nth_error prefix (N.to_nat (N.of_nat (Datatypes.length prefix))) = None)
    by now rewrite A.
  apply List.nth_error_None.
  lia.
}
rewrite M.
assert (IH := IHn (prefix ++ h :: nil)%list (N.pred arity) OkN args
                  ((map_insert loc (var_name (N.of_nat (Datatypes.length prefix)))
                               (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 h))))).
cbn. cbn in IH.
unfold range_nat in IH.
subst n.
repeat rewrite<- List.app_assoc in IH. cbn in IH.
repeat rewrite List.app_length in IH. cbn in IH.
repeat rewrite Nat2N.id in *.
assert (R: forall x y, x + 1 + y = x + S y) by lia. repeat rewrite R in IH.
apply IH. clear IH IHn R.
split.
{
  subst var_name.
  apply only_vars_insert.
  tauto.
}
intro k.
unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
destruct string_dec as [E|NE].
{
  subst var_name. apply make_var_name_inj in E.
  subst k. rewrite Nat2N.id.
  rewrite List.nth_error_app2 by lia.
  now rewrite Nat.sub_diag.
}
assert (K := proj2 F k).
assert (T := N.lt_trichotomy k (N.of_nat (Datatypes.length prefix))).
destruct T as [LT | [EQ | GT]].
{
  rewrite List.nth_error_app1 by lia.
  apply K.
}
{ subst k. contradiction. }
rewrite (proj2 (List.nth_error_None _ _)). 2:{ rewrite List.app_length. cbn. lia. }
rewrite (proj2 (List.nth_error_None _ _)) in K. 2:{ lia. }
apply K.
Qed.

Fixpoint bind_zeros {C: VyperConfig}
                    (loc: string_map dynamic_value)
                    (start: N)
                    (count: nat)
{struct count}
:= match count with
   | O => loc
   | S count' => bind_zeros (map_insert loc (make_var_name "var" start)
                                            (existT _ U256 (yul_uint256 zero256)))
                            (N.succ start)
                            count'
   end.

Definition lookup_in_init_loc {C: VyperConfig} (args: list uint256) (cap: N) (index: N)
: option dynamic_value
:= if (index <? N.max cap (N.of_nat (List.length args)))%N
     then Some (existT _ U256 (yul_uint256 (List.nth (N.to_nat index) args zero256)))
     else None.

Definition ArgsAndZerosAgree {C: VyperConfig}
                             (loc: string_map dynamic_value)
                             (args: list uint256)
                             (cap: N)
:= (forall name, map_lookup loc name <> None ->
      name = "$$result"%string \/ exists k : N, make_var_name "var" k = name)
     /\
    map_lookup loc "$$result" = Some (existT _ U256 (yul_uint256 zero256))
     /\
    forall k, map_lookup loc (make_var_name "var" k) = lookup_in_init_loc args cap k.

Lemma zeros_eq {C: VyperConfig}:
  int_zero_value I256 false = yul_uint256 zero256.
Proof.
unfold int_zero_value.
unfold zero256.
unfold yul_uint256.
f_equal.
apply Eqdep_dec.eq_proofs_unicity.
decide equality.
Qed.

Lemma args_and_zeros_agree_init {C: VyperConfig}
                                (args: list uint256)
                                (loc_with_args: string_map dynamic_value)
                                (A: ArgsAgree args loc_with_args)
                                (varcap: N)
                                (SmallVarcap: (varcap <= (N.of_nat (List.length args)))%N):
  ArgsAndZerosAgree
     (map_insert loc_with_args "$$result"
                     (existT _ U256 (int_zero_value I256 false)))
     args
     varcap.
Proof.
unfold ArgsAndZerosAgree.
unfold map_lookup. unfold map_insert.
repeat split; intros; repeat rewrite Map.insert_ok in *.
{
  rewrite Map.insert_ok in H.
  destruct string_dec as [|NE]. { now left. }
  right. now apply A.
}
{
  destruct string_dec. 2:contradiction.
  repeat f_equal. apply zeros_eq.
}
destruct string_dec. { discriminate. }
unfold lookup_in_init_loc.
unfold ArgsAgree in A. unfold map_lookup in A.
rewrite<- (proj2 A k).
destruct (Nat.lt_ge_cases (N.to_nat k) (List.length args)) as [KL|KGE].
{
  replace ((k <? N.max varcap (N.of_nat (Datatypes.length args)))%N) with true.
  2:{ symmetry. apply N.ltb_lt. lia. }
  remember (List.nth_error args (N.to_nat k)) as x. symmetry in Heqx.
  destruct x as [x|]. 2:{ exfalso. apply (proj2 (List.nth_error_Some _ _) KL Heqx). }
  now rewrite (List.nth_error_nth _ _ _ Heqx).
}
replace ((k <? N.max varcap (N.of_nat (Datatypes.length args)))%N) with false.
2:{ symmetry. apply N.ltb_ge. lia. }
now rewrite (proj2 (List.nth_error_None _ _) KGE).
Qed.

Lemma args_and_zeros_agree_step {C: VyperConfig}
                                (args: list uint256)
                                (loc: string_map dynamic_value)
                                (varcap: N)
                                (A: ArgsAndZerosAgree loc args varcap)
                                (LargeVarcap: ((N.of_nat (List.length args)) <= varcap)%N):
  ArgsAndZerosAgree
     (map_insert loc (make_var_name "var" varcap)
                     (existT _ U256 (yul_uint256 zero256)))
     args
     (N.succ varcap).
Proof.
unfold ArgsAndZerosAgree.
unfold map_lookup. unfold map_insert.
repeat split; intros; repeat rewrite Map.insert_ok in *.
{
  rewrite Map.insert_ok in H.
  destruct string_dec as [|NE]. { right. now exists varcap. }
  now apply A.
}
{
  destruct string_dec. 1:discriminate.
  apply A.
}
destruct string_dec as [E|NE].
{
  apply make_var_name_inj in E.
  subst k.
  unfold lookup_in_init_loc.
  replace (varcap <? N.max (N.succ varcap) (N.of_nat (Datatypes.length args)))%N with true.
  2:{ symmetry. apply N.ltb_lt. lia. }
  now rewrite List.nth_overflow by lia.
}
destruct A as (_, (_, A)).
unfold map_lookup in A.
rewrite A.
unfold lookup_in_init_loc.
destruct (N.lt_trichotomy k varcap) as [LT|[EQ|GT]].
{
  replace (k <? N.max varcap (N.of_nat (Datatypes.length args)))%N with true.
  2:{ symmetry. apply N.ltb_lt. lia. }
  replace (k <? N.max (N.succ varcap) (N.of_nat (Datatypes.length args)))%N with true.
  2:{ symmetry. apply N.ltb_lt. lia. }
  trivial.
}
{ now subst. }
replace (k <? N.max varcap (N.of_nat (Datatypes.length args)))%N with false.
2:{ symmetry. apply N.ltb_ge. lia. }
replace (k <? N.max (N.succ varcap) (N.of_nat (Datatypes.length args)))%N with false.
2:{ symmetry. apply N.ltb_ge. lia. }
trivial.
Qed.

Lemma bind_zeros_ok {C: VyperConfig}
                    (args: list uint256)
                    (l: string_map dynamic_value)
                    (n: nat)
                    (Init: ArgsAndZerosAgree l args (N.of_nat (Datatypes.length args))):
  ArgsAndZerosAgree (bind_zeros l (N.of_nat (Datatypes.length args)) n) args
    (N.of_nat (n + Datatypes.length args)).
Proof.
remember n as k. replace k with n at 2.
replace (N.of_nat (Datatypes.length args)) with (N.of_nat (n - k + Datatypes.length args)) in Init by lia.
replace (N.of_nat (Datatypes.length args)) with (N.of_nat (n - k + Datatypes.length args)) by lia.
assert (K: k <= n) by lia.
clear Heqk.
revert l Init K. induction k; intros. { now rewrite Nat.sub_0_r in Init. }
simpl.
assert (G: ArgsAndZerosAgree
             (map_insert l (make_var_name "var" (N.of_nat (n - S k + Datatypes.length args)))
                (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 zero256))) args
             (N.succ (N.of_nat (n - S k + Datatypes.length args)))).
{
  apply (args_and_zeros_agree_step _ _ _ Init).
  lia.
}
replace (N.succ (N.of_nat (n - S k + Datatypes.length args)))
   with (N.of_nat (n - k + Datatypes.length args))
   in * by lia.
apply (IHk _ G (le_Sn_le _ _ K)).
Qed.

Lemma bind_zeros_for_loc_with_args {C: VyperConfig}
                                   (args: list uint256)
                                   (loc_with_args: string_map dynamic_value)
                                   (A: ArgsAgree args loc_with_args)
                                   (varcap: N):
  ArgsAndZerosAgree
    (bind_zeros (map_insert loc_with_args "$$result"
                           (existT _ U256 (int_zero_value I256 false)))
                     (N.of_nat (List.length args))
                     (N.to_nat varcap - List.length args))
    args varcap.
Proof.
destruct (Nat.lt_ge_cases (N.to_nat varcap) (List.length args)) as [L|GE].
{ (* small varcap *)
  replace (N.to_nat varcap - Datatypes.length args) with 0 by lia.
  cbn.
  apply (args_and_zeros_agree_init args loc_with_args A). lia.
}
remember (N.to_nat varcap - List.length args) as n.
assert (V: varcap = N.of_nat (n + List.length args)) by lia.
subst varcap.
clear Heqn GE.
assert (Init := args_and_zeros_agree_init _ _ A (N.of_nat (Datatypes.length args)) (N.le_refl _)).
remember (map_insert loc_with_args "$$result"
            (existT _ U256 (int_zero_value I256 false))) as l. clear Heql. clear A.
now apply bind_zeros_ok.
Qed.


Local Lemma interpret_generated_var_decls {C: VyperConfig}
                                          (max_loop_iterations: nat)
                                          (builtins50: string -> option L50.Builtins.yul_builtin)
                                          (decls50: string_map L50.AST.fun_decl)
                                          (this_fun_decl50: option L50.AST.fun_decl)
                                          (args: list uint256)
                                          (loc: string_map dynamic_value)
                                          (arity varcap: N)
                                          (ArityOk: arity = N.of_nat (List.length args))
                                          (A: ArgsAndZerosAgree loc args arity)
                                          (call50: L50.AST.fun_decl -> world_state -> list dynamic_value ->
                                                   world_state * option (expr_result (list dynamic_value)))
                                          (world: world_state):
   L50.Stmt.interpret_stmt_list_no_unbind max_loop_iterations builtins50 (map_lookup decls50)
     this_fun_decl50 call50
     world loc
     (make_var_declarations arity varcap)
    =
   (world,
    bind_zeros loc arity (N.to_nat (varcap - arity)%N),
    Some StmtSuccess,
    List.map (fun k => (U256, make_var_name "var" k))
             (List.rev (range arity (varcap - arity)%N))).
Proof.
unfold make_var_declarations.
rewrite range_via_nat.
remember (N.to_nat (varcap - arity)%N) as n.
clear varcap Heqn.
subst arity.
remember n as k.
replace (N.of_nat (Datatypes.length args)) with (N.of_nat (n - k + Datatypes.length args)) in A by lia.
replace (N.of_nat (Datatypes.length args)) with (N.of_nat (n - k + Datatypes.length args)) by lia.
assert (K: k <= n) by lia.
clear Heqk.
revert loc K A. induction k; intros. { easy. }
simpl.
rewrite Nat2N.id.
replace (n - S k + Datatypes.length args + S k - 1 - k) with (n - S k + Datatypes.length args) by lia.

(* shadowing check *)
rewrite (proj2 (proj2 A) (N.of_nat (n - S k + Datatypes.length args))).
unfold lookup_in_init_loc.
replace (N.of_nat (n - S k + Datatypes.length args) <?
         N.max (N.of_nat (n - S k + Datatypes.length args)) (N.of_nat (Datatypes.length args)))%N
  with false by (symmetry; apply N.ltb_ge; lia).
assert (G: ArgsAndZerosAgree
             (map_insert loc (make_var_name "var" (N.of_nat (n - S k + Datatypes.length args)))
                (existT (fun t : yul_type => yul_value t) U256 (int_zero_value I256 false))) args (N.of_nat (n - k + Datatypes.length args))).
{
  replace (N.of_nat (n - k + Datatypes.length args))
    with (N.succ (N.of_nat (n - S k + Datatypes.length args))) by lia.
  rewrite zeros_eq.
  apply (args_and_zeros_agree_step _ _ _ A).
  lia.
}
assert (IH := IHk (map_insert loc (make_var_name "var" (N.of_nat (n - S k + Datatypes.length args)))
                  (existT (fun t : yul_type => yul_value t) U256 (int_zero_value I256 false)))
                  (le_Sn_le _ _ K) G).
replace (n - S k + Datatypes.length args + S k - 1) with (n - k + Datatypes.length args + k - 1) by lia.
unfold range_nat in IH.
rewrite Nat2N.id in IH.
rewrite IH.
f_equal. 2:{ now rewrite List.map_app. }
repeat f_equal; trivial. { apply zeros_eq. }
lia.
Qed.


Lemma interpret_translated_call {C: VyperConfig}
                                (max_call_depth: nat)
                                (max_loop_iterations: nat)

                                {B: builtin_names_config}
                                (builtins40: string -> option L10.Base.builtin)
                                (builtins50: string -> option L50.Builtins.yul_builtin)
                                (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
                                (BuiltinsBasics: BuiltinsSupportBasics builtins50)
                                (BuiltinsSafe: forall x,
                                                 builtins50 ("$" ++ x)%string = None)
                                (BuiltinsHaveArith: BuiltinsSupportUInt256 B builtins40)

                                {protos: string_map proto}
                                (KnownProtosOk: check_known_protos B (map_lookup protos) = true)
                                (ProtosOk: ProtosAgree (map_lookup protos) builtins50)

                                {decls40: string_map L40.AST.decl}
                                {decls50: string_map L50.AST.fun_decl}
                                (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)

                                (d40: L40.AST.decl)
                                (d50: L50.AST.fun_decl)
                                (Ok: translate_fun_decl B protos d40 = inr d50)

                                (EnoughIterationsForEverything:
                                   (L40.AST.max_loop_count_decl_map decls40 < N.of_nat max_loop_iterations)%N)
                                (EnoughIterations:
                                   (L40.AST.max_loop_count_decl d40 < N.of_nat max_loop_iterations)%N)

                                (world: world_state)
                                (arg_values: list uint256):
  ResultsAgree
    (interpret_call_metered max_call_depth decls40 builtins40 d40 world arg_values)
    (L50.Call.interpret_call max_call_depth max_loop_iterations builtins50
                             (map_lookup decls50) d50 world
                             (List.map (fun x => (existT _ U256 (yul_uint256 x))) arg_values))
    1%N.
Proof.
revert max_loop_iterations d40 d50 Ok world arg_values EnoughIterations EnoughIterationsForEverything.
induction max_call_depth; intros. { easy. }
cbn.
pose (decl40 := d40).
pose (decl50 := d50).
assert (Ok': translate_fun_decl B protos decl40 = inr decl50) by assumption.
destruct d40 as (fn_name, arity40, body40).
cbn in Ok.
remember (translate_block true B protos body40 0) as body. symmetry in Heqbody.
destruct body as [|(body50)]. { discriminate. } (* body50 is executed after the var decls *)
inversion Ok. subst d50. clear Ok.
remember interpret_block_metered as do_block40.  (* saving from cbn *)
remember L50.Stmt.interpret_block as do_block50.
remember LocalVars.get_vars_by_typenames as get_output.
cbn.

remember (LocalVars.bind_vars_to_values (make_input_typenames arity40)
            (List.map (fun x : uint256 => existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x))
                arg_values) Map.empty) as loc_with_args.
assert (ViaBindArgs: let _ := string_map_impl in
                     loc_with_args = bind_args arg_values arity40 0 Map.empty)
  by easy.
cbn in ViaBindArgs.
assert (BA := bind_args_ok arg_values nil arity40 _ args_agree_nil).
cbn in BA.
repeat rewrite<- ViaBindArgs in BA.
remember (Datatypes.length arg_values ?= N.to_nat arity40) as cmp. symmetry in Heqcmp.
destruct cmp.
2:{
  apply nat_compare_Lt_lt in Heqcmp.
  assert (NE: Datatypes.length arg_values =? N.to_nat arity40 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite NE. rewrite BA. cbn.
  replace (match N.to_nat arity40 with
           | 0 => false
           | S m' => Datatypes.length arg_values <=? m'
           end) with (Datatypes.length arg_values <? N.to_nat arity40) by easy.
  rewrite (proj2 (Nat.ltb_lt _ _) Heqcmp).
  easy.
}
2:{
  apply nat_compare_Gt_gt in Heqcmp. apply gt_not_le in Heqcmp. apply not_le in Heqcmp.
  assert (NE: Datatypes.length arg_values =? N.to_nat arity40 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite NE. rewrite BA. cbn.
  replace (match N.to_nat arity40 with
           | 0 => false
           | S m' => Datatypes.length arg_values <=? m'
           end) with (Datatypes.length arg_values <? N.to_nat arity40) by easy.
  assert (Q: Datatypes.length arg_values <? N.to_nat arity40 = false) by (rewrite Nat.ltb_ge; lia).
  now rewrite Q.
}
apply Nat.compare_eq in Heqcmp.
rewrite (proj2 (Nat.eqb_eq _ _) Heqcmp).
destruct loc_with_args as [|loc_with_args]; try contradiction.

assert (ResultUndeclared: map_lookup loc_with_args "$$result" = None).
{
  destruct BA as (OV, _).
  assert (OVR := OV "$$result"%string).
  destruct (map_lookup loc_with_args "$$result"). 2:{ trivial. }
  assert (D: Some d <> None) by discriminate.
  destruct (OVR D) as (k, X).
  discriminate.
}
rewrite ResultUndeclared.
subst do_block50.
rewrite L50.Stmt.interpret_stmt_list_ok.
rewrite L50.Stmt.interpret_stmt_list_unbind_later.
rewrite L50.Stmt.interpret_stmt_list_no_unbind_app.

assert (AInit := args_and_zeros_agree_init _ _ BA _ (N.le_refl _)).
assert (Arity40Ok: arity40 = N.of_nat (Datatypes.length arg_values)) by lia.
rewrite<- Arity40Ok in AInit.
rewrite (interpret_generated_var_decls max_loop_iterations builtins50 decls50
                                       _ _ _ _ (AST.var_cap_block body40) Arity40Ok AInit _ world).

(* variable declarations done, now there's the post-body assignment that we need to separate *)
assert (NoVars50: L50.Stmt.stmt_list_has_top_level_var_decls body50 = false)
  by apply (translated_block_declares_nothing Heqbody).
assert (NoVarsAssign:
  Stmt.stmt_list_has_top_level_var_decls
    (AST.Assign ("$$result"%string :: nil) (AST.Const U256 (yul_uint256 zero256)) :: nil) = false)
  by easy.
rewrite L50.Stmt.interpret_stmt_list_no_vars_bind.
2:{
  rewrite L50.Stmt.stmt_list_has_top_level_var_decls_app.
  now rewrite NoVars50.
}
rewrite L50.Stmt.interpret_stmt_list_app; try assumption.

(* now we'll look into the variables in pre-body state *)
assert (PreLocAZ := bind_zeros_for_loc_with_args arg_values loc_with_args BA (AST.var_cap_block body40)).
replace (N.to_nat (AST.var_cap_block body40) - Datatypes.length arg_values)
  with (N.to_nat (AST.var_cap_block body40 - arity40))
  in PreLocAZ by lia.
rewrite<- Arity40Ok in PreLocAZ.
remember (bind_zeros
           (map_insert loc_with_args "$$result"
              (existT (fun t : yul_type => yul_value t) U256 (int_zero_value I256 false))) arity40
           (N.to_nat (AST.var_cap_block body40 - arity40)))
  as pre_loc50.
clear Heqpre_loc50. (* PreLocAZ should contain everything we need *)

assert (PreLVA: let _ := memory_impl in
                LocalVarsAgree (OpenArray.from_list arg_values) pre_loc50 (AST.var_cap_block body40)).
{
  cbn. intros k L. rewrite OpenArray.from_list_ok.
  rewrite ((proj2 (proj2 PreLocAZ)) k).
  unfold lookup_in_init_loc.
  replace (k <? N.max (AST.var_cap_block body40) (N.of_nat (Datatypes.length arg_values)))%N
    with true
    by (symmetry; apply N.ltb_lt; lia).
  easy.
}
assert (PreSV: SecondaryVarsOk nil pre_loc50).
{
  split.
  { now rewrite (proj1 (proj2 PreLocAZ)). }
  { intros k L. cbn in L. lia. }
  { intros k L. cbn in L. lia. }
  {
    intros k _.
    assert (P := proj1 PreLocAZ (make_var_name "offset" (N.of_nat k))).
    destruct (map_lookup pre_loc50 (make_var_name "offset" (N.of_nat k))) as [m|]. 2:trivial.
    assert (M: Some m <> None) by discriminate.
    now destruct (P M) as [R|(v, V)].
  }
  intros k _.
  assert (P := proj1 PreLocAZ (make_var_name "cursor" (N.of_nat k))).
  destruct (map_lookup pre_loc50 (make_var_name "cursor" (N.of_nat k))) as [m|]. 2:trivial.
  assert (M: Some m <> None) by discriminate.
  now destruct (P M) as [R|(v, V)].
}

(* finally it's interpret_translated_block time *)
subst do_block40.
remember (interpret_block_metered decls40 (interpret_call_metered max_call_depth decls40 builtins40)
              builtins40 world (OpenArray.from_list arg_values) nil body40) as output40.
remember (Stmt.interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50)
          _
          (Call.interpret_call max_call_depth max_loop_iterations builtins50 (map_lookup decls50)) world
          pre_loc50 body50) as output50.

assert (BodyOk:
  let '(w, l, result) := output50 in
  StmtResultsAgree
    output40
    (w, l, result)
    (AST.var_cap_block body40)
   /\
  SecondaryVarsOk nil l).
{
  subst output40 output50.
  assert (this_fun40 := L40.AST.FunDecl fn_name arity40 body40).

  assert (LoopDepthOk: @List.length L40.Expr.loop_ctx nil = N.to_nat 0%N) by easy.
  refine (interpret_translated_block
                  decls40 decls50 (Some decl40) (Some decl50) Ok' DeclsOk
    (* call40: *) (interpret_call_metered max_call_depth decls40 builtins40)
    (* call50: *) (fun m => L50.Call.interpret_call max_call_depth m builtins50 (map_lookup decls50))
    (* CallsOk *) _
                  builtins40 builtins50 BuiltinsOk BuiltinsBasics BuiltinsSafe BuiltinsHaveArith
                  ProtosOk KnownProtosOk world (OpenArray.from_list arg_values) pre_loc50
                  nil LoopDepthOk PreSV body40 body50 Heqbody
                  (L40.AST.var_cap_block body40) (N.le_refl _)
                  PreLVA EnoughIterationsForEverything EnoughIterations).
  intros max_loop_iterations' d40' d50' dOk' world' args' arity50 Arity50Ok.
  subst arity50.
  apply (IHmax_call_depth max_loop_iterations' d40' d50' dOk' world' args').
}
clear Heqoutput40 Heqoutput50.
destruct output40 as ((w40, l40), r40).
destruct output50 as ((w50, l50), r50).
destruct r40 as [r40|], r50 as [r50|]; cbn in BodyOk; try easy.
simpl.
destruct BodyOk as ((PostLVA, Agreement), PostSV).
assert (RD := sv_result_declared PostSV).
destruct (map_lookup l50 "$$result") as [(result_type, _)|]. 2:contradiction.
destruct (yul_type_eq_dec result_type U256) as [|NE].
2:{
  destruct result_type; try contradiction.
  destruct size; try contradiction.
  destruct signed; contradiction.
}
(* undoing all the local declarations can't undeclare $$result *)
assert (GetOutput: forall (indices: list N),
  get_output ((U256, "$$result"%string) :: nil)%list
      (LocalVars.unbind_vars
         (List.map (fun k : N => (U256, make_var_name "var" k)) indices)
         (map_insert l50 "$$result"
            (existT _ U256 (yul_uint256 zero256))))
   =
  inr ((existT _ U256 (yul_uint256 zero256)) :: nil)%list).
{
  intro indices.
  remember (map_insert l50 "$$result"
             (existT _ U256 (yul_uint256 zero256))) as m.
  assert (M: map_lookup m "$$result"
              =
             Some (existT _ U256 (yul_uint256 zero256))).
  { subst. unfold map_lookup. unfold map_insert. rewrite Map.insert_ok. now destruct string_dec. }
  clear Heqm.
  subst get_output.
  unfold LocalVars.get_vars_by_typenames.
  enough (L: map_lookup
               (LocalVars.unbind_vars (List.map (fun k : N => (U256, make_var_name "var" k)) indices) m)
               "$$result"
              =
             Some (existT _ U256 (yul_uint256 zero256))).
  { now rewrite L. }
  unfold map_lookup in *.
  revert m M. induction indices; intros. { easy. }
  simpl.
  apply IHindices.
  unfold map_remove.
  rewrite Map.remove_ok.
  destruct string_dec. { discriminate. }
  exact M.
}
destruct r40 as [|ab40|x40], r50 as [|ab50|x50]; try easy; try rewrite GetOutput;
  try destruct ab40; try destruct ab50; subst; try easy.
(* success on both sides *)
split. { tauto. }
now rewrite (proj2 Agreement).
Qed.

Lemma translate_ok {C: VyperConfig}
                   (max_call_depth: nat)
                   (max_loop_iterations: nat)

                   {B: builtin_names_config}
                   (builtins40: string -> option L10.Base.builtin)
                   (builtins50: string -> option L50.Builtins.yul_builtin)
                   (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
                   (BuiltinsBasics: BuiltinsSupportBasics builtins50)
                   (BuiltinsSafe: forall x,
                                    builtins50 ("$" ++ x)%string = None)
                   (BuiltinsHaveArith: BuiltinsSupportUInt256 B builtins40)
                   {protos: string_map proto}
                   (KnownProtosOk: check_known_protos B (map_lookup protos) = true)
                   (ProtosOk: ProtosAgree (map_lookup protos) builtins50)
                   {decls40: string_map L40.AST.decl}
                   {decls50: string_map L50.AST.fun_decl}
                   (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)

                   (EnoughIterationsForEverything:
                      (L40.AST.max_loop_count_decl_map decls40 < N.of_nat max_loop_iterations)%N)

                   (fun_name: string)
                   (world: world_state)
                   (arg_values: list uint256):
  ResultsAgree
    (L40Metered.Interpret.interpret_metered max_call_depth decls40 builtins40
                                            fun_name world arg_values)
    (L50.Call.interpret max_call_depth max_loop_iterations builtins50
                        (map_lookup decls50)
                        ("$" ++ fun_name) world
                        (List.map (fun x => (existT _ U256 (yul_uint256 x))) arg_values))
    1%N.
Proof.
unfold L40Metered.Interpret.interpret_metered.
unfold L50.Call.interpret.
assert (T := translate_fun_decls_ok DeclsOk fun_name).
remember (map_lookup decls40 fun_name) as maybe_d40.
destruct maybe_d40 as [d40|], (map_lookup decls50 ("$" ++ fun_name)) as [d50|];
  try easy.
assert (EnoughIters := L40.AST.enough_iterations_for_decl (eq_sym Heqmaybe_d40)
                                                          EnoughIterationsForEverything).
apply (interpret_translated_call _ _ _ _ BuiltinsOk BuiltinsBasics BuiltinsSafe BuiltinsHaveArith
                                 KnownProtosOk ProtosOk DeclsOk
                                 d40 d50 T
                                 EnoughIterationsForEverything EnoughIters).
Qed.
