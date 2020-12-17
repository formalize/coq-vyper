From Coq Require Import String ZArith NArith Eqdep_dec List Lia.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L20.AST L20.Expr L30.AST L20.Interpret L30.Interpret.

From Vyper.From20To30 Require Import Translate Callset FunCtx Expr Stmt.

Lemma nodup_app {A: Type} (EqDec: forall x y: A, {x = y} + {x <> y})
                {a b: list A}
                (NA: NoDup a)
                (NB: NoDup b)
                (Disjoint: forall x,
                             (ListSet.set_mem EqDec x a && ListSet.set_mem EqDec x b = false)%bool):
  NoDup (a ++ b).
Proof.
induction a as [|ha]. { apply NB. }
cbn. constructor.
{ (* ~ In ha (a ++ b) *)
  rewrite in_app_iff.
  intro H. case H; clear H; intro H.
  { now inversion NA. }
  assert (Q := Disjoint ha).
  cbn in Q. destruct EqDec. 2:tauto.
  rewrite Bool.andb_true_l in Q.
  now rewrite ListSet2.set_mem_false in Q.
}
apply IHa. { now inversion NA. }
intro x.
assert (U := Disjoint x).
cbn in U.
destruct EqDec. 2:assumption.
now destruct (ListSet.set_mem EqDec x a).
Qed.

Lemma nodup_app_elim_r {A: Type} (EqDec: forall x y: A, {x = y} + {x <> y})
                       {a b: list A}
                       (H: NoDup (a ++ b)):
  NoDup b.
Proof.
induction a as [|ha]. { apply H. }
cbn in H. apply IHa. inversion H. assumption.
Qed.

Lemma nodup_disjoint {A: Type} (EqDec: forall x y: A, {x = y} + {x <> y})
                     {a b: list A}
                     (H: NoDup (a ++ b))
                     (x: A):
  (ListSet.set_mem EqDec x a && ListSet.set_mem EqDec x b = false)%bool.
Proof.
induction a as [|ha]. { easy. }
cbn.
destruct (EqDec x ha). 2:{ inversion H. tauto. }
subst x.
rewrite Bool.andb_true_l.
rewrite ListSet2.set_mem_false.
cbn in H.
assert (W: ~ In ha (a ++ b)) by now inversion H.
rewrite in_app_iff in W. tauto.
Qed.

Lemma alist_set_mem {A B: Type} (EqDec: forall x y: A, {x = y} + {x <> y})
                    (x: A) (alist: list (A * B)):
  ListSet.set_mem EqDec x (map fst alist)
   =
  match Map.alist_lookup EqDec alist x with
  | Some _ => true
  | None => false
  end.
Proof.
induction alist. { easy. }
cbn. rewrite IHalist.
destruct a as (k, v). cbn.
now destruct (EqDec x k).
Qed.

Lemma varmap_if_nodup {C: VyperConfig}
                      (names: list string)
                      (ND: NoDup names)
                      (err: string):
  make_varmap names <> inl err.
Proof.
unfold make_varmap.
pose (empty  := @Map.empty  string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (items  := @Map.items  string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (insert := @Map.insert string string_dec N (@string_map C N) (@string_map_impl C N)).
fold empty.
assert (ND': NoDup (map fst (items empty) ++ names)).
{ unfold empty. unfold items. rewrite Map.empty_items. cbn. exact ND. }
enough (H: forall m n,
             NoDup (map fst (items m) ++ names)
              ->
             make_varmap_rec m n names <> inl err).
{ apply H. apply ND'. }
clear ND ND'.
induction names; intros m n H. { easy. }
cbn.
rewrite Map.items_ok.
destruct (NoDup_remove _ _ _ H) as (H', NotIn).
rewrite in_app_iff in NotIn.
rewrite Map.alist_lookup_not_in by tauto.
apply IHnames.
(* goal: NoDup (map fst (items (Map.insert m a n)) ++ names) *)
apply (nodup_app string_dec).
{ apply Map.items_nodup. }
{ apply (nodup_app_elim_r string_dec H'). }
(* disjoint *)
intro x.
assert (D := nodup_disjoint string_dec H x).
cbn in D.
assert (F: ListSet.set_mem string_dec x (map fst (items (insert m a n)))
            =
           if string_dec x a then true else ListSet.set_mem string_dec x (map fst (items m))).
{
  repeat rewrite alist_set_mem. unfold items. repeat rewrite<- Map.items_ok.
  unfold insert. rewrite Map.insert_ok.
  destruct (string_dec a x), (string_dec x a); now subst.
}
fold insert. rewrite F. clear F.
destruct (ListSet.set_mem string_dec x (map fst (items m))), (string_dec x a); try easy.
rewrite Bool.andb_true_l.
rewrite ListSet2.set_mem_false.
subst x. tauto.
Qed.

Lemma varmap_rec_not_in {C: VyperConfig}
                        (a: string)
                        (names: list string)
                        (m: string_map N)
                        (init: N)
                        (L: let _ := string_map_impl in Map.lookup m a <> None)
                        (Ok: forall err, make_varmap_rec m init names <> inl err):
  ~ In a names.
Proof.
pose (insert := @Map.insert string string_dec N (@string_map C N) (@string_map_impl C N)).
revert m init L Ok. induction names as [|head]; intros. { easy. }
cbn in *.
remember (Map.lookup m head) as m_head. destruct m_head.
{ exfalso. exact (Ok _ eq_refl). }
assert (NE: head <> a).
{ intro. subst. rewrite<- Heqm_head in L. tauto. }
enough (~ In a names) by tauto.
apply (IHnames (insert m head init) (N.succ init)).
2: apply Ok.
unfold insert.
rewrite Map.insert_ok.
now destruct (string_dec head a).
Qed.

Lemma varmap_rec_cons {C: VyperConfig}
                      (head: string)
                      (tail: list string)
                      (m: string_map N)
                      (init: N)
                      (Ok: forall err, make_varmap_rec m init (head :: tail) <> inl err):
  ~ In head tail.
Proof.
cbn in Ok.
destruct (Map.lookup m head). { exfalso. exact (Ok _ eq_refl). }
refine (varmap_rec_not_in head tail _ _ _ Ok).
cbn. rewrite Map.insert_ok.
now destruct (string_dec head head).
Qed.

(** If [make_varmap names] finished successfully, then there's no duplicates in [names]. *)
Lemma varmap_nodup {C: VyperConfig}
                   (names: list string)
                   (Ok: forall err, make_varmap names <> inl err):
  NoDup names.
Proof.
unfold make_varmap in Ok.
pose (empty  := @Map.empty  string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (items  := @Map.items  string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (insert := @Map.insert string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (lookup := @Map.lookup string string_dec N (@string_map C N) (@string_map_impl C N)).
fold empty in Ok.
enough (H: forall (m: string_map N)
               (init: N)
               (Disjoint: forall x,
                            match lookup m x with
                            | Some _ => ~ In x names
                            | None => True
                            end)
               (Success: forall err, make_varmap_rec m init names <> inl err),
            NoDup names).
{
  apply (H empty 0%N); try assumption.
  unfold lookup. unfold empty. intro x. now rewrite Map.empty_lookup.
}
clear Ok.
induction names. { constructor. }
intros.
assert (V := varmap_rec_cons a names m init Success).
cbn in Success.
remember (Map.lookup m a) as ma.
destruct ma. { exfalso. exact (Success "duplicate argument name"%string eq_refl). }
constructor. { exact V. }
refine (IHnames (insert m a init) (N.succ init) _ Success).
intro x.
unfold lookup in *. unfold insert. rewrite Map.insert_ok.
cbn in Disjoint. assert (Dx := Disjoint x).
destruct (string_dec a x). { now subst. }
destruct (Map.lookup m x); tauto.
Qed.


(** Given that [names] and [values] have the same length and there is no duplication in [names],
    [bind_args] computes successfully and returns a map that is only defined on strings from [names].
 *)
Lemma bind_args_domain_if_nodup {C: VyperConfig}
                                (names: list string)
                                (values: list uint256)
                                (SameLen: length names = length values)
                                (ND: NoDup names):
  let _ := string_map_impl in
  match L10.Interpret.bind_args names values with
  | inl err => False
  | inr m => forall x,
               match Map.lookup m x with
               | None => ~ In x names
               | Some _ => In x names
               end
  end.
Proof.
revert values SameLen. induction names, values; try easy.
{ cbn. intro H. clear H. intro x. now rewrite Map.empty_lookup. }
cbn. intro SameLen'.
assert (L: length names = length values) by now inversion SameLen'. clear SameLen'.
assert (ND_names: NoDup names) by now inversion ND.
assert (IH := IHnames ND_names values L).
destruct (Interpret.bind_args names values). { exact IH. }
assert (A := IH a). destruct (Map.lookup s a). { now inversion ND. }
intro x.
assert (X := IH x). rewrite Map.insert_ok.
destruct (string_dec a x). { now left. }
destruct Map.lookup; tauto.
Qed.

(** This is a variant of [bind_args_domain_if_nodup] but it directly assumes
    successful completion of [bind_args] instead of preconditions. *)
Lemma bind_args_domain {C: VyperConfig}
                   (names: list string)
                   (values: list uint256)
                   (loc: string_map uint256)
                   (Ok: L10.Interpret.bind_args names values = inr loc):
  let _ := string_map_impl in
     forall x,
       match Map.lookup loc x with
       | None => ~ In x names
       | Some _ => In x names
       end.
Proof.
revert values loc Ok. induction names as [|head_name], values as [|head_value]; try easy; intros.
{ cbn in *. inversion Ok. subst. now rewrite Map.empty_lookup. }
cbn in *.
remember (Interpret.bind_args names values) as loc'. destruct loc' as [|loc']. { discriminate. }
assert (IH := IHnames _ _ (eq_sym Heqloc') x).
destruct (Map.lookup loc' head_name). { discriminate. }
inversion Ok. subst. rewrite Map.insert_ok.
destruct (string_dec head_name x).
{ subst. left. trivial. }
destruct (Map.lookup loc' x); tauto.
Qed.

Lemma bind_args_lt {C: VyperConfig}
                   (names: list string)
                   (values: list uint256)
                   (L: length names < length values)
                   (ND: NoDup names):
   L10.Interpret.bind_args names values = inl "function called with too many arguments"%string.
Proof.
revert values L. induction names, values; intros; try easy.
cbn.
assert (ND': NoDup names) by now inversion ND.
cbn in L. apply lt_S_n in L.
now rewrite (IHnames ND' values L).
Qed.

Lemma bind_args_gt {C: VyperConfig}
                   (names: list string)
                   (values: list uint256)
                   (G: length values < length names)
                   (ND: NoDup names):
   L10.Interpret.bind_args names values = inl "function called with too few arguments"%string.
Proof.
revert values G. induction names, values; intros; try easy.
cbn.
assert (ND': NoDup names) by now inversion ND.
cbn in G. apply gt_S_n in G.
now rewrite (IHnames ND' values G).
Qed.

Lemma bind_args_nodup {C: VyperConfig}
                      (names: list string)
                      (values: list uint256)
                      (loc: string_map uint256)
                      (Ok: L10.Interpret.bind_args names values = inr loc):
  NoDup names.
Proof.
revert values loc Ok. induction names as [|head_name], values as [|head_value]; intros; try easy.
{ constructor. }
cbn in Ok.
remember (Interpret.bind_args names values) as loc'. destruct loc' as [|loc']; try discriminate.
remember (Map.lookup loc' head_name) as loc'_head. destruct loc'_head; try discriminate.
constructor.
{
  assert (D := bind_args_domain _ _ _ (eq_sym Heqloc') head_name).
  now rewrite<- Heqloc'_head in D.
}
exact (IHnames values loc' (eq_sym Heqloc')).
Qed.

Lemma bind_args_same_len {C: VyperConfig}
                         (names: list string)
                         (values: list uint256)
                         (loc: string_map uint256)
                         (Ok: L10.Interpret.bind_args names values = inr loc):
  length names = length values.
Proof.
assert (T := Nat.lt_trichotomy (length names) (length values)).
case T; clear T; intro T.
{
  rewrite bind_args_lt in Ok. { discriminate. } { assumption. }
  apply (bind_args_nodup _ _ _ Ok).
}
case T; clear T; intro T. { assumption. }
rewrite bind_args_gt in Ok. { discriminate. } { assumption. }
apply (bind_args_nodup _ _ _ Ok).
Qed.

Lemma varmap_rec_ok {C: VyperConfig}
                    (names: list string)
                    (varmap: string_map N)
                    (m: string_map N)
                    (init: N)
                    (Bound: VarsBound m init)
                    (Inj: VarmapInj m)
                    (Ok: make_varmap_rec m init names = inr varmap):
  VarmapInj varmap /\ VarsBound varmap (init + N.of_nat (length names))%N.
Proof.
pose (empty  := @Map.empty  string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (insert := @Map.insert string string_dec N (@string_map C N) (@string_map_impl C N)).
pose (lookup := @Map.lookup string string_dec N (@string_map C N) (@string_map_impl C N)).
revert m init Bound Inj Ok. induction names; cbn; intros.
{
  assert (m = varmap) by now inversion Ok.
  subst varmap. rewrite N.add_0_r. tauto.
}
remember (Map.lookup m a) as ma. destruct ma. { discriminate. }
replace (init + N.pos (Pos.of_succ_nat (Datatypes.length names)))%N
   with (N.succ init + N.of_nat (Datatypes.length names))%N by lia.
refine (IHnames (insert m a init) (N.succ init) _ _ Ok).
{
  (* VarsBound (insert m a init) (N.succ init) *)
  intro x.
  unfold insert. rewrite Map.insert_ok.
  assert (B := Bound x).
  destruct (string_dec a x). { apply N.lt_succ_diag_r. }
  destruct (Map.lookup m x) as [k|]. 2:trivial.
  lia.
}
intros x y.
unfold insert. repeat rewrite Map.insert_ok.
destruct (string_dec a x).
{
  destruct (string_dec a y). { now subst. }
  assert (B := Bound y).
  destruct (Map.lookup m y) as [k|]. 2:trivial.
  intro H. lia.
}
destruct (string_dec a y).
{
  assert (B := Bound x).
  destruct (Map.lookup m x) as [k|]. 2:trivial.
  intro H. lia.
}
apply Inj.
Qed.

Lemma varmap_ok {C: VyperConfig}
                (names: list string)
                (varmap: string_map N)
                (Ok: make_varmap names = inr varmap):
  VarmapInj varmap /\ VarsBound varmap (N.of_nat (length names))%N.
Proof.
unfold make_varmap in *.
pose (empty  := @Map.empty  string string_dec N (@string_map C N) (@string_map_impl C N)).
assert (R := varmap_rec_ok names varmap empty 0%N).
cbn in R. apply R.
{ (* VarsBound empty 0 *) intro x. unfold empty. now rewrite Map.empty_lookup. }
{ (* VarmapInj empty *) intros x y. unfold empty. now rewrite Map.empty_lookup. }
apply Ok.
Qed.

Lemma varmap_rec_mono {C: VyperConfig}
                      (names: list string)
                      (m varmap: string_map N)
                      (init: N)
                      (VarmapOk: make_varmap_rec m init names = inr varmap)
                      (x: string):
  let _ := string_map_impl in
  match Map.lookup m x with
  | Some y => Map.lookup varmap x = Some y
  | None => True
  end.
Proof.
revert m init VarmapOk.
induction names as [|head]; intros; cbn in *.
{ inversion VarmapOk. subst varmap. now destruct Map.lookup. }
remember (Map.lookup m head) as m_head. destruct m_head. { discriminate. }
assert (IH := IHnames _ _ VarmapOk).
rewrite Map.insert_ok in IH.
destruct (string_dec head x).
{ subst. now destruct (Map.lookup m x). }
apply IH.
Qed.

Local Lemma varmap_rec_index {C: VyperConfig}
                             (names: list string)
                             (m varmap: string_map N)
                             (init: N)
                             (VarmapOk: make_varmap_rec m init names = inr varmap)
                             (x: string):
  let _ := string_map_impl in
  match Map.lookup m x, Map.lookup varmap x with
  | None, Some index => (init <= index)%N /\ nth_error names (N.to_nat (index - init)%N) = Some x
  | _, _ => ~ In x names
  end.
Proof.
revert m varmap init VarmapOk x. induction names as [|head]; intros; cbn in *.
{
  inversion VarmapOk; subst varmap.
  now destruct (Map.lookup m x).
}
remember (Map.lookup m head) as m_head. destruct m_head. { discriminate. }
assert (IH := IHnames _ _ _ VarmapOk x).
rewrite Map.insert_ok in IH.
destruct (string_dec head x).
{
  subst head.
  destruct (Map.lookup m x). { discriminate. }
  assert (V := varmap_rec_mono _ _ _ _ VarmapOk x).
  cbn in V. rewrite Map.insert_ok in V.
  destruct (string_dec x x). 2:tauto.
  destruct (Map.lookup varmap x). 2:discriminate.
  inversion V. subst.
  rewrite N.sub_diag.
  split. { lia. }
  trivial.
}
destruct (Map.lookup m x). { tauto. }
destruct (Map.lookup varmap x) as [k|]. 2:tauto.
remember (N.to_nat (k - N.succ init)) as a.
remember (N.to_nat (k - init)) as b.
destruct IH as (Bound, E).
assert (B: b = S a) by lia.
rewrite B.
cbn.
split. 2:assumption.
lia.
Qed.

Lemma varmap_index {C: VyperConfig}
                   (names: list string)
                   (varmap: string_map N)
                   (VarmapOk: make_varmap names = inr varmap)
                   (x: string):
  let _ := string_map_impl in
  match Map.lookup varmap x with
  | Some index => nth_error names (N.to_nat index) = Some x
  | None => ~ In x names
  end.
Proof.
unfold make_varmap in VarmapOk.
cbn.
assert (R := varmap_rec_index _ _ _ _ VarmapOk x). cbn in R.
rewrite Map.empty_lookup in R.
destruct (Map.lookup varmap x). 2:tauto.
rewrite N.sub_0_r in R.
tauto.
Qed.

Lemma bind_args_index {C: VyperConfig}
                      (names: list string)
                      (values: list uint256)
                      (loc: string_map uint256)
                      (LocOk: L10.Interpret.bind_args names values = inr loc)
                      (index: nat)
                      (x: string)
                      (Ok: nth_error names index = Some x):
  let _ := string_map_impl in
  Map.lookup loc x = nth_error values index.
Proof.
cbn. revert index values loc LocOk Ok.
induction names as [|head_name], values as [|head_value]; intros; try easy.
{
  assert (Oops: index < @length string nil).
  { apply nth_error_Some. intro H. rewrite H in Ok. discriminate. }
  cbn in Oops.
  now apply Nat.nlt_0_r in Oops.
}
assert (F := bind_args_nodup _ _ _ LocOk).
cbn in LocOk.
remember (Interpret.bind_args names values) as loc'.
destruct loc' as [|loc']. { discriminate. }
remember (Map.lookup loc' head_name) as loc'_head. destruct loc'_head. { discriminate. }
symmetry in Heqloc'.
inversion LocOk. subst.
rewrite Map.insert_ok.
destruct index as [|index'].
{
  cbn in *. inversion Ok. subst.
  destruct (string_dec x x); tauto.
}
cbn in *.
rewrite<- (IHnames _ _ _ Heqloc' Ok).
destruct (string_dec head_name x). 2:trivial.
subst.
apply nth_error_In in Ok.
inversion F. contradiction.
Qed.

Lemma bind_varmap_agree {C: VyperConfig}
                        (names: list string)
                        (values: list uint256)
                        (varmap: string_map N)
                        (loc: string_map uint256)
                        (VarmapOk: make_varmap names = inr varmap)
                        (LocOk: L10.Interpret.bind_args names values = inr loc):
  let _ := memory_impl in
  VarsAgree varmap loc (OpenArray.from_list values).
Proof.
cbn. intro x.
assert (V := varmap_index _ _ VarmapOk x). cbn in V.
assert (D := bind_args_domain _ _ _ LocOk x).
remember (Map.lookup varmap x) as varmap_x.
destruct varmap_x. 2:now destruct (Map.lookup loc x).
rewrite OpenArray.from_list_ok.
assert (W := bind_args_index _ _ _ LocOk _ _ V). cbn in W.
rewrite W in *.
assert (L := bind_args_same_len _ _ _ LocOk).
assert (BN: N.to_nat n < length names).
{ apply nth_error_Some. rewrite V. discriminate. }
assert (BV: N.to_nat n < length values). { rewrite<- L. apply BN. }
remember (nth_error values (N.to_nat n)) as z. symmetry in Heqz. destruct z.
2:{ apply nth_error_Some in BV. contradiction. }
apply nth_error_nth with (d := uint256_of_Z 0) in Heqz. exact Heqz.
Qed.

Lemma interpret_translated_call {C: VyperConfig}
                                (builtins: string -> option builtin)
                                {cd20: L20.Descend.calldag}
                                {call_depth_bound: nat}
                                (fc: fun_ctx cd20 call_depth_bound)
                                {cd30: L30.Descend.calldag}
                                (ok: translate_calldag cd20 = inr cd30)
                                (world: world_state)
                                (arg_values: list uint256):
  L30.Interpret.interpret_call builtins (translate_fun_ctx fc ok) world arg_values
   =
  L20.Interpret.interpret_call builtins fc world arg_values.
Proof.
revert world arg_values. induction call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))). }
assert(F: inr (cached_translated_decl fc ok)
           =
          translate_decl (fun_decl fc)).
{
  clear IHcall_depth_bound.
  unfold translate_fun_ctx in *. cbn in *.
  unfold cached_translated_decl in *.
  remember (FunCtx.translate_fun_ctx_fun_decl_helper fc ok) as foo. clear Heqfoo.
  remember (cd_declmap cd30 (fun_name fc)) as d.
  destruct d. 2:{ contradiction. }
  subst.
  assert (Q := translate_fun_ctx_declmap ok (fun_name fc)).
  destruct (cd_declmap cd30 (fun_name fc)) as [d'|]. 2:discriminate.
  inversion Heqd. subst d'. clear Heqd.
  remember (cd_declmap cd20 (fun_name fc)) as x.
  destruct x as [x|]. 2:discriminate.
  inversion Q. f_equal.
  assert (D := fun_decl_ok fc).
  rewrite D in *. inversion Heqx.
  trivial.
}
intros.
cbn.
remember (fun name arity body
              (E: cached_translated_decl fc ok = AST.FunDecl name arity body) =>
          if Datatypes.length arg_values =? N.to_nat arity
          then
           let
           '(world', _, result) :=
            Stmt.interpret_stmt eq_refl (translate_fun_ctx fc ok) (Interpret.interpret_call builtins)
              builtins world (OpenArray.from_list arg_values) body (Interpret.interpret_call_helper E) in
            (world',
            match result with
            | StmtSuccess => ExprSuccess zero256
            | StmtAbort a => ExprAbort a
            | StmtReturnFromFunction x => ExprSuccess x
            end)
          else (world,
     expr_error
       (if match N.to_nat arity with
           | 0 => false
           | S m' => Datatypes.length arg_values <=? m'
           end
        then "function called with too few arguments"%string
        else "function called with too many arguments"%string))) as branch_30.
remember (fun name arg_names body
              (E : fun_decl fc = L20.AST.FunDecl name arg_names body) =>
            match Interpret.bind_args arg_names arg_values with
            | inl err => (world, expr_error err)
            | inr loc =>
                let
                '(world', _, result) :=
                 L20.Stmt.interpret_stmt eq_refl fc (L20.Interpret.interpret_call builtins) builtins world loc
                   body (L20.Interpret.interpret_call_helper E) in
                 (world',
                 match result with
                 | StmtSuccess => ExprSuccess zero256
                 | StmtAbort a => ExprAbort a
                 | StmtReturnFromFunction x => ExprSuccess x
                 end)
            end) as branch_20.
assert (B: forall name arg_names body30 body20 E30 E20,
             branch_30 name (N.of_nat (List.length arg_names)) body30 E30
              =
             branch_20 name arg_names body20 E20).
{
  intros. subst. rewrite Nat2N.id. rewrite E20 in F. rewrite E30 in F. cbn in F.
  remember (make_varmap arg_names) as maybe_varmap.
  destruct maybe_varmap as [err|varmap]. { discriminate. }
  (* argument names have no duplication because translation would have failed *)
  assert (ND: NoDup arg_names).
  { apply varmap_nodup. intro err. rewrite<- Heqmaybe_varmap. discriminate. }

  (* arity check *)
  assert (T := Nat.lt_trichotomy (length arg_names) (length arg_values)).
  case T; clear T; intro T.
  {
    replace (length arg_values =? length arg_names) with false.
    2:{ symmetry. rewrite Nat.eqb_neq. apply Nat.neq_sym. apply Nat.lt_neq. exact T. }
    replace (match length arg_names with
             | 0 => false
             | S m' => length arg_values <=? m'
             end) with (length arg_values <? length arg_names) by trivial.
    replace (length arg_values <? length arg_names) with false.
    2:{ symmetry. rewrite Nat.ltb_ge. apply Nat.lt_le_incl. exact T. }
    now rewrite (bind_args_lt _ _ T ND).
  }
  case T; clear T; intro T.
  2:{
    replace (length arg_values =? length arg_names) with false.
    2:{ symmetry. rewrite Nat.eqb_neq. apply Nat.lt_neq. exact T. }
    replace (match length arg_names with
         | 0 => false
         | S m' => length arg_values <=? m'
         end) with (length arg_values <? length arg_names) by trivial.
    assert (G := T).
    rewrite<- Nat.ltb_lt in T. rewrite T.
    now rewrite (bind_args_gt _ _ G ND).
  }
  assert (SameLen := T).
  symmetry in T. rewrite<- Nat.eqb_eq in T. rewrite T. clear T.

  assert (BindArgsOk := bind_args_domain_if_nodup arg_names arg_values SameLen ND).
  remember (Interpret.bind_args arg_names arg_values) as loc.
  destruct loc as [err|loc]. { contradiction. }
  destruct (varmap_ok arg_names varmap (eq_sym Heqmaybe_varmap)) as (Inj, Bound).
  remember (translate_stmt varmap (N.of_nat (Datatypes.length arg_names)) body20) as body30'.
  destruct body30'. { discriminate. }
  inversion F. subst.
  assert (IS := interpret_translated_stmt eq_refl builtins fc ok
                                          IHcall_depth_bound world loc
                                          (OpenArray.from_list arg_values)
                                          varmap Inj _
                                          (bind_varmap_agree _ _ _ _
                                            (eq_sym Heqmaybe_varmap)
                                            (eq_sym Heqloc))
                                          Bound
                                          (eq_sym Heqbody30')
                                          (L30.Interpret.interpret_call_helper E30)
                                          (L20.Interpret.interpret_call_helper E20)).
  cbn in IS.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Stmt.interpret_stmt as ((world20, loc20), result20).
  destruct IS as (R, (W, Agree)).
  subst.
  trivial.
}
clear Heqbranch_20. clear Heqbranch_30.
destruct (fun_decl fc); cbn in F.
{ (* [fun_decl fc] is a global var *) now destruct cached_translated_decl. }
destruct (make_varmap args). { discriminate. }
destruct (translate_stmt s (N.of_nat (Datatypes.length args)) body). { discriminate. }
inversion F.
destruct (cached_translated_decl fc ok). { discriminate. }
inversion H0 (* XXX *). subst.
apply B.
Qed.

Lemma make_fun_ctx_and_bound_ok {C: VyperConfig}
                                (cd20: L20.Descend.calldag)
                                (cd30: L30.Descend.calldag)
                                (Ok: translate_calldag cd20 = inr cd30)
                                (fun_name: string):
   make_fun_ctx_and_bound cd30 fun_name
    =
   match make_fun_ctx_and_bound cd20 fun_name with
   | Some (existT _ bound fc) => Some (existT _ bound (translate_fun_ctx fc Ok))
   | None => None
   end.
Proof.
(* this is too complicated due to destructing convoys *)
unfold make_fun_ctx_and_bound.
remember (fun d (Ed : cd_declmap cd30 fun_name = Some d) =>
    match
      cd_depthmap cd30 fun_name as depth'
      return (cd_depthmap cd30 fun_name = depth' -> option {bound : nat & fun_ctx cd30 bound})
    with
    | Some depth =>
        fun Edepth : cd_depthmap cd30 fun_name = Some depth =>
        Some
          (existT (fun bound : nat => fun_ctx cd30 bound) (S depth)
             {|
             fun_name := fun_name;
             fun_depth := depth;
             fun_depth_ok := Edepth;
             fun_decl := d;
             fun_decl_ok := Ed;
             fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |})
    | None =>
        fun Edepth : cd_depthmap cd30 fun_name = None =>
        False_rect (option {bound : nat & fun_ctx cd30 bound}) (Calldag.make_fun_ctx_helper Ed Edepth)
    end eq_refl) as lhs_some_branch.
remember (fun d (Ed : cd_declmap cd20 fun_name = Some d) =>
      match
        cd_depthmap cd20 fun_name as depth'
        return (cd_depthmap cd20 fun_name = depth' -> option {bound : nat & fun_ctx cd20 bound})
      with
      | Some depth =>
          fun Edepth : cd_depthmap cd20 fun_name = Some depth =>
          Some
            (existT (fun bound : nat => fun_ctx cd20 bound) (S depth)
               {|
               fun_name := fun_name;
               fun_depth := depth;
               fun_depth_ok := Edepth;
               fun_decl := d;
               fun_decl_ok := Ed;
               fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |})
      | None =>
          fun Edepth : cd_depthmap cd20 fun_name = None =>
          False_rect (option {bound : nat & fun_ctx cd20 bound})
            (Calldag.make_fun_ctx_helper Ed Edepth)
      end eq_refl) as rhs_some_branch.
enough (SomeBranchOk: forall d30 d20 Ed30 Ed20
                             (DeclOk: translate_decl d20 = inr d30),
                        lhs_some_branch d30 Ed30
                         =
                        match rhs_some_branch d20 Ed20 with
                        | Some (existT _ bound fc) =>
                            Some
                              (existT _ bound
                                 (translate_fun_ctx fc Ok))
                        | None => None
                        end).
{
  cbn in *.
  remember (fun _: _ = None => None) as lhs_none_branch.
  assert (NoneBranchOk: forall E, lhs_none_branch E = None).
  { subst. trivial. }
  clear Heqlhs_some_branch Heqrhs_some_branch Heqlhs_none_branch.
  assert (T := translate_fun_ctx_declmap Ok fun_name).
  destruct (cd_declmap cd20 fun_name); destruct (cd_declmap cd30 fun_name);
    try easy.
  apply SomeBranchOk.
  now inversion T.
}
subst. cbn. intros.

(* This is even more messed up than usual because just the implicit arguments weren't enough. *)
remember (fun depth
       (Edepth : @eq (option nat)
                    (@cd_depthmap C (@AST.decl C) (@Callset.decl_callset C) false cd30 fun_name)
                    (@Some nat depth)) =>
       @Some
         (@sigT nat (fun bound : nat => @fun_ctx C (@AST.decl C) (@Callset.decl_callset C) false cd30 bound))
         (@existT nat
            (fun bound : nat => @fun_ctx C (@AST.decl C) (@Callset.decl_callset C) false cd30 bound)
            (S depth)
            _))
  as depth_lhs_some_branch.
remember (fun (depth: nat)
        (Edepth: cd_depthmap cd20 fun_name = Some depth) =>
      Some
        (existT (fun bound : nat => fun_ctx cd20 bound) (S depth)
           _))
  as depth_rhs_some_branch.
enough (A: forall depth E30 E20,
          depth_lhs_some_branch depth E30
           =
          match depth_rhs_some_branch depth E20 with
          | Some (existT _ bound fc) =>
              Some
                (existT (fun bound0 : nat => fun_ctx cd30 bound0) bound
                   (translate_fun_ctx fc Ok))
          | None => None
          end).
{
  clear Heqdepth_lhs_some_branch Heqdepth_rhs_some_branch.
  remember (fun Edepth : cd_depthmap cd30 fun_name = None =>
      False_rect (option {bound : nat & fun_ctx cd30 bound}) (Calldag.make_fun_ctx_helper Ed30 Edepth))
    as lhs_none_branch.
  remember (fun Edepth : cd_depthmap cd20 fun_name = None =>
        False_rect (option {bound : nat & fun_ctx cd20 bound}) (Calldag.make_fun_ctx_helper Ed20 Edepth))
    as rhs_none_branch.
  clear Heqlhs_none_branch Heqrhs_none_branch.
  assert (Guard30 := Calldag.make_fun_ctx_helper Ed30).
  assert (Guard20 := Calldag.make_fun_ctx_helper Ed20).
  assert (T := translate_fun_ctx_depthmap Ok fun_name).
  destruct (cd_depthmap cd30 fun_name), (cd_depthmap cd20 fun_name); try easy.
  inversion T. subst.
  apply A.
}
intros. subst.
f_equal. f_equal.
unfold translate_fun_ctx. cbn.
assert (FunCtxEq: forall name1 depth depth_ok1 decl1 decl_ok1 bound_ok1
                         name2       depth_ok2 decl2 decl_ok2 bound_ok2
                         (Name: name1 = name2)
                         (Decl: decl1 = decl2),
  ({| fun_name := name1
    ; fun_depth := depth
    ; fun_depth_ok := depth_ok1
    ; fun_decl := decl1
    ; fun_decl_ok := decl_ok1
    ; fun_bound_ok := bound_ok1 |}: fun_ctx cd30 (S depth))
   =
  {| fun_name := name2
   ; fun_depth := depth
   ; fun_depth_ok := depth_ok2
   ; fun_decl := decl2
   ; fun_decl_ok := decl_ok2
   ; fun_bound_ok := bound_ok2 |}).
{
  intros. subst.
  assert (depth_ok1 = depth_ok2) by apply PropExtensionality.proof_irrelevance.
  assert (decl_ok1 = decl_ok2) by apply PropExtensionality.proof_irrelevance.
  assert (bound_ok1 = bound_ok2) by apply PropExtensionality.proof_irrelevance.
  subst.
  trivial.
}
apply FunCtxEq. { (* name: *) trivial. }
clear FunCtxEq.
assert (Unsome: forall {T} (x y: T), Some x = Some y -> x = y).
{ intros T x y H. now inversion H. }
apply Unsome.
rewrite<- FunCtx.translate_fun_ctx_decl_ok. cbn. symmetry. exact Ed30.
Qed.

Theorem translate_ok {C: VyperConfig}
                     (builtins: string -> option builtin)
                     (cd20: L20.Descend.calldag)
                     (cd30: L30.Descend.calldag)
                     (Ok: translate_calldag cd20 = inr cd30)
                     (fun_name: string)
                     (world: world_state)
                     (arg_values: list uint256):
  L30.Interpret.interpret builtins cd30 fun_name world arg_values
   =
  L20.Interpret.interpret builtins cd20 fun_name world arg_values.
Proof.
unfold L20.Interpret.interpret. unfold L30.Interpret.interpret.
rewrite (make_fun_ctx_and_bound_ok cd20 cd30 Ok).
destruct (make_fun_ctx_and_bound cd20 fun_name) as [(bound, fc)|]; cbn.
{ apply interpret_translated_call. }
trivial.
Qed.