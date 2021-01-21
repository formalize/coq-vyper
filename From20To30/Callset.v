From Coq Require Import String ZArith Eqdep_dec.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L20.AST L30.AST L20.Callset L30.Callset.

From Vyper.From20To30 Require Import Translate.

Local Ltac rr
:= repeat (rewrite FSet.union_ok
        || rewrite FSet.add_ok
        || rewrite FSet.empty_ok
        || rewrite FSet.singleton_iff
        || rewrite Bool.andb_true_l
        || rewrite Bool.andb_true_r
        || rewrite Bool.andb_false_l
        || rewrite Bool.andb_false_r
        || rewrite Bool.orb_true_l
        || rewrite Bool.orb_true_r
        || rewrite Bool.orb_false_l
        || rewrite Bool.orb_false_r).

(** After translation, the callsets are the same. *)
Lemma callset_translate_expr {C: VyperConfig}
                             (e: L20.AST.expr)
                             (s: L30.AST.stmt)
                             {dst offset: N}
                             {varmap: string_map N}
                             (E: translate_expr varmap dst offset e = inr s)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L30.Callset.stmt_callset s) x
   =
  FSet.has (L20.Callset.expr_callset e) x.
Proof.
revert dst offset s E.
induction e using L20.AST.expr_ind'; intros; cbn in E; inversion E; cbn; trivial.
{ (* SmallStmt *) destruct map_lookup; inversion E; subst. easy. }
{ (* UnOp *)
  assert (IH := IHe dst offset).
  destruct translate_expr. { discriminate. }
  inversion E. subst. cbn. rr. now apply IH.
}
{ (* BinOp *)
  destruct (AST.binop_eq op AST.Pow) as [EQ|NE].
  {
    (* Pow *)
    subst op.
    destruct (try_const e1) as [(base, Ebase)|NEbase].
    { (* base is const *)
      assert (IH := IHe2 dst offset).
      destruct translate_expr. { discriminate. }
      inversion E. subst. cbn. rr. now apply IH.
    }
    destruct (try_const e2) as [(exp, Eexp)|NEexp]. 2:discriminate.
    (* exp is const *)
    assert (IH := IHe1 dst offset).
    destruct translate_expr. { discriminate. }
    inversion E. subst. cbn. rr. now apply IH.
  }
  (* not pow *)
  assert (IH1 := IHe1 dst offset).
  assert (IH2 := IHe2 offset (N.succ offset)).
  remember (translate_expr varmap dst offset e1) as e1'.
  destruct e1'. { discriminate. }
  remember (translate_expr varmap offset (N.succ offset) e2) as e2'.
  destruct e2'. { discriminate. }
  inversion E. subst. cbn. rr.
  rewrite IH1 by trivial. now rewrite IH2.
}
{ (* IfElse *)
  rr.
  remember (translate_expr varmap dst offset e1) as e1'.
  destruct e1'. { discriminate. }
  remember (translate_expr varmap dst offset e2) as e2'.
  destruct e2'. { discriminate. }
  remember (translate_expr varmap dst offset e3) as e3'.
  destruct e3'. { discriminate. }
  inversion E. subst. cbn. rr.
  rewrite (IHe1 dst offset) by apply (eq_sym Heqe1').
  rewrite (IHe2 dst offset) by apply (eq_sym Heqe2').
  rewrite (IHe3 dst offset) by apply (eq_sym Heqe3').
  trivial.
}
{ (* and *)
  rr.
  remember (translate_expr varmap dst offset e1) as e1'.
  destruct e1'. { discriminate. }
  remember (translate_expr varmap dst offset e2) as e2'.
  destruct e2'. { discriminate. }
  inversion E. subst. cbn. rr.
  rewrite (IHe1 dst offset) by apply (eq_sym Heqe1').
  rewrite (IHe2 dst offset) by apply (eq_sym Heqe2').
  trivial.
}
{ (* or *)
  rr.
  remember (translate_expr varmap dst offset e1) as e1'.
  destruct e1'. { discriminate. }
  remember (translate_expr varmap dst offset e2) as e2'.
  destruct e2'. { discriminate. }
  inversion E. subst. cbn. rr.
  rewrite (IHe1 dst offset) by apply (eq_sym Heqe1').
  rewrite (IHe2 dst offset) by apply (eq_sym Heqe2').
  trivial.
}
{ (* PrivateCall *)
  rr.
  remember (_ varmap offset args) as e'. destruct e'. { discriminate. }
  inversion E. subst. clear E. cbn.
  rr.
  match goal with
  |- (?a || (if string_dec name x then true else false))%bool
      =
     if string_dec name x then true else ?b
      =>
     enough (a = b)
  end.
  { destruct (string_dec name x); now rr. }
  (* now we do args *)
  clear H1. (* XXX *)
  revert offset s1 Heqe'.
  induction args as [|h]; intros. { inversion Heqe'. now subst. }
  rr.
  remember (translate_expr varmap offset (N.succ offset) h) as h'.
  destruct h'. { discriminate. }
  remember (_ varmap (N.succ offset) args) as tail. destruct tail. { discriminate. }
  inversion Heqe'. subst. clear Heqe'.
  assert (Hhead := List.Forall_inv H).
  assert (Htail := List.Forall_inv_tail H).
  cbn. rr. f_equal.
  { (* head *) apply (Hhead offset (N.succ offset)). symmetry. exact Heqh'. }
  (* tail *)
  apply IHargs with (offset := N.succ offset). { apply Htail. } apply Heqtail.
}
(* BuiltinCall *)
rr.
remember (_ varmap offset args) as e'. destruct e'. { discriminate. }
inversion E. subst. clear E. cbn.
rr.
(* now we do args *)
clear H1. (* XXX *)
revert offset s1 Heqe'.
induction args as [|h]; intros. { inversion Heqe'. now subst. }
rr.
remember (translate_expr varmap offset (N.succ offset) h) as h'.
destruct h'. { discriminate. }
remember (_ varmap (N.succ offset) args) as tail. destruct tail. { discriminate. }
inversion Heqe'. subst. clear Heqe'.
assert (Hhead := List.Forall_inv H).
assert (Htail := List.Forall_inv_tail H).
cbn. rr. f_equal.
{ (* head *) apply (Hhead offset (N.succ offset)). symmetry. exact Heqh'. }
(* tail *)
apply IHargs with (offset := N.succ offset). { apply Htail. } apply Heqtail.
Qed.

Lemma callset_translate_small_stmt {C: VyperConfig}
                                   (ss: L20.AST.small_stmt)
                                   (s: L30.AST.stmt)
                                   {offset: N}
                                   {varmap: string_map N}
                                   (E: translate_small_stmt varmap offset ss = inr s)
                                   (x: string):
  let _ := string_set_impl in
  FSet.has (L30.Callset.stmt_callset s) x
   =
  FSet.has (L20.Callset.small_stmt_callset ss) x.
Proof.
destruct ss; cbn in *; rr; inversion E; subst; clear E; cbn; rr; trivial.
{ (* return *)
  remember (translate_expr varmap offset (N.succ offset) result) as e'.
  destruct e'. { discriminate. }
  inversion H0. (* XXX *)
  cbn. rr. symmetry in Heqe'.
  apply (callset_translate_expr _ _ Heqe').
}
{ (* raise *)
  remember (translate_expr varmap offset (N.succ offset) error) as e'.
  destruct e'. { discriminate. }
  inversion H0. (* XXX *)
  cbn. rr. symmetry in Heqe'.
  apply (callset_translate_expr _ _ Heqe').
}
{ (* assign *)
  destruct lhs.
  { (* local *)
    destruct (map_lookup varmap name). 2:{ discriminate. }
    remember (translate_expr varmap _ _ rhs) as e'.
    destruct e'. { discriminate. }
    inversion H0. (* XXX *)
    cbn. rr. symmetry in Heqe'. subst.
    apply (callset_translate_expr _ _ Heqe').
  }
  (* storage *)
  remember (translate_expr varmap offset (N.succ offset) rhs) as e'.
  destruct e'. { discriminate. }
  inversion H0. (* XXX *)
  cbn. rr. symmetry in Heqe'. subst.
  apply (callset_translate_expr _ _ Heqe').
}
(* expr *)
remember (translate_expr varmap offset (N.succ offset) e) as e'.
destruct e'. { discriminate. }
inversion H0. (* XXX *)
cbn. rr. symmetry in Heqe'. subst.
apply (callset_translate_expr _ _ Heqe').
Qed.

Lemma callset_translate_stmt {C: VyperConfig}
                             (s20: L20.AST.stmt)
                             (s30: L30.AST.stmt)
                             {offset: N}
                             {varmap: string_map N}
                             (E: translate_stmt varmap offset s20 = inr s30)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L30.Callset.stmt_callset s30) x
   =
  FSet.has (L20.Callset.stmt_callset s20) x.
Proof.
revert s30 offset varmap E. induction s20; intros; cbn in *; rr.
{ (* small *) apply (callset_translate_small_stmt _ _ E). }
{ (* local var decl *)
  destruct (map_lookup varmap name). { discriminate. }
  remember (translate_expr varmap offset (N.succ offset) init) as init'.
  destruct init'. { discriminate. }
  remember (translate_stmt (map_insert varmap name offset) _ s20) as s20'.
  destruct s20'. { discriminate. }
  symmetry in Heqs20'.
  inversion E; subst; clear E.
  cbn. rr. subst s.
  rewrite (IHs20 _ _ _ Heqs20').
  f_equal.
  symmetry in Heqinit'. apply (callset_translate_expr _ _ Heqinit').
}
{ (* if *)
  remember (translate_expr varmap offset (N.succ offset) cond) as cond'.
  destruct cond'. { discriminate. }
  remember (translate_stmt varmap offset s20_1) as s20_1'.
  destruct s20_1'. { discriminate. }
  remember (translate_stmt varmap offset s20_2) as s20_2'.
  destruct s20_2'. { discriminate. }
  inversion E; subst; clear E. 
  cbn. rr. subst s.
  rewrite (IHs20_1 _ _ _ (eq_sym Heqs20_1')).
  rewrite (IHs20_2 _ _ _ (eq_sym Heqs20_2')).
  now rewrite (callset_translate_expr _ _ (eq_sym Heqcond')).
}
{ (* loop *)
  destruct (map_lookup varmap var). { discriminate. }
  destruct (Z_of_uint256 count =? 0)%Z. { discriminate. }
  remember (translate_expr varmap offset (N.succ offset) start) as start'.
  destruct start'. { discriminate. }
  remember (translate_stmt (map_insert varmap var offset) (N.succ offset) s20) as s20'.
  destruct s20'. { discriminate. }
  inversion E; subst; clear E.
  cbn. rr. subst s.
  rewrite (IHs20 _ _ _ (eq_sym Heqs20')).
  now rewrite (callset_translate_expr _ _ (eq_sym Heqstart')).
}
(* semicolon *)
remember (translate_stmt varmap offset s20_1) as s20_1'.
destruct s20_1'. { discriminate. }
remember (translate_stmt varmap offset s20_2) as s20_2'.
destruct s20_2'. { discriminate. }
inversion E; subst; clear E. 
cbn. rr. subst s.
rewrite (IHs20_1 _ _ _ (eq_sym Heqs20_1')).
now rewrite (IHs20_2 _ _ _ (eq_sym Heqs20_2')).
Qed.

Lemma callset_translate_decl {C: VyperConfig}
                             (d20: L20.AST.decl)
                             (d30: L30.AST.decl)
                             (E: translate_decl d20 = inr d30)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L30.Callset.decl_callset d30) x
   =
  FSet.has (L20.Callset.decl_callset d20) x.
Proof.
unfold L30.Callset.decl_callset.
unfold L20.Callset.decl_callset.
destruct d30, d20; cbn in E; try easy.
{ (* function got translated to a variable *)
  destruct make_varmap. { discriminate. }
  destruct translate_stmt. { discriminate. }
  now inversion E.
}
destruct make_varmap as [|varmap]. { discriminate. }
remember (translate_stmt varmap (N.of_nat (Datatypes.length args)) _) as s30.
destruct s30. { discriminate. }
symmetry in Heqs30.
inversion E; subst.
apply (callset_translate_stmt _ _ Heqs30).
Qed.