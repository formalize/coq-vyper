From Coq Require Import String ZArith Eqdep_dec.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L20.AST L10.Interpret L20.Interpret.

From Vyper.From10To20 Require Import Translate.

(** After translation, the callsets get filtered by [is_private_call] predicate. *)
Lemma callset_translate_expr {C: VyperConfig}
                             (is_private_call: string -> bool)
                             (e: L10.AST.expr)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L20.Callset.expr_callset (translate_expr is_private_call e)) x
   =
  (FSet.has (L10.Callset.expr_callset e) x && is_private_call x)%bool.
Proof.
cbn.
induction e using L10.AST.expr_ind'; intros; cbn;
  try repeat rewrite FSet.union_ok;
  try rewrite FSet.empty_ok;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3;
  try repeat rewrite<- Bool.andb_orb_distrib_l;
  try easy.
(* only the PrivateOrBuiltinCall case remains *)
rewrite FSet.add_ok.
remember (is_private_call name) as priv_name. destruct priv_name; cbn.
{
  rewrite FSet.add_ok.
  destruct (string_dec name x). { subst. now rewrite<- Heqpriv_name. }
  induction args. { now rewrite FSet.empty_ok. }
  cbn.
  repeat rewrite FSet.union_ok.
  rewrite (List.Forall_inv H).
  rewrite IHargs by apply (List.Forall_inv_tail H).
  (* clear H IHargs Heqpriv_name n.
  remember (FSet.has (L10.Callset.expr_callset a) x) as p. clear Heqp.
  remember (FSet.has (_ args) x) as q. clear Heqq.
  remember (is_private_call x) as r. clear Heqr. *)
  symmetry.
  apply Bool.andb_orb_distrib_l.
}
(* a builtin call *)
destruct (string_dec name x).
{
  subst. rewrite<- Heqpriv_name. cbn.
  induction args. { apply FSet.empty_ok. }
  rewrite FSet.union_ok.
  rewrite IHargs by apply (List.Forall_inv_tail H).
  rewrite (List.Forall_inv H).
  rewrite<- Heqpriv_name.
  rewrite Bool.andb_false_r.
  trivial.
}
(* name <> x *)
induction args. { now rewrite FSet.empty_ok. }
repeat rewrite FSet.union_ok.
rewrite IHargs by apply (List.Forall_inv_tail H).
rewrite (List.Forall_inv H).
symmetry.
apply Bool.andb_orb_distrib_l.
Qed.

Lemma callset_translate_small_stmt {C: VyperConfig}
                                   (is_private_call: string -> bool)
                                   (ss: L10.AST.small_stmt)
                                   (x: string):
  let _ := string_set_impl in
  FSet.has (L20.Callset.stmt_callset (translate_small_stmt is_private_call ss)) x
   =
  (FSet.has (L10.Callset.small_stmt_callset ss) x && is_private_call x)%bool.
Proof.
destruct ss; cbn;
  repeat rewrite FSet.union_ok;
  try rewrite FSet.empty_ok;
  repeat rewrite callset_translate_expr;
  try easy.
{ (* return *)
  destruct result. { cbn. apply callset_translate_expr. }
  rewrite FSet.empty_ok. cbn. apply FSet.empty_ok.
}
{ (* assert *)
  destruct error.
  {
    rewrite callset_translate_expr. cbn.
    rewrite FSet.union_ok.
    symmetry. apply Bool.andb_orb_distrib_l.
  }
  cbn. rewrite FSet.empty_ok. apply Bool.orb_false_r.
}
(* binop assign *)
destruct lhs; cbn; rewrite FSet.empty_ok; easy.
Qed.

(* The callsets of statement lists behave normally ASSUMING that each statement behaves normally.
   We'll get rid of this assumption later.
 *)
Local Lemma callset_translate_stmt_list_aux {C: VyperConfig}
                                            (is_private_call: string -> bool)
                                            (l: list L10.AST.stmt)
                                            (x: string)
                 (Ok: let _ := string_set_impl in
                      List.Forall
                        (fun s : L10.AST.stmt =>
                          FSet.has (Callset.stmt_callset (translate_stmt is_private_call s)) x
                           =
                         (FSet.has (L10.Callset.stmt_callset s) x && is_private_call x)%bool) 
                        l):
  let _ := string_set_impl in
  FSet.has (L20.Callset.stmt_callset (translate_stmt_list is_private_call l)) x
   =
  (FSet.has (L10.Callset.stmt_list_callset l) x && is_private_call x)%bool.
Proof.
cbn in *. induction l. { cbn. now repeat rewrite FSet.empty_ok. }
cbn. rewrite FSet.union_ok.
assert (Inv := List.Forall_inv Ok).
assert (IH := (IHl (List.Forall_inv_tail Ok))).
assert (SemicolonRewrite:
          forall (a b: L20.AST.stmt),
            L20.Callset.stmt_callset (L20.AST.Semicolon a b)
             =
            let _ := string_set_impl in
            FSet.union (L20.Callset.stmt_callset a) (L20.Callset.stmt_callset b)).
{ easy. }
assert (LocalVarDeclRewrite:
          forall name init body,
            L20.Callset.stmt_callset
             (L20.AST.LocalVarDecl name init body)
             =
            let _ := string_set_impl in
            FSet.union (L20.Callset.expr_callset init)
                       (L20.Callset.stmt_callset body)).
{ easy. }
destruct a, l; try destruct init;
  try rewrite SemicolonRewrite;
  try rewrite LocalVarDeclRewrite;
  try rewrite FSet.union_ok;
  try rewrite callset_translate_expr;
  try rewrite Inv; try rewrite IH;
  try (symmetry; apply Bool.andb_orb_distrib_l);
  try (cbn; rewrite FSet.empty_ok; rewrite Bool.orb_false_r);
  try easy.
(* remaining case: LocalVarDecl without init *)
cbn. now repeat rewrite FSet.empty_ok.
Qed.

Lemma callset_translate_stmt {C: VyperConfig}
                             (is_private_call: string -> bool)
                             (s: L10.AST.stmt)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L20.Callset.stmt_callset (translate_stmt is_private_call s)) x
   =
  (FSet.has (L10.Callset.stmt_callset s) x && is_private_call x)%bool.
Proof.
cbn.
induction s using L10.AST.stmt_ind'; intros; cbn;
  repeat rewrite FSet.union_ok.
{ (* SmallStmt *) apply callset_translate_small_stmt. }
{ (* LocalVarDecl *)
  destruct init; rewrite FSet.empty_ok; rewrite Bool.orb_false_r.
  { apply callset_translate_expr. }
  cbn. apply FSet.empty_ok.
}
{ (* If *)
  assert (OkYes := callset_translate_stmt_list_aux is_private_call yes x H).
  destruct no; repeat rewrite FSet.union_ok; rewrite callset_translate_expr; cbn.
  {
    assert (OkNo := callset_translate_stmt_list_aux is_private_call l x H0).
    unfold translate_stmt_list in OkYes. rewrite OkYes.
    unfold translate_stmt_list in OkNo. rewrite OkNo.
    repeat rewrite Bool.andb_orb_distrib_l.
    trivial.
  }
  unfold translate_stmt_list in OkYes. rewrite OkYes.
  rewrite Bool.andb_orb_distrib_l. rewrite FSet.empty_ok.
  rewrite Bool.orb_false_r.
  trivial.
}
{ (* FixedRangeLoop *)
  assert (OkBody := callset_translate_stmt_list_aux is_private_call body x H).
  unfold translate_stmt_list in OkBody. rewrite OkBody.
  rewrite FSet.empty_ok. rewrite Bool.orb_false_l.
  trivial.
}
(* FixedCountLoop *)
assert (OkBody := callset_translate_stmt_list_aux is_private_call body x H).
unfold translate_stmt_list in OkBody. rewrite OkBody.
rewrite Bool.andb_orb_distrib_l.
now rewrite callset_translate_expr.
Qed.

Lemma callset_translate_stmt_list {C: VyperConfig}
                                  (is_private_call: string -> bool)
                                  (l: list L10.AST.stmt)
                                  (x: string):
  let _ := string_set_impl in
  FSet.has (L20.Callset.stmt_callset (translate_stmt_list is_private_call l)) x
   =
  (FSet.has (L10.Callset.stmt_list_callset l) x && is_private_call x)%bool.
Proof.
apply callset_translate_stmt_list_aux.
induction l. { easy. }
refine (List.Forall_cons _ _ IHl).
apply callset_translate_stmt.
Qed.

Lemma callset_translate_decl {C: VyperConfig}
                             (is_private_call: string -> bool)
                             (d: L10.AST.decl)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L20.Callset.decl_callset (translate_decl is_private_call d)) x
   =
  (FSet.has (L10.Callset.decl_callset d) x && is_private_call x)%bool.
Proof.
destruct d; cbn. { now rewrite FSet.empty_ok. }
apply callset_translate_stmt_list.
Qed.
