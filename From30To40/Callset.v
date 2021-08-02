From Coq Require Import String ZArith Eqdep_dec.

From Vyper Require Import Config Calldag L10.Base CheckArith.Builtins.
From Vyper Require L30.AST L40.AST L30.Callset L40.Callset.

From Vyper.From30To40 Require Import Translate.


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
Lemma callset_translate_small_stmt {C: VyperConfig}
                                   (B: Builtins.builtin_names_config)
                                   (ss: L30.AST.small_stmt)
                                   (l: list L40.AST.stmt)
                                   (E: translate_small_stmt B ss = inr l)
                                   (x: string):
  let _ := string_set_impl in
  FSet.has (L40.Callset.stmt_list_callset l) x
   =
  FSet.has (L30.Callset.small_stmt_callset ss) x.
Proof.
destruct ss; cbn in *; inversion E; subst; cbn; rr; try easy;
  [ destruct string_dec; trivial | ];
  unfold Translate.var_range;
  remember (N.to_nat args_count) as k; clear Heqk;
  induction k; cbn; rr; trivial;
  apply IHk.
Qed.

Lemma callset_translate_stmt {C: VyperConfig}
                             (B: Builtins.builtin_names_config)
                             (s: L30.AST.stmt)
                             (l: list L40.AST.stmt)
                             (E: translate_stmt B s = inr l)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (L40.Callset.stmt_list_callset l) x
   =
  FSet.has (L30.Callset.stmt_callset s) x.
Proof.
cbn. revert l E. induction s; intros; cbn; rr.
{ (* small *) cbn in E. apply (callset_translate_small_stmt B). exact E. }
{ (* if-else *)
  cbn in E. rename s1 into yes. rename s2 into no.
  destruct (translate_stmt B yes) as [err | yes']. { discriminate. }
  destruct (translate_stmt B no) as [err | no']. { discriminate. }
  inversion E; subst; clear E.
  assert (IHyes := IHs1 yes' eq_refl). clear IHs1.
  assert (IHno := IHs2 no' eq_refl). clear IHs2.
  unfold Callset.stmt_list_callset. rr.
  cbn. rr.
  rewrite Bool.orb_comm.
  f_equal. { apply IHyes. } apply IHno.
}
{ (* loop *)
  (* both "cbn in E" and "simpl in E" hang up *)
  unfold translate_stmt in E. fold translate_stmt in E.
  destruct (Z_of_uint256 count =? 0)%Z. { discriminate. }
  destruct (translate_stmt B s) as [err | body]. { discriminate. }
  assert (IHbody := IHs body eq_refl). clear IHs.
  (* here "inversion E" hangs up but this remember helps *)
  remember (AST.Switch
         (AST.BuiltinCall (builtin_name_uint256_lt B)
            (AST.LocalVar var :: AST.Const (uint256_of_Z (2 ^ 256 - Z_of_uint256 count + 1)) :: nil))
         (AST.Case zero256
            (AST.Block
               (AST.SmallStmt
                  (AST.Abort (AbortException (uint256_of_Z (Z_of_string "loop range overflows")))) :: nil))
          :: nil)
         (Some
            (AST.Block
               (AST.SmallStmt
                  (AST.Assign var
                     (AST.BuiltinCall (builtin_name_uint256_add B) (AST.LoopOffset :: AST.LoopCursor :: nil)))
                :: body))) :: nil)%list as l'.
  inversion E; subst; clear E.
  cbn. rr. apply IHbody.
}
(* semicolon *)
cbn in E.
destruct (translate_stmt B s1) as [err | t1]. { discriminate. }
destruct (translate_stmt B s2) as [err | t2]. { discriminate. }
inversion E; subst; clear E.
unfold Callset.stmt_list_callset. rr.
cbn. rr.
assert (IH1 := IHs1 t1 eq_refl). clear IHs1.
assert (IH2 := IHs2 t2 eq_refl). clear IHs2.
rewrite<- IH1. rewrite<- IH2. clear s1 s2 IH1 IH2.
induction t1; intros; cbn; rr. { easy. }
rewrite<- Bool.orb_assoc. f_equal.
apply IHt1.
Qed.
