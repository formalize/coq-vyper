From Coq Require Import String NArith.

From Vyper Require Import Config FSet.

From Vyper.L30 Require Import AST.


Section Callset.

Context {C: VyperConfig}.

(** Get the set of functions called by an expression. *)
Definition small_stmt_callset (ss: small_stmt)
: string_set
:= let _ := string_set_impl in 
   match ss with
   | PrivateCall _ name _ _ => singleton name
   | _ => empty
   end.

Fixpoint stmt_callset (s: stmt)
:= let _ := string_set_impl in
   match s with
   | SmallStmt a => small_stmt_callset a
   | IfElseStmt cond yes no => (union (stmt_callset yes) (stmt_callset no))
   | Loop _ _ body => stmt_callset body
   | Semicolon a b => union (stmt_callset a) (stmt_callset b)
   end.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in match d with
   | StorageVarDecl _ => empty
   | FunDecl name args body => stmt_callset body
   end.



Ltac descend H 
:= subst; cbn in H;
   repeat try rewrite union_subset_and in H;
   repeat rewrite Bool.andb_true_iff in H;
   try tauto.

Lemma callset_descend_small_stmt {s: stmt} {ss: small_stmt}
                                 {allowed_calls: string_set}
                                 (E: s = SmallStmt ss)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (small_stmt_callset ss) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmt_if_then {cond: N} {yes no s: stmt}
                                   {allowed_calls: string_set}
                                   (E: s = IfElseStmt cond yes no)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset yes) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmt_if_else {cond: N} {yes no s: stmt}
                                   {allowed_calls: string_set}
                                   (E: s = IfElseStmt cond yes no)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset no) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_loop_body {s: stmt} {body: stmt} {var count}
                                {allowed_calls: string_set}
                                (E: s = Loop var count body)
                                (ok: let _ := string_set_impl in
                                     FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset body) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_semicolon_left {a b s: stmt}
                                     {allowed_calls: string_set}
                                     (E: s = Semicolon a b)
                                     (ok: let _ := string_set_impl in
                                          FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_semicolon_right {a b s: stmt}
                                      {allowed_calls: string_set}
                                      (E: s = Semicolon a b)
                                      (ok: let _ := string_set_impl in
                                           FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset b) allowed_calls = true.
Proof.
descend ok.
Qed.



End Callset.