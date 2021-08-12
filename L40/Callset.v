From Coq Require Import List String NArith.
From Vyper Require Import FSet Config L40.AST.

Section Callset.

Context {C: VyperConfig}.

(** Get the set of functions called by an expression. *)
Fixpoint expr_callset (e: expr)
: string_set
:= let _ := string_set_impl in
   let fix expr_list_callset (exprs: list expr)
       := match exprs with
          | nil => empty
          | (h :: t)%list => union (expr_callset h) (expr_list_callset t)
          end
   in match e with
      | Const _ | LocalVar _ | LoopOffset | LoopCursor => empty
      | PrivateCall name args => add (expr_list_callset args) name
      | BuiltinCall name args => expr_list_callset args
      end.
Fixpoint expr_list_callset (exprs: list expr)
: string_set
:= let _ := string_set_impl in
   match exprs with
   | nil => empty
   | (h :: t)%list => union (expr_callset h) (expr_list_callset t)
   end.

Definition small_stmt_callset (s: small_stmt)
:= let _ := string_set_impl in
   match s with
   | Abort _ => empty
   | Return e | Raise e | ExprStmt e =>
       expr_callset e
   | Assign lhs rhs => expr_callset rhs
   end.

Fixpoint stmt_callset (s: stmt)
:= let _ := string_set_impl in
   let fix case_list_callset (l: list case)
       := let _ := string_set_impl in
          match l with
          | nil => empty
          | h :: t => union (case_callset h) (case_list_callset t)
          end in
   match s with
   | SmallStmt a => small_stmt_callset a
   | Switch cond cases None => union (expr_callset cond)
                                     (case_list_callset cases)
   | Switch cond cases (Some default) => union (expr_callset cond)
                                                       (union (case_list_callset cases)
                                                              (block_callset default))
   | Loop _ _ body => block_callset body
   end
with block_callset (b: block)
     := let '(Block body) := b in
        (fix stmt_list_callset (l: list stmt)
         := let _ := string_set_impl in
            match l with
            | nil => empty
            | h :: t => union (stmt_callset h) (stmt_list_callset t)
            end) body
with case_callset (c: case)
  := let '(Case _ body) := c in block_callset body.

Fixpoint stmt_list_callset (l: list stmt)
:= let _ := string_set_impl in
   match l with
   | nil => empty
   | h :: t => union (stmt_callset h) (stmt_list_callset t)
   end.

Fixpoint case_list_callset (l: list case)
:= let _ := string_set_impl in
   match l with
   | nil => empty
   | h :: t => union (case_callset h) (case_list_callset t)
   end.

Ltac descend H 
:= subst; cbn in H;
   repeat try rewrite union_subset_and in H;
   repeat rewrite Bool.andb_true_iff in H;
   try tauto.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in
   match d with
   | FunDecl name args body => block_callset body
   end.

Lemma callset_leaf {e: expr} {name: string} {args: list expr}
                   {allowed_calls: string_set}
                   (E: e = PrivateCall name args)
                   (ok: let _ := string_set_impl in
                         FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.has allowed_calls name = true.
Proof.
subst e. cbn in ok.
rewrite FSet.is_subset_ok in ok.
assert (Ok := ok name). clear ok.
rewrite FSet.add_ok in Ok.
destruct (string_dec name name). 2:{ tauto. }
cbn.
destruct (FSet.has allowed_calls name). { trivial. }
cbn in Ok. discriminate.
Qed.

Lemma callset_descend_args {e: expr} {name: string} {args: list expr}
                           {allowed_calls: string_set}
                           (E: e = PrivateCall name args)
                           (ok: let _ := string_set_impl in
                                FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_list_callset args) allowed_calls = true.
Proof.
subst e. cbn in *.
unfold expr_list_callset.
apply (FSet.is_subset_trans (FSet.add_subset _ _) ok).
Qed.

Lemma callset_descend_builtin_args {e: expr} {name: string} {args: list expr}
                                   {allowed_calls: string_set}
                                   (E: e = BuiltinCall name args)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_list_callset args) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_head {h: expr} {t e: list expr}
                           {allowed_calls: string_set}
                           (E: e = (h :: t)%list)
                           (ok: let _ := string_set_impl in
                           FSet.is_subset (expr_list_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset h) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_tail {h: expr} {t e: list expr}
                           {allowed_calls: string_set}
                           (E: e = (h :: t)%list)
                           (ok: let _ := string_set_impl in
                                FSet.is_subset (expr_list_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_list_callset t) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_cases_head {h: case} {t l: list case}
                                 {allowed_calls: string_set}
                                 (E: l = (h :: t)%list)
                                 (ok: let _ := string_set_impl in
                                 FSet.is_subset (case_list_callset l) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (case_callset h) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_cases_tail {h: case} {t l: list case}
                                 {allowed_calls: string_set}
                                 (E: l = (h :: t)%list)
                                 (ok: let _ := string_set_impl in
                                 FSet.is_subset (case_list_callset l) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (case_list_callset t) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_switch_expr {s: stmt} {cond: expr} {cases: list case} {def: option block}
                                       {allowed_calls: string_set}
                                       (E: s = Switch cond cases def)
                                       (ok: let _ := string_set_impl in
                                            FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset cond) allowed_calls = true.
Proof.
destruct def; descend ok.
Qed.

Lemma callset_descend_cases_no_default {s: stmt} {cond: expr} {cases: list case}
                                       {allowed_calls: string_set}
                                       (E: s = Switch cond cases None)
                                       (ok: let _ := string_set_impl in
                                            FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (case_list_callset cases) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_cases_some_default {s: stmt} {cond: expr} {cases: list case} {default: block}
                                         {allowed_calls: string_set}
                                         (E: s = Switch cond cases (Some default))
                                         (ok: let _ := string_set_impl in
                                              FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (case_list_callset cases) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_cases {s: stmt} {cond: expr} {cases: list case} {default: option block}
                            {allowed_calls: string_set}
                            (E: s = Switch cond cases default)
                            (ok: let _ := string_set_impl in
                                 FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (case_list_callset cases) allowed_calls = true.
Proof.
destruct default; descend ok.
Qed.

Lemma callset_descend_cases_default {s: stmt} {cond: expr} {cases: list case} {default: block}
                                    {allowed_calls: string_set}
                                    (E: s = Switch cond cases (Some default))
                                    (ok: let _ := string_set_impl in
                                         FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (block_callset default) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_return {s: small_stmt} {e: expr}
                             {allowed_calls: string_set}
                             (E: s = Return e)
                             (ok: let _ := string_set_impl in
                                  FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset e) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_raise {s: small_stmt} {e: expr}
                            {allowed_calls: string_set}
                            (E: s = Raise e)
                            (ok: let _ := string_set_impl in
                                 FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset e) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_expr_stmt {s: small_stmt} {e: expr}
                                {allowed_calls: string_set}
                                (E: s = ExprStmt e)
                                (ok: let _ := string_set_impl in
                                     FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset e) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_assign_rhs {s: small_stmt} {lhs: N} {rhs: expr}
                                 {allowed_calls: string_set}
                                 (E: s = Assign lhs rhs)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset rhs) allowed_calls = true.
Proof.
descend ok.
Qed.

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

Lemma callset_descend_loop_body {s: stmt} {body: block} {var count}
                                {allowed_calls: string_set}
                                (E: s = Loop var count body)
                                (ok: let _ := string_set_impl in
                                     FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (block_callset body) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_block {l: list stmt} {b: block}
                            {allowed_calls: string_set}
                            (E: b = Block l)
                            (ok: let _ := string_set_impl in
                                 FSet.is_subset (block_callset b) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_list_callset l) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmts_head {h: stmt} {t l: list stmt}
                                 {allowed_calls: string_set}
                                 (E: l = (h :: t)%list)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (stmt_list_callset l) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset h) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmts_tail {h: stmt} {t l: list stmt}
                                 {allowed_calls: string_set}
                                 (E: l = (h :: t)%list)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (stmt_list_callset l) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_list_callset t) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmts_app_left {l a b: list stmt}
                                     {allowed_calls: string_set}
                                     (E: l = (a ++ b)%list)
                                     (ok: let _ := string_set_impl in
                                        FSet.is_subset (stmt_list_callset l) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_list_callset a) allowed_calls = true.
Proof.
subst. cbn in *.
induction a as [|h]; cbn. { apply empty_subset. }
cbn in ok.
rewrite union_subset_and.
apply andb_true_intro.
rewrite union_subset_and in ok.
apply Bool.andb_true_iff in ok.
destruct ok as (OkH, OkAB).
exact (conj OkH (IHa OkAB)).
Qed.

Lemma callset_descend_stmts_app_right {l a b: list stmt}
                                      {allowed_calls: string_set}
                                      (E: l = (a ++ b)%list)
                                      (ok: let _ := string_set_impl in
                                         FSet.is_subset (stmt_list_callset l) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_list_callset b) allowed_calls = true.
Proof.
subst. cbn in *.
induction a as [|h]; cbn. { rewrite app_nil_l in ok. exact ok. }
cbn in ok.
rewrite union_subset_and in ok.
apply Bool.andb_true_iff in ok.
destruct ok as (OkH, OkAB).
exact (IHa OkAB).
Qed.

End Callset.