From Coq Require Import List String.
Require Import FSet Config UntypedAST.

Section Callset.

Context {C: VyperConfig}.

(** Get the set of functions called by an expression. *)
Fixpoint expr_callset (e: expr)
: string_set
:= let _ := string_set_impl in
   match e with
   | Const _ | LocalVar _ | StorageVar _ => empty
   | UnOp _ a => expr_callset a
   | BinOp _ a b
   | LogicalOr a b
   | LogicalAnd a b => union (expr_callset a) (expr_callset b)
   | IfThenElse a b c => union (expr_callset a) (union (expr_callset b) (expr_callset c))
   | PrivateOrBuiltinCall name args =>
      let expr_list_callset := fix expr_list_callset (exprs: list expr) :=
         match exprs with
         | nil => empty
         | (h :: t)%list => union (expr_callset h) (expr_list_callset t)
         end
      in add (expr_list_callset args) name
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
   | Pass | Break | Continue | Return None | Revert => empty
   | Return (Some e) | Raise e | Assert e None | ExprStmt e =>
       expr_callset e
   | Assign lhs rhs | BinOpAssign lhs _ rhs => expr_callset rhs
   | Assert cond (Some error) => union (expr_callset cond) (expr_callset error)
   end.

Fixpoint stmt_callset (s: stmt)
:= let _ := string_set_impl in
   let stmt_list_callset := fix stmt_list_callset (stmts: list stmt) :=
         match stmts with
         | nil => empty
         | (h :: t)%list => union (stmt_callset h) (stmt_list_callset t)
         end
   in match s with
   | SmallStmt a => small_stmt_callset a
   | LocalVarDecl _ None => empty
   | LocalVarDecl _ (Some e) => expr_callset e
   | IfElseStmt cond yes None => union (expr_callset cond) (stmt_list_callset yes)
   | IfElseStmt cond yes (Some no) => union (expr_callset cond)
                                            (union (stmt_list_callset yes) (stmt_list_callset no))
   | FixedRangeLoop var start _ body | FixedCountLoop var start _ body =>
       stmt_list_callset body
   end.

Fixpoint stmt_list_callset (stmts: list stmt)
:= let _ := string_set_impl in
   match stmts with
   | nil => empty
   | (h :: t)%list => union (stmt_callset h) (stmt_list_callset t)
   end.

Definition stmt_list_callset' (stmts: list stmt)
:= let _ := string_set_impl in fold_right union empty (map stmt_callset stmts).

Ltac descend H 
:= subst; cbn in H;
   repeat try rewrite union_subset_and in H;
   repeat rewrite Bool.andb_true_iff in H;
   try tauto.

Lemma stmt_list_callset_alt (s: list stmt):
  stmt_list_callset s = stmt_list_callset' s.
Proof.
induction s. { easy. }
cbn. f_equal. apply IHs.
Qed.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in match d with
   | StorageVarDecl _ => empty
   | FunDecl name args body => (* stmt_list_callset *) small_stmt_callset body
   end.

Lemma callset_descend_unop {e a: expr} {op: unop}
                           {allowed_calls: string_set}
                           (E: e = UnOp op a)
                           (ok: let _ := string_set_impl in
                                FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_binop_left {e a b: expr} {op: binop}
                                 {allowed_calls: string_set}
                                 (E: e = BinOp op a b)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_binop_right {e a b: expr} {op: binop}
                                  {allowed_calls: string_set}
                                  (E: e = BinOp op a b)
                                  (ok: let _ := string_set_impl in
                                       FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset b) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_leaf {e: expr} {name: string} {args: list expr}
                   {allowed_calls: string_set}
                   (E: e = PrivateOrBuiltinCall name args)
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
                           (E: e = PrivateOrBuiltinCall name args)
                           (ok: let _ := string_set_impl in
                                FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_list_callset args) allowed_calls = true.
Proof.
subst e. cbn in *.
unfold expr_list_callset.
apply (FSet.is_subset_trans (FSet.add_subset _ _) ok).
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

Lemma callset_descend_if_cond {cond yes no e: expr}
                              {allowed_calls: string_set}
                              (E: e = IfThenElse cond yes no)
                              (ok: let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset cond) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_if_then {cond yes no e: expr}
                              {allowed_calls: string_set}
                              (E: e = IfThenElse cond yes no)
                              (ok: let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset yes) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_if_else {cond yes no e: expr}
                              {allowed_calls: string_set}
                              (E: e = IfThenElse cond yes no)
                              (ok: let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset no) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_and_left {a b e: expr}
                               {allowed_calls: string_set}
                               (E: e = LogicalAnd a b)
                               (ok: let _ := string_set_impl in
                                    FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_and_right {a b e: expr}
                                {allowed_calls: string_set}
                                (E: e = LogicalAnd a b)
                                (ok: let _ := string_set_impl in
                                     FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset b) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_or_left {a b e: expr}
                              {allowed_calls: string_set}
                              (E: e = LogicalOr a b)
                              (ok: let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_or_right {a b e: expr}
                               {allowed_calls: string_set}
                               (E: e = LogicalOr a b)
                               (ok: let _ := string_set_impl in
                                    FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset b) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_return {s: small_stmt} {e: expr}
                             {allowed_calls: string_set}
                             (E: s = Return (Some e))
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

Lemma callset_descend_assert_cond {s: small_stmt} {cond: expr} {maybe_e: option expr}
                                  {allowed_calls: string_set}
                                  (E: s = Assert cond maybe_e)
                                  (ok: let _ := string_set_impl in
                                       FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset cond) allowed_calls = true.
Proof.
subst. cbn in *. destruct maybe_e; cbn in ok; descend ok.
Qed.

Lemma callset_descend_assert_error {s: small_stmt} {cond e: expr} {maybe_e: option expr}
                                   {allowed_calls: string_set}
                                   (E: s = Assert cond maybe_e)
                                   (Ee: maybe_e = Some e)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset e) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_assign_rhs {s: small_stmt} {lhs: assignable} {rhs: expr}
                                 {allowed_calls: string_set}
                                 (E: s = Assign lhs rhs)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset rhs) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_binop_assign_rhs {s: small_stmt} {lhs: assignable} {rhs: expr}
                                       {allowed_calls: string_set}
                                       {op: binop}
                                       (E: s = BinOpAssign lhs op rhs)
                                       (ok: let _ := string_set_impl in
                                            FSet.is_subset (small_stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset rhs) allowed_calls = true.
Proof.
descend ok.
Qed.

End Callset.