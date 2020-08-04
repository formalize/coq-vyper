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
   | BinOp _ a b => union (expr_callset a) (expr_callset b)
(*   | IfThenElse a b c => union (expr_callset a) (union (expr_callset b) (expr_callset c)) *)
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

Lemma stmt_list_callset_alt (s: list stmt):
  stmt_list_callset s = stmt_list_callset' s.
Proof.
induction s. { easy. }
cbn. f_equal. apply IHs.
Qed.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in match d with
   | StorageVarDecl _ => empty
   | FunDecl name args body => (* XXX stmt_list_callset *) expr_callset body
   end.

Lemma callset_descend_unop {e a: expr} {op: unop}
                           {allowed_calls: string_set}
                           (E: e = UnOp op a)
                           (ok: let _ := string_set_impl in
                                FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
subst e. apply ok.
Qed.

Lemma callset_descend_binop_left {e a b: expr} {op: binop}
                                 {allowed_calls: string_set}
                                 (E: e = BinOp op a b)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof. 
subst e. cbn in ok.
apply (FSet.is_subset_trans (FSet.union_subset_l _ _) ok).
Qed.

Lemma callset_descend_binop_right {e a b: expr} {op: binop}
                                  {allowed_calls: string_set}
                                  (E: e = BinOp op a b)
                                  (ok: let _ := string_set_impl in
                                       FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset b) allowed_calls = true.
Proof. 
subst e. cbn in ok.
apply (FSet.is_subset_trans (FSet.union_subset_r _ _) ok).
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
subst e. cbn in ok.
apply (FSet.is_subset_trans (FSet.union_subset_l _ _) ok).
Qed.

Lemma callset_descend_tail {h: expr} {t e: list expr}
                           {allowed_calls: string_set}
                           (E: e = (h :: t)%list)
                           (ok: let _ := string_set_impl in
                           FSet.is_subset (expr_list_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_list_callset t) allowed_calls = true.
Proof. 
subst e. cbn in ok.
apply (FSet.is_subset_trans (FSet.union_subset_r _ _) ok).
Qed.


End Callset.