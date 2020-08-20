From Coq Require Import List String.
From Vyper Require Import FSet Config L20.AST.

Section Callset.

Context {C: VyperConfig}.

(** Get the set of functions called by an expression. *)
Fixpoint expr_callset (e: expr)
: string_set
:= let _ := string_set_impl in
   let expr_list_callset := fix expr_list_callset (exprs: list expr) :=
      match exprs with
      | nil => empty
      | (h :: t)%list => union (expr_callset h) (expr_list_callset t)
      end
   in match e with
      | Const _ | LocalVar _ | StorageVar _ => empty
      | UnOp _ a => expr_callset a
      | BinOp _ a b
      | LogicalOr a b
      | LogicalAnd a b => union (expr_callset a) (expr_callset b)
      | IfThenElse a b c => union (expr_callset a) (union (expr_callset b) (expr_callset c))
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
   | Pass | Abort _ => empty
   | Return e | Raise e | ExprStmt e =>
       expr_callset e
   | Assign lhs rhs => expr_callset rhs
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
   | LocalVarDecl _ e scope => union (expr_callset e) (stmt_callset scope)
   | IfElseStmt cond yes no => union (expr_callset cond)
                                     (union (stmt_callset yes) (stmt_callset no))
   | Loop var start _ body => union (expr_callset start) (stmt_callset body)
   | Semicolon a b => union (stmt_callset a) (stmt_callset b)
   end.

Ltac descend H 
:= subst; cbn in H;
   repeat try rewrite union_subset_and in H;
   repeat rewrite Bool.andb_true_iff in H;
   try tauto.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in match d with
   | StorageVarDecl _ => empty
   | FunDecl name args body => stmt_callset body
   end.

Lemma callset_descend_unop {e a: expr} {op: L10.AST.unop}
                           {allowed_calls: string_set}
                           (E: e = UnOp op a)
                           (ok: let _ := string_set_impl in
                                FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_binop_left {e a b: expr} {op: L10.AST.binop}
                                 {allowed_calls: string_set}
                                 (E: e = BinOp op a b)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (expr_callset e) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset a) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_binop_right {e a b: expr} {op: L10.AST.binop}
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

Lemma callset_descend_assign_rhs {s: small_stmt} {lhs: L10.AST.assignable} {rhs: expr}
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

Lemma callset_descend_stmt_if_cond {cond: expr} {yes no s: stmt}
                                   {allowed_calls: string_set}
                                   (E: s = IfElseStmt cond yes no)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset cond) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmt_if_then {cond: expr} {yes no s: stmt}
                                   {allowed_calls: string_set}
                                   (E: s = IfElseStmt cond yes no)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset yes) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_stmt_if_else {cond: expr} {yes no s: stmt}
                                   {allowed_calls: string_set}
                                   (E: s = IfElseStmt cond yes no)
                                   (ok: let _ := string_set_impl in
                                        FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset no) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_loop_body {s: stmt} {body: stmt} {var start stop}
                                {allowed_calls: string_set}
                                (E: s = Loop var start stop body)
                                (ok: let _ := string_set_impl in
                                     FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset body) allowed_calls = true.
Proof.
descend ok.
Qed.

Lemma callset_descend_loop_start {s: stmt} {body: stmt} {var start count}
                                 {allowed_calls: string_set}
                                 (E: s = Loop var start count body)
                                 (ok: let _ := string_set_impl in
                                      FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset start) allowed_calls = true.
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

Lemma callset_descend_var_scope {s: stmt} {name init scope}
                                {allowed_calls: string_set}
                                (E: s = LocalVarDecl name init scope)
                                (ok: let _ := string_set_impl in
                                     FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset scope) allowed_calls = true.
Proof.
destruct init; descend ok.
Qed.


Lemma callset_descend_var_init {s: stmt} {name init scope}
                               {allowed_calls: string_set}
                               (E: s = LocalVarDecl name init scope)
                               (ok: let _ := string_set_impl in
                                    FSet.is_subset (stmt_callset s) allowed_calls = true):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset init) allowed_calls = true.
Proof.
descend ok.
Qed.

End Callset.
