From Coq Require Import String ZArith.
From Vyper Require Import Config.
From Vyper Require L10.AST L20.AST L10.Interpret L20.Interpret.

Section Translate.

Context {C: VyperConfig}
        (is_private_call: string -> bool).

(* The only difference in L10 and L20 expressions are the calls. *)
Fixpoint translate_expr (e: L10.AST.expr)
: L20.AST.expr
:= match e with
   | L10.AST.Const val => L20.AST.Const val
   | L10.AST.LocalVar name => L20.AST.LocalVar name
   | L10.AST.StorageVar name => L20.AST.StorageVar name
   | L10.AST.UnOp op a => L20.AST.UnOp op (translate_expr a)
   | L10.AST.BinOp op a b => L20.AST.BinOp op (translate_expr a)
                                              (translate_expr b)
   | L10.AST.IfThenElse cond yes no => L20.AST.IfThenElse (translate_expr cond)
                                                          (translate_expr yes)
                                                          (translate_expr no)
   | L10.AST.LogicalAnd a b => L20.AST.LogicalAnd (translate_expr a)
                                                  (translate_expr b)
   | L10.AST.LogicalOr a b => L20.AST.LogicalOr (translate_expr a)
                                                (translate_expr b)
   | L10.AST.PrivateOrBuiltinCall name args =>
      (if is_private_call name then L20.AST.PrivateCall else L20.AST.BuiltinCall)
        name
        ((fix translate_expr_list (l: list L10.AST.expr)
          := match l with
             | nil => nil
             | cons h t => cons (translate_expr h) (translate_expr_list t)
             end) args)
  end.

(* break, continue and revert are joined together into abort
   assert is translated to if
   augmented assignments are translated to usual ones
 *)
Fixpoint translate_small_stmt (ss: L10.AST.small_stmt)
: L20.AST.stmt
:= match ss with
   | L10.AST.Pass => L20.AST.SmallStmt L20.AST.Pass
   | L10.AST.Break    => L20.AST.SmallStmt (L20.AST.Abort (L10.Interpret.AbortBreak))
   | L10.AST.Continue => L20.AST.SmallStmt (L20.AST.Abort (L10.Interpret.AbortContinue))
   | L10.AST.Revert   => L20.AST.SmallStmt (L20.AST.Abort (L10.Interpret.AbortRevert))
   | L10.AST.Return (Some result) => L20.AST.SmallStmt (L20.AST.Return (translate_expr result))
   | L10.AST.Return None => L20.AST.SmallStmt (L20.AST.Return (L20.AST.Const zero256))
   | L10.AST.Raise error => L20.AST.SmallStmt (L20.AST.Raise (translate_expr error))
   | L10.AST.Assert cond error =>
        L20.AST.IfElseStmt (translate_expr cond)
                           (L20.AST.SmallStmt L20.AST.Pass)
                           (L20.AST.SmallStmt
                             (L20.AST.Raise
                               match error with
                               | Some e => translate_expr e
                               | None => L20.AST.Const zero256
                               end))
   | L10.AST.Assign lhs rhs =>
        L20.AST.SmallStmt (L20.AST.Assign lhs (translate_expr rhs ))
   | L10.AST.BinOpAssign lhs op rhs =>
        L20.AST.SmallStmt
          (L20.AST.Assign lhs 
                          (L20.AST.BinOp op
                                         match lhs with
                                         | L10.AST.AssignableLocalVar name => L20.AST.LocalVar name
                                         | L10.AST.AssignableStorageVar name => L20.AST.StorageVar name
                                         end
                                         (translate_expr rhs)))
   | L10.AST.ExprStmt e => 
        L20.AST.SmallStmt (L20.AST.ExprStmt (translate_expr e))
   end.

(* list of statements are now joined with a 'semicolon' statement
   var declarations are now keeping their scope (let _ = _ in _)
   else branch is obligatory
   there's now only one kind of loop
 *)
Fixpoint translate_stmt (s: L10.AST.stmt)
: L20.AST.stmt
:= let translate_stmt_list
   := fix translate_stmt_list (l: list L10.AST.stmt)
      := match l with
         | nil => L20.AST.SmallStmt L20.AST.Pass
         (* | (h :: nil)%list => translate_stmt h      <- this case makes stuff too complicated *)
         | (L10.AST.LocalVarDecl name maybe_init :: t)%list =>
             L20.AST.LocalVarDecl name
                                  match maybe_init with
                                  | Some init => translate_expr init
                                  | None => L20.AST.Const zero256
                                  end
                                  (translate_stmt_list t)
         | (h :: t)%list => L20.AST.Semicolon (translate_stmt h)
                                              (translate_stmt_list t)
         end
   in match s with
   | L10.AST.LocalVarDecl name maybe_init =>
        L20.AST.LocalVarDecl name
                             match maybe_init with
                             | Some init => translate_expr init
                             | None => L20.AST.Const zero256
                             end
                             (L20.AST.SmallStmt L20.AST.Pass)
   | L10.AST.SmallStmt ss => translate_small_stmt ss
   | L10.AST.IfElseStmt cond yes no =>
        L20.AST.IfElseStmt (translate_expr cond)
                           (translate_stmt_list yes)
                           match no with
                           | Some n => translate_stmt_list n
                           | None => L20.AST.SmallStmt L20.AST.Pass
                           end
   | L10.AST.FixedRangeLoop var maybe_start stop body =>
        let start := match maybe_start with
                           | Some x => x
                           | None => zero256
                           end
         in L20.AST.Loop var
                          (L20.AST.Const start)
                          (uint256_of_Z (Z_of_uint256 stop - Z_of_uint256 start)%Z)
                          (translate_stmt_list body)
   | L10.AST.FixedCountLoop var start count body =>
        L20.AST.Loop var (translate_expr start) count (translate_stmt_list body)
   end.

(* XXX this is a dup from translate_stmt *)
Fixpoint translate_stmt_list (l: list L10.AST.stmt)
: L20.AST.stmt
:= match l with
   | nil => L20.AST.SmallStmt L20.AST.Pass
   | (L10.AST.LocalVarDecl name maybe_init :: t)%list =>
       L20.AST.LocalVarDecl name
                            match maybe_init with
                            | Some init => translate_expr init
                            | None => L20.AST.Const zero256
                            end
                            (translate_stmt_list t)
   | (h :: t)%list => L20.AST.Semicolon (translate_stmt h)
                                        (translate_stmt_list t)
   end.

Definition translate_decl (d: L10.AST.decl)
: L20.AST.decl
:= match d with
   | L10.AST.StorageVarDecl name => L20.AST.StorageVarDecl name
   | L10.AST.FunDecl name arg_names body =>
       L20.AST.FunDecl name arg_names (translate_stmt_list body)
   end.

End Translate.

Fixpoint decl_names {C: VyperConfig} (decls: list L10.AST.decl)
:= List.map L10.AST.decl_name decls.

Definition decl_set {C: VyperConfig} (decls: list L10.AST.decl)
: string_set
:= let _ := string_set_impl in FSet.from_list (decl_names decls).

(* superceded by translate_calldag *)
Definition translate_decl_list {C: VyperConfig} (d: list L10.AST.decl)
: list L20.AST.decl
:= let f := decl_set d in
   let is_private_call (name: string) := let _ := string_set_impl in FSet.has f name in
   List.map (translate_decl is_private_call) d.

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
Lemma callset_translate_stmt_list_aux {C: VyperConfig}
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

(*************************************************************************************************)

Lemma translate_calldag_helper {C: VyperConfig}
                               (cd: L10.Interpret.calldag):
  let is_private_call (name: string)
   := match L10.Interpret.cd_declmap cd name with
      | Some _ => true
      | _ => false
      end 
  in forall name: string,
       match
          match L10.Interpret.cd_declmap cd name with
          | Some f => Some (translate_decl is_private_call f)
          | None => None
          end
       with
       | Some decl =>
           match L10.Interpret.cd_depthmap cd name with
           | Some x =>
               let _ := string_set_impl in
               FSet.for_all (Callset.decl_callset decl)
                 (fun callee : string =>
                  match L10.Interpret.cd_depthmap cd callee with
                  | Some y => y <? x
                  | None => false
                  end) = true
           | None => False
           end
       | None => True
       end.
Proof.
intros is_private_call name.
assert (D := L10.Interpret.cd_depthmap_ok cd name).
cbn.
remember (L10.Interpret.cd_declmap cd name) as maybe_f. destruct maybe_f. 2:easy.
destruct (L10.Interpret.cd_depthmap cd name). 2:easy.
rewrite FSet.for_all_ok in *. intros x H.
rewrite callset_translate_decl in H.
apply Bool.andb_true_iff in H.
assert (Q := D x (proj1 H)). clear D.
destruct (L10.Interpret.cd_depthmap cd x). 2:easy.
destruct n; rewrite Nat.ltb_lt in Q. { now apply Nat.nlt_0_r in Q. }
rewrite Nat.leb_le.
apply Nat.lt_succ_r. exact Q.
Qed.


(* XXX This is inefficient since functions are translated at each lookup.
   It's better to rebuild the calldag.
 *)
Definition translate_calldag {C: VyperConfig} (cd: L10.Interpret.calldag)
:= let is_private_call (name: string)
   := match L10.Interpret.cd_declmap cd name with
      | Some _ => true
      | _ => false
      end
   in {| L20.Interpret.cd_declmap (name: string) :=
              match L10.Interpret.cd_declmap cd name with
              | Some f => Some (translate_decl is_private_call f)
              | None => None
              end
       ; L20.Interpret.cd_depthmap := L10.Interpret.cd_depthmap cd
       ; L20.Interpret.cd_depthmap_ok := translate_calldag_helper cd
      |}.

(***************************************************************************************************)

(*
Theorem translate_ok {C: VyperConfig}
                     (builtins: string -> option L10.Interpret.builtin)
                     (cd: L10.Interpret.calldag)
                     (fun_name: string)
                     (world: world_state)
                     (arg_values: list uint256):
  L20.Interpret.interpret builtins (translate_calldag cd) fun_name world arg_values
   =
  L10.Interpret.interpret builtins cd fun_name world arg_values.
Proof.
unfold L10.Interpret.interpret.
unfold L20.Interpret.interpret. *)