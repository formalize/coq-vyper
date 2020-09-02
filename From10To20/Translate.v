From Coq Require Import String ZArith Eqdep_dec.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
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
   | L10.AST.Break    => L20.AST.SmallStmt (L20.AST.Abort (AbortBreak))
   | L10.AST.Continue => L20.AST.SmallStmt (L20.AST.Abort (AbortContinue))
   | L10.AST.Revert   => L20.AST.SmallStmt (L20.AST.Abort (AbortRevert))
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

(*************************************************************************************************)

Local Lemma translate_calldag_helper {C: VyperConfig}
                                     (cd: L10.Descend.calldag):
  let is_private_call (name: string)
   := match cd_declmap cd name with
      | Some _ => true
      | _ => false
      end 
  in forall name: string,
       match
          match cd_declmap cd name with
          | Some f => Some (translate_decl is_private_call f)
          | None => None
          end
       with
       | Some decl =>
           match cd_depthmap cd name with
           | Some x =>
               let _ := string_set_impl in
               FSet.for_all (Callset.decl_callset decl)
                 (fun callee : string =>
                  match cd_depthmap cd callee with
                  | Some y => y <? x
                  | None => false
                  end) = true
           | None => False
           end
       | None => True
       end.
Proof.
intros is_private_call name.
assert (D := cd_depthmap_ok cd name).
cbn.
remember (cd_declmap cd name) as maybe_f. destruct maybe_f. 2:easy.
destruct (cd_depthmap cd name). 2:easy.
rewrite FSet.for_all_ok in *. intros x H.
rewrite callset_translate_decl in H.
apply Bool.andb_true_iff in H.
assert (Q := D x (proj1 H)). clear D.
destruct (cd_depthmap cd x). 2:easy.
destruct n; rewrite Nat.ltb_lt in Q. { now apply Nat.nlt_0_r in Q. }
rewrite Nat.leb_le.
apply Nat.lt_succ_r. exact Q.
Qed.


(* This is inefficient since functions are translated at each lookup.
   It's better to rebuild the calldag.
 *)
Definition translate_calldag {C: VyperConfig} (cd: L10.Descend.calldag)
: L20.Descend.calldag
:= let is_private_call (name: string)
   := match cd_declmap cd name with
      | Some _ => true
      | _ => false
      end
   in {| cd_declmap (name: string) :=
              match cd_declmap cd name with
              | Some f => Some (translate_decl is_private_call f)
              | None => None
              end
       ; cd_depthmap := cd_depthmap cd
       ; cd_depthmap_ok := translate_calldag_helper cd
      |}.

(***************************************************************************************************)

Section FunCtx.
  Context {C: VyperConfig}
          {bound: nat}
          {cd: L10.Descend.calldag}
          (fc: fun_ctx cd bound)
          {cd2: L20.Descend.calldag}
          (ok: cd2 = translate_calldag cd).

  Local Lemma translate_fun_ctx_depthmap_helper (name: string):
    cd_depthmap cd2 name
     =
    cd_depthmap cd name.
  Proof.
  subst. trivial.
  Qed.

  Local Lemma translate_fun_ctx_fun_decl_helper:
    cd_declmap cd2 (fun_name fc) <> None.
  Proof.
  intro E.
  assert (Ok := fun_decl_ok fc).
  subst cd2. cbn in E. rewrite Ok in E. discriminate.
  Qed.

  Definition cached_translated_decl
  := match cd_declmap cd2 (fun_name fc)
     as d' return _ = d' -> _
     with
     | Some f => fun _ => f
     | None => fun E =>
          False_rect _ (translate_fun_ctx_fun_decl_helper E)
     end eq_refl.

  Local Lemma translate_fun_ctx_decl_ok:
    cd_declmap cd2 (fun_name fc) 
     =
    Some cached_translated_decl.
  Proof.
  assert (D := fun_decl_ok fc).
  unfold cached_translated_decl.
  remember translate_fun_ctx_fun_decl_helper as foo. clear Heqfoo. revert foo.
  destruct (cd_declmap cd2 (fun_name fc)). { trivial. }
  intro. contradiction.
  Qed.

  Definition translate_fun_ctx
  : fun_ctx cd2 bound
  := let name := fun_name fc in
     {| fun_name := name
      ; fun_depth := fun_depth fc
      ; fun_depth_ok :=
          eq_trans (translate_fun_ctx_depthmap_helper name)
                   (fun_depth_ok fc)
      ; fun_decl := cached_translated_decl
      ; fun_decl_ok := translate_fun_ctx_decl_ok
      ; fun_bound_ok := fun_bound_ok fc
     |}.

End FunCtx.
(***************************************************************************************************)

Lemma interpret_translated_expr {C: VyperConfig}
                                {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                {cd: L10.Descend.calldag}
                                (builtins: string -> option builtin)
                                (fc: fun_ctx cd bigger_call_depth_bound)
                                {cd2: L20.Descend.calldag}
                                (ok: cd2 = translate_calldag cd)
                                {do_call_10: forall
                                      (fc': fun_ctx cd smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                {do_call_20: forall
                                      (fc': fun_ctx cd2 smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                (DoCallOk: forall fc' world arg_values,
                                             do_call_20 (translate_fun_ctx fc' ok) world arg_values
                                              =
                                             do_call_10 fc' world arg_values)
                                (world: world_state)
                                (loc: string_map uint256)
                                {e10: L10.AST.expr}
                                {e20: L20.AST.expr}
                                (ExprOk: e20 = let is_private_call := fun name: string =>
                                                  match cd_declmap cd name with
                                                  | Some _ => true
                                                  | _ => false
                                                  end
                                               in translate_expr is_private_call e10)
                                (CallOk20: let _ := string_set_impl in 
                                   FSet.is_subset (L20.Callset.expr_callset e20)
                                                  (L20.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk10: let _ := string_set_impl in 
                                   FSet.is_subset (L10.Callset.expr_callset e10)
                                                  (L10.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
   L20.Expr.interpret_expr Ebound (translate_fun_ctx fc ok) do_call_20 builtins
                                world loc e20 CallOk20
    =
   L10.Expr.interpret_expr Ebound fc do_call_10 builtins
                                world loc e10 CallOk10.
Proof.
revert e20 ExprOk CallOk20 world loc. induction e10 using L10.AST.expr_ind'; intros.
{ (* Const *) now subst. }
{ (* LocalVar *) now subst. }
{ (* StorageVar *) now subst. }
{ (* UnOp *)
  subst. cbn.
  rewrite (IHe10 (L10.Callset.callset_descend_unop eq_refl CallOk10)); trivial.
}
{ (* BinOp *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_binop_left eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_binop_left eq_refl CallOk10)) as (world_a, result_a).
  destruct result_a. 2:{ trivial. }
  rewrite (IHe10_2 (L10.Callset.callset_descend_binop_right eq_refl CallOk10)); trivial.
}
{ (* IfThenElse *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_if_cond eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_if_cond eq_refl CallOk10)) as (world_cond, result_cond).
  destruct result_cond. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z).
  { (* else *) rewrite (IHe10_3 (L10.Callset.callset_descend_if_else eq_refl CallOk10)); trivial. }
  (* then *)   rewrite (IHe10_2 (L10.Callset.callset_descend_if_then eq_refl CallOk10)); trivial.
}
{ (* LogicalAnd *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_and_left eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_and_left eq_refl CallOk10)) as (world_a, result_a).
  destruct result_a. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z). { trivial. }
  rewrite (IHe10_2 (L10.Callset.callset_descend_and_right eq_refl CallOk10)); trivial.
}
{ (* LogicalOr *)
  subst. cbn.
  rewrite (IHe10_1 (L10.Callset.callset_descend_or_left eq_refl CallOk10)) by trivial.
  destruct (L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world loc e10_1
             (L10.Callset.callset_descend_or_left eq_refl CallOk10)) as (world_a, result_a).
  destruct result_a. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z). 2:{ trivial. }
  rewrite (IHe10_2 (L10.Callset.callset_descend_or_right eq_refl CallOk10)); trivial.
}
(* call *)
subst. cbn.
cbn in CallOk20.
remember (cd_declmap cd name) as d.
destruct d; cbn;
  remember (fix interpret_expr_list 
                        (w: world_state) (loc: string_map uint256) 
                        (exprs : list L20.AST.expr)
                        (CallOk : FSet.is_subset (Callset.expr_list_callset exprs)
                                    (L20.Callset.decl_callset (cached_translated_decl fc eq_refl))
                                  = true)
                        := _)
    as interpret_expr_list_20;
  remember (fix translate_expr_list (l: list L10.AST.expr): list L20.AST.expr := _)
    as translate_expr_list;
  remember (fix interpret_expr_list
                        (w: world_state) (loc: string_map uint256) 
                        (exprs : list L10.AST.expr)
                        (CallOk : FSet.is_subset (L10.Callset.expr_list_callset exprs)
                                    (L10.Callset.decl_callset
                                       (fun_decl fc)) =
                                  true)
                        := _)
    as interpret_expr_list_10.
{ (* PrivateCall *)
  assert (L: interpret_expr_list_20 world loc (translate_expr_list args)
               (L20.Callset.callset_descend_args eq_refl CallOk20)
              =
             interpret_expr_list_10 world loc args 
               (L10.Callset.callset_descend_args eq_refl CallOk10)).
  {
    remember (L20.Callset.callset_descend_args eq_refl CallOk20) as CallsOk20.
    remember (L10.Callset.callset_descend_args eq_refl CallOk10) as CallsOk10.
    clear CallOk10 HeqCallsOk10 CallOk20 HeqCallsOk20.
    revert world loc. induction args. { now subst. }
    intros. cbn in *.
    assert (CallsOk10' := CallsOk10).
    rewrite FSet.union_subset_and in CallsOk10'.
    rewrite Bool.andb_true_iff in CallsOk10'.
    destruct CallsOk10' as (HeadCallOk, TailCallsOk).
    subst. cbn.
    rewrite (List.Forall_inv H HeadCallOk) by trivial.
    match goal with
    |- (let (_, _) := ?l in _) = let (_, _) := ?r in _ =>
       remember l as lhs_head_result;
       remember r as rhs_head_result
    end.
    assert (R: lhs_head_result = rhs_head_result).
    { subst. f_equal. apply Eqdep_dec.eq_proofs_unicity. decide equality. }
    rewrite<- R.
    clear Heqlhs_head_result Heqrhs_head_result R rhs_head_result.
    destruct lhs_head_result as (world', result_h).
    destruct result_h. 2:{ trivial. }
    now rewrite (IHargs (List.Forall_inv_tail H)
                        (L20.Callset.callset_descend_tail eq_refl CallsOk20)
                        (L10.Callset.callset_descend_tail eq_refl CallsOk10) world' loc).
  }
  rewrite L.
  clear L Heqinterpret_expr_list_10 Heqinterpret_expr_list_20 H.
  destruct (interpret_expr_list_10 world loc args (L10.Callset.callset_descend_args eq_refl CallOk10))
    as (world', result_args).
  destruct result_args. 2:{ trivial. }
  match goal with
  |- _ = match ?x with Some _ => _ | None => _ end =>
          remember x as maybe_ctx10
  end.
  clear interpret_expr_list_10 interpret_expr_list_20 world.
  assert (D: L20.Descend.fun_ctx_descend (translate_fun_ctx fc eq_refl) CallOk20 eq_refl eq_refl
              =
             match maybe_ctx10 with
             | Some ctx => Some (translate_fun_ctx ctx eq_refl)
             | None => None
             end).
  {
    (* This follows fun_ctx_descend_irrel. *)
    unfold L10.Descend.fun_ctx_descend in Heqmaybe_ctx10.
    unfold L20.Descend.fun_ctx_descend.
    assert (InnerOk: forall (d1: L10.AST.decl)
                            (Edecl1: cd_declmap cd name = Some d1)
                            (d2: L20.AST.decl)
                            (Edecl2: cd_declmap (translate_calldag cd) name = Some d2),
                   L20.Descend.fun_ctx_descend_inner (translate_fun_ctx fc eq_refl) CallOk20 
                                                     eq_refl eq_refl Edecl2
                    =
                   match L10.Descend.fun_ctx_descend_inner fc CallOk10 eq_refl eq_refl Edecl1 with
                   | Some ctx10 => Some (translate_fun_ctx ctx10 eq_refl)
                   | None => None
                   end).
    {
      intros.
      unfold L10.Descend.fun_ctx_descend_inner.
      unfold L20.Descend.fun_ctx_descend_inner.
      remember (fun (depth: nat) (Edepth: cd_depthmap (translate_calldag cd) name = Some depth) =>
          Some
            {|
            fun_name := name;
            fun_depth := depth;
            fun_depth_ok := Edepth;
            fun_decl := d2;
            fun_decl_ok := Edecl2;
            fun_bound_ok := L20.Descend.call_descend'
                              (translate_fun_ctx fc eq_refl) CallOk20 eq_refl eq_refl
                              Edecl2 Edepth |})
        as some_branch_l.
      remember (fun (Edepth: cd_depthmap (translate_calldag cd) name = None) =>
        False_rect (option (fun_ctx (translate_calldag cd) smaller_call_depth_bound))
          (Descend.fun_ctx_descend_helper Edecl2 Edepth))
        as none_branch_l.
      remember (fun (depth: nat) (Edepth: cd_depthmap cd name = Some depth) =>
        Some
          {|
          fun_name := name;
          fun_depth := depth;
          fun_depth_ok := Edepth;
          fun_decl := d1;
          fun_decl_ok := Edecl1;
          fun_bound_ok := L10.Descend.call_descend' fc CallOk10 eq_refl eq_refl Edecl1 Edepth |})
        as some_branch_r.
      remember (fun Edepth : cd_depthmap cd name = None =>
                  False_rect (option (fun_ctx cd smaller_call_depth_bound))
                             (L10.Descend.fun_ctx_descend_helper Edecl1 Edepth))
        as none_branch_r.
      assert (NoneOkL: forall (Edepth: cd_depthmap (translate_calldag cd) name = None),
                         none_branch_l Edepth = None).
      { intro. exfalso. exact (Descend.fun_ctx_descend_helper Edecl2 Edepth). }
      assert (NoneOkR: forall (Edepth: cd_depthmap cd name = None),
                         none_branch_r Edepth = None).
      { intro. exfalso. exact (L10.Descend.fun_ctx_descend_helper Edecl1 Edepth). }
      clear Heqnone_branch_l Heqnone_branch_r.
      revert none_branch_l none_branch_r NoneOkL NoneOkR.
      assert (SomeBranchOk: forall (depth: nat)
                                   (Edepth1: cd_depthmap cd name = Some depth)
                                   (Edepth2: cd_depthmap (translate_calldag cd) name = Some depth),
                     some_branch_l depth Edepth2 
                      =
                     match some_branch_r depth Edepth1 with
                     | Some ctx10 => Some (translate_fun_ctx ctx10 eq_refl)
                     | None => None
                     end).
      {
        intros. subst. unfold translate_fun_ctx. cbn.
        f_equal.
        assert (D: d2 = cached_translated_decl
                {|
                fun_name := name;
                fun_depth := depth;
                fun_depth_ok := Edepth1;
                fun_decl := d1;
                fun_decl_ok := Edecl1;
                fun_bound_ok := L10.Descend.call_descend' fc CallOk10 eq_refl eq_refl Edecl1 Edepth1 |}
                eq_refl).
        {
          unfold cached_translated_decl. cbn.
          remember (translate_fun_ctx_fun_decl_helper _ eq_refl) as Bad. clear HeqBad.
          cbn in Bad. revert Bad.
          rewrite Edecl1.
          intro Bad. clear Bad.
          unfold translate_calldag in Edecl2. cbn in Edecl2. rewrite Edecl1 in Edecl2.
          symmetry in Edecl2. inversion Edecl2. trivial.
        }
        subst. f_equal; apply PropExtensionality.proof_irrelevance.
      } (* SomeBranchOk *)
      clear Heqsome_branch_l Heqsome_branch_r Heqmaybe_ctx10 translate_expr_list Heqtranslate_expr_list
            CallOk10 CallOk20 Edecl1 Edecl2 d1 d2 maybe_ctx10 world' loc args value DoCallOk
            do_call_10 do_call_20.
      assert (R: cd_depthmap (translate_calldag cd) name = cd_depthmap cd name). { trivial. }
      revert some_branch_l some_branch_r SomeBranchOk.
      rewrite R. clear R.
      destruct (cd_depthmap cd name); intros. { apply SomeBranchOk. }
      rewrite (NoneOkL eq_refl).
      rewrite (NoneOkR eq_refl).
      trivial.
    } (* InnerOk *)
    remember L20.Descend.fun_ctx_descend_inner as inner20. clear Heqinner20.
    remember L10.Descend.fun_ctx_descend_inner as inner10. clear Heqinner10.
    subst.
    revert inner10 inner20 InnerOk.
    remember (cd_declmap cd name) as maybe_d1.
    remember (cd_declmap (translate_calldag cd) name) as maybe_d2.
    destruct maybe_d1; destruct maybe_d2; intros. 4:{ trivial. }
    { apply InnerOk. }
    1-2: exfalso; clear inner10 inner20 InnerOk.
    1-2: unfold translate_calldag in Heqmaybe_d2; cbn in Heqmaybe_d2; 
           rewrite<- Heqmaybe_d1 in Heqmaybe_d2; discriminate.
  } (* D *)
  rewrite D.
  assert (DNone := L10.Descend.fun_ctx_descend_none fc CallOk10 eq_refl eq_refl).
  destruct maybe_ctx10.
  { apply DoCallOk. }
  exfalso. rewrite<- Heqmaybe_ctx10 in DNone.
  rewrite<- Heqd in DNone.
  assert (Bad: Some d = None) by tauto.
  discriminate.
}
(* BuiltinCall *)
  assert (L: interpret_expr_list_20 world loc (translate_expr_list args)
               (L20.Callset.callset_descend_builtin_args eq_refl CallOk20)
              =
             interpret_expr_list_10 world loc args 
               (L10.Callset.callset_descend_args eq_refl CallOk10)).
  {
    remember (L20.Callset.callset_descend_builtin_args eq_refl CallOk20) as CallsOk20.
    remember (L10.Callset.callset_descend_args eq_refl CallOk10) as CallsOk10.
    clear CallOk10 HeqCallsOk10 CallOk20 HeqCallsOk20.
    revert world loc. induction args. { now subst. }
    intros. cbn in *.
    assert (CallsOk10' := CallsOk10).
    rewrite FSet.union_subset_and in CallsOk10'.
    rewrite Bool.andb_true_iff in CallsOk10'.
    destruct CallsOk10' as (HeadCallOk, TailCallsOk).
    subst. cbn.
    rewrite (List.Forall_inv H HeadCallOk) by trivial.
    match goal with
    |- (let (_, _) := ?l in _) = let (_, _) := ?r in _ =>
       remember l as lhs_head_result;
       remember r as rhs_head_result
    end.
    assert (R: lhs_head_result = rhs_head_result).
    { subst. f_equal. apply Eqdep_dec.eq_proofs_unicity. decide equality. }
    rewrite<- R.
    clear Heqlhs_head_result Heqrhs_head_result R rhs_head_result.
    destruct lhs_head_result as (world', result_h).
    destruct result_h. 2:{ trivial. }
    now rewrite (IHargs (List.Forall_inv_tail H)
                        (L20.Callset.callset_descend_tail eq_refl CallsOk20)
                        (L10.Callset.callset_descend_tail eq_refl CallsOk10) world' loc).
  }
  rewrite L.
  clear L Heqinterpret_expr_list_10 Heqinterpret_expr_list_20 H.
  destruct (interpret_expr_list_10 world loc args (L10.Callset.callset_descend_args eq_refl CallOk10))
    as (world', result_args).
  destruct result_args. 2:{ trivial. }
  assert (DNone := L10.Descend.fun_ctx_descend_none fc CallOk10 eq_refl eq_refl).
  symmetry in Heqd.
  apply DNone in Heqd.
  rewrite Heqd.
  trivial.
Qed.

(*
Theorem interpret_translated_call {C: VyperConfig}
                                  (builtins: string -> option L10.Interpret.builtin)
                                  {cd: L10.Interpret.calldag}
                                  {call_depth_bound: nat}
                                  (fc: L10.Interpret.fun_ctx cd call_depth_bound)
                                  {cd2: L20.Interpret.calldag}
                                  (ok: cd2 = translate_calldag cd)
                                  (world: world_state)
                                  (arg_values: list uint256):
  L20.Interpret.interpret_call builtins (translate_fun_ctx fc ok) world arg_values
   =
  L10.Interpret.interpret_call builtins fc world arg_values.
Proof.
induction call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (L10.Interpret.fun_bound_ok _ _ fc)). }
pose (is_private_call := fun name: string =>
          match L10.Interpret.cd_declmap _ _ cd name with
          | Some _ => true
          | _ => false
          end).
assert(F: L20.Interpret.fun_decl _ _ (translate_fun_ctx fc ok)
           = 
          translate_decl is_private_call (L10.Interpret.fun_decl _ _ fc)).
{
  clear IHcall_depth_bound.
  unfold translate_fun_ctx in *. cbn in *.
  unfold cached_translated_decl in *.
  remember (translate_fun_ctx_fun_decl_helper fc ok) as foo. clear Heqfoo.
  remember (Interpret.cd_declmap cd2 (L10.Interpret.fun_name cd (S call_depth_bound) fc)) as d.
  destruct d. 2:{ contradiction. }
  subst. cbn in Heqd.
  remember (L10.Interpret.cd_declmap L10.AST.decl L10.Callset.decl_callset cd
                                     (L10.Interpret.fun_name cd (S call_depth_bound) fc)) as x.
  destruct x. 2:{ discriminate. }
  inversion Heqd. unfold is_private_call.
  f_equal. inversion Heqx.
  assert (D := L10.Interpret.fun_decl_ok _ _ fc).
  rewrite D in *. inversion H1. (* XXX *)
  trivial.
}
unfold L20.Interpret.interpret_call.
unfold L10.Interpret.interpret_call.
rewrite F.






  intro H. clear H.
  
  
  
remember  as d10.


unfold translate_fun_ctx. unfold cached_translated_decl.
remember (L10.Interpret.fun_name _ _ fc) as fun_name.

unfold translate_fun_ctx.





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
unfold L10.Interpret.interpret. unfold L20.Interpret.interpret.
remember (L10.Interpret.cd_declmap cd fun_name) as d. 
unfold translate_calldag.
unfold L20.Interpret.make_fun_ctx_and_bound. cbn.
revert translate_dag_helper.
destruct d.
*)

