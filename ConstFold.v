From Coq Require Import String ZArith.
From Vyper Require Import Config L10.Base L20.AST L20.Callset.

(** Do constant folding in expressions.
   (We don't have const declarations yet, so this is going to be somewhat more complicated.) *)
Fixpoint const_fold_expr {C: VyperConfig} (e: expr)
: expr_result expr
:= let fix const_fold_expr_list (l: list expr)
       := match l with
          | nil => ExprSuccess nil
          | (h :: t)%list =>
              match const_fold_expr h, const_fold_expr_list t with
              | ExprAbort ab, _ | _, ExprAbort ab => ExprAbort ab 
              | ExprSuccess h', ExprSuccess t' => ExprSuccess (h' :: t')%list
              end
          end
   in match e with
   | Const _ | LocalVar _ | StorageVar _ => ExprSuccess e
   | UnOp op a =>
      let a' := const_fold_expr a in
      match a' with
      | ExprAbort ab => a'
      | ExprSuccess (Const x) =>
          match L10.Base.interpret_unop op x with
          | ExprAbort ab => ExprAbort ab
          | ExprSuccess val => ExprSuccess (Const val)
          end
      | ExprSuccess x => ExprSuccess (UnOp op x)
      end
   | BinOp op a b =>
      let a' := const_fold_expr a in
      let b' := const_fold_expr b in
      match a', b' with
      | ExprAbort ab, _ | _, ExprAbort ab => ExprAbort ab
      | ExprSuccess (Const x), ExprSuccess (Const y) =>
          match L10.Base.interpret_binop op x y with
          | ExprAbort ab => ExprAbort ab
          | ExprSuccess val => ExprSuccess (Const val)
          end
      | ExprSuccess x, ExprSuccess y => ExprSuccess (BinOp op x y)
      end
   | IfThenElse cond yes no =>
      let yes'  := const_fold_expr yes  in
      let no'   := const_fold_expr no   in
      match const_fold_expr cond with
      | ExprAbort ab => ExprAbort ab
      | ExprSuccess (Const x) => if (Z_of_uint256 x =? 0)%Z then no' else yes'
      | ExprSuccess cond' =>
          match yes', no' with
          | ExprAbort ab, _ | _, ExprAbort ab => ExprAbort ab
          | ExprSuccess x, ExprSuccess y => ExprSuccess (IfThenElse cond' x y)
          end
      end
   | LogicalAnd a b =>
      match const_fold_expr a with
      | ExprAbort ab => ExprAbort ab
      | ExprSuccess (Const x) => if (Z_of_uint256 x =? 0)%Z
                                   then ExprSuccess (Const x)
                                   else const_fold_expr b
      | ExprSuccess a' => match const_fold_expr b with
                          | ExprAbort ab => ExprAbort ab
                          | ExprSuccess b' => ExprSuccess (LogicalAnd a' b')
                          end
      end
   | LogicalOr a b =>
      match const_fold_expr a with
      | ExprAbort ab => ExprAbort ab
      | ExprSuccess (Const x) => if (Z_of_uint256 x =? 0)%Z
                                   then const_fold_expr b
                                   else ExprSuccess (Const x)
      | ExprSuccess a' => match const_fold_expr b with
                          | ExprAbort ab => ExprAbort ab
                          | ExprSuccess b' => ExprSuccess (LogicalOr a' b')
                          end
      end
   | PrivateCall name args => match const_fold_expr_list args with
                              | ExprAbort ab => ExprAbort ab
                              | ExprSuccess args' => ExprSuccess (PrivateCall name args')
                              end
   | BuiltinCall name args => match const_fold_expr_list args with
                              | ExprAbort ab => ExprAbort ab
                              | ExprSuccess args' => ExprSuccess (BuiltinCall name args')
                              end
   end.


(** Constant folding cannot add new calls. *)
Lemma callset_const_fold_expr {C: VyperConfig}
                              {e e': expr}
                              (ok: const_fold_expr e = ExprSuccess e'):
  let _ := string_set_impl in
  FSet.is_subset (expr_callset e') (expr_callset e) = true.
Proof.
rewrite FSet.is_subset_ok. intro s.
enough (H: let _ := string_set_impl in
           FSet.has (expr_callset e') s = true -> FSet.has (expr_callset e) s = true).
{
  cbn in H.
  destruct (FSet.has (expr_callset e) s); destruct (FSet.has (expr_callset e') s); try easy.
  tauto.
}
cbn. revert e' ok. induction e using expr_ind'; intros; inversion ok; subst; cbn in *.
{ (* Const *) assumption. }
{ (* LocalVar *) assumption. }
{ (* StorageVar *) assumption. }
{ (* UnOp *)
  destruct (const_fold_expr e). 2:discriminate.
  apply (IHe value eq_refl).
  destruct value; cbn; inversion ok; try subst e'; try apply H.
  destruct (interpret_unop op val). 2:discriminate.
  inversion ok. subst e'. apply H.
}
{ (* BinOp *)
  rewrite FSet.union_ok; apply Bool.orb_true_intro.
  assert (D: forall A A' B B': Prop, (A -> A') -> (B -> B') -> (A \/ B) -> (A' \/ B')) by tauto.
  destruct (const_fold_expr e1). 2:discriminate.
  destruct value; cbn.
  { (* e1 is Const *)
    destruct (const_fold_expr e2). 2:discriminate.
    enough (E2: let _ := string_set_impl in FSet.has ((expr_callset e2)) s = true).
    { cbn in E2. rewrite E2. now right. }
    cbn. apply (IHe2 value eq_refl).
    destruct value; cbn; inversion ok; try subst e'; cbn in H;
      try rewrite FSet.union_ok in H;
      try rewrite FSet.empty_ok in H;
      try rewrite Bool.orb_false_l in H;
      try easy.
    (* e2 is Const *)
    destruct (interpret_binop op val). 2:discriminate.
    inversion ok. subst e'. cbn in H. now rewrite FSet.empty_ok in H.
  }
  1-9:destruct (const_fold_expr e2); try discriminate;
      inversion ok; subst e'; cbn in H;
      try rewrite FSet.union_ok in H;
      try rewrite FSet.empty_ok in H;
      try rewrite Bool.orb_false_l in H;
      apply (D _ _ _ _ (IHe1 _ eq_refl) (IHe2 _ eq_refl));
      cbn; try repeat rewrite FSet.union_ok;
      try repeat rewrite FSet.union_ok in H;
      try apply Bool.orb_prop in H; tauto.
}
{ (* IfThenElse *)
  repeat rewrite FSet.union_ok. repeat rewrite Bool.orb_true_iff.
  assert (D: forall A A' B B' C C': Prop, (A -> A') -> (B -> B') -> (C -> C')
                                            -> (A \/ B \/ C) -> (A' \/ B' \/ C')) by tauto.
  destruct (const_fold_expr e1). 2:discriminate.
  destruct value.
  { (* Const *)
    destruct (Z_of_uint256 val =? 0)%Z.
    {
      destruct (const_fold_expr e3). 2:discriminate.
      inversion ok. subst e'.
      repeat rewrite FSet.union_ok.
      rewrite (IHe3 _ eq_refl H).
      right. right. trivial.
    }
    (* same as in the previous branch but we dig into "yes" (e2) this time *)
    destruct (const_fold_expr e2). 2:discriminate.
    inversion ok. subst e'.
    repeat rewrite FSet.union_ok.
    rewrite (IHe2 _ eq_refl H).
    right. left. trivial.
  }
  1-9:destruct (const_fold_expr e2) as [v2|]; try discriminate;
      destruct (const_fold_expr e3) as [v3|]; try discriminate;
      inversion ok; subst e'; cbn in H;
      repeat rewrite FSet.union_ok in H;
      repeat rewrite FSet.empty_ok in H;
      apply (D _ _ _ _ _ _ (IHe1 _ eq_refl) (IHe2 _ eq_refl) (IHe3 _ eq_refl));
      repeat rewrite Bool.orb_true_iff in H; cbn; try rewrite FSet.empty_ok;
      repeat rewrite FSet.union_ok; repeat rewrite Bool.orb_true_iff; tauto.
}
{ (* LogicalAnd *)
  rewrite FSet.union_ok; apply Bool.orb_true_intro.
  assert (D: forall A A' B B': Prop, (A -> A') -> (B -> B') -> (A \/ B) -> (A' \/ B')) by tauto.
  destruct (const_fold_expr e1). 2:discriminate.
  destruct value; cbn.
  { (* e1 is Const *)
    destruct (Z_of_uint256 val =? 0)%Z.
    { inversion ok. subst e'. cbn in H. rewrite FSet.empty_ok in H. discriminate. }
    right. apply (IHe2 _ ok H).
  }
  1-9:destruct (const_fold_expr e2) as [v2|]; try discriminate;
      inversion ok; subst e'; cbn in H;
      repeat rewrite FSet.union_ok in H;
      repeat rewrite FSet.empty_ok in H;
      apply (D _ _ _ _ (IHe1 _ eq_refl) (IHe2 _ eq_refl));
      repeat rewrite Bool.orb_true_iff in H; cbn; try rewrite FSet.empty_ok;
      repeat rewrite FSet.union_ok; repeat rewrite Bool.orb_true_iff; tauto.
}
{ (* LogicalOr *)
  rewrite FSet.union_ok; apply Bool.orb_true_intro.
  assert (D: forall A A' B B': Prop, (A -> A') -> (B -> B') -> (A \/ B) -> (A' \/ B')) by tauto.
  destruct (const_fold_expr e1). 2:discriminate.
  destruct value; cbn.
  { (* e1 is Const *)
    destruct (Z_of_uint256 val =? 0)%Z.
    right. apply (IHe2 _ ok H).
    { inversion ok. subst e'. cbn in H. rewrite FSet.empty_ok in H. discriminate. }
  }
  1-9:destruct (const_fold_expr e2) as [v2|]; try discriminate;
      inversion ok; subst e'; cbn in H;
      repeat rewrite FSet.union_ok in H;
      repeat rewrite FSet.empty_ok in H;
      apply (D _ _ _ _ (IHe1 _ eq_refl) (IHe2 _ eq_refl));
      repeat rewrite Bool.orb_true_iff in H; cbn; try rewrite FSet.empty_ok;
      repeat rewrite FSet.union_ok; repeat rewrite Bool.orb_true_iff; tauto.
}
{ (* PrivateCall *)
  rewrite FSet.add_ok. destruct (string_dec name s) as [_|NE]. { trivial. }
  clear H2. rename H into F. rename H0 into H. (* XXX *)
  revert e' ok H. induction args as [|head]; intros.
  {
    inversion ok. subst e'. cbn in H.
    rewrite FSet.add_ok in H.
    destruct (string_dec name s). { contradiction. } exact H.
  }
  assert (FH := List.Forall_inv F). cbn in FH.
  destruct (const_fold_expr head). 2:discriminate.
  assert (FHvalue := FH value eq_refl). clear FH.
  rewrite FSet.union_ok.
  destruct (_ args). 2:discriminate.
  inversion ok. subst e'.
  cbn in H. rewrite FSet.add_ok in H.
  destruct (string_dec name s) as [|_]. { contradiction. }
  rewrite FSet.union_ok in H.
  rewrite Bool.orb_true_iff in H.
  rewrite Bool.orb_true_iff.
  assert (IH := IHargs (List.Forall_inv_tail F) _ eq_refl).
  cbn in IH. rewrite FSet.add_ok in IH.
  destruct (string_dec name s) as [|_]. { contradiction. }
  tauto.
}
(* BuiltinCall *)
clear H2. rename H into F. rename H0 into H. (* XXX *)
revert e' ok H. induction args as [|head]; intros.
{ inversion ok. subst e'. cbn in H. exact H. }
assert (FH := List.Forall_inv F). cbn in FH.
destruct (const_fold_expr head). 2:discriminate.
assert (FHvalue := FH value eq_refl). clear FH.
rewrite FSet.union_ok.
destruct (_ args). 2:discriminate.
inversion ok. subst e'.
cbn in H.
rewrite FSet.union_ok in H.
rewrite Bool.orb_true_iff in H.
rewrite Bool.orb_true_iff.
assert (IH := IHargs (List.Forall_inv_tail F) _ eq_refl).
cbn in IH.
tauto.
Qed.


Definition expr_result_map {C: VyperConfig} {A B} (f: A -> B) (e: expr_result A)
: expr_result B
:= match e with
   | ExprSuccess a => ExprSuccess (f a)
   | ExprAbort ab => ExprAbort ab
   end.

Definition const_fold_small_stmt {C: VyperConfig} (ss: small_stmt)
: expr_result small_stmt
:= match ss with
   | Pass | Abort _ => ExprSuccess ss
   | Return     e => expr_result_map Return       (const_fold_expr e)
   | Raise      e => expr_result_map Raise        (const_fold_expr e)
   | Assign lhs e => expr_result_map (Assign lhs) (const_fold_expr e)
   | ExprStmt   e => expr_result_map ExprStmt     (const_fold_expr e)
   end.

Lemma callset_const_fold_small_stmt {C: VyperConfig}
                                    {ss ss': small_stmt}
                                    (ok: const_fold_small_stmt ss = ExprSuccess ss'):
  let _ := string_set_impl in
  FSet.is_subset (small_stmt_callset ss') (small_stmt_callset ss) = true.
Proof.
cbn. destruct ss; cbn in ok; unfold expr_result_map in *.
1-2: (* Pass, Abort *) inversion ok; subst ss'; apply FSet.is_subset_refl.
1-4:
  remember (const_fold_expr _) as z; symmetry in Heqz; destruct z; try discriminate;
  assert (E := callset_const_fold_expr Heqz); cbn in E;
  inversion ok; subst ss'; apply E.
Qed.


Definition expr_result_ap {C: VyperConfig} {A B} (f: expr_result (A -> B)) (e: expr_result A)
: expr_result B
:= match f with
   | ExprSuccess g => match e with
                      | ExprSuccess a => ExprSuccess (g a)
                      | ExprAbort ab => ExprAbort ab
                      end
   | ExprAbort ab => ExprAbort ab
   end.

Fixpoint const_fold_stmt {C: VyperConfig} (s: stmt)
: expr_result stmt
:= match s with
   | SmallStmt ss => expr_result_map SmallStmt (const_fold_small_stmt ss)
   | LocalVarDecl name init body =>
        expr_result_ap (expr_result_map (LocalVarDecl name) (const_fold_expr init))
                       (const_fold_stmt body)
   | IfElseStmt cond yes no =>
        (* no attempt is made here to throw away the unused branch if [cond] is a constant. *)
        expr_result_ap (expr_result_ap (expr_result_map IfElseStmt (const_fold_expr cond))
                                       (const_fold_stmt yes))
                       (const_fold_stmt no)
   | Loop name init count body =>
        expr_result_ap (expr_result_map
                         (fun f => f count)
                         (expr_result_map (Loop name) (const_fold_expr init)))
                       (const_fold_stmt body)
   | Semicolon a b =>
        expr_result_ap (expr_result_map Semicolon (const_fold_stmt a))
                       (const_fold_stmt b)
   end.

Lemma callset_const_fold_stmt {C: VyperConfig}
                              {s s': stmt}
                              (ok: const_fold_stmt s = ExprSuccess s'):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset s') (stmt_callset s) = true.
Proof.
cbn.
revert s' ok.
induction s; intros; cbn in ok; unfold expr_result_map in *; unfold expr_result_ap in *; cbn.
{ (* SmallStmt *)
  remember (const_fold_small_stmt _) as z; symmetry in Heqz; destruct z; try discriminate.
  inversion ok; subst s'.
  apply (callset_const_fold_small_stmt Heqz).
}
{ (* LocalVarDecl *)
  remember (const_fold_expr _) as init'; symmetry in Heqinit'; destruct init'; try discriminate.
  remember (const_fold_stmt _) as body'; symmetry in Heqbody'; destruct body'; try discriminate.
  assert (InitOk := callset_const_fold_expr Heqinit').
  assert (BodyOk := IHs _ eq_refl).
  inversion ok; subst s'.
  cbn in *.
  now apply FSet.union_monotonic.
}
{ (* IfElseStmt *)
  rename s1 into yes. rename IHs1 into IHyes. rename s2 into no. rename IHs2 into IHno.
  remember (const_fold_expr cond) as cond'; symmetry in Heqcond'; destruct cond'; try discriminate.
  remember (const_fold_stmt yes)  as yes';  symmetry in Heqyes';  destruct yes';  try discriminate.
  remember (const_fold_stmt no)   as no';   symmetry in Heqno';   destruct no';   try discriminate.
  assert (CondOk := callset_const_fold_expr Heqcond').
  assert (YesOk := IHyes _ eq_refl).
  assert (NoOk := IHno _ eq_refl).
  inversion ok; subst s'.
  cbn in *.
  apply FSet.union_monotonic. { assumption. }
  now apply FSet.union_monotonic.
}
{ (* Loop *)
  remember (const_fold_expr start) as start'; symmetry in Heqstart'; destruct start'; try discriminate.
  remember (const_fold_stmt _)     as body';  symmetry in Heqbody';  destruct body';  try discriminate.
  assert (StartOk := callset_const_fold_expr Heqstart').
  assert (BodyOk := IHs _ eq_refl).
  inversion ok; subst s'.
  cbn in *.
  now apply FSet.union_monotonic.
}
(* Semicolon *)
remember (const_fold_stmt s1) as s1'; symmetry in Heqs1'; destruct s1'; try discriminate.
remember (const_fold_stmt s2) as s2'; symmetry in Heqs2'; destruct s2'; try discriminate.
assert (Ok1 := IHs1 _ eq_refl).
assert (Ok2 := IHs2 _ eq_refl).
inversion ok; subst s'.
cbn in *.
now apply FSet.union_monotonic.
Qed.


Definition const_fold_decl {C: VyperConfig} (d: decl)
: expr_result decl
:= match d with
   | StorageVarDecl name => ExprSuccess d
   | FunDecl name arg_names body =>
       expr_result_map (FunDecl name arg_names) (const_fold_stmt body)
   end.

(*
Lemma interpret_const_fold_expr {C: VyperConfig}
                                {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                (builtins: string -> option builtin)
                                {cd cd': L20.Descend.calldag}
                                (fc fc': fun_ctx cd bigger_call_depth_bound)
                                {do_call: forall
                                      (smaller_fc: fun_ctx cd smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                {do_call': forall
                                      (smaller_fc: fun_ctx cd' smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                (DoCallOk: forall smaller_fc world arg_values,
                                             do_call smaller_fc world arg_values
                                              =
                                             do_call' smaller_fc' world arg_values)
                                (world: world_state)
                                (loc: string_map uint256)
                                {e e': expr}
                                (ExprOk: const_fold_expr e = ExprSuccess e')
                                (CallOk: let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e)
                                                  (L20.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk10: let _ := string_set_impl in 
                                   FSet.is_subset (L10.Callset.expr_callset e10)
                                                  (L10.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
 *)