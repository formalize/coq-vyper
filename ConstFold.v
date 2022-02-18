From Coq Require Import String ZArith Lia.
From Coq Require PropExtensionality.
From Vyper Require Import Config UInt256 Calldag.
From Vyper.L20 Require Import AST Callset Descend Expr Stmt.

(** Do constant folding in expressions.
   (We don't have const declarations yet,
    once we do, this will be somewhat more complicated.) *)
Fixpoint const_fold_expr {C: VyperConfig} (e: expr)
: string + expr
:= let fix const_fold_expr_list (l: list expr)
       := match l with
          | nil => inr nil
          | (h :: t)%list =>
              match const_fold_expr h, const_fold_expr_list t with
              | inl err, _ | _, inl err => inl err
              | inr h', inr t' => inr (h' :: t')%list
              end
          end
   in match e with
   | Const _ | LocalVar _ | StorageVar _ => inr e
   | UnOp op a =>
      let a' := const_fold_expr a in
      match a' with
      | inl _ => a'
      | inr (Const x) =>
          match interpret_unop op x with
          | Some val => inr (Const val)
          | None => inl ("arithmetic error in unary " ++ L10.ToString.string_of_unop op)%string
          end
      | inr x => inr (UnOp op x)
      end
   | BinOp op a b =>
      let a' := const_fold_expr a in
      let b' := const_fold_expr b in
      match a', b' with
      | inl err, _ | _, inl err => inl err
      | inr (Const x), inr (Const y) =>
          match interpret_binop op x y with
          | Some val => inr (Const val)
          | None => inl ("arithmetic error in binary" ++ L10.ToString.string_of_binop op)%string
          end
      | inr x, inr y => inr (BinOp op x y)
      end
   | IfThenElse cond yes no =>
      let yes'  := const_fold_expr yes  in
      let no'   := const_fold_expr no   in
      match const_fold_expr cond with
      | inl err => inl err
      | inr (Const x) => if (Z_of_uint256 x =? 0)%Z then no' else yes'
      | inr cond' =>
          match yes', no' with
          | inl err, _ | _, inl err => inl err
          | inr x, inr y => inr (IfThenElse cond' x y)
          end
      end
   | LogicalAnd a b =>
      match const_fold_expr a with
      | inl err => inl err
      | inr (Const x) => if (Z_of_uint256 x =? 0)%Z
                                   then inr (Const x)
                                   else const_fold_expr b
      | inr a' => match const_fold_expr b with
                  | inl err => inl err
                  | inr b' => inr (LogicalAnd a' b')
                  end
      end
   | LogicalOr a b =>
      match const_fold_expr a with
      | inl err => inl err
      | inr (Const x) => if (Z_of_uint256 x =? 0)%Z
                           then const_fold_expr b
                           else inr (Const x)
      | inr a' => match const_fold_expr b with
                  | inl err => inl err
                  | inr b' => inr (LogicalOr a' b')
                  end
      end
   | PrivateCall name args => match const_fold_expr_list args with
                              | inl err => inl err
                              | inr args' => inr (PrivateCall name args')
                              end
   | BuiltinCall name args => match const_fold_expr_list args with
                              | inl err => inl err
                              | inr args' => inr (BuiltinCall name args')
                              end
   end.


(** Constant folding cannot add new calls. *)
Lemma callset_const_fold_expr {C: VyperConfig}
                              {e e': expr}
                              (ok: const_fold_expr e = inr e'):
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
  destruct (const_fold_expr e). { discriminate. }
  apply (IHe _ eq_refl).
  destruct e0; cbn; inversion ok; try subst e'; try apply H. (* XXX: e0 *)
  destruct (interpret_unop op val). 2:discriminate.
  { inversion ok. subst e'. apply H. }
}
{ (* BinOp *)
  rewrite FSet.union_ok; apply Bool.orb_true_intro.
  assert (D: forall A A' B B': Prop, (A -> A') -> (B -> B') -> (A \/ B) -> (A' \/ B')) by tauto.
  destruct (const_fold_expr e1). discriminate.
  destruct e; cbn.
  { (* e1 is Const *)
    destruct (const_fold_expr e2). discriminate.
    enough (E2: let _ := string_set_impl in FSet.has ((expr_callset e2)) s = true).
    { cbn in E2. rewrite E2. now right. }
    cbn. apply (IHe2 _ eq_refl).
    destruct e; cbn; inversion ok; try subst e'; cbn in H;
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
  destruct (const_fold_expr e1). discriminate.
  destruct e.
  { (* Const *)
    destruct (Z_of_uint256 val =? 0)%Z.
    {
      destruct (const_fold_expr e3). discriminate.
      inversion ok. subst e'.
      repeat rewrite FSet.union_ok.
      rewrite (IHe3 _ eq_refl H).
      right. right. trivial.
    }
    (* same as in the previous branch but we dig into "yes" (e2) this time *)
    destruct (const_fold_expr e2). discriminate.
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
  destruct (const_fold_expr e1). discriminate.
  destruct e; cbn.
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
  destruct (const_fold_expr e1). discriminate.
  destruct e; cbn.
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
  destruct (const_fold_expr head). discriminate.
  assert (FHvalue := FH _ eq_refl). clear FH.
  rewrite FSet.union_ok.
  destruct (_ args). discriminate.
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
destruct (const_fold_expr head). discriminate.
assert (FHvalue := FH _ eq_refl). clear FH.
rewrite FSet.union_ok.
destruct (_ args). discriminate.
inversion ok. subst e'.
cbn in H.
rewrite FSet.union_ok in H.
rewrite Bool.orb_true_iff in H.
rewrite Bool.orb_true_iff.
assert (IH := IHargs (List.Forall_inv_tail F) _ eq_refl).
cbn in IH.
tauto.
Qed.


Definition sum_map {C: VyperConfig} {Err A B} (f: A -> B) (e: Err + A)
: Err + B
:= match e with
   | inl err => inl err
   | inr a => inr (f a)
   end.

Definition const_fold_small_stmt {C: VyperConfig} (ss: small_stmt)
: string + small_stmt
:= match ss with
   | Pass | Abort _ => inr ss
   | Return     e => sum_map Return       (const_fold_expr e)
   | Raise      e => sum_map Raise        (const_fold_expr e)
   | Assign lhs e => sum_map (Assign lhs) (const_fold_expr e)
   | ExprStmt   e => sum_map ExprStmt     (const_fold_expr e)
   end.

Lemma callset_const_fold_small_stmt {C: VyperConfig}
                                    {ss ss': small_stmt}
                                    (ok: const_fold_small_stmt ss = inr ss'):
  let _ := string_set_impl in
  FSet.is_subset (small_stmt_callset ss') (small_stmt_callset ss) = true.
Proof.
cbn. destruct ss; cbn in ok; unfold sum_map in *.
1-2: (* Pass, Abort *) inversion ok; subst ss'; apply FSet.is_subset_refl.
1-4:
  remember (const_fold_expr _) as z; symmetry in Heqz; destruct z; try discriminate;
  assert (E := callset_const_fold_expr Heqz); cbn in E;
  inversion ok; subst ss'; apply E.
Qed.


Definition sum_ap {C: VyperConfig} {Err A B} (f: Err + (A -> B)) (e: Err + A)
: Err + B
:= match f with
   | inr g => match e with
              | inr a => inr (g a)
              | inl err => inl err
              end
   | inl err => inl err
   end.

Fixpoint const_fold_stmt {C: VyperConfig} (s: stmt)
: string + stmt
:= match s with
   | SmallStmt ss => sum_map SmallStmt (const_fold_small_stmt ss)
   | LocalVarDecl name init body =>
        sum_ap (sum_map (LocalVarDecl name) (const_fold_expr init))
               (const_fold_stmt body)
   | IfElseStmt cond yes no =>
        (* no attempt is made here to throw away the unused branch if [cond] is a constant. *)
        sum_ap (sum_ap (sum_map IfElseStmt (const_fold_expr cond))
                       (const_fold_stmt yes))
               (const_fold_stmt no)
   | Loop name init count body =>
        sum_ap (sum_map (fun f => f count)
                        (sum_map (Loop name) (const_fold_expr init)))
               (const_fold_stmt body)
   | Semicolon a b =>
        sum_ap (sum_map Semicolon (const_fold_stmt a)) (const_fold_stmt b)
   end.

Lemma callset_const_fold_stmt {C: VyperConfig}
                              {s s': stmt}
                              (ok: const_fold_stmt s = inr s'):
  let _ := string_set_impl in
  FSet.is_subset (stmt_callset s') (stmt_callset s) = true.
Proof.
cbn.
revert s' ok.
induction s; intros; cbn in ok; unfold sum_map in *; unfold sum_ap in *; cbn.
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
: string + decl
:= match d with
   | StorageVarDecl name => inr d
   | FunDecl name arg_names body =>
       sum_map (FunDecl name arg_names) (const_fold_stmt body)
   end.

Lemma callset_const_fold_decl {C: VyperConfig}
                              {d d': decl}
                              (ok: const_fold_decl d = inr d'):
  let _ := string_set_impl in
  FSet.is_subset (decl_callset d') (decl_callset d) = true.
Proof.
destruct d; cbn in *.
{ inversion ok. subst d'. cbn. apply FSet.is_subset_refl. }
remember (const_fold_stmt body) as body'. symmetry in Heqbody'. destruct body'. { easy. }
cbn in ok. inversion ok. subst d'. cbn.
now apply callset_const_fold_stmt.
Qed.

Definition const_fold_calldag {C: VyperConfig} (cd: calldag)
:= calldag_maybe_map const_fold_decl (@callset_const_fold_decl C) cd.

Definition const_fold_fun_ctx {C: VyperConfig}
          {bound: nat}
          {cd cd': calldag}
          (Ok: const_fold_calldag cd = inr cd')
: fun_ctx cd bound -> fun_ctx cd' bound
:= fun_ctx_maybe_map const_fold_decl (@callset_const_fold_decl C) Ok.

(*************************************************************************************)

Lemma weak_interpret_const_fold_expr_list
              {C: VyperConfig}
              {(*bigger_call_depth_bound*) smaller_call_depth_bound: nat}
              (*(Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)*)
              (builtins: string -> option L10.Base.builtin)
              {cd cd': calldag}
              (ok: const_fold_calldag cd = inr cd')
              (fc: fun_ctx cd (S smaller_call_depth_bound))
              {do_call: forall
                    (smaller_fc: fun_ctx cd smaller_call_depth_bound)
                    (world: world_state)
                    (arg_values: list uint256),
                  world_state * L10.Base.expr_result uint256}
              {do_call': forall
                    (smaller_fc: fun_ctx cd' smaller_call_depth_bound)
                    (world: world_state)
                    (arg_values: list uint256),
                  world_state * L10.Base.expr_result uint256}
              (DoCallOk: forall smaller_fc world arg_values,
                           do_call' (const_fold_fun_ctx ok smaller_fc) world arg_values
                            =
                           do_call smaller_fc world arg_values)
              (world: world_state)
              (loc: string_map uint256)
              {l l': list expr}
              (ExprOk: (fix const_fold_expr_list (l: list expr)
                        := match l with
                           | nil => inr nil
                           | (h :: t)%list =>
                               match const_fold_expr h, const_fold_expr_list t with
                               | inl err, _ | _, inl err => inl err
                               | inr h', inr t' => inr (h' :: t')%list
                               end
                           end) l = inr l')
              (CallOk': let _ := string_set_impl in
                 FSet.is_subset (expr_list_callset l')
                                (decl_callset
                                   (fun_decl
                                     (const_fold_fun_ctx ok fc)))
                 = true)
              (CallOk: let _ := string_set_impl in
                 FSet.is_subset (expr_list_callset l)
                                (decl_callset (fun_decl fc))
                 = true)
              (ItemsOk: List.Forall
                  (fun e : expr =>
                   forall e' : expr,
                   const_fold_expr e = inr e' ->
                   forall
                     (CallOk : let H := string_set_impl in
                               FSet.is_subset (expr_callset e) (decl_callset (fun_decl fc)) = true)
                     (CallOk' : let H := string_set_impl in
                                FSet.is_subset (expr_callset e')
                                  (decl_callset (fun_decl (const_fold_fun_ctx ok fc))) = true)
                     (world : world_state) (loc : string_map uint256),
                   interpret_expr eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world loc e' CallOk' =
                   interpret_expr eq_refl fc do_call builtins world loc e CallOk) l):
   interpret_expr_list eq_refl (const_fold_fun_ctx ok fc)
                       do_call' builtins
                       world loc l' CallOk'
    =
   interpret_expr_list eq_refl fc
                       do_call builtins
                       world loc l CallOk.
Proof.
revert l' ExprOk CallOk' world loc. induction l as [|lhead]; intros.
{ inversion ExprOk. now subst l'. }
remember (const_fold_expr lhead) as chead. symmetry in Heqchead.
destruct chead. { discriminate. }
assert (HeadItemOk := List.Forall_inv ItemsOk).
assert (TailItemsOk := List.Forall_inv_tail ItemsOk).
remember ((fix const_fold_expr_list (l : list expr) : string + list expr :=
              match l with
              | nil => inr nil
              | (h :: t)%list =>
                  match const_fold_expr h with
                  | inl err => inl err
                  | inr h' =>
                      match const_fold_expr_list t with
                      | inl err => inl err
                      | inr t' => inr (h' :: t')%list
                      end
                  end
              end) l) as c'.
symmetry in Heqc'.
destruct c'. { discriminate. }
inversion ExprOk. subst l'.
cbn.
rewrite (HeadItemOk _ Heqchead
                    (callset_descend_head eq_refl CallOk)
                    (callset_descend_head eq_refl CallOk')).
destruct interpret_expr as (world', result_h). destruct result_h. 2:{ trivial. }
now rewrite (IHl (callset_descend_tail eq_refl CallOk) TailItemsOk _ eq_refl
                 (callset_descend_tail eq_refl CallOk')).
Qed.


Lemma interpret_const_fold_expr {C: VyperConfig}
                                {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                (builtins: string -> option L10.Base.builtin)
                                {cd cd': calldag}
                                (ok: const_fold_calldag cd = inr cd')
                                (fc: fun_ctx cd bigger_call_depth_bound)
                                {do_call: forall
                                      (smaller_fc: fun_ctx cd smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * L10.Base.expr_result uint256}
                                {do_call': forall
                                      (smaller_fc: fun_ctx cd' smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * L10.Base.expr_result uint256}
                                (DoCallOk: forall smaller_fc world arg_values,
                                             do_call' (const_fold_fun_ctx ok smaller_fc) world arg_values
                                              =
                                             do_call smaller_fc world arg_values)
                                (world: world_state)
                                (loc: string_map uint256)
                                {e e': expr}
                                (ExprOk: const_fold_expr e = inr e')
                                (CallOk': let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e')
                                                  (decl_callset
                                                     (fun_decl
                                                       (const_fold_fun_ctx ok fc)))
                                   = true)
                                (CallOk: let _ := string_set_impl in
                                   FSet.is_subset (expr_callset e)
                                                  (decl_callset (fun_decl fc))
                                   = true):
   interpret_expr Ebound (const_fold_fun_ctx ok fc)
                  do_call' builtins
                  world loc e' CallOk'
    =
   interpret_expr Ebound fc
                  do_call builtins
                  world loc e CallOk.
Proof.
revert e' ExprOk CallOk CallOk' world loc. induction e using expr_ind'; intros;
  cbn in ExprOk; inversion ExprOk; subst.
(* Const, LocalVar *) 1-2: reflexivity.
{ (* StorageVar *)
  cbn.
  unfold storage_var_is_declared.
  assert (F := calldag_maybe_map_declmap const_fold_decl (@callset_const_fold_decl C) ok name).
  destruct (cd_declmap cd name), (cd_declmap cd' name); try easy.
  destruct d; cbn in F; inversion F. { now subst. }
  remember (const_fold_stmt body) as body'.
  destruct body'. { discriminate. }
  inversion F. now subst.
}
{ (* UnOp *)
  remember (const_fold_expr e) as ce.
  destruct ce as [|arg]. { discriminate. }
  destruct arg.
  { (* arg is const, so interpret immediately *)
    remember (interpret_unop op val) as unop_result. destruct unop_result. 2:discriminate.
    inversion ExprOk. subst e'. cbn.
    rewrite<- (IHe _ eq_refl _ CallOk').
    cbn. unfold Base.interpret_unop.
    now rewrite<- Hequnop_result.
  }
  (* arg is not const *)
  1-9: inversion ExprOk; subst e';
       assert (IH := IHe _ eq_refl
                      (callset_descend_unop eq_refl CallOk) 
                      (callset_descend_unop eq_refl CallOk')
                      world loc);
       cbn; now rewrite<- IH.
}
{ (* BinOp *)
  assert (BinOpOk:
    forall (e1' e2': expr) CallOk' CallOk
           (Left: interpret_expr eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world loc
                                e1' (callset_descend_binop_left eq_refl CallOk') 
                    =
                  interpret_expr eq_refl fc do_call builtins world loc e1
                                 (callset_descend_binop_left eq_refl CallOk))
           (Right: forall world loc,
                     interpret_expr eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world loc e2'
                                    (callset_descend_binop_right eq_refl CallOk') 
                      =
                     interpret_expr eq_refl fc do_call builtins world loc e2
                                    (callset_descend_binop_right eq_refl CallOk)),
          interpret_expr eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world loc
                         (BinOp op e1' e2') CallOk'
           =
          interpret_expr eq_refl fc do_call builtins world loc (BinOp op e1 e2) CallOk).
  {
    intros.
    cbn. rewrite<- Left. cbn.
    match goal with
    |- (let (world', result_a) := ?x in _) = _ =>
          destruct x as (world', result_a)
    end.
    destruct result_a. 2:reflexivity.
    cbn. now rewrite Right.
  }
  remember (const_fold_expr e1) as ce1.
  destruct ce1 as [|arg1]. { discriminate. }
  destruct arg1; remember (const_fold_expr e2) as ce2; destruct ce2 as [|arg2]; try discriminate.
  { (* arg1 is const, so check out arg2 *)
    destruct arg2.
    { (* arg2 is const, so interpret immediately *)
      remember (interpret_binop op _ _) as binop_result. destruct binop_result. 2:discriminate.
      inversion ExprOk. subst e'. cbn.
      rewrite<- (IHe1 _ eq_refl _ CallOk').
      cbn.
      rewrite<- (IHe2 _ eq_refl _ CallOk').
      unfold Base.interpret_binop. cbn.
      now rewrite<- Heqbinop_result.
    }
    (* arg2 is not const *)
    1-9: inversion ExprOk; subst e';
         assert (IH1 := IHe1 _ eq_refl
                        (callset_descend_binop_left eq_refl CallOk)
                        (callset_descend_binop_left eq_refl CallOk')
                        world loc);
         assert (IH2 := IHe2 _ eq_refl
                        (callset_descend_binop_right eq_refl CallOk)
                        (callset_descend_binop_right eq_refl CallOk')
                        world loc);
         cbn; rewrite<- IH1; cbn; now rewrite<- IH2.
  }
  (* arg1 is not const *)
  1-9: inversion ExprOk; subst e';
        assert (IH1 := IHe1 _ eq_refl
                       (callset_descend_binop_left eq_refl CallOk)
                       (callset_descend_binop_left eq_refl CallOk')
                       world loc);
        assert (IH2 := IHe2 _ eq_refl
                       (callset_descend_binop_right eq_refl CallOk)
                       (callset_descend_binop_right eq_refl CallOk'));
        apply (BinOpOk _ _ CallOk' CallOk IH1 IH2).
}
{ (* IfThenElse *)
  rename e1 into cond. rename IHe1 into IHcond.
  rename e2 into yes. rename IHe2 into IHyes.
  rename e3 into no. rename IHe3 into IHno.
  remember (const_fold_expr cond) as cc. destruct cc as [|cc]. { discriminate. }
  cbn.
  destruct cc.
  { (* cond is a const *)
    rewrite<- (IHcond _ eq_refl
                      (callset_descend_if_cond eq_refl CallOk)
                      FSet.empty_subset).
    cbn.
    destruct (Z_of_uint256 val =? 0)%Z.
    { now apply IHno. }
    now apply IHyes.
  }
  (* cond is not const *)
  1-9: remember (const_fold_expr yes) as cyes; destruct cyes as [|cyes]; try discriminate;
       remember (const_fold_expr no)  as cno;  destruct cno  as [|cno];  try discriminate;
       inversion ExprOk; subst e';
       try match goal with
           | H: inr ?c = const_fold_expr _ |- _ => remember c as cond'
           end;
       rewrite<- (IHcond _ eq_refl
                        (callset_descend_if_cond eq_refl CallOk)
                        (callset_descend_if_cond eq_refl CallOk'));
       cbn;
       destruct interpret_expr;
       rewrite (IHyes _ eq_refl
                      (callset_descend_if_then eq_refl CallOk)
                      (callset_descend_if_then eq_refl CallOk'));
       rewrite (IHno _ eq_refl
                     (callset_descend_if_else eq_refl CallOk)
                     (callset_descend_if_else eq_refl CallOk'));
       trivial.
}
{ (* LogicalAnd *)
  remember (const_fold_expr e1) as c1. destruct c1 as [|c1]. { discriminate. }
  cbn.
  destruct c1.
  { (* left arg is a const *)
    rewrite<- (IHe1 _ eq_refl
                    (callset_descend_and_left eq_refl CallOk)
                    FSet.empty_subset).
    cbn.
    destruct (Z_of_uint256 val =? 0)%Z.
    { inversion ExprOk. now subst e'. }
    now apply IHe2.
  }
  (* left arg is not const *)
  1-9: remember (const_fold_expr e2) as c2; destruct c2 as [|c2]; try discriminate;
       inversion ExprOk; subst e';
       try match goal with
           | H: inr ?c = const_fold_expr _ |- _ => remember c as cond'
           end;
       rewrite<- (IHe1 _ eq_refl
                      (callset_descend_and_left eq_refl CallOk)
                      (callset_descend_and_left eq_refl CallOk'));
       cbn;
       destruct interpret_expr;
       now rewrite (IHe2 _ eq_refl
                         (callset_descend_and_right eq_refl CallOk)
                         (callset_descend_and_right eq_refl CallOk')).
}
{ (* LogicalOr *)
  remember (const_fold_expr e1) as c1. destruct c1 as [|c1]. { discriminate. }
  cbn.
  destruct c1.
  { (* left arg is a const *)
    rewrite<- (IHe1 _ eq_refl
                    (callset_descend_or_left eq_refl CallOk)
                    FSet.empty_subset).
    cbn.
    destruct (Z_of_uint256 val =? 0)%Z.
    { now apply IHe2. }
    inversion ExprOk. now subst e'.
  }
  (* left arg is not const *)
  1-9: remember (const_fold_expr e2) as c2; destruct c2 as [|c2]; try discriminate;
       inversion ExprOk; subst e';
       try match goal with
           | H: inr ?c = const_fold_expr _ |- _ => remember c as cond'
           end;
       rewrite<- (IHe1 _ eq_refl
                      (callset_descend_or_left eq_refl CallOk)
                      (callset_descend_or_left eq_refl CallOk'));
       cbn;
       destruct interpret_expr;
       now rewrite (IHe2 _ eq_refl
                         (callset_descend_or_right eq_refl CallOk)
                         (callset_descend_or_right eq_refl CallOk')).
}
{ (* PrivateCall *)
  remember ((fix const_fold_expr_list (l : list expr) : string + list expr :=
              match l with
              | nil => inr nil
              | (h :: t)%list =>
                  match const_fold_expr h with
                  | inl err => inl err
                  | inr h' =>
                      match const_fold_expr_list t with
                      | inl err => inl err
                      | inr t' => inr (h' :: t')%list
                      end
                  end
              end) args) as cargs. symmetry in Heqcargs. destruct cargs. { discriminate. }
  inversion ExprOk. subst e'. cbn.
  rename l into args'.
  assert (R':
    forall Ok' Ok,  (* initially: (callset_descend_args eq_refl CallOk') etc *)
    interpret_expr_list eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world loc args' Ok'
     =
    (fix
    interpret_expr_list (world0 : world_state) (loc0 : string_map uint256) 
                        (e : list expr)
                        (CallOk0 : FSet.is_subset (expr_list_callset e)
                                     (decl_callset (cached_maybe_mapped_decl const_fold_decl
                                           (@callset_const_fold_decl C) ok fc)) = true) {struct
                        e} : world_state * Base.expr_result (list uint256) :=
      match e as e' return (e = e' -> world_state * Base.expr_result (list uint256)) with
      | nil => fun _ : e = nil => (world0, Base.ExprSuccess nil)
      | (h :: t)%list =>
          fun E : e = (h :: t)%list =>
          let (world', result_h) :=
            interpret_expr eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world0 loc0 h
              (callset_descend_head E CallOk0) in
          match result_h with
          | Base.ExprSuccess x =>
              let (world'', result_t) :=
                interpret_expr_list world' loc0 t (callset_descend_tail E CallOk0) in
              (world'',
              match result_t with
              | Base.ExprSuccess y => Base.ExprSuccess (x :: y)%list
              | Base.ExprAbort _ => result_t
              end)
          | Base.ExprAbort ab => (world', Base.ExprAbort ab)
          end
      end eq_refl) world loc args' Ok).
  {
    clear CallOk CallOk' Heqcargs ExprOk H1.
    revert world loc. induction args'. { easy. }
    intros. cbn.
    assert (Irrel:
        (@callset_descend_head C a args' (a :: args')
          (@decl_callset C
             (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok')
         =
        (@callset_descend_head C a args' (a :: args')
        (@decl_callset C
           (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
              (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
              (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok)).
    { apply PropExtensionality.proof_irrelevance. }
    rewrite Irrel.
    destruct interpret_expr. destruct e. 2:{ trivial. }
    now rewrite (IHargs' w loc 
                  (@callset_descend_tail C a args' (a :: args')
                    (@decl_callset C
                       (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                          (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                          (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok')
                  (@callset_descend_tail C a args' (a :: args')
                    (@decl_callset C
                       (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                          (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                          (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok) ).
  }
  rewrite<- (R' (callset_descend_args eq_refl CallOk')). clear R'.
  assert (W := weak_interpret_const_fold_expr_list builtins ok fc DoCallOk world loc Heqcargs
                                                   (callset_descend_args eq_refl CallOk')
                                                   (callset_descend_args eq_refl CallOk)
                                                   H).
  rewrite W.
  assert (R:
    forall Ok' Ok,
    interpret_expr_list eq_refl fc do_call builtins world loc args Ok'
     =
    (fix
      interpret_expr_list (world0 : world_state) (loc0 : string_map uint256) 
                          (e : list expr)
                          (CallOk0 : FSet.is_subset (expr_list_callset e) (decl_callset (fun_decl fc)) =
                                     true) {struct e} : world_state * Base.expr_result (list uint256) :=
        match e as e' return (e = e' -> world_state * Base.expr_result (list uint256)) with
        | nil => fun _ : e = nil => (world0, Base.ExprSuccess nil)
        | (h :: t)%list =>
            fun E : e = (h :: t)%list =>
            let (world', result_h) :=
              interpret_expr eq_refl fc do_call builtins world0 loc0 h (callset_descend_head E CallOk0) in
            match result_h with
            | Base.ExprSuccess x =>
                let (world'', result_t) :=
                  interpret_expr_list world' loc0 t (callset_descend_tail E CallOk0) in
                (world'',
                match result_t with
                | Base.ExprSuccess y => Base.ExprSuccess (x :: y)%list
                | Base.ExprAbort _ => result_t
                end)
            | Base.ExprAbort ab => (world', Base.ExprAbort ab)
            end
        end eq_refl) world loc args Ok).
  {
    clear CallOk CallOk' Heqcargs args' W ExprOk H H1.
    revert world loc. induction args. { easy. }
    intros. cbn.
    (* this is relatively horror-free this time: *)
    assert (Irrel: callset_descend_head eq_refl Ok' = callset_descend_head eq_refl Ok).
    { apply PropExtensionality.proof_irrelevance. }
    rewrite Irrel.
    destruct interpret_expr. destruct e. 2:{ trivial. }
    now rewrite (IHargs w loc 
                        (callset_descend_tail eq_refl Ok')
                        (callset_descend_tail eq_refl Ok)).
  }
  rewrite<- (R (callset_descend_args eq_refl CallOk)). clear R.
  remember (interpret_expr_list eq_refl fc do_call builtins world loc args
             (callset_descend_args eq_refl CallOk)) as after_args. clear Heqafter_args.
  destruct after_args as (world', result_args).
  destruct result_args. 2:{ trivial. }
  (* args computation has succeeded *)

  enough (D: fun_ctx_descend (const_fold_fun_ctx ok fc)
              CallOk' eq_refl eq_refl
              =
             match fun_ctx_descend fc CallOk eq_refl eq_refl with
             | Some ctx => Some (const_fold_fun_ctx ok ctx)
             | None => None
             end).
  {
    rewrite D.
    now destruct (fun_ctx_descend fc CallOk eq_refl eq_refl).
  }
  (* This follows the proof of D from From20To30/Expr.v, which in turn follows fun_ctx_descend_irrel. *)
  unfold fun_ctx_descend.
  assert (InnerOk: forall (d1 d2: decl)
                          (Edecl1: cd_declmap cd  name = Some d1)
                          (Edecl2: cd_declmap cd' name = Some d2),
                 L20.Descend.fun_ctx_descend_inner (const_fold_fun_ctx ok fc) CallOk'
                    eq_refl eq_refl Edecl2
                  =
                 match L20.Descend.fun_ctx_descend_inner fc CallOk eq_refl eq_refl Edecl1 with
                 | Some ctx => Some (const_fold_fun_ctx ok ctx)
                 | None => None
                 end).
  {
    intros.
    unfold Descend.fun_ctx_descend_inner.
    remember (fun (depth: nat) (Edepth: cd_depthmap cd' name = Some depth) =>
        Some
          {|
          fun_name := name;
          fun_depth := depth;
          fun_depth_ok := Edepth;
          fun_decl := d2;
          fun_decl_ok := Edecl2;
          fun_bound_ok := Descend.call_descend' (const_fold_fun_ctx ok fc)
                      CallOk' eq_refl eq_refl
                            Edecl2 Edepth |})
      as some_branch_l.
    remember (fun Edepth : cd_depthmap cd' name = None =>
                False_rect (option (fun_ctx cd' smaller_call_depth_bound))
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
        fun_bound_ok := Descend.call_descend' fc CallOk eq_refl eq_refl Edecl1 Edepth |})
      as some_branch_r.
    remember (fun Edepth : cd_depthmap cd name = None =>
                  False_rect (option (fun_ctx cd smaller_call_depth_bound))
                    (L20.Descend.fun_ctx_descend_helper Edecl1 Edepth))
      as none_branch_r.
    assert (NoneOkL: forall (Edepth: cd_depthmap cd' name = None),
                       none_branch_l Edepth = None).
    { intro. exfalso. exact (Descend.fun_ctx_descend_helper Edecl2 Edepth). }
    assert (NoneOkR: forall (Edepth: cd_depthmap cd name = None),
                       none_branch_r Edepth = None).
    { intro. exfalso. exact (Descend.fun_ctx_descend_helper Edecl1 Edepth). }
    clear Heqnone_branch_l Heqnone_branch_r.
    revert none_branch_l none_branch_r NoneOkL NoneOkR.
    assert (SomeBranchOk: forall (depth: nat)
                                 (Edepth1: cd_depthmap cd name = Some depth)
                                 (Edepth2: cd_depthmap cd' name = Some depth),
                   some_branch_l depth Edepth2 
                    =
                   match some_branch_r depth Edepth1 with
                   | Some ctx => Some (const_fold_fun_ctx ok ctx)
                   | None => None
                   end).
    {
      intros. subst. unfold const_fold_fun_ctx. cbn.
      f_equal.
      assert (D: d2 = cached_maybe_mapped_decl const_fold_decl (@callset_const_fold_decl C) ok
              {|
              fun_name := name;
              fun_depth := depth;
              fun_depth_ok := Edepth1;
              fun_decl := d1;
              fun_decl_ok := Edecl1;
              fun_bound_ok := Descend.call_descend' fc CallOk eq_refl eq_refl Edecl1 Edepth1 |}).
      {
        unfold cached_maybe_mapped_decl. cbn.
        remember (Calldag.calldag_maybe_map_fun_ctx_fun_decl_helper _ _ ok _) as Bad. clear HeqBad.
        cbn in Bad. revert Bad.
        destruct (cd_declmap cd' name). { now inversion Edecl2. }
        intro Bad. discriminate.
      }
      subst. unfold fun_ctx_maybe_map. cbn.
      f_equal; apply PropExtensionality.proof_irrelevance.
    } (* SomeBranchOk *)
    clear Heqsome_branch_l Heqsome_branch_r
          CallOk CallOk' Edecl1 Edecl2 d1 d2 args value DoCallOk
          do_call do_call' H Heqcargs W.
    revert some_branch_l some_branch_r SomeBranchOk.
    rewrite (calldag_maybe_map_depthmap_ok const_fold_decl _ ok name).
    destruct (cd_depthmap cd' name), (cd_depthmap cd name); intros;
      try apply SomeBranchOk; rewrite (NoneOkL eq_refl); rewrite (NoneOkR eq_refl); trivial.
  } (* InnerOk *)
  remember (@Descend.fun_ctx_descend_inner C (S smaller_call_depth_bound) smaller_call_depth_bound cd'
             (@PrivateCall C name args') name args') as inner'.
  remember (@Descend.fun_ctx_descend_inner C (S smaller_call_depth_bound) smaller_call_depth_bound cd
             (@PrivateCall C name args) name args) as inner.
  clear Heqinner' Heqinner.
  subst.
  remember (fun d (Edecl: cd_declmap cd' name = Some d) =>
                inner' (const_fold_fun_ctx ok fc) CallOk' eq_refl eq_refl d Edecl)
    as some_branch'.
  remember (cd_declmap cd name) as maybe_d. destruct maybe_d.
  {
    assert (SomeBranchOk: forall (d': decl)
                                 (Edecl: cd_declmap cd' name = Some d'),
                   some_branch' d' Edecl
                    =
                   match inner fc CallOk eq_refl eq_refl d eq_refl with
                   | Some ctx => Some (const_fold_fun_ctx ok ctx)
                   | None => None
                   end).
    { intros. apply InnerOk. }
    clear Heqsome_branch'.
    remember (cd_declmap cd' name) as maybe_d'.
    destruct maybe_d'. { apply SomeBranchOk. }
    assert (T := calldag_maybe_map_declmap const_fold_decl _ ok name).
    rewrite<- Heqmaybe_d' in T.
    rewrite<- Heqmaybe_d in T.
    discriminate.
  }
  assert (SomeBranchOk: forall (d': decl)
                               (Edecl: cd_declmap cd' name = Some d'),
             some_branch' d' Edecl
              =
             None).
  {
    intros.
    assert (T := calldag_maybe_map_declmap const_fold_decl _ ok name).
    rewrite<- Heqmaybe_d in T. rewrite Edecl in T.
    discriminate.
  }
  clear Heqsome_branch'.
  now destruct (cd_declmap cd' name).
}
(* BuiltinCall *)
(* following PrivateCall until the args are computed successfully *)
remember ((fix const_fold_expr_list (l : list expr) : string + list expr :=
            match l with
            | nil => inr nil
            | (h :: t)%list =>
                match const_fold_expr h with
                | inl err => inl err
                | inr h' =>
                    match const_fold_expr_list t with
                    | inl err => inl err
                    | inr t' => inr (h' :: t')%list
                    end
                end
            end) args) as cargs. symmetry in Heqcargs. destruct cargs. { discriminate. }
inversion ExprOk. subst e'. cbn.
rename l into args'.
assert (R':
  forall Ok' Ok,  (* initially: (callset_descend_args eq_refl CallOk') etc *)
  interpret_expr_list eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world loc args' Ok'
   =
  (fix
  interpret_expr_list (world0 : world_state) (loc0 : string_map uint256) 
                      (e : list expr)
                      (CallOk0 : FSet.is_subset (expr_list_callset e)
                                   (decl_callset (cached_maybe_mapped_decl const_fold_decl (@callset_const_fold_decl C) ok fc)) = true) {struct
                      e} : world_state * Base.expr_result (list uint256) :=
    match e as e' return (e = e' -> world_state * Base.expr_result (list uint256)) with
    | nil => fun _ : e = nil => (world0, Base.ExprSuccess nil)
    | (h :: t)%list =>
        fun E : e = (h :: t)%list =>
        let (world', result_h) :=
          interpret_expr eq_refl (const_fold_fun_ctx ok fc) do_call' builtins world0 loc0 h
            (callset_descend_head E CallOk0) in
        match result_h with
        | Base.ExprSuccess x =>
            let (world'', result_t) :=
              interpret_expr_list world' loc0 t (callset_descend_tail E CallOk0) in
            (world'',
            match result_t with
            | Base.ExprSuccess y => Base.ExprSuccess (x :: y)%list
            | Base.ExprAbort _ => result_t
            end)
        | Base.ExprAbort ab => (world', Base.ExprAbort ab)
        end
    end eq_refl) world loc args' Ok).
{
  clear CallOk CallOk' Heqcargs ExprOk H1.
  revert world loc. induction args'. { easy. }
  intros. cbn.
  assert (Irrel:
        (@callset_descend_head C a args' (a :: args')
        (@decl_callset C
           (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
              (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
              (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok')
       =
         (@callset_descend_head C a args' (a :: args')
        (@decl_callset C
           (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
              (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
              (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok)).
  { apply PropExtensionality.proof_irrelevance. }
  rewrite Irrel.
  destruct interpret_expr. destruct e. 2:{ trivial. }
  now rewrite (IHargs' w loc 
                (@callset_descend_tail C a args' (a :: args')
                  (@decl_callset C
                     (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                        (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                        (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok')
                (@callset_descend_tail C a args' (a :: args')
                  (@decl_callset C
                     (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                        (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                        (S smaller_call_depth_bound) fc)) (@eq_refl (list (@expr C)) (a :: args')%list) Ok)).
}
rewrite<- (R' (callset_descend_builtin_args eq_refl CallOk')). clear R'.
assert (W := weak_interpret_const_fold_expr_list builtins ok fc DoCallOk world loc Heqcargs
                                                 (callset_descend_builtin_args eq_refl CallOk')
                                                 (callset_descend_builtin_args eq_refl CallOk)
                                                 H).
rewrite W.
assert (R:
  forall Ok' Ok,
  interpret_expr_list eq_refl fc do_call builtins world loc args Ok'
   =
  (fix
    interpret_expr_list (world0 : world_state) (loc0 : string_map uint256) 
                        (e : list expr)
                        (CallOk0 : FSet.is_subset (expr_list_callset e) (decl_callset (fun_decl fc)) =
                                   true) {struct e} : world_state * Base.expr_result (list uint256) :=
      match e as e' return (e = e' -> world_state * Base.expr_result (list uint256)) with
      | nil => fun _ : e = nil => (world0, Base.ExprSuccess nil)
      | (h :: t)%list =>
          fun E : e = (h :: t)%list =>
          let (world', result_h) :=
            interpret_expr eq_refl fc do_call builtins world0 loc0 h (callset_descend_head E CallOk0) in
          match result_h with
          | Base.ExprSuccess x =>
              let (world'', result_t) :=
                interpret_expr_list world' loc0 t (callset_descend_tail E CallOk0) in
              (world'',
              match result_t with
              | Base.ExprSuccess y => Base.ExprSuccess (x :: y)%list
              | Base.ExprAbort _ => result_t
              end)
          | Base.ExprAbort ab => (world', Base.ExprAbort ab)
          end
      end eq_refl) world loc args Ok).
{
  clear CallOk CallOk' Heqcargs args' W ExprOk H H1.
  revert world loc. induction args. { easy. }
  intros. cbn.
  (* this is relatively horror-free this time: *)
  assert (Irrel: callset_descend_head eq_refl Ok' = callset_descend_head eq_refl Ok).
  { apply PropExtensionality.proof_irrelevance. }
  rewrite Irrel.
  destruct interpret_expr. destruct e. 2:{ trivial. }
  now rewrite (IHargs w loc 
                      (callset_descend_tail eq_refl Ok')
                      (callset_descend_tail eq_refl Ok)).
}
rewrite<- (R (callset_descend_builtin_args eq_refl CallOk)). clear R.
remember (interpret_expr_list eq_refl fc do_call builtins world loc args
           (callset_descend_builtin_args eq_refl CallOk)) as after_args. clear Heqafter_args.
destruct after_args as (world', result_args).
now destruct result_args.
Qed.


Lemma interpret_const_fold_small_stmt {C: VyperConfig}
                        {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        (builtins: string -> option L10.Base.builtin)
                        {cd cd': calldag}
                        (ok: const_fold_calldag cd = inr cd')
                        (fc: fun_ctx cd bigger_call_depth_bound)
                        {do_call: forall
                            (smaller_fc: fun_ctx cd smaller_call_depth_bound)
                            (world: world_state)
                            (arg_values: list uint256),
                          world_state * L10.Base.expr_result uint256}
                        {do_call': forall
                              (smaller_fc: fun_ctx cd' smaller_call_depth_bound)
                              (world: world_state)
                              (arg_values: list uint256),
                            world_state * L10.Base.expr_result uint256}
                        (DoCallOk: forall smaller_fc world arg_values,
                                     do_call' (const_fold_fun_ctx ok smaller_fc) world arg_values
                                      =
                                     do_call smaller_fc world arg_values)
                        (world: world_state)
                        (loc: string_map uint256)
                        {ss ss': small_stmt}
                        (StmtOk: const_fold_small_stmt ss = inr ss')
                        (CallOk': let _ := string_set_impl in
                           FSet.is_subset (small_stmt_callset ss')
                                          (decl_callset
                                             (fun_decl
                                               (const_fold_fun_ctx ok fc)))
                           = true)
                        (CallOk: let _ := string_set_impl in
                           FSet.is_subset (small_stmt_callset ss)
                                          (decl_callset (fun_decl fc))
                           = true):
   interpret_small_stmt Ebound (const_fold_fun_ctx ok fc)
                        do_call' builtins
                        world loc ss' CallOk'
    =
   interpret_small_stmt Ebound fc
                        do_call builtins
                        world loc ss CallOk.
Proof.
destruct ss; cbn in StmtOk; unfold sum_map in *; cbn.
{ (* Pass *) inversion StmtOk. now subst ss'. }
{ (* Abort *) inversion StmtOk. now subst ss'. }
{ (* Return *)
  remember (const_fold_expr result) as result'. symmetry in Heqresult'.
  destruct result'. { discriminate. }
  inversion StmtOk. subst ss'.
  cbn.
  (* prepare for the next rewrite *)
  assert (R: (@callset_descend_return C (@Return C e) e
                (@decl_callset C
                   (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                      (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                      bigger_call_depth_bound fc)) (@eq_refl (@small_stmt C) (@Return C e)) CallOk')
              =
         (@callset_descend_return C (@Return C e) e
            (@decl_callset C
               (@fun_decl C (@decl C) (@decl_callset C) false cd' bigger_call_depth_bound
                  (@const_fold_fun_ctx C bigger_call_depth_bound cd cd' ok fc)))
            (@eq_refl (@small_stmt C) (@Return C e)) CallOk')).
  { easy. }
  rewrite R.
  rewrite (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqresult'
                                          (callset_descend_return eq_refl CallOk')
                                          (callset_descend_return eq_refl CallOk)).
  now destruct interpret_expr.
}
{ (* Raise *) 
  remember (const_fold_expr error) as error'. symmetry in Heqerror'.
  destruct error'. { discriminate. }
  inversion StmtOk. subst ss'.
  cbn.
  assert (R: (@callset_descend_raise C (@Raise C e) e
              (@decl_callset C
                 (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                    (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                    bigger_call_depth_bound fc)) (@eq_refl (@small_stmt C) (@Raise C e)) CallOk')
              =
             (@callset_descend_raise C (@Raise C e) e
                (@decl_callset C
                   (@fun_decl C (@decl C) (@decl_callset C) false cd' bigger_call_depth_bound
                      (@const_fold_fun_ctx C bigger_call_depth_bound cd cd' ok fc)))
                (@eq_refl (@small_stmt C) (@Raise C e)) CallOk')).
  { easy. }
  rewrite R.
  rewrite (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqerror'
                                          (callset_descend_raise eq_refl CallOk')
                                          (callset_descend_raise eq_refl CallOk)).
  now destruct interpret_expr.
}
{ (* Assign *)
  remember (const_fold_expr rhs) as rhs'. symmetry in Heqrhs'.
  destruct rhs'. { discriminate. }
  inversion StmtOk. subst ss'.
  cbn.
  assert (R: (@callset_descend_assign_rhs C (@Assign C lhs e) lhs e
                (@decl_callset C
                   (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                      (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                      bigger_call_depth_bound fc)) (@eq_refl (@small_stmt C) (@Assign C lhs e)) CallOk')
              =
             (@callset_descend_assign_rhs C (@Assign C lhs e) lhs e
              (@decl_callset C
                 (@fun_decl C (@decl C) (@decl_callset C) false cd' bigger_call_depth_bound
                    (@const_fold_fun_ctx C bigger_call_depth_bound cd cd' ok fc)))
              (@eq_refl (@small_stmt C) (@Assign C lhs e)) CallOk')).
  { easy. }
  rewrite R.
  rewrite (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqrhs'
                                          (callset_descend_assign_rhs eq_refl CallOk')
                                          (callset_descend_assign_rhs eq_refl CallOk)).
  destruct interpret_expr as (world', result).
  destruct result; cbn. 2:{ trivial. }
  destruct lhs. { trivial. }
  unfold storage_var_is_declared.
  assert (D := calldag_maybe_map_declmap const_fold_decl _ ok name).
  destruct (cd_declmap cd' name), (cd_declmap cd name); try discriminate; trivial.
  destruct d0; (* XXX *)
    cbn in D; inversion D; subst; trivial.
  unfold sum_map in *.
  destruct (const_fold_stmt body). { discriminate. }
  inversion D; subst. trivial.
}
(* ExprStmt *)
remember (const_fold_expr e) as e'. symmetry in Heqe'.
destruct e' as [|e']. { discriminate. }
inversion StmtOk. subst ss'.
cbn.
rewrite<- (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqe'
                                        (callset_descend_expr_stmt eq_refl CallOk')
                                        (callset_descend_expr_stmt eq_refl CallOk)).
now destruct interpret_expr.
Qed.

Lemma interpret_const_fold_stmt {C: VyperConfig}
                        {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        (builtins: string -> option L10.Base.builtin)
                        {cd cd': calldag}
                        (ok: const_fold_calldag cd = inr cd')
                        (fc: fun_ctx cd bigger_call_depth_bound)
                        {do_call: forall
                            (smaller_fc: fun_ctx cd smaller_call_depth_bound)
                            (world: world_state)
                            (arg_values: list uint256),
                          world_state * L10.Base.expr_result uint256}
                        {do_call': forall
                              (smaller_fc: fun_ctx cd' smaller_call_depth_bound)
                              (world: world_state)
                              (arg_values: list uint256),
                            world_state * L10.Base.expr_result uint256}
                        (DoCallOk: forall smaller_fc world arg_values,
                                     do_call' (const_fold_fun_ctx ok smaller_fc) world arg_values
                                      =
                                     do_call smaller_fc world arg_values)
                        (world: world_state)
                        (loc: string_map uint256)
                        {s s': stmt}
                        (StmtOk: const_fold_stmt s = inr s')
                        (CallOk': let _ := string_set_impl in
                           FSet.is_subset (stmt_callset s')
                                          (decl_callset
                                             (fun_decl
                                               (const_fold_fun_ctx ok fc)))
                           = true)
                        (CallOk: let _ := string_set_impl in
                           FSet.is_subset (stmt_callset s)
                                          (decl_callset (fun_decl fc))
                           = true):
   interpret_stmt Ebound (const_fold_fun_ctx ok fc)
                  do_call' builtins
                  world loc s' CallOk'
    =
   interpret_stmt Ebound fc
                  do_call builtins
                  world loc s CallOk.
Proof.
revert world loc s' StmtOk CallOk' CallOk.
induction s; intros; cbn in StmtOk; unfold sum_map in *; unfold sum_ap in *.
{ (* SmallStmt *)
  remember (const_fold_small_stmt s) as ss'. symmetry in Heqss'.
  destruct ss' as [|ss']. { discriminate. }
  inversion StmtOk. subst s'. cbn.
  now apply interpret_const_fold_small_stmt.
}
{ (* LocalVarDecl *)
  remember (const_fold_expr init) as init'. symmetry in Heqinit'.
  destruct init' as [|init']. { discriminate. }
  destruct const_fold_stmt as [|body]. { discriminate. }
  inversion StmtOk. subst s'. cbn.
  destruct (Base.map_lookup loc name). { trivial. }
  rewrite<- (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqinit'
                                        (callset_descend_var_init eq_refl CallOk')
                                        (callset_descend_var_init eq_refl CallOk)).
  destruct interpret_expr as (world', result). destruct result. 2:{ trivial. }
  assert (IH := IHs world' (Base.map_insert loc name value) body eq_refl
                    (callset_descend_var_scope eq_refl CallOk')
                    (callset_descend_var_scope eq_refl CallOk)).
  assert (R: (@callset_descend_var_scope C (@LocalVarDecl C name init' body) name init' body
               (@decl_callset C
                  (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                     (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                     bigger_call_depth_bound fc)) (@eq_refl (@stmt C) (@LocalVarDecl C name init' body))
               CallOk')
              =
              (@callset_descend_var_scope C (@LocalVarDecl C name init' body) name init' body
                (@decl_callset C
                   (@fun_decl C (@decl C) (@decl_callset C) false cd' bigger_call_depth_bound
                      (@const_fold_fun_ctx C bigger_call_depth_bound cd cd' ok fc)))
                (@eq_refl (@stmt C) (@LocalVarDecl C name init' body)) CallOk')).
  { easy. }
  rewrite R.
  now rewrite IH.
}
{ (* IfElseStmt *)
  rename s1 into yes. rename s2 into no. rename IHs1 into IHyes. rename IHs2 into IHno.
  remember (const_fold_expr cond) as cond'. symmetry in Heqcond'.
  destruct cond' as [|cond']. { discriminate. }
  remember (const_fold_stmt yes) as yes'. symmetry in Heqyes'.
  destruct yes' as [|yes']. { discriminate. }
  remember (const_fold_stmt no) as no'. symmetry in Heqno'.
  destruct no' as [|no']. { discriminate. }
  inversion StmtOk. subst s'. cbn.
  rewrite<- (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqcond'
                   (callset_descend_stmt_if_cond eq_refl CallOk')
                   (callset_descend_stmt_if_cond eq_refl CallOk)).
  destruct interpret_expr as (world', result). destruct result. 2:{ trivial. }
  destruct (Z_of_uint256 value =? 0)%Z.
  { (* no *)
    apply (IHno _ _ _ eq_refl (callset_descend_stmt_if_else eq_refl CallOk')
                              (callset_descend_stmt_if_else eq_refl CallOk)).
  }
  apply (IHyes _ _ _ eq_refl (callset_descend_stmt_if_then eq_refl CallOk')
                             (callset_descend_stmt_if_then eq_refl CallOk)).
}
2:{ (* Semicolon *)
  remember (const_fold_stmt s1) as s1'. symmetry in Heqs1'.
  destruct s1' as [|s1']. { discriminate. }
  remember (const_fold_stmt s2) as s2'. symmetry in Heqs2'.
  destruct s2' as [|s2']. { discriminate. }
  inversion StmtOk. subst s'. cbn.
  rewrite (IHs1 _ _ _ eq_refl (callset_descend_semicolon_left eq_refl CallOk')
                              (callset_descend_semicolon_left eq_refl CallOk)).
  destruct interpret_stmt as ((world', loc'), result). destruct result; trivial.
  apply (IHs2 _ _ _ eq_refl (callset_descend_semicolon_right eq_refl CallOk')
                            (callset_descend_semicolon_right eq_refl CallOk)).
}
(* Loop *)
remember (const_fold_expr start) as start'. symmetry in Heqstart'.
destruct start' as [|start']. { discriminate. }
rename s into body. remember (const_fold_stmt body) as body'. symmetry in Heqbody'.
destruct body' as [|body']. { discriminate. }
inversion StmtOk. subst s'. cbn.
remember (Base.map_lookup loc var) as lookup_var.
destruct lookup_var. { trivial. }
remember (Z_of_uint256 count =? 0)%Z as count_is_0.
destruct count_is_0. { trivial. }
rewrite<- (interpret_const_fold_expr Ebound builtins ok fc DoCallOk world loc Heqstart'
                   (callset_descend_loop_start eq_refl CallOk')
                   (callset_descend_loop_start eq_refl CallOk)).
destruct interpret_expr as (world', result_start).
destruct result_start. 2:{ trivial. }
remember (Z_of_uint256 (uint256_of_Z (Z_of_uint256 value + Z_of_uint256 count - 1)) =?
           Z_of_uint256 value + Z_of_uint256 count - 1)%Z
  as no_overflow.
destruct no_overflow. 2:{ trivial. }
(* checks completed, now the loop itself *)
remember (Z.to_nat (Z_of_uint256 count)) as countdown.
remember (Z_of_uint256 value) as cursor.

(* closely following From20To30/Stmt.v here *)
remember (Z_of_uint256 value + Z_of_uint256 count - 1)%Z as cap.
assert (CapRange: (0 <= cap < 2 ^ 256)%Z).
{
  symmetry in Heqno_overflow. rewrite Z.eqb_eq in Heqno_overflow.
  rewrite uint256_ok in Heqno_overflow.
  rewrite Z.mod_small_iff in Heqno_overflow by apply two_to_256_ne_0.
  subst cursor cap.
  enough (~ (2 ^ 256 < (Z_of_uint256 value + Z_of_uint256 count - 1)%Z <= 0)%Z). 
  { tauto. }
  intro Y.
  assert (Bad := proj2 (Z.ltb_lt _ _) (Z.lt_le_trans _ _ _ (proj1 Y) (proj2 Y))).
  cbn in Bad. discriminate.
}

assert (WeakMainLoopEq: 
          cap = (cursor + Z_of_uint256 count - 1)%Z
           \/
          Z_of_uint256 count = 0%Z).
{ left. subst cursor. exact Heqcap. }

clear Heqcap Heqcursor world Heqno_overflow Heqcount_is_0 Heqlookup_var.
revert count world' loc cursor WeakMainLoopEq CallOk' CallOk Heqcountdown StmtOk.
induction countdown; intros. { trivial. } (* ----------- induction -------------*)
rewrite (IHs _ _ _ eq_refl (callset_descend_loop_body eq_refl CallOk')
                           (callset_descend_loop_body eq_refl CallOk)).

(* checking that the counter doesn't go below 0 *)
pose (count' := uint256_of_Z (Z.pred (Z_of_uint256 count))).
assert (CountOk: countdown = Z.to_nat (Z_of_uint256 count')).
{
  unfold count'. rewrite uint256_ok.
  assert (R := uint256_range count).
  remember (Z_of_uint256 count) as z. clear Heqz.
  assert (W: z = Z.succ (Z.of_nat countdown)).
  {
    rewrite<- Nat2Z.inj_succ. rewrite Heqcountdown.
    symmetry. apply Z2Nat.id. tauto.
  }
  subst z. rewrite Z.pred_succ.
  replace (Z.of_nat countdown mod 2 ^ 256)%Z with (Z.of_nat countdown).
  { symmetry. apply Nat2Z.id. }
  symmetry. apply Z.mod_small.
  split.
  { (* 0 <= countdown *) apply Nat2Z.is_nonneg. }
  exact (Z.lt_trans _ _ _ (Z.lt_succ_diag_r (Z.of_nat countdown)) (proj2 R)).
}

(* strengthening WeakMainLoopEq *)
assert (MainLoopEq: cap = (cursor + Z_of_uint256 count - 1)%Z).
{
  enough (Z_of_uint256 count <> 0%Z). { tauto. }
  intro J. rewrite J in *.
  cbn in Heqcountdown. discriminate.
}

assert (NextLoopEq: cap = (Z.succ cursor + Z_of_uint256 count' - 1)%Z).
{
  rewrite MainLoopEq.
  enough (Z_of_uint256 count = Z_of_uint256 count' + 1)%Z by lia.
  subst countdown.
  assert (R := uint256_range count).
  assert (R' := uint256_range count').
  lia.
}

assert (WeakNextLoopEq: (cap = Z.succ cursor + Z_of_uint256 count' - 1 \/ Z_of_uint256 count' = 0)%Z).
{ left. apply NextLoopEq. }

destruct (interpret_stmt Ebound fc do_call builtins world'
            (Base.map_insert loc var (uint256_of_Z cursor))
            body (callset_descend_loop_body eq_refl CallOk)) as ((world''', loc'''), result''').

assert (IH := IHcountdown count' world''' loc''' (Z.succ cursor)
                          WeakNextLoopEq CallOk' CallOk CountOk eq_refl).
assert (FixCallL:
         (@callset_descend_loop_body C (@Loop C var start' count' body') body' var start' count'
            (@decl_callset C
               (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                  (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                  bigger_call_depth_bound fc)) (@eq_refl (@stmt C) (@Loop C var start' count' body'))
            CallOk') 
        =
         (@callset_descend_loop_body C (@Loop C var start' count body') body' var start' count
            (@decl_callset C
               (@cached_maybe_mapped_decl C (@decl C) (@decl C) (@decl_callset C) false 
                  (@decl_callset C) (@const_fold_decl C) (@callset_const_fold_decl C) cd cd' ok
                  bigger_call_depth_bound fc)) (@eq_refl (@stmt C) (@Loop C var start' count body'))
            CallOk'))
  by apply PropExtensionality.proof_irrelevance.
rewrite FixCallL in IH.
assert (FixCallR:
         (@callset_descend_loop_body C (@Loop C var start count' body) body var start count'
            (@decl_callset C
               (@fun_decl C (@decl C) (@decl_callset C) false cd bigger_call_depth_bound fc))
            (@eq_refl (@stmt C) (@Loop C var start count' body)) CallOk)
          =
        (@callset_descend_loop_body C (@Loop C var start count body) body var start count
            (@decl_callset C
               (@fun_decl C (@decl C) (@decl_callset C) false cd bigger_call_depth_bound fc))
            (@eq_refl (@stmt C) (@Loop C var start count body)) CallOk))
  by apply PropExtensionality.proof_irrelevance.
rewrite FixCallR in IH. clear FixCallL FixCallR.
destruct result'''; try trivial.
now destruct a.
Qed.

(* XXX XXX XXX shit happens if this is placed in the beginning *)
From Vyper.L20 Require Import Interpret.

Lemma interpret_const_fold_call {C: VyperConfig}
                                (builtins: string -> option L10.Base.builtin)
                                {cd cd': calldag}
                                (ok: const_fold_calldag cd = inr cd')
                                {call_depth_bound: nat}
                                (fc: fun_ctx cd call_depth_bound)
                                (world: world_state)
                                (arg_values: list uint256):
  interpret_call builtins (const_fold_fun_ctx ok fc) world arg_values
   =
  interpret_call builtins fc world arg_values.
Proof.
revert world arg_values. induction call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))). }
assert(F: inr (cached_maybe_mapped_decl const_fold_decl _ ok fc)
           =
          const_fold_decl (fun_decl fc)).
{
  clear IHcall_depth_bound.
  unfold const_fold_fun_ctx in *. cbn in *.
  unfold cached_maybe_mapped_decl in *.
  remember (Calldag.calldag_maybe_map_fun_ctx_fun_decl_helper const_fold_decl _ ok fc) as foo.
  clear Heqfoo.
  remember (cd_declmap cd' (fun_name fc)) as d.
  destruct d. 2:{ contradiction. }
  subst.
  assert (Q := calldag_maybe_map_declmap const_fold_decl _ ok (fun_name fc)).
  destruct (cd_declmap cd' (fun_name fc)) as [d'|]. 2:discriminate.
  inversion Heqd. subst d'. clear Heqd.
  remember (cd_declmap cd (fun_name fc)) as x.
  destruct x as [x|]. 2:discriminate.
  inversion Q. f_equal.
  assert (D := fun_decl_ok fc).
  rewrite D in *. inversion Heqx.
  trivial.
}
intros.
cbn.
remember (fun name arg_names body
              (E : cached_maybe_mapped_decl const_fold_decl (@callset_const_fold_decl C) ok fc = FunDecl name arg_names body) =>
    match Interpret.bind_args arg_names arg_values with
    | inl err => (world, Base.expr_error err)
    | inr loc =>
        let
        '(world', _, result) :=
         interpret_stmt eq_refl (const_fold_fun_ctx ok fc) (interpret_call builtins) builtins world
           loc body (Interpret.interpret_call_helper E) in
         (world', _)
    end) as branch_l.
remember (fun name arg_names body
              (E : fun_decl fc = FunDecl name arg_names body) =>
          match Interpret.bind_args arg_names arg_values with
          | inl err => (world, Base.expr_error err)
          | inr loc =>
              let
              '(world', _, result) :=
               interpret_stmt eq_refl fc (interpret_call builtins) builtins world loc body
                 (Interpret.interpret_call_helper E) in
               (world', _)
          end) as branch_r.
enough (B: forall name arg_names body_l body_r E_l E_r,
             branch_l name arg_names body_l E_l
              =
             branch_r name arg_names body_r E_r).
{
  clear Heqbranch_l Heqbranch_r.
  destruct (fun_decl fc); cbn in F; destruct cached_maybe_mapped_decl;
    unfold sum_map in *; try destruct (const_fold_stmt body); try easy.
  inversion F; subst.
  apply B.
}
intros. subst.
rewrite E_l in F. rewrite E_r in F. cbn in F.
destruct (Interpret.bind_args arg_names arg_values) as [|loc]. { trivial. }
enough (E: interpret_stmt eq_refl (const_fold_fun_ctx ok fc) (interpret_call builtins) builtins world loc
                          body_l (Interpret.interpret_call_helper E_l)
            =
           interpret_stmt eq_refl fc (interpret_call builtins) builtins world loc body_r
                          (Interpret.interpret_call_helper E_r)).
{ rewrite E. now destruct interpret_stmt. }
apply interpret_const_fold_stmt.
{ apply IHcall_depth_bound. }
unfold sum_map in F. destruct (const_fold_stmt body_r). { discriminate. }
inversion F. now subst.
Qed.

Theorem const_fold_ok {C: VyperConfig}
                      {cd cd': calldag}
                      (builtins: string -> option L10.Base.builtin)
                      (ok: const_fold_calldag cd = inr cd')
                      (fun_name: string)
                      (world: world_state)
                      (arg_values: list uint256):
  interpret builtins cd' fun_name world arg_values
   =
  interpret builtins cd fun_name world arg_values.
Proof.
unfold interpret.
rewrite (make_fun_ctx_and_bound_ok const_fold_decl _ ok).
destruct (make_fun_ctx_and_bound cd fun_name) as [(bound, fc)|]; cbn.
{ apply interpret_const_fold_call. }
trivial.
Qed.
