From Coq Require Import String ZArith NArith Eqdep_dec Lia.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L20.AST L30.AST L20.Interpret L30.Interpret.

From Vyper.From20To30 Require Import Translate Callset FunCtx.

(** The local memory as a dictionary agrees with the local memory as an array.
  Here's the equation in pseudocode: [
    locmap[name] = locmem[locvar[name]]
  ]
 *)
Definition VarsAgree {C: VyperConfig}
                     (varmap: string_map N)
                     (locmap: string_map uint256)
                     (locmem: memory)
:= let _ := string_map_impl in
   let _ := memory_impl in
   forall name: string,
     match Map.lookup locmap name, Map.lookup varmap name with
     | Some value, Some index => OpenArray.get locmem index = value
     | None, Some _ | Some _, None => False
     | None, None => True
     end.

(* There's no Map.for_all so here it is: *)
(** All variables in the varmap stay lower then the given bound. *)
Definition VarsBound {C: VyperConfig}
                     (varmap: string_map N)
                     (bound: N)
:= let _ := string_map_impl in
   forall name: string,
     match Map.lookup varmap name with
     | Some index => (index < bound)%N
     | None => True
     end.

Lemma vars_agree_put {C: VyperConfig}
                     (varmap: string_map N)
                     (locmap: string_map uint256)
                     (locmem: memory)
                     (dst: N)
                     (value: uint256)
                     (Agree: VarsAgree varmap locmap locmem)
                     (Bound: VarsBound varmap dst):
  let _ := memory_impl in
  VarsAgree varmap locmap (OpenArray.put locmem dst value).
Proof.
unfold VarsAgree in *. intro name.
unfold VarsBound in Bound.
assert (A := Agree name).
assert (B := Bound name).
destruct (Map.lookup locmap name).
destruct (Map.lookup varmap name). 2-3: exact A.
subst.
rewrite OpenArray.put_ok.
enough (NE: (dst =? n)%N = false) by now rewrite NE.
rewrite N.eqb_neq. apply N.lt_neq in B. intro H. symmetry in H. tauto.
Qed.

Lemma vars_bound_loosen {C: VyperConfig}
                        {varmap: string_map N}
                        {old_bound new_bound: N}
                        (B: VarsBound varmap old_bound)
                        (L: (old_bound <= new_bound)%N):
  VarsBound varmap new_bound.
Proof.
unfold VarsBound in *.
intro name. assert (B' := B name). clear B.
destruct Map.lookup. 2:trivial.
apply (N.lt_le_trans _ _ _ B' L).
Qed.

Definition mem_agree {C: VyperConfig} 
                     (bound exception: N) (mem1 mem2: memory)
:= let _ := memory_impl in
   forall n: N,
     (n < bound)%N
      ->
     n <> exception
      ->
     OpenArray.get mem1 n = OpenArray.get mem2 n.

Lemma vars_agree_if_mem_agree {C: VyperConfig}
                              (varmap: string_map N)
                              (locmap: string_map uint256)
                              (mem1 mem2: memory)
                              (Agree1: VarsAgree varmap locmap mem1)
                              (dst offset: N)
                              (Bound : VarsBound varmap dst)
                              (OffsetOk : (dst < offset)%N)
                              (M: mem_agree offset dst mem1 mem2):
  VarsAgree varmap locmap mem2.
Proof.
unfold VarsAgree in *. intro name.
unfold mem_agree in M.
unfold VarsBound in Bound.
assert (A := Agree1 name).
assert (B := Bound name).
destruct (Map.lookup locmap name), (Map.lookup varmap name); try easy.
rewrite<- M.
{ exact A. }
{ apply (N.lt_trans _ _ _ B OffsetOk). }
apply N.lt_neq. exact B.
Qed.

Lemma weak_interpret_translated_exprs {C: VyperConfig}
    {bigger_call_depth_bound smaller_call_depth_bound: nat}
    (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
    {cd20: L20.Descend.calldag}
    (builtins: string -> option builtin)
    (fc: fun_ctx cd20 bigger_call_depth_bound)
    {cd30: L30.Descend.calldag}
    (ok: translate_calldag cd20 = inr cd30)
    {do_call_20: forall
          (fc': fun_ctx cd20 smaller_call_depth_bound)
          (world: world_state)
          (arg_values: list uint256),
        world_state * expr_result uint256}
    {do_call_30: forall
          (fc': fun_ctx cd30 smaller_call_depth_bound)
          (world: world_state)
          (arg_values: list uint256),
        world_state * expr_result uint256}
    (DoCallOk: forall fc' world arg_values,
                 do_call_30 (translate_fun_ctx fc' ok) world arg_values
                  =
                 do_call_20 fc' world arg_values)
    (world: world_state)
    (locmap: string_map uint256)
    (locmem: memory)
    {e20: list L20.AST.expr}
    {s30: L30.AST.stmt}
    (varmap: string_map N)
    (offset: N)
    (Agree: VarsAgree varmap locmap locmem)
    (Bound: VarsBound varmap offset)
    (ExprOk: (fix translate_expr_list (varmap: string_map N) (offset: N) (exprs: list AST.expr)
              {struct exprs}
              : string + AST.stmt
              := match exprs with
                 | nil => inr (AST.SmallStmt AST.Pass)
                 | (h :: t)%list =>
                     match translate_expr varmap offset (N.succ offset) h with
                     | inl err => inl err
                     | inr h' =>
                         match translate_expr_list varmap (N.succ offset) t with
                         | inl err => inl err
                         | inr t' => inr (AST.Semicolon h' t')
                         end
                     end
                 end) varmap offset e20 = inr s30)
    (CallOk30: let _ := string_set_impl in 
       FSet.is_subset (L30.Callset.stmt_callset s30)
                      (L30.Callset.decl_callset
                         (fun_decl
                           (translate_fun_ctx fc ok)))
       = true)
    (CallOk20: let _ := string_set_impl in 
       FSet.is_subset (L20.Callset.expr_list_callset e20)
                      (L20.Callset.decl_callset
                        (fun_decl fc))
       = true)
    (AllOk: List.Forall
          (fun e : AST.expr =>
           forall
             (CallOk20 : let H := string_set_impl in
                         FSet.is_subset (L20.Callset.expr_callset e)
                           (L20.Callset.decl_callset (fun_decl fc)) = true) (world : world_state)
             (locmem : memory) (dst offset : N),
           VarsAgree varmap locmap locmem ->
           VarsBound varmap dst ->
           (dst < offset)%N ->
           forall s30 : AST.stmt,
           translate_expr varmap dst offset e = inr s30 ->
           forall
             CallOk30 : let H := string_set_impl in
                        FSet.is_subset (Callset.stmt_callset s30)
                          (Callset.decl_callset (fun_decl (translate_fun_ctx fc ok))) = true,
           let _ := string_map_impl in
           let _ := memory_impl in
           let
           '(world30, mem30, result30) :=
            Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok) do_call_30 builtins world locmem s30
              CallOk30 
            in let '(world20, result20) := L20.Expr.interpret_expr Ebound fc do_call_20 builtins
                                                                   world locmap e CallOk20
            in world30 = world20
                /\
               mem_agree offset dst locmem mem30 
                /\
               match result20 with
               | ExprSuccess value20 =>
                   result30 = StmtSuccess 
                    /\
                   OpenArray.get mem30 dst = value20
               | ExprAbort abort => result30 = StmtAbort abort
               end) e20):
   let _ := string_map_impl in
   let _ := memory_impl in
   let '(world30, mem30, result30) := L30.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok)
                                                              do_call_30 builtins
                                                              world locmem s30 CallOk30
   in let '(world20, result20) :=
     (fix
       interpret_expr_list (world0 : world_state) (loc : string_map uint256) 
                           (e : list AST.expr)
                           (CallOk : FSet.is_subset (L20.Callset.expr_list_callset e)
                                       (L20.Callset.decl_callset (fun_decl fc)) = true) {struct e} :
         world_state * expr_result (list uint256) :=
         match e as e' return (e = e' -> world_state * expr_result (list uint256)) with
         | nil => fun _ : e = nil => (world0, ExprSuccess nil)
         | (h :: t)%list =>
             fun E : e = (h :: t)%list =>
             let (world', result_h) :=
               L20.Expr.interpret_expr Ebound fc do_call_20 builtins world0 loc h
                 (L20.Callset.callset_descend_head E CallOk) in
             match result_h with
             | ExprSuccess x =>
                 let (world'', result_t) :=
                   interpret_expr_list world' loc t (L20.Callset.callset_descend_tail E CallOk) in
                 (world'',
                 match result_t with
                 | ExprSuccess y => ExprSuccess (x :: y)%list
                 | ExprAbort _ => result_t
                 end)
             | ExprAbort ab => (world', ExprAbort ab)
             end
         end eq_refl) world locmap e20 CallOk20
   in world30 = world20 
       /\
      mem_agree offset offset locmem mem30
       /\
      match result20 with
      | ExprSuccess values20 => result30 = StmtSuccess
                                 /\
                                List.length values20 = List.length e20
                                 /\
                                forall i: nat,
                                  i < List.length e20
                                   ->
                                  List.nth_error values20 i
                                   =
                                  Some (OpenArray.get mem30 (offset + N.of_nat i)%N)
      | ExprAbort abort => result30 = StmtAbort abort
      end.
Proof.
cbn. revert world locmem Agree s30 CallOk30 offset Bound ExprOk. induction e20 as [|h]; intros.
{ inversion ExprOk. now subst. }
remember (translate_expr varmap offset (N.succ offset) h) as head30.
destruct head30. { discriminate. }

assert (HeadOk := List.Forall_inv AllOk). cbn in HeadOk.
assert (TailOk := List.Forall_inv_tail AllOk).
clear AllOk.
remember (fix
            translate_expr_list (varmap : string_map N) (offset : N) (exprs : list AST.expr) {struct
                                exprs} : string + AST.stmt :=
              match exprs with
              | nil => inr (AST.SmallStmt AST.Pass)
              | (h :: t)%list =>
                  match translate_expr varmap offset (N.succ offset) h with
                  | inl err => inl err
                  | inr h' =>
                      match translate_expr_list varmap (N.succ offset) t with
                      | inl err => inl err
                      | inr t' => inr (AST.Semicolon h' t')
                      end
                  end
              end) as translate_expr_list.
remember (translate_expr_list varmap (N.succ offset) e20) as tail30.
destruct tail30 as [|tail30]. { discriminate. }
inversion ExprOk. subst s30.

cbn.
assert (H := HeadOk (L20.Callset.callset_descend_head eq_refl CallOk20)
             world locmem offset (N.succ offset) Agree Bound (N.lt_succ_diag_r offset)
             s (eq_sym Heqhead30)
             (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)).
clear HeadOk.
assert (R: (@Callset.callset_descend_semicolon_left C s tail30 (@AST.Semicolon C s tail30)
          (@Callset.decl_callset C
             (@fun_decl C (@AST.decl C) (@Callset.decl_callset C) cd30 bigger_call_depth_bound
                (@translate_fun_ctx C bigger_call_depth_bound cd20 fc cd30 ok)))
             (@eq_refl (@AST.stmt C) (@AST.Semicolon C s tail30)) CallOk30)
             =
         (@Callset.callset_descend_semicolon_left C s tail30 (@AST.Semicolon C s tail30)
            (@Callset.decl_callset C (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
            (@eq_refl (@AST.stmt C) (@AST.Semicolon C s tail30)) CallOk30)).
{ apply PropExtensionality.proof_irrelevance. }
rewrite<- R. clear R.
destruct (Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok) do_call_30 builtins world locmem s
                              (Callset.callset_descend_semicolon_left eq_refl CallOk30))
      as ((world30, mem30), result30).
destruct L20.Expr.interpret_expr as (world20, result20).
destruct result20, result30; try easy.
2:{
  split. { tauto. }
  split. 2:tauto.
  destruct H as (H_world, (H_agree, _)).
  unfold mem_agree in *.
  intros n L NE.
  apply (H_agree n (N.lt_trans _ _ _ L (N.lt_succ_diag_r offset)) NE).
}
destruct H as (H_world, (H_agree, (H_result, H_value))).
subst world20 value.

(* head computation succeeded *)
assert (R:
        (@Callset.callset_descend_semicolon_right C s tail30 (@AST.Semicolon C s tail30)
           (@Callset.decl_callset C
              (@fun_decl C (@AST.decl C) (@Callset.decl_callset C) cd30 bigger_call_depth_bound
                 (@translate_fun_ctx C bigger_call_depth_bound cd20 fc cd30 ok)))
           (@eq_refl (@AST.stmt C) (@AST.Semicolon C s tail30)) CallOk30)
         =
       (@Callset.callset_descend_semicolon_right C s tail30 (@AST.Semicolon C s tail30)
          (@Callset.decl_callset C (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
          (@eq_refl (@AST.stmt C) (@AST.Semicolon C s tail30)) CallOk30)).
{ apply PropExtensionality.proof_irrelevance. }
rewrite<- R. clear R.

assert (Agree': VarsAgree varmap locmap mem30).
{
  unfold VarsAgree in *. intro name.
  assert (A := Agree name).
  assert (B := Bound name).
  destruct (Map.lookup locmap name); destruct (Map.lookup varmap name); try easy.
  unfold mem_agree in H_agree.
  rewrite<- (H_agree n (N.lt_trans _ _ _ B (N.lt_succ_diag_r offset)) (N.lt_neq _ _ B)).
  exact A.
}

assert (IH := IHe20 (L20.Callset.callset_descend_tail eq_refl CallOk20) TailOk world30 mem30
                    Agree'
                    tail30
                    (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30)
                    (N.succ offset) (vars_bound_loosen Bound (N.le_succ_diag_r offset))
                    (eq_sym Heqtail30)).
clear IHe20.
destruct Stmt.interpret_stmt as ((world30', mem30'), result30').
remember (fix
      interpret_expr_list (world0 : world_state) (loc : string_map uint256) 
                          (e : list AST.expr)
                          (CallOk : FSet.is_subset (L20.Callset.expr_list_callset e)
                                      (L20.Callset.decl_callset (fun_decl fc)) = true) {struct e} :
        world_state * expr_result (list uint256) :=
        match e as e' return (e = e' -> world_state * expr_result (list uint256)) with
        | nil => fun _ : e = nil => (world0, ExprSuccess nil)
        | (h0 :: t)%list =>
            fun E : e = (h0 :: t)%list =>
            let (world', result_h) :=
              L20.Expr.interpret_expr Ebound fc do_call_20 builtins world0 loc h0
                (L20.Callset.callset_descend_head E CallOk) in
            match result_h with
            | ExprSuccess x =>
                let (world'', result_t) :=
                  interpret_expr_list world' loc t (L20.Callset.callset_descend_tail E CallOk) in
                (world'',
                match result_t with
                | ExprSuccess y => ExprSuccess (x :: y)%list
                | ExprAbort _ => result_t
                end)
            | ExprAbort ab => (world', ExprAbort ab)
            end
        end eq_refl) as interpret_expr_list.
destruct (interpret_expr_list world30 locmap e20
            (L20.Callset.callset_descend_tail eq_refl CallOk20))
  as (world20', result20').
destruct IH as (IH_world, (IH_agree, IH')).
assert (Agree'': mem_agree offset offset locmem mem30').
{
  unfold mem_agree in *.
  intros n L NE.
  rewrite (H_agree n (N.lt_trans _ _ _ L (N.lt_succ_diag_r offset)) NE).
  assert (NE' := N.lt_trans _ _ _ L (N.lt_succ_diag_r offset)).
  apply (IH_agree n NE' (N.lt_neq _ _ NE')).
}
destruct result20', result30'; try easy.
destruct IH' as (_, (IH_len, IH_value)).
(* tail computation is finished *)
split. { assumption. }
clear translate_expr_list Heqtranslate_expr_list ExprOk TailOk Heqhead30 Heqtail30.
split.
{
  unfold mem_agree in *.
  intros n L NE.
  rewrite (H_agree n (N.lt_trans _ _ _ L (N.lt_succ_diag_r offset)) NE).
  assert (NE' := N.lt_trans _ _ _ L (N.lt_succ_diag_r offset)).
  apply (IH_agree n NE' (N.lt_neq _ _ NE')).
}
split. { trivial. }
split. { cbn. now rewrite IH_len. }
intro i.
destruct i; cbn.
{
  intro Foo. clear Foo.
  f_equal.
  rewrite N.add_0_r.
  apply IH_agree. { apply N.lt_succ_diag_r. }
  apply N.lt_neq. apply N.lt_succ_diag_r.
}
intro L.
apply lt_S_n in L.
rewrite (IH_value i L).
f_equal. f_equal.
lia.
Qed.

(* XXX move *)
Lemma list_eq_by_items {T: Type} (a b: list T)
                       (Ok: forall i: nat,
                                 List.nth_error a i
                                  =
                                 List.nth_error b i):
  a = b.
Proof.
revert b Ok. induction a as [|ha]; intros; assert (Ok0 := Ok 0); cbn in *.
{ now destruct b. }
destruct b as [|hb]. { easy. }
inversion Ok0. subst hb. f_equal.
apply IHa. intro i.
assert (OkSi := Ok (S i)).
apply OkSi.
Qed.

Lemma interpret_translated_expr {C: VyperConfig}
                                {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                {cd20: L20.Descend.calldag}
                                (builtins: string -> option builtin)
                                (fc: fun_ctx cd20 bigger_call_depth_bound)
                                {cd30: L30.Descend.calldag}
                                (ok: translate_calldag cd20 = inr cd30)
                                {do_call_20: forall
                                      (fc': fun_ctx cd20 smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                {do_call_30: forall
                                      (fc': fun_ctx cd30 smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256}
                                (DoCallOk: forall fc' world arg_values,
                                             do_call_30 (translate_fun_ctx fc' ok) world arg_values
                                              =
                                             do_call_20 fc' world arg_values)
                                (world: world_state)
                                (locmap: string_map uint256)
                                (locmem: memory)
                                {e20: L20.AST.expr}
                                {s30: L30.AST.stmt}
                                (varmap: string_map N)
                                (dst offset: N)
                                (Agree: VarsAgree varmap locmap locmem)
                                (Bound: VarsBound varmap dst)
                                (OffsetOk: (dst < offset)%N)
                                (ExprOk: translate_expr varmap dst offset e20 = inr s30)
                                (CallOk30: let _ := string_set_impl in 
                                   FSet.is_subset (L30.Callset.stmt_callset s30)
                                                  (L30.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk20: let _ := string_set_impl in 
                                   FSet.is_subset (L20.Callset.expr_callset e20)
                                                  (L20.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
   let _ := string_map_impl in
   let _ := memory_impl in
   let '(world30, mem30, result30) := L30.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok)
                                                              do_call_30 builtins
                                                              world locmem s30 CallOk30
   in let '(world20, result20) := L20.Expr.interpret_expr Ebound fc do_call_20 builtins
                                                          world locmap e20 CallOk20
   in world30 = world20
       /\
      mem_agree offset dst locmem mem30
       /\
      match result20 with
      | ExprSuccess value20 => result30 = StmtSuccess
                                /\
                               OpenArray.get mem30 dst = value20
      | ExprAbort abort => result30 = StmtAbort abort
      end.
Proof.
revert world locmem dst offset Agree Bound OffsetOk s30 ExprOk CallOk30.
induction e20 using L20.AST.expr_ind'; intros; cbn in ExprOk.
{ (* Const *)
  inversion ExprOk. subst.
  split. { trivial. }
  split.
  {
    unfold mem_agree. intros n L NE.
    rewrite OpenArray.put_ok.
    enough (F: (dst =? n)%N = false) by now rewrite F.
    apply N.eqb_neq. intro E. symmetry in E. tauto.
  }
  split. { trivial. }
  now rewrite OpenArray.put_same.
}
{ (* LocalVar *)
  assert (A := Agree name).
  unfold map_lookup in *.
  remember (Map.lookup locmap name) as look_locmap. destruct look_locmap as [value | ].
  2:{ now destruct (Map.lookup varmap name). }
  (* the variable is found *)
  destruct (Map.lookup varmap name). 2:{ contradiction. }
  inversion ExprOk. subst s30. cbn.
  unfold map_lookup.
  rewrite<- Heqlook_locmap.
  split. { trivial. }
  split.
  {
    unfold mem_agree. intros k L NE.
    rewrite OpenArray.put_ok.
    enough (F: (dst =? k)%N = false) by now rewrite F.
    apply N.eqb_neq. intro E. symmetry in E. tauto.
  }
  split. { trivial. }
  now rewrite OpenArray.put_same.
}
{ (* StorageVar *)
  inversion ExprOk. subst s30. clear ExprOk.
  cbn.
  unfold L20.Expr.storage_var_is_declared.
  assert (D := translate_fun_ctx_declmap ok name).
  destruct (cd_declmap cd20 name) as [vardecl20 | ];
    destruct (cd_declmap cd30 name) as [vardecl30 | ]; try discriminate.
  2:easy.
  destruct vardecl20; cbn in D.
  {
    inversion D. subst vardecl30.
    split. { trivial. }
    split.
    {
      unfold mem_agree. intros n L NE.
      rewrite OpenArray.put_ok.
      enough (F: (dst =? n)%N = false) by now rewrite F.
      apply N.eqb_neq. intro E. symmetry in E. tauto.
    }
    split. { trivial. }
    apply OpenArray.put_same.
  }
  destruct make_varmap. { discriminate. }
  destruct translate_stmt. { discriminate. }
  inversion D. subst vardecl30.
  easy.
}
{ (* UnOp *)
  remember (translate_expr varmap dst offset e20) as t.
  destruct t. { discriminate. }
  inversion ExprOk. subst s30. cbn. clear ExprOk.
  assert (IH := IHe20 (L20.Callset.callset_descend_unop eq_refl CallOk20) 
                      world locmem dst offset Agree Bound OffsetOk s0 (eq_sym Heqt)
                      (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)).
  cbn in IH.
  destruct L30.Stmt.interpret_stmt as ((world30, mem30), result30).
  destruct L20.Expr.interpret_expr as (world20, result20).
  destruct result20, result30; try destruct IH as (I_world, (I_agree, (I_result, I_dst)));
    try easy.
  (* both computations are successful *)
  subst value.
  destruct interpret_unop. 2:{ tauto. }
  split. { trivial. }
  split.
  {
    unfold mem_agree in *. intros n L NE.
    rewrite OpenArray.put_ok.
    assert (A := I_agree n L NE).
    enough (F: (dst =? n)%N = false) by now rewrite F.
    apply N.eqb_neq. intro E. symmetry in E. tauto.
  }
  split. { trivial. }
  apply OpenArray.put_same.
}
{ (* BinOp *)
  remember (translate_expr varmap dst offset e20_1) as t_1.
  destruct t_1. { discriminate. }
  remember (translate_expr varmap offset (N.succ offset) e20_2) as t_2. 
  destruct t_2. { discriminate. }
  inversion ExprOk. subst s30. cbn. clear ExprOk.
  assert (IH_1 := IHe20_1 (L20.Callset.callset_descend_binop_left eq_refl CallOk20)
                          world locmem dst offset Agree Bound OffsetOk s0 (eq_sym Heqt_1)
                          (L30.Callset.callset_descend_semicolon_left eq_refl
                            (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30))).
  assert (Bound2: VarsBound varmap offset).
  {
    apply (vars_bound_loosen Bound).
    apply N.lt_le_incl.
    assumption.
  }
  cbn in IH_1. clear IHe20_1.
  destruct L30.Stmt.interpret_stmt as ((world30_1, mem30_1), result30_1).
  destruct L20.Expr.interpret_expr as (world20_1, result20_1).
  destruct result20_1, result30_1;
    try destruct IH_1 as (I1_world, (I1_agree, (I1_result, I1_dst)));
    try easy.
  (* both computations of the left operand are successful *)
  subst world20_1 value.
  assert (IH_2 := IHe20_2 (L20.Callset.callset_descend_binop_right eq_refl CallOk20)
                          world30_1 mem30_1 offset (N.succ offset)
                          (vars_agree_if_mem_agree _ _ _ _ Agree _ _ Bound OffsetOk I1_agree)
                          Bound2
                          (N.lt_succ_diag_r offset)
                          s1 (eq_sym Heqt_2)
                          (L30.Callset.callset_descend_semicolon_right eq_refl
                            (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30))).
  cbn in IH_2. clear IHe20_2.
  destruct L30.Stmt.interpret_stmt as ((world30_2, mem30_2), result30_2).
  destruct L20.Expr.interpret_expr as (world20_2, result20_2).
  destruct result20_2, result30_2;
    try destruct IH_2 as (I2_world, (I2_agree, (I2_result, I2_dst)));
    try easy.
  {
    (* both computations of the right operand are successful *)
    subst world20_2 value.
    assert (A: OpenArray.get mem30_1 dst = OpenArray.get mem30_2 dst).
    {
      apply I2_agree.
      { apply (N.lt_trans _ _ _ OffsetOk (N.lt_succ_diag_r _)). }
      apply (N.lt_neq _ _ OffsetOk).
    }
    unfold m in *.
    rewrite A.
    destruct interpret_binop.
    2:{
      split. { trivial. }
      split. 2:{ trivial. }
      unfold mem_agree in *. intros n L NE.
      rewrite I1_agree by assumption.
      apply I2_agree.
      apply (N.lt_trans _ _ _ L (N.lt_succ_diag_r _)).
      apply (N.lt_neq _ _ L).
    }
    split. { trivial. }
    split.
    {
      unfold mem_agree in *. intros n L NE.
      rewrite OpenArray.put_ok.
      assert (F: (dst =? n)%N = false).
      { apply N.eqb_neq. intro E. symmetry in E. tauto. }
      rewrite F.
      rewrite I1_agree by assumption.
      apply I2_agree.
      { apply (N.lt_trans _ _ _ L (N.lt_succ_diag_r _)). }
      apply (N.lt_neq _ _ L).
    }
    split. { trivial. }
    apply OpenArray.put_same.
  }
  destruct IH_2 as (I2_world, (I2_agree, I2_result)).
  split. { tauto. }
  split. 2:{ tauto. }
  unfold mem_agree in *. intros n L NE.
  rewrite I1_agree by assumption.
  apply I2_agree.
  apply (N.lt_trans _ _ _ L (N.lt_succ_diag_r _)).
  apply (N.lt_neq _ _ L).
}
{ (* IfThenElse *)
  remember (translate_expr varmap dst offset e20_1) as t_cond.
  destruct t_cond. { discriminate. }
  remember (translate_expr varmap dst offset e20_2) as t_yes.
  destruct t_yes. { discriminate. }
  remember (translate_expr varmap dst offset e20_3) as t_no.
  destruct t_no. { discriminate. }
  inversion ExprOk. subst s30. cbn. clear ExprOk.
  assert (IH_1 := IHe20_1 (L20.Callset.callset_descend_if_cond eq_refl CallOk20)
                          world locmem dst offset Agree Bound OffsetOk s0 (eq_sym Heqt_cond)
                          (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)).
  cbn in IH_1. clear IHe20_1.
  destruct L30.Stmt.interpret_stmt as ((world30_1, mem30_1), result30_1).
  destruct L20.Expr.interpret_expr as (world20_1, result20_1).
  destruct result20_1, result30_1;
    try destruct IH_1 as (I1_world, (I1_agree, (I1_result, I1_dst)));
    try easy.
  (* cond computation succeeded *)
  subst value.
  destruct (Z_of_uint256 (OpenArray.get mem30_1 dst) =? 0)%Z.
  {
    (* else *)
    clear IHe20_2. subst world20_1.
    assert (IH_3 := IHe20_3 (L20.Callset.callset_descend_if_else eq_refl CallOk20)
                        world30_1 mem30_1 dst offset
                        (vars_agree_if_mem_agree _ _ _ _ Agree _ _ Bound OffsetOk I1_agree)
                        Bound OffsetOk s2 (eq_sym Heqt_no)
                        (L30.Callset.callset_descend_stmt_if_else eq_refl
                          (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30))).
    cbn in IH_3. clear IHe20_3.
    destruct L30.Stmt.interpret_stmt as ((world30_3, mem30_3), result30_3).
    destruct L20.Expr.interpret_expr as (world20_3, result20_3).
    destruct result20_3, result30_3;
      try destruct IH_3 as (I3_world, (I3_agree, (I3_result, I3_dst)));
      try easy.
    {
      (* else branch computation succeeded *)
      split. { trivial. }
      split. 2:tauto.
      unfold mem_agree in *. intros.
      rewrite I1_agree by assumption.
      apply I3_agree; assumption.
    }
    destruct IH_3 as (I3_world, (I3_agree, I3_result)).
    split. { tauto. }
    split. 2:tauto.
    unfold mem_agree in *. intros.
    rewrite I1_agree by assumption.
    apply I3_agree; assumption.
  }
  (* then *)
  clear IHe20_3. subst world20_1.
  assert (IH_2 := IHe20_2 (L20.Callset.callset_descend_if_then eq_refl CallOk20)
                      world30_1 mem30_1 dst offset
                      (vars_agree_if_mem_agree _ _ _ _ Agree _ _ Bound OffsetOk I1_agree)
                      Bound OffsetOk s1 (eq_sym Heqt_yes)
                      (L30.Callset.callset_descend_stmt_if_then eq_refl
                        (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30))).
  cbn in IH_2. clear IHe20_2.
  destruct L30.Stmt.interpret_stmt as ((world30_2, mem30_2), result30_2).
  destruct L20.Expr.interpret_expr as (world20_2, result20_2).
  destruct result20_2, result30_2;
    try destruct IH_2 as (I2_world, (I2_agree, (I2_result, I2_dst)));
    try easy.
  {
    (* then branch computation succeeded *)
    split. { trivial. }
    split. 2:tauto.
    unfold mem_agree in *. intros.
    rewrite I1_agree by assumption.
    apply I2_agree; assumption.
  }
  destruct IH_2 as (I2_world, (I2_agree, I2_result)).
  split. { tauto. }
  split. 2:tauto.
  unfold mem_agree in *. intros.
  rewrite I1_agree by assumption.
  apply I2_agree; assumption.
}
{ (* LogicalAnd *)
  remember (translate_expr varmap dst offset e20_1) as t_1.
  destruct t_1. { discriminate. }
  remember (translate_expr varmap dst offset e20_2) as t_2.
  destruct t_2. { discriminate. }
  inversion ExprOk. subst s30. cbn. clear ExprOk.
  assert (IH_1 := IHe20_1 (L20.Callset.callset_descend_and_left eq_refl CallOk20)
                        world locmem dst offset Agree Bound OffsetOk s0 (eq_sym Heqt_1)
                        (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)).
  cbn in IH_1. clear IHe20_1.
  destruct L30.Stmt.interpret_stmt as ((world30_1, mem30_1), result30_1).
  destruct L20.Expr.interpret_expr as (world20_1, result20_1).
  destruct result20_1, result30_1;
    try destruct IH_1 as (I1_world, (I1_agree, (I1_result, I1_dst)));
    try easy.
  (* left operand computation succeeded *)
  subst value.
  destruct (Z_of_uint256 (OpenArray.get mem30_1 dst) =? 0)%Z.
  {
    split. { trivial. }
    split. { assumption. }
    split. { trivial. }
    trivial.
  }
  (* we'll compute the right operand *)
  subst world20_1.
  assert (IH_2 := IHe20_2 (L20.Callset.callset_descend_and_right eq_refl CallOk20)
                      world30_1 mem30_1 dst offset
                      (vars_agree_if_mem_agree _ _ _ _ Agree _ _ Bound OffsetOk I1_agree)
                      Bound OffsetOk s1 (eq_sym Heqt_2)
                      (L30.Callset.callset_descend_stmt_if_then eq_refl
                        (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30))).
  cbn in IH_2. clear IHe20_2.
  destruct L30.Stmt.interpret_stmt as ((world30_2, mem30_2), result30_2).
  destruct L20.Expr.interpret_expr as (world20_2, result20_2).
  destruct result20_2, result30_2;
    try destruct IH_2 as (I2_world, (I2_agree, (I2_result, I2_dst)));
    try easy.
  {
    (* right operand computation succeeded *)
    split. { trivial. }
    split. 2:tauto.
    unfold mem_agree in *. intros.
    rewrite I1_agree by assumption.
    apply I2_agree; assumption.
  }
  destruct IH_2 as (I2_world, (I2_agree, I2_result)).
  split. { trivial. }
  split. 2:tauto.
  unfold mem_agree in *. intros.
  rewrite I1_agree by assumption.
  apply I2_agree; assumption.
}
{ (* LogicalOr *)
  remember (translate_expr varmap dst offset e20_1) as t_1.
  destruct t_1. { discriminate. }
  remember (translate_expr varmap dst offset e20_2) as t_2.
  destruct t_2. { discriminate. }
  inversion ExprOk. subst s30. cbn. clear ExprOk.
  assert (IH_1 := IHe20_1 (L20.Callset.callset_descend_or_left eq_refl CallOk20)
                        world locmem dst offset Agree Bound OffsetOk s0 (eq_sym Heqt_1)
                        (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)).
  cbn in IH_1. clear IHe20_1.
  destruct L30.Stmt.interpret_stmt as ((world30_1, mem30_1), result30_1).
  destruct L20.Expr.interpret_expr as (world20_1, result20_1).
  destruct result20_1, result30_1;
    try destruct IH_1 as (I1_world, (I1_agree, (I1_result, I1_dst)));
    try easy.
  (* left operand computation succeeded *)
  subst value.
  destruct (Z_of_uint256 (OpenArray.get mem30_1 dst) =? 0)%Z.
  2:{
    split. { trivial. }
    split. { trivial. }
    split. { assumption. }
    trivial.
  }
  (* we'll compute the right operand *)
  subst world20_1.
  assert (IH_2 := IHe20_2 (L20.Callset.callset_descend_or_right eq_refl CallOk20)
                      world30_1 mem30_1 dst offset
                      (vars_agree_if_mem_agree _ _ _ _ Agree _ _ Bound OffsetOk I1_agree)
                      Bound OffsetOk s1 (eq_sym Heqt_2)
                      (L30.Callset.callset_descend_stmt_if_else eq_refl
                        (L30.Callset.callset_descend_semicolon_right eq_refl CallOk30))).
  cbn in IH_2. clear IHe20_2.
  destruct L30.Stmt.interpret_stmt as ((world30_2, mem30_2), result30_2).
  destruct L20.Expr.interpret_expr as (world20_2, result20_2).
  destruct result20_2, result30_2;
    try destruct IH_2 as (I2_world, (I2_agree, (I2_result, I2_dst)));
    try easy.
  {
    (* right operand computation succeeded *)
    split. { trivial. }
    split. 2:tauto.
    unfold mem_agree in *. intros.
    rewrite I1_agree by assumption.
    apply I2_agree; assumption.
  }
  destruct IH_2 as (I2_world, (I2_agree, I2_result)).
  split. { assumption. }
  split. 2:tauto.
  unfold mem_agree in *. intros.
  rewrite I1_agree by assumption.
  apply I2_agree; assumption.
}
{ (* PrivateCall *)
  remember (_ varmap offset args) as translated_args.
  destruct translated_args. { discriminate. }
  inversion ExprOk. subst s30. clear ExprOk. clear s. unfold m. clear m.
  assert (ArgsOk := weak_interpret_translated_exprs Ebound builtins fc ok DoCallOk
                    world locmap locmem varmap offset Agree 
                    (vars_bound_loosen Bound (N.lt_le_incl _ _ OffsetOk))
                    (eq_sym Heqtranslated_args)
                    (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                    (L20.Callset.callset_descend_args eq_refl CallOk20)
                    H).
  cbn in ArgsOk. clear H Heqtranslated_args. cbn.
  destruct L30.Stmt.interpret_stmt as ((world30_args, mem30_args), result30_args).
  remember (fix
      interpret_expr_list (world0 : world_state) (loc : string_map uint256) 
                          (e : list AST.expr)
                          (CallOk : FSet.is_subset (L20.Callset.expr_list_callset e)
                                      (L20.Callset.decl_callset (fun_decl fc)) = true) {struct e} :
        world_state * expr_result (list uint256) :=
        match e as e' return (e = e' -> world_state * expr_result (list uint256)) with
        | nil => fun _ : e = nil => (world0, ExprSuccess nil)
        | (h0 :: t)%list =>
            fun E : e = (h0 :: t)%list =>
            let (world', result_h) :=
              L20.Expr.interpret_expr Ebound fc do_call_20 builtins world0 loc h0
                (L20.Callset.callset_descend_head E CallOk) in
            match result_h with
            | ExprSuccess x =>
                let (world'', result_t) :=
                  interpret_expr_list world' loc t (L20.Callset.callset_descend_tail E CallOk) in
                (world'',
                match result_t with
                | ExprSuccess y => ExprSuccess (x :: y)%list
                | ExprAbort _ => result_t
                end)
            | ExprAbort ab => (world', ExprAbort ab)
            end
        end eq_refl) as interpret_expr_list.
  destruct interpret_expr_list as (world20_args, result20_args).
  destruct result20_args, result30_args; try easy.
  2:{
    destruct ArgsOk as (Args_world, (Args_agree, Args_result)).
    split. { trivial. }
    split. 2:trivial.
    intros x L NE.
    exact (Args_agree x L (N.lt_neq _ _ L)).
  }
  destruct ArgsOk as (Args_world, (Args_agree, (Args_result, (Args_len, Args_dst)))).
  (* args computation has succeeded *)

  assert (D: L30.Descend.fun_ctx_descend (translate_fun_ctx fc ok)
              (Callset.callset_descend_small_stmt eq_refl
                (Callset.callset_descend_semicolon_right eq_refl CallOk30))
              Ebound eq_refl
              =
             match L20.Descend.fun_ctx_descend fc CallOk20 Ebound eq_refl with
             | Some ctx => Some (translate_fun_ctx ctx ok)
             | None => None
             end).
  {
    (* This follows fun_ctx_descend_irrel. *)
    unfold L20.Descend.fun_ctx_descend.
    unfold L30.Descend.fun_ctx_descend.
    assert (InnerOk: forall (d1: L20.AST.decl)
                            (Edecl1: cd_declmap cd20 name = Some d1)
                            (d2: L30.AST.decl)
                            (Edecl2: cd_declmap cd30 name = Some d2),
                   L30.Descend.fun_ctx_descend_inner (translate_fun_ctx fc ok)
                      (Callset.callset_descend_small_stmt eq_refl
                        (Callset.callset_descend_semicolon_right eq_refl CallOk30))
                      Ebound eq_refl Edecl2
                    =
                   match L20.Descend.fun_ctx_descend_inner fc CallOk20 Ebound eq_refl Edecl1 with
                   | Some ctx20 => Some (translate_fun_ctx ctx20 ok)
                   | None => None
                   end).
    {
      intros.
      unfold L20.Descend.fun_ctx_descend_inner.
      unfold L30.Descend.fun_ctx_descend_inner.
      remember (fun (depth: nat) (Edepth: cd_depthmap cd30 name = Some depth) =>
          Some
            {|
            fun_name := name;
            fun_depth := depth;
            fun_depth_ok := Edepth;
            fun_decl := d2;
            fun_decl_ok := Edecl2;
            fun_bound_ok := L30.Descend.call_descend' (translate_fun_ctx fc ok)
                        (Callset.callset_descend_small_stmt eq_refl
                           (Callset.callset_descend_semicolon_right eq_refl CallOk30)) Ebound eq_refl
                              Edecl2 Edepth |})
        as some_branch_l.
      remember (fun Edepth : cd_depthmap cd30 name = None =>
                  False_rect (option (fun_ctx cd30 smaller_call_depth_bound))
                             (Descend.fun_ctx_descend_helper Edecl2 Edepth))
        as none_branch_l.
      remember (fun (depth: nat) (Edepth: cd_depthmap cd20 name = Some depth) =>
        Some
          {|
          fun_name := name;
          fun_depth := depth;
          fun_depth_ok := Edepth;
          fun_decl := d1;
          fun_decl_ok := Edecl1;
          fun_bound_ok := L20.Descend.call_descend' fc CallOk20 Ebound eq_refl Edecl1 Edepth |})
        as some_branch_r.
      remember (fun Edepth : cd_depthmap cd20 name = None =>
                    False_rect (option (fun_ctx cd20 smaller_call_depth_bound))
                      (L20.Descend.fun_ctx_descend_helper Edecl1 Edepth))
        as none_branch_r.
      assert (NoneOkL: forall (Edepth: cd_depthmap cd30 name = None),
                         none_branch_l Edepth = None).
      { intro. exfalso. exact (L30.Descend.fun_ctx_descend_helper Edecl2 Edepth). }
      assert (NoneOkR: forall (Edepth: cd_depthmap cd20 name = None),
                         none_branch_r Edepth = None).
      { intro. exfalso. exact (L20.Descend.fun_ctx_descend_helper Edecl1 Edepth). }
      clear Heqnone_branch_l Heqnone_branch_r.
      revert none_branch_l none_branch_r NoneOkL NoneOkR.
      assert (SomeBranchOk: forall (depth: nat)
                                   (Edepth1: cd_depthmap cd20 name = Some depth)
                                   (Edepth2: cd_depthmap cd30 name = Some depth),
                     some_branch_l depth Edepth2 
                      =
                     match some_branch_r depth Edepth1 with
                     | Some ctx20 => Some (translate_fun_ctx ctx20 ok)
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
                fun_bound_ok := L20.Descend.call_descend' fc CallOk20 eq_refl eq_refl Edecl1 Edepth1 |}
                ok).
        {
          unfold cached_translated_decl. cbn.
          remember (FunCtx.translate_fun_ctx_fun_decl_helper _ ok) as Bad. clear HeqBad.
          cbn in Bad. revert Bad.
          destruct (cd_declmap cd30 name). { now inversion Edecl2. }
          intro Bad. discriminate.
        }
        subst. f_equal; apply PropExtensionality.proof_irrelevance.
      } (* SomeBranchOk *)
      clear Heqsome_branch_l Heqsome_branch_r
            CallOk20 CallOk30 Edecl1 Edecl2 d1 d2 args value DoCallOk
            do_call_20 do_call_30 Heqinterpret_expr_list Args_dst Args_len.
      revert some_branch_l some_branch_r SomeBranchOk.
      rewrite (translate_fun_ctx_depthmap ok name).
      destruct (cd_depthmap cd20 name); intros. { apply SomeBranchOk. }
      rewrite (NoneOkL eq_refl).
      rewrite (NoneOkR eq_refl).
      trivial.
    } (* InnerOk *)
    remember L30.Descend.fun_ctx_descend_inner as inner30. clear Heqinner30.
    remember L20.Descend.fun_ctx_descend_inner as inner20. clear Heqinner20.
    subst.
    remember (cd_declmap cd20 name) as maybe_d20.
    remember (fun d0 (Edecl : cd_declmap cd30 name = Some d0) =>
                    inner30 (translate_fun_ctx fc ok)
                      (Callset.callset_descend_small_stmt eq_refl
                         (Callset.callset_descend_semicolon_right eq_refl CallOk30)) eq_refl name dst offset
                      (N.of_nat (Datatypes.length args)) eq_refl d0 Edecl)
      as some_branch.
    destruct maybe_d20.
    {
      assert (SomeBranchOk: forall (d30: L30.AST.decl)
                                   (Edecl: cd_declmap cd30 name = Some d30),
                     some_branch d30 Edecl
                      =
                     match inner20 fc CallOk20 eq_refl eq_refl d eq_refl with
                     | Some ctx => Some (translate_fun_ctx ctx ok)
                     | None => None
                     end).
      { apply InnerOk. }
      clear Heqsome_branch.
      remember (cd_declmap cd30 name) as maybe_d30.
      destruct maybe_d30. { apply SomeBranchOk. }
      assert (T := translate_fun_ctx_declmap ok name).
      rewrite<- Heqmaybe_d20 in T. rewrite<- Heqmaybe_d30 in T.
      discriminate.
    }
    assert (SomeBranchOk: forall (d30: L30.AST.decl)
                             (Edecl: cd_declmap cd30 name = Some d30),
               some_branch d30 Edecl
                =
               None).
    {
      intros.
      assert (T := translate_fun_ctx_declmap ok name).
      rewrite<- Heqmaybe_d20 in T. rewrite Edecl in T.
      discriminate.
    }
    clear Heqsome_branch.
    now destruct (cd_declmap cd30 name).
  } (* D *)
  assert (R: (@Callset.callset_descend_small_stmt C
         (@AST.SmallStmt C
            (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args))))
         (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args)))
         (@Callset.decl_callset C
            (@fun_decl C (@AST.decl C) (@Callset.decl_callset C) cd30 bigger_call_depth_bound
               (@translate_fun_ctx C bigger_call_depth_bound cd20 fc cd30 ok)))
         (@eq_refl (@AST.stmt C)
            (@AST.SmallStmt C
               (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args)))))
         (@Callset.callset_descend_semicolon_right C s0
            (@AST.SmallStmt C
               (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args))))
            (@AST.Semicolon C s0
               (@AST.SmallStmt C
                  (@AST.PrivateCall C dst name offset
                     (N.of_nat (@Datatypes.length (@AST.expr C) args)))))
            (@Callset.decl_callset C
               (@fun_decl C (@AST.decl C) (@Callset.decl_callset C) cd30 bigger_call_depth_bound
                  (@translate_fun_ctx C bigger_call_depth_bound cd20 fc cd30 ok)))
            (@eq_refl (@AST.stmt C)
               (@AST.Semicolon C s0
                  (@AST.SmallStmt C
                     (@AST.PrivateCall C dst name offset
                        (N.of_nat (@Datatypes.length (@AST.expr C) args)))))) CallOk30))
            =
         (@Callset.callset_descend_small_stmt C
            (@AST.SmallStmt C
               (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args))))
            (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args)))
            (@Callset.decl_callset C (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
            (@eq_refl (@AST.stmt C)
               (@AST.SmallStmt C
                  (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args)))))
            (@Callset.callset_descend_semicolon_right C s0
               (@AST.SmallStmt C
                  (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args))))
               (@AST.Semicolon C s0
                  (@AST.SmallStmt C
                     (@AST.PrivateCall C dst name offset (N.of_nat (@Datatypes.length (@AST.expr C) args)))))
               (@Callset.decl_callset C
                  (@cached_translated_decl C bigger_call_depth_bound cd20 fc cd30 ok))
               (@eq_refl (@AST.stmt C)
                  (@AST.Semicolon C s0
                     (@AST.SmallStmt C
                        (@AST.PrivateCall C dst name offset
                           (N.of_nat (@Datatypes.length (@AST.expr C) args)))))) CallOk30))).
  { apply PropExtensionality.proof_irrelevance. }
  rewrite<- R. clear R.
  rewrite D. clear D.
  destruct (L20.Descend.fun_ctx_descend fc CallOk20 Ebound eq_refl).
  2:{
    split. { assumption. }
    split. 2:easy.
    unfold mem_agree in *.
    intros x L NE.
    exact (Args_agree x L (N.lt_neq _ _ L)).
  }
  rewrite DoCallOk. rewrite Args_world.

  assert (V: let _ := memory_impl in
             OpenArray.view mem30_args offset (N.of_nat (Datatypes.length args)) = value).
  {
    clear interpret_expr_list Heqinterpret_expr_list CallOk30 world30_args world20_args
          f Args_world Args_agree CallOk20 dst OffsetOk Bound.
    apply list_eq_by_items.
    intro i.
    assert (OkV := let _ := memory_impl in
                   OpenArray.view_ok mem30_args offset (N.of_nat (Datatypes.length args))).
    assert (K := Nat.lt_ge_cases i (List.length args)).
    case K; clear K; intro K.
    {
      rewrite (Args_dst i K).
      rewrite<- (OkV (N.of_nat i)).
      { now rewrite Nat2N.id. }
      lia.
    }
    assert (L := K).
    rewrite<- Args_len in L.
    rewrite<- List.nth_error_None in L. rewrite L.
    apply List.nth_error_None.
    rewrite OpenArray.view_len.
    lia.
  } (* V *)
  rewrite V.
  destruct (do_call_20 f world20_args value).
  destruct e as [value20|].
  2:{
    split. { trivial. }
    split. 2:trivial.
    intros n L NE.
    apply (Args_agree n L (N.lt_neq _ _ L)).
  }
  split. { trivial. }
  split.
  2:{
    split. { trivial. }
    apply OpenArray.put_same.
  }
  unfold mem_agree in *.
  intros n L NE.
  rewrite (Args_agree n L (N.lt_neq _ _ L)).
  rewrite OpenArray.put_ok.
  enough (F: (dst =? n)%N = false) by now rewrite F.
  rewrite N.eqb_sym.
  apply N.eqb_neq.
  exact NE.
}
(* BuiltinCall *)
remember (_ varmap offset args) as translated_args.
destruct translated_args. { discriminate. }
inversion ExprOk. subst s30. clear ExprOk. clear s. unfold m. clear m.
assert (ArgsOk := weak_interpret_translated_exprs Ebound builtins fc ok DoCallOk
                  world locmap locmem varmap offset Agree 
                  (vars_bound_loosen Bound (N.lt_le_incl _ _ OffsetOk))
                  (eq_sym Heqtranslated_args)
                  (L30.Callset.callset_descend_semicolon_left eq_refl CallOk30)
                  (L20.Callset.callset_descend_builtin_args eq_refl CallOk20)
                  H).
cbn in ArgsOk. clear H Heqtranslated_args. cbn.
destruct L30.Stmt.interpret_stmt as ((world30_args, mem30_args), result30_args).
remember (fix
    interpret_expr_list (world0 : world_state) (loc : string_map uint256) 
                        (e : list AST.expr)
                        (CallOk : FSet.is_subset (L20.Callset.expr_list_callset e)
                                    (L20.Callset.decl_callset (fun_decl fc)) = true) {struct e} :
      world_state * expr_result (list uint256) :=
      match e as e' return (e = e' -> world_state * expr_result (list uint256)) with
      | nil => fun _ : e = nil => (world0, ExprSuccess nil)
      | (h0 :: t)%list =>
          fun E : e = (h0 :: t)%list =>
          let (world', result_h) :=
            L20.Expr.interpret_expr Ebound fc do_call_20 builtins world0 loc h0
              (L20.Callset.callset_descend_head E CallOk) in
          match result_h with
          | ExprSuccess x =>
              let (world'', result_t) :=
                interpret_expr_list world' loc t (L20.Callset.callset_descend_tail E CallOk) in
              (world'',
              match result_t with
              | ExprSuccess y => ExprSuccess (x :: y)%list
              | ExprAbort _ => result_t
              end)
          | ExprAbort ab => (world', ExprAbort ab)
          end
      end eq_refl) as interpret_expr_list.
destruct interpret_expr_list as (world20_args, result20_args).
destruct result20_args, result30_args; try easy.
2:{
  destruct ArgsOk as (Args_world, (Args_agree, Args_result)).
  split. { trivial. }
  split. 2:{ trivial. }
  intros n L NE.
  apply (Args_agree n L (N.lt_neq _ _ L)).
}
destruct ArgsOk as (Args_world, (Args_agree, (Args_result, (Args_len, Args_dst)))).

assert (V: let _ := memory_impl in
           OpenArray.view mem30_args offset (N.of_nat (Datatypes.length args)) = value).
{
  clear interpret_expr_list Heqinterpret_expr_list CallOk30 world30_args world20_args
        Args_world Args_agree CallOk20 dst OffsetOk Bound.
  apply list_eq_by_items.
  intro i.
  assert (OkV := let _ := memory_impl in
                 OpenArray.view_ok mem30_args offset (N.of_nat (Datatypes.length args))).
  assert (K := Nat.lt_ge_cases i (List.length args)).
  case K; clear K; intro K.
  {
    rewrite (Args_dst i K).
    rewrite<- (OkV (N.of_nat i)).
    { now rewrite Nat2N.id. }
    lia.
  }
  assert (L := K).
  rewrite<- Args_len in L.
  rewrite<- List.nth_error_None in L. rewrite L.
  apply List.nth_error_None.
  rewrite OpenArray.view_len.
  lia.
} (* V *)

destruct (builtins name) as [(arity, builtin)|].
2:{
  split. { assumption. }
  split. 2:easy.
  intros n L NE.
  apply (Args_agree n L (N.lt_neq _ _ L)).
}
remember (fun Earity : (arity =? Datatypes.length (OpenArray.view mem30_args offset (N.of_nat (Datatypes.length args)))) = true =>
   let '(world', call_result) :=
     call_builtin (OpenArray.view mem30_args offset (N.of_nat (Datatypes.length args))) Earity (builtin world30_args) in
   match call_result with
   | ExprSuccess result => (world', OpenArray.put mem30_args dst result, StmtSuccess)
   | ExprAbort ab => (world', mem30_args, StmtAbort ab)
   end) as good_branch_30.
assert (GoodBranch30Ok: let _ := memory_impl in
         forall Earity: (arity =? Datatypes.length (OpenArray.view mem30_args offset (N.of_nat (Datatypes.length args))) = true),
          let '(world30, mem30, result30) := good_branch_30 Earity in
           let '(world20, result20) :=
            (if arity =? Datatypes.length value as arity_ok
              return ((arity =? Datatypes.length value) = arity_ok -> world_state * expr_result uint256)
             then
              fun Earity : (arity =? Datatypes.length value) = true =>
              call_builtin value Earity (builtin world20_args)
             else
              fun _ : (arity =? Datatypes.length value) = false =>
              (world20_args, expr_error "builtin with wrong arity")) eq_refl in
            world30 = world20 /\
              mem_agree offset dst locmem mem30 /\
              match result20 with
              | ExprSuccess value20 => result30 = StmtSuccess /\ OpenArray.get mem30 dst = value20
              | ExprAbort abort => result30 = StmtAbort abort
              end).
{
  cbn. intro Earity. subst good_branch_30.
  subst world30_args.
  assert (Earity': (arity =? Datatypes.length value) = true).
  {
    rewrite OpenArray.view_len in Earity.
    rewrite Nat2N.id in Earity.
    now rewrite Args_len.
  }
  replace ((if arity =? Datatypes.length value as arity_ok
             return ((arity =? Datatypes.length value) = arity_ok -> world_state * expr_result uint256)
            then fun Earity0 : (arity =? Datatypes.length value) = true =>
                   call_builtin value Earity0 (builtin world20_args)
            else
             fun _ : (arity =? Datatypes.length value) = false =>
             (world20_args, expr_error "builtin with wrong arity")) eq_refl) 
  with (call_builtin value Earity' (builtin world20_args)).
  2:{
    clear Earity.
    remember (call_builtin value Earity' (builtin world20_args)) as lhs.
    remember (fun Earity0 : (arity =? Datatypes.length value) = true =>
                call_builtin value Earity0 (builtin world20_args)) as good_rhs.
    assert (E: lhs = good_rhs Earity') by now subst.
    clear Heqlhs Heqgood_rhs.
    destruct (arity =? Datatypes.length value).
    {
      assert (Earity' = eq_refl). { apply PropExtensionality.proof_irrelevance. }
      now subst.
    }
    discriminate.
  }
  revert Earity Earity'.
  rewrite V.
  intros.
  assert (Earity = Earity'). { apply PropExtensionality.proof_irrelevance. }
  subst Earity'.
  destruct (call_builtin value Earity (builtin world20_args)).
  destruct e. 
  2:{
    split. { trivial. }
    split. 2: { trivial. }
    intros n L NE. apply (Args_agree n L (N.lt_neq _ _ L)).
  }
  split. { trivial. }
  split. 2:{ split. { trivial. } apply OpenArray.put_same. }
  intros n L NE.
  rewrite (Args_agree n L (N.lt_neq _ _ L)).
  rewrite OpenArray.put_ok.
  enough (Q: (dst =? n)%N = false) by now rewrite Q.
  rewrite N.eqb_neq. intro H. symmetry in H. tauto.
}
clear Heqgood_branch_30.
remember (arity =? Datatypes.length (OpenArray.view mem30_args offset (N.of_nat (Datatypes.length args))))
  as arity_ok.
destruct arity_ok. { apply GoodBranch30Ok. }
(* arity check failed *)
assert (F: arity =? Datatypes.length value = false).
{
  rewrite OpenArray.view_len in Heqarity_ok.
  rewrite Nat2N.id in Heqarity_ok.
  now rewrite Args_len.
}
remember (fun Earity : (arity =? Datatypes.length value) = true =>
            call_builtin value Earity (builtin world20_args)) as good_branch_20.
clear Heqgood_branch_20.
destruct (arity =? Datatypes.length value). { discriminate. }
split. { trivial. }
split. 2:easy.
intros n L NE.
apply (Args_agree n L (N.lt_neq _ _ L)).
Qed.