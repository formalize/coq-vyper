From Coq Require Import String ZArith Eqdep_dec Lia.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L10.Expr L20.AST L10.Interpret L20.Interpret.

From Vyper.From10To20 Require Import Translate Callset FunCtx Expr.

(* This tactic applies interpret_translated_expr wherever possible. *)
Local Ltac expr :=
  let e20 := fresh "e20" in
  let e10 := fresh "e10" in
  let E := fresh "E" in
  remember (L20.Expr.interpret_expr _ _ _ _ _ _ _ _) as e20;
  remember (L10.Expr.interpret_expr _ _ _ _ _ _ _ _) as e10;
  assert (E: e20 = e10) by (subst; now apply interpret_translated_expr);
  rewrite E; clear E; subst e10; subst e20.


Lemma interpret_translated_small_stmt {C: VyperConfig}
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
                                (ss10: L10.AST.small_stmt)
                                {s20: L20.AST.stmt}
                                (StmtOk: s20 = let is_private_call := fun name: string =>
                                                  match cd_declmap cd name with
                                                  | Some _ => true
                                                  | _ => false
                                                  end
                                               in translate_small_stmt is_private_call ss10)
                                (CallOk20: let _ := string_set_impl in 
                                   FSet.is_subset (L20.Callset.stmt_callset s20)
                                                  (L20.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk10: let _ := string_set_impl in 
                                   FSet.is_subset (L10.Callset.small_stmt_callset ss10)
                                                  (L10.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
   L20.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok) do_call_20 builtins
                           world loc s20 CallOk20
    =
   L10.Stmt.interpret_small_stmt Ebound fc do_call_10 builtins
                                 world loc ss10 CallOk10.
Proof.
induction ss10.
{ (* pass *) now subst. }
{ (* break *) now subst. }
{ (* continue *) now subst. }
{ (* return *)
  subst. cbn.
  destruct result. 2:{ easy. }
  cbn. now expr.
}
{ (* revert *) now subst. }
{ (* raise *)
  subst. cbn. expr.
  now L10.Expr.destruct_let_pair.
}
{ (* assert *)
  subst. cbn. expr.
  L10.Expr.destruct_let_pair.
  destruct e. 2:{ trivial. }
  destruct ((Z_of_uint256 value =? 0)%Z). 2:{ trivial. }
  destruct error. 2: { easy. }
  (* there's an error message *)
  expr.
  L10.Expr.destruct_let_pair.
  match goal with
  |- _ = match ?e with | ExprSuccess _ => _ | ExprAbort _ => _ end => now destruct e
  end.
}
{ (* assign *)
  subst. cbn. expr.
  L10.Expr.destruct_let_pair.
  unfold L10.Stmt.do_assign. unfold L20.Stmt.do_assign.
  destruct e. 2:{ trivial. } 
  destruct lhs. { trivial. }
  now rewrite storage_var_is_declared_ok.
}
{ (* binop assign *)
  subst. cbn.
  destruct lhs; cbn.
  { (* local var *)
    unfold map_lookup.
    remember (Map.lookup loc name) as m.
    destruct m.
    {
      expr.
      destruct L10.Expr.interpret_expr.
      unfold L20.Stmt.do_assign.
      destruct e. 2:{ trivial. }
      rewrite<- Heqm. trivial.
    }
    unfold expr_error. trivial.
  }
  (* global var *)
  rewrite storage_var_is_declared_ok.
  unfold L20.Stmt.do_assign.
  remember (L10.Expr.storage_var_is_declared _ _) as is_declared.
  destruct is_declared. 2:easy.
  expr.
  destruct L10.Expr.interpret_expr.
  destruct e. 2:{ trivial. }
  rewrite storage_var_is_declared_ok.
  rewrite<- Heqis_declared.
  trivial.
}
(* expr *)
subst. cbn. expr.
now L10.Expr.destruct_let_pair.
Qed.

Ltac mark :=
  let lhs := fresh "lhs" in
  let rhs := fresh "rhs" in
  match goal with
  |- ?a = ?b => remember a as lhs; remember b as rhs
  end.

(** Interpreting [head; tail] in L20 is the same as interpreting [head :: tail] in L10. *)
Local Lemma semicolon_ok {C: VyperConfig}
                  {bigger_call_depth_bound smaller_call_depth_bound: nat}
                  (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                  {cd: L10.Descend.calldag}
                  (builtins: string -> option builtin)
                  (fc: fun_ctx cd bigger_call_depth_bound)
                  {do_call_10: forall
                        (fc': fun_ctx cd smaller_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256),
                      world_state * expr_result uint256}
                  {do_call_20: forall
                        (fc': fun_ctx (translate_calldag cd) smaller_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256),
                      world_state * expr_result uint256}
                  (DoCallOk: forall fc' world arg_values,
                               do_call_20 (translate_fun_ctx fc' eq_refl) world arg_values
                                =
                               do_call_10 fc' world arg_values)
                  (world: world_state)
                  (loc: string_map uint256)
                  {head10: L10.AST.stmt}
                  {tail10: list L10.AST.stmt}
                  (NotLocalVar: L10.AST.is_local_var_decl head10 = false)
                  (CallOk20: let _ := string_set_impl in
                             let is_private_call :=
                                   fun name: string => match cd_declmap cd name with
                                                       | Some _ => true
                                                       | None => false
                                                       end in
                               FSet.is_subset
                                 (Callset.stmt_callset
                                    (AST.Semicolon
                                       (translate_stmt is_private_call head10)
                                       (translate_stmt_list is_private_call tail10)))
                                 (Callset.decl_callset (fun_decl (translate_fun_ctx fc eq_refl)))
                               = true)
                  (HeadCallOk10: let _ := string_set_impl in 
                     FSet.is_subset (L10.Callset.stmt_callset head10)
                                    (L10.Callset.decl_callset
                                      (fun_decl fc))
                     = true)
                  (TailCallOk10: let _ := string_set_impl in 
                     FSet.is_subset (L10.Callset.stmt_list_callset tail10)
                                    (L10.Callset.decl_callset
                                      (fun_decl fc))
                     = true)
                  (HeadOk:
                    forall (NotVarDecl: AST.is_local_var_decl head10 = false)
                           (CallOk20: FSet.is_subset
                                        (Callset.stmt_callset
                                           (translate_stmt
                                              (fun name : string =>
                                               match cd_declmap cd name with
                                               | Some _ => true
                                               | None => false
                                               end) head10))
                                        (Callset.decl_callset (cached_translated_decl fc eq_refl))
                                      = true)
                           (CallOk10: FSet.is_subset
                                        (L10.Callset.stmt_callset head10)
                                        (L10.Callset.decl_callset (fun_decl fc)) = true)
                           (world: world_state)
                           (loc: string_map uint256),
                       Stmt.interpret_stmt Ebound (translate_fun_ctx fc eq_refl) do_call_20 builtins world loc
                         (translate_stmt
                            (fun name : string => match cd_declmap cd name with
                                                  | Some _ => true
                                                  | None => false
                                                  end) head10) CallOk20 =
                       L10.Stmt.interpret_stmt Ebound fc do_call_10 builtins world loc head10 NotVarDecl
                         CallOk10)
                  (TailOk: forall (world: world_state) (loc: string_map uint256),
                    Stmt.interpret_stmt Ebound (translate_fun_ctx fc eq_refl) do_call_20 builtins world loc
                      (translate_stmt_list
                         (fun name : string => match cd_declmap cd name with
                                               | Some _ => true
                                               | None => false
                                               end) tail10) (Callset.callset_descend_semicolon_right eq_refl CallOk20) =
                    Stmt.interpret_stmt_list Ebound fc do_call_10 builtins world loc tail10 TailCallOk10):
  Stmt.interpret_stmt Ebound (translate_fun_ctx fc eq_refl) do_call_20 builtins world loc
    (AST.Semicolon
        (translate_stmt
           (fun name: string => match cd_declmap cd name with
                                 | Some _ => true
                                 | None => false
                                 end) head10)
        (translate_stmt_list
           (fun name: string => match cd_declmap cd name with
                                 | Some _ => true
                                 | None => false
                                 end) tail10))
    CallOk20
   =
  match
    L10.Stmt.interpret_stmt Ebound fc do_call_10 builtins world loc head10 NotLocalVar HeadCallOk10
  with
  | (world', loc', StmtSuccess) =>
      Stmt.interpret_stmt_list Ebound fc do_call_10 builtins world' loc' tail10 TailCallOk10
  | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
      (world', loc', result)
  end.
Proof.
cbn.
rewrite (HeadOk NotLocalVar
           (Callset.callset_descend_semicolon_left eq_refl CallOk20)
           HeadCallOk10).
destruct L10.Stmt.interpret_stmt.
destruct p as (world', loc').
destruct s. 2-3:easy.
apply TailOk.
Qed.

(* Stmt lists work fine assuming that single stmts work fine. *)
Local Lemma weak_stmt_list_ok {C: VyperConfig}
                  {bigger_call_depth_bound smaller_call_depth_bound: nat}
                  (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                  {cd: L10.Descend.calldag}
                  (builtins: string -> option builtin)
                  (fc: fun_ctx cd bigger_call_depth_bound)
                  {do_call_10: forall
                        (fc': fun_ctx cd smaller_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256),
                      world_state * expr_result uint256}
                  {do_call_20: forall
                        (fc': fun_ctx (translate_calldag cd) smaller_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256),
                      world_state * expr_result uint256}
                  (DoCallOk: forall fc' world arg_values,
                               do_call_20 (translate_fun_ctx fc' eq_refl) world arg_values
                                =
                               do_call_10 fc' world arg_values)
                  (world: world_state)
                  (loc: string_map uint256)
                  {list10: list L10.AST.stmt}
                  (CallOk20: let _ := string_set_impl in 
                             let is_private_call := fun name: string =>
                                      match cd_declmap cd name with
                                      | Some _ => true
                                      | _ => false
                                      end in
                           FSet.is_subset (L20.Callset.stmt_callset
                                            (translate_stmt_list is_private_call list10))
                                          (L20.Callset.decl_callset
                                             (fun_decl
                                               (translate_fun_ctx fc eq_refl)))
                     = true)
                  (CallOk10: let _ := string_set_impl in 
                     FSet.is_subset (L10.Callset.stmt_list_callset list10)
                                    (L10.Callset.decl_callset
                                      (fun_decl fc))
                     = true)
                  (ItemsOk: List.Forall
                     (fun s: L10.AST.stmt =>
                        let is_private_call :=
                          fun name : string => match cd_declmap cd name with
                                               | Some _ => true
                                               | None => false
                                               end in
                       forall 
                         (NotVarDecl: AST.is_local_var_decl s = false)
                         (CallOk20: let H := string_set_impl in
                                     FSet.is_subset (L20.Callset.stmt_callset (translate_stmt is_private_call s))
                                       (L20.Callset.decl_callset
                                         (fun_decl (translate_fun_ctx fc eq_refl))) = true)
                         (CallOk10: let H := string_set_impl in
                                     FSet.is_subset (L10.Callset.stmt_callset s)
                                       (L10.Callset.decl_callset (fun_decl fc)) = true)
                         (world: world_state)
                         (loc: string_map uint256),
                       L20.Stmt.interpret_stmt Ebound (translate_fun_ctx fc eq_refl) do_call_20 builtins world loc
                          (translate_stmt is_private_call s) CallOk20
                        =
                       L10.Stmt.interpret_stmt Ebound fc do_call_10 builtins world loc s NotVarDecl CallOk10)
                    list10):
  let is_private_call := fun name: string =>
                            match cd_declmap cd name with
                            | Some _ => true
                            | _ => false
                            end in
  L20.Stmt.interpret_stmt Ebound (translate_fun_ctx fc eq_refl) do_call_20 builtins world loc
    (translate_stmt_list is_private_call list10) CallOk20
   =
  L10.Stmt.interpret_stmt_list Ebound fc do_call_10 builtins world loc list10 CallOk10.
Proof.
cbn. revert world loc. induction list10; intros. { easy. }
cbn.
assert (HeadOk := List.Forall_inv ItemsOk).
assert (TailOk := List.Forall_inv_tail ItemsOk). 
clear ItemsOk. cbn in HeadOk.
pose (is_loc_var := AST.is_local_var_decl a).
assert (IsLocVar: AST.is_local_var_decl a = is_loc_var) by trivial.
destruct a;
  (* this succeeds for everything except loc var decls: *)
  try rewrite (semicolon_ok Ebound builtins fc DoCallOk world loc IsLocVar
               CallOk20
               (Callset.callset_descend_stmt_head eq_refl CallOk10)
               (Callset.callset_descend_stmt_tail eq_refl CallOk10) 
               HeadOk
               (IHlist10 _ _ TailOk));
  try easy.
(* local var *)
cbn. destruct map_lookup. { trivial. }
destruct init.
{ (* with init *)
  expr. destruct L10.Expr.interpret_expr as (w,[result|abort]). 2:trivial.
  (* why can't I match goal with let '(_, _, _) := ... ? *)
  remember (L20.Stmt.interpret_stmt _ _ _ _ _ _ _ _) as lhs.
  remember (Stmt.interpret_stmt_list Ebound fc do_call_10 builtins w
                                     (map_insert loc name result) list10
                                     (Callset.callset_descend_stmt_tail eq_refl CallOk10)) as rhs.
  assert (G: lhs = rhs). { subst. apply IHlist10. apply TailOk. }
  now rewrite G.
}
(* without init *)
cbn.
remember (L20.Stmt.interpret_stmt _ _ _ _ _ _ _ _) as lhs.
remember (Stmt.interpret_stmt_list Ebound fc do_call_10 builtins world 
                                   (map_insert loc name zero256) list10
                                   (Callset.callset_descend_stmt_tail eq_refl CallOk10)) as rhs.
assert (G: lhs = rhs). { subst. apply IHlist10. apply TailOk. }
now rewrite G.
Qed.

Lemma interpret_translated_stmt {C: VyperConfig}
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
                                {s10: L10.AST.stmt}
                                {s20: L20.AST.stmt}
                                (NotVarDecl: L10.AST.is_local_var_decl s10 = false)
                                (StmtOk: s20 = let is_private_call := fun name: string =>
                                                  match cd_declmap cd name with
                                                  | Some _ => true
                                                  | _ => false
                                                  end
                                               in translate_stmt is_private_call s10)
                                (CallOk20: let _ := string_set_impl in 
                                   FSet.is_subset (L20.Callset.stmt_callset s20)
                                                  (L20.Callset.decl_callset
                                                     (fun_decl
                                                       (translate_fun_ctx fc ok)))
                                   = true)
                                (CallOk10: let _ := string_set_impl in 
                                   FSet.is_subset (L10.Callset.stmt_callset s10)
                                                  (L10.Callset.decl_callset
                                                    (fun_decl fc))
                                   = true):
   L20.Stmt.interpret_stmt Ebound (translate_fun_ctx fc ok) do_call_20 builtins
                           world loc s20 CallOk20
    =
   L10.Stmt.interpret_stmt Ebound fc do_call_10 builtins
                           world loc s10 NotVarDecl CallOk10.
Proof.
subst bigger_call_depth_bound.
(* Unfortunately, the inline fixpoints for interpret_stmt_list are not
   the same as interpret_stmt_list from Coq's viewpoint.
   All this is really stupid.
 *)
pose (is_private_call :=
                 fun name : string => match cd_declmap cd name with
                                      | Some _ => true
                                      | None => false
                                      end).
pose (interpret_stmt_list' := fix
 interpret_stmt_list (world0 : world_state) (loc0 : string_map uint256) (stmts : list L10.AST.stmt)
                     (CallOk : FSet.is_subset (Callset.stmt_list_callset stmts)
                                 (L10.Callset.decl_callset (fun_decl fc)) = true) {struct stmts} :
   world_state * string_map uint256 * stmt_result uint256 :=
   match
     stmts as stmts' return (stmts = stmts' -> world_state * string_map uint256 * stmt_result uint256)
   with
   | nil => fun _ : stmts = nil => (world0, loc0, StmtSuccess)
   | (h :: t)%list =>
       fun E : stmts = (h :: t)%list =>
       (if AST.is_local_var_decl h as h_is_var_decl
         return
           (AST.is_local_var_decl h = h_is_var_decl ->
            world_state * string_map uint256 * stmt_result uint256)
        then
         fun Evar : AST.is_local_var_decl h = true =>
         match map_lookup loc0 (fst (AST.var_decl_unpack h Evar)) with
         | Some _ => (world0, loc0, stmt_error "local variable already exists")
         | None =>
             match
               snd (AST.var_decl_unpack h Evar) as init'
               return
                 (snd (AST.var_decl_unpack h Evar) = init' ->
                  world_state * string_map uint256 * stmt_result uint256)
             with
             | Some init_expr =>
                 fun Einit : snd (AST.var_decl_unpack h Evar) = Some init_expr =>
                 match
                   L10.Expr.interpret_expr eq_refl fc do_call_10 builtins world0 loc0 init_expr
                     (Callset.callset_descend_init_expr E Evar Einit CallOk)
                 with
                 | (world', ExprSuccess value0) =>
                     let
                     '(world2, loc2, result2) :=
                      interpret_stmt_list world'
                        (map_insert loc0 (fst (AST.var_decl_unpack h Evar)) value0) t
                        (Callset.callset_descend_stmt_tail E CallOk) in
                      (world2, map_remove loc2 (fst (AST.var_decl_unpack h Evar)), result2)
                 | (world', ExprAbort ab) => (world', loc0, StmtAbort ab)
                 end
             | None =>
                 fun _ : snd (AST.var_decl_unpack h Evar) = None =>
                 let
                 '(world', loc', result) :=
                  interpret_stmt_list world0 (map_insert loc0 (fst (AST.var_decl_unpack h Evar)) zero256)
                    t (Callset.callset_descend_stmt_tail E CallOk) in
                  (world', map_remove loc' (fst (AST.var_decl_unpack h Evar)), result)
             end eq_refl
         end
        else
         fun Evar : AST.is_local_var_decl h = false =>
         match
           L10.Stmt.interpret_stmt eq_refl fc do_call_10 builtins world0 loc0 h Evar
             (Callset.callset_descend_stmt_head E CallOk)
         with
         | (world', loc', StmtSuccess) =>
             interpret_stmt_list world' loc' t (Callset.callset_descend_stmt_tail E CallOk)
         | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
             (world', loc', result)
         end) eq_refl
   end eq_refl).
assert (interpret_stmt_list_alt: forall (w: world_state) 
                                         (loc: string_map uint256)
                                         (l: list L10.AST.stmt)
                                         (LCallOk: let _ := string_set_impl in
                                                   FSet.is_subset
                                                     (Callset.stmt_list_callset l)
                                                     (L10.Callset.decl_callset (fun_decl fc))
                                                   = true),
   interpret_stmt_list' w loc l LCallOk
    =
   L10.Stmt.interpret_stmt_list eq_refl fc do_call_10 builtins w loc l LCallOk).
{
  clear world loc NotVarDecl s10 s20 StmtOk CallOk10 CallOk20.
  intros w loc l. revert w loc.
  induction l. { easy. }
  cbn. intros.
  remember (fun Evar : AST.is_local_var_decl a = false =>
              match
                L10.Stmt.interpret_stmt eq_refl fc do_call_10 builtins w loc a Evar
                  (Callset.callset_descend_stmt_head eq_refl LCallOk)
              with
              | (world', loc', StmtSuccess) =>
                  interpret_stmt_list' world' loc' l
                    (Callset.callset_descend_stmt_tail eq_refl LCallOk)
              | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
                  (world', loc', result)
              end) as not_var_branch1.
  remember (fun Evar : AST.is_local_var_decl a = false =>
              match
                L10.Stmt.interpret_stmt eq_refl fc do_call_10 builtins w loc a Evar
                  (Callset.callset_descend_stmt_head eq_refl LCallOk)
              with
              | (world', loc', StmtSuccess) =>
                  L10.Stmt.interpret_stmt_list eq_refl fc do_call_10 builtins world' loc' l
                    (Callset.callset_descend_stmt_tail eq_refl LCallOk)
              | (world', loc', StmtAbort _ as result) | (world', loc', StmtReturnFromFunction _ as result) =>
                  (world', loc', result)
              end) as not_var_branch2.
  assert (B: forall (Evar: AST.is_local_var_decl a = false),
               not_var_branch1 Evar = not_var_branch2 Evar).
  {
    subst. intro Evar.
    L10.Expr.destruct_let_pair. destruct p. now destruct s.
  }
  clear Heqnot_var_branch1 Heqnot_var_branch2.
  destruct a; try easy.
  (* local var *)
  cbn.
  destruct map_lookup. { trivial. }
  destruct init. 2:{ now rewrite IHl. }
  destruct L10.Expr.interpret_expr.
  destruct e0. { now rewrite IHl. }
  trivial.
} (* interpret_stmt_list_alt *)
subst cd2.
(* Another round of stupidity: we also need to fold translate_stmt_list. *)
pose (translate_stmt_list' := fix translate_stmt_list (l : list L10.AST.stmt) : AST.stmt :=
                 match l with
                 | nil => AST.SmallStmt AST.Pass
                 | (L10.AST.LocalVarDecl name maybe_init :: t)%list =>
                     AST.LocalVarDecl name
                       match maybe_init with
                       | Some init =>
                           translate_expr
                             (fun name0 : string =>
                              match cd_declmap cd name0 with
                              | Some _ => true
                              | None => false
                              end) init
                       | None => AST.Const zero256
                       end (translate_stmt_list t)
                 | (L10.AST.SmallStmt _ as h :: t)%list | (L10.AST.IfElseStmt _ _ _ as h :: t)%list |
                   (AST.FixedRangeLoop _ _ _ _ as h :: t)%list |
                   (AST.FixedCountLoop _ _ _ _ as h :: t)%list =>
                     AST.Semicolon
                       (translate_stmt
                          (fun name : string =>
                           match cd_declmap cd name with
                           | Some _ => true
                           | None => false
                           end) h) (translate_stmt_list t)
                 end).
assert (translate_stmt_list_alt: forall l: list L10.AST.stmt,
          translate_stmt_list' l  =  translate_stmt_list is_private_call l).
{ now induction l. }
pose (AllOk := (* all statements in the given list of statements translate correctly *)
         List.Forall
             (fun s : L10.AST.stmt =>
              let is_private_call :=
                fun name : string => match cd_declmap cd name with
                                     | Some _ => true
                                     | None => false
                                     end in
              forall (NotVarDecl0 : AST.is_local_var_decl s = false)
                (CallOk21 : let H := string_set_impl in
                            FSet.is_subset (Callset.stmt_callset (translate_stmt is_private_call s))
                              (Callset.decl_callset (fun_decl (translate_fun_ctx fc eq_refl))) = true)
                (CallOk11 : let H := string_set_impl in
                            FSet.is_subset (L10.Callset.stmt_callset s) (L10.Callset.decl_callset (fun_decl fc)) =
                            true) (world0 : world_state) (loc0 : string_map uint256),
              L20.Stmt.interpret_stmt eq_refl (translate_fun_ctx fc eq_refl) do_call_20 builtins world0 loc0
                (translate_stmt is_private_call s) CallOk21 =
              L10.Stmt.interpret_stmt eq_refl fc do_call_10 builtins world0 loc0 s NotVarDecl0 CallOk11)).
revert world loc. subst s20.
assert (P: cached_translated_decl fc eq_refl = fun_decl (translate_fun_ctx fc eq_refl)).
{ unfold translate_fun_ctx. now subst. }
induction s10 using L10.AST.stmt_ind'; intros.
{ (* small *) now apply interpret_translated_small_stmt. }
{ (* local var *) cbn in NotVarDecl. discriminate. }
{ (* if *)
  cbn.
  expr. L10.Expr.destruct_let_pair.
  destruct e. 2:{ trivial. }
  destruct (Z_of_uint256 value =? 0)%Z.
  { (* else *)
    destruct no. 2:easy.

    assert (G: let _ := string_set_impl in
               FSet.is_subset (Callset.stmt_callset (translate_stmt_list is_private_call l))
                 (Callset.decl_callset (fun_decl (translate_fun_ctx fc eq_refl))) = true).
    { rewrite<- P. apply (L20.Callset.callset_descend_stmt_if_else eq_refl CallOk20). }

    assert (L: AllOk l).
    {
      unfold AllOk.
      rewrite List.Forall_forall.
      rewrite List.Forall_forall in H0.
      intros.
      now apply H0. (* why can't it just apply it directly? *)
    }
    mark.
    assert (W := weak_stmt_list_ok eq_refl builtins fc DoCallOk w loc
                 G
                 (L10.Callset.callset_descend_stmt_if_else eq_refl eq_refl CallOk10)
                 L).
    assert (E: G = L20.Callset.callset_descend_stmt_if_else eq_refl CallOk20).
    { apply PropExtensionality.proof_irrelevance. }
    rewrite E in W.
    assert (T := eq_trans Heqlhs W). (* why rewrite W doesn't work? *)
    clear Heqlhs. subst.
    rewrite interpret_stmt_list_alt.
    trivial.
  }
  (* then *)
  assert (G: let _ := string_set_impl in
           FSet.is_subset (Callset.stmt_callset (translate_stmt_list is_private_call yes))
             (Callset.decl_callset (fun_decl (translate_fun_ctx fc eq_refl))) = true).
  { rewrite<- P. apply (L20.Callset.callset_descend_stmt_if_then eq_refl CallOk20). }
  assert (L: AllOk yes).
  {
    unfold AllOk.
    rewrite List.Forall_forall.
    rewrite List.Forall_forall in H.
    intros.
    now apply H. (* why can't it just apply it directly? *)
  }
  mark.
  assert (W := weak_stmt_list_ok eq_refl builtins fc DoCallOk w loc
               G
               (L10.Callset.callset_descend_stmt_if_then eq_refl CallOk10)
               L).
  assert (E: G = L20.Callset.callset_descend_stmt_if_then eq_refl CallOk20).
  { apply PropExtensionality.proof_irrelevance. }
  rewrite E in W.
  assert (T := eq_trans Heqlhs W). (* why rewrite W doesn't work? *)
  clear Heqlhs. subst.
  rewrite interpret_stmt_list_alt.
  trivial.
}
2:{ (* fixed count loop *)
  cbn.

  (* checks *)
  destruct (map_lookup loc var). { trivial. }
  destruct (Z_of_uint256 count =? 0)%Z. { easy. }
  expr.
  L10.Expr.destruct_let_pair. destruct e. 2:{ trivial. }
  remember
    (Z_of_uint256 (uint256_of_Z (Z_of_uint256 value + Z_of_uint256 count - 1)) 
     =? 
    Z_of_uint256 value + Z_of_uint256 count - 1)%Z as overflow_check.
  destruct overflow_check. 2:{ trivial. }

  (* preparing induction *)
  remember (Z.to_nat (Z_of_uint256 count)) as n.
  remember (Z_of_uint256 value + Z_of_uint256 count - 1)%Z as cap.
  (* Here Heqcap is the main loop equation: [

        cap = Z_of_uint256 value + Z_of_uint256 count - 1

    ] where cap is constant, value goes up and count goes down.
  However, in our interpretation of the count loop we allow overflow
  during the last iteration, for example [

      for i in count(2^256 - 2, 2):
        ...

  ] is the same as [

      for i in [2^256 - 2, 2^256 - 1]:
        ...
  ] and therefore legit (except that the latter syntax is currently 
  not supported). Therefore the main loop equation must be weakened to this: *)
  assert (WeakMainLoopEq: 
            cap = (Z_of_uint256 value + Z_of_uint256 count - 1)%Z
             \/
            Z_of_uint256 count = 0%Z).
  { left. exact Heqcap. }
  clear Heqcap.
  revert count NotVarDecl CallOk10 CallOk20 Heqn w loc value WeakMainLoopEq.
  induction n. { easy. }  (* --- induction --- *)
  intros.

  (* checking that the counter doesn't go below 0 *)
  pose (count' := uint256_of_Z (Z.pred (Z_of_uint256 count))).
  assert (CountOk: n = Z.to_nat (Z_of_uint256 count')).
  {
    unfold count'. rewrite uint256_ok.
    assert (R := uint256_range count).
    remember (Z_of_uint256 count) as z. clear Heqz.
    assert (Q: z = Z.succ (Z.of_nat n)).
    {
      rewrite<- Nat2Z.inj_succ. rewrite Heqn.
      symmetry. apply Z2Nat.id. tauto.
    }
    subst z. rewrite Z.pred_succ.
    replace (Z.of_nat n mod 2 ^ 256)%Z with (Z.of_nat n).
    { symmetry. apply Nat2Z.id. }
    symmetry. apply Z.mod_small.
    split.
    { (* 0 <= n *) apply Nat2Z.is_nonneg. }
    exact (Z.lt_trans _ _ _ (Z.lt_succ_diag_r (Z.of_nat n)) (proj2 R)).
  }

  (* first iteration *)
  assert (G: let _ := string_set_impl in
             FSet.is_subset (Callset.stmt_callset (translate_stmt_list is_private_call body))
               (Callset.decl_callset (fun_decl (translate_fun_ctx fc eq_refl))) = true).
  { rewrite<- P. apply (L20.Callset.callset_descend_loop_body eq_refl CallOk20). }

  assert (L: AllOk body).
  {
    unfold AllOk.
    rewrite List.Forall_forall.
    rewrite List.Forall_forall in H.
    intros.
    now apply H.
  }
  mark.
  assert (W := weak_stmt_list_ok eq_refl builtins fc DoCallOk w
               (map_insert loc var (uint256_of_Z (Z_of_uint256 value)))
               G
               (L10.Callset.callset_descend_fixed_count_loop_body eq_refl CallOk10)
               L).
  fold is_private_call in W. 
  fold translate_stmt_list' in Heqlhs.
  rewrite interpret_stmt_list_alt in Heqrhs.
  destruct L10.Stmt.interpret_stmt_list as ((world', loc'), result').

  (* This hairball is copied from Heqlhs.
     It looks like [
          Stmt.interpret_stmt eq_refl (translate_fun_ctx fc eq_refl) do_call_20 builtins w
              (map_insert loc var (uint256_of_Z (Z_of_uint256 value)))
              (translate_stmt_list' body)
              (Callset.callset_descend_loop_body eq_refl CallOk20)
    ] but if I write just that then it doesn't match. *)
  assert (V: @Stmt.interpret_stmt C (S smaller_call_depth_bound) smaller_call_depth_bound
             (@eq_refl nat (S smaller_call_depth_bound)) (@translate_calldag C cd)
             (@translate_fun_ctx C (S smaller_call_depth_bound) cd fc (@translate_calldag C cd)
                (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))) do_call_20 builtins w
             (@map_insert C (@uint256 C) loc var (@uint256_of_Z C (@Z_of_uint256 C value)))
             (translate_stmt_list' body)
             (@Callset.callset_descend_loop_body C
                (@AST.Loop C var
                   (@translate_expr C
                      (fun name : string =>
                       match @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name with
                       | Some _ => true
                       | None => false
                       end) start) count (translate_stmt_list' body)) (translate_stmt_list' body) var
                (@translate_expr C
                   (fun name : string =>
                    match @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name with
                    | Some _ => true
                    | None => false
                    end) start) count
                (@Callset.decl_callset C
                   (@cached_translated_decl C (S smaller_call_depth_bound) cd fc 
                      (@translate_calldag C cd) (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))))
                (@eq_refl (@AST.stmt C)
                   (@AST.Loop C var
                      (@translate_expr C
                         (fun name : string =>
                          match @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name with
                          | Some _ => true
                          | None => false
                          end) start) count (translate_stmt_list' body))) CallOk20)
             = (world', loc', result')).
  {
    assert (E: G = L20.Callset.callset_descend_loop_body eq_refl CallOk20).
    { apply PropExtensionality.proof_irrelevance. }
    rewrite E in W.
    apply W.
  }
  rewrite V in Heqlhs.
  clear V W G.

  (* fixing stuff before looking into the result of the first iteration *)
  assert (CapRange: (0 <= cap < 2 ^ 256)%Z).
  {
    symmetry in Heqoverflow_check. rewrite Z.eqb_eq in Heqoverflow_check.
    rewrite uint256_ok in Heqoverflow_check.
    rewrite Z.mod_small_iff in Heqoverflow_check by apply two_to_256_ne_0.
    enough (~ (2 ^ 256 < cap <= 0)%Z). { tauto. }
    intro Y.
    assert (Bad := proj2 (Z.ltb_lt _ _) (Z.lt_le_trans _ _ _ (proj1 Y) (proj2 Y))).
    cbn in Bad. discriminate.
  }

  assert (MainLoopEq: cap = (Z_of_uint256 value + Z_of_uint256 count - 1)%Z).
  {
    enough (Z_of_uint256 count <> 0%Z). { tauto. }
    intro J. rewrite J in *.
    cbn in Heqn. discriminate.
  }

  pose (value' := uint256_of_Z (Z.succ (Z_of_uint256 value))).
  assert (NextWeakMainLoopEq:
     cap = (Z_of_uint256 value' + Z_of_uint256 count' - 1)%Z 
      \/
     Z_of_uint256 count' = 0%Z).
  {
    unfold value'.
    rewrite uint256_ok.
    destruct n.
    {
      (* CountOk: 0 = Z.to_nat (Z_of_uint256 count') *)
      right.
      assert (Y: Z.of_nat (Z.to_nat (Z_of_uint256 count')) = 0%Z)
        by now rewrite<- CountOk.
      rewrite Z2Nat.id in Y. { exact Y. }
      exact (proj1 (uint256_range count')).
    }
    left.
    assert (ValueOk: Z_of_uint256 value' = Z.succ (Z_of_uint256 value)).
    {
      unfold value'.
      rewrite uint256_ok.
      apply Z.mod_small.
      subst cap.
      split.
      { (* 0 <= Z.succ (Z_of_uint256 value)) *)
        apply Z.le_le_succ_r.
        apply (proj1 (uint256_range _)).
      }
      (* Heqn: S (S n) = Z.to_nat (Z_of_uint256 count) *)
      lia.
    }
    rewrite<- ValueOk.
    replace (Z_of_uint256 value' mod 2 ^ 256)%Z with (Z_of_uint256 value').
    2:{ symmetry. apply Z.mod_small. apply uint256_range. }
    rewrite MainLoopEq.
    f_equal.
    rewrite ValueOk.
    assert (CountOk': Z_of_uint256 count' = Z.pred (Z_of_uint256 count)).
    {
      replace (Z_of_uint256 count') with (Z.of_nat (S n)).
      2:{
        rewrite CountOk. rewrite Z2Nat.id. { trivial. }
        exact (proj1 (uint256_range count')).
      }
      replace (Z_of_uint256 count) with (Z.of_nat (S (S n))).
      2:{
        rewrite Heqn. rewrite Z2Nat.id. { trivial. }
        exact (proj1 (uint256_range count)).
      }
      lia.
    }
    rewrite CountOk'.
    lia.
  }

  (* Fix invisible problems in the induction hypothesis:
      IHn' arrives to the callset of the body via a loop with count',
      but the goal arrives to the same via a loop with count.
     *)

  assert (FixCount20: @L20.Callset.callset_descend_loop_body C
              (@AST.Loop C var
                 (@translate_expr C
                    (fun name : string =>
                     match
                       @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name
                     with
                     | Some _ => true
                     | None => false
                     end) start) count' (translate_stmt_list' body)) (translate_stmt_list' body)
              var
              (@translate_expr C
                 (fun name : string =>
                  match @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name with
                  | Some _ => true
                  | None => false
                  end) start) count'
              (@Callset.decl_callset C
                 (@cached_translated_decl C (S smaller_call_depth_bound) cd fc
                    (@translate_calldag C cd)
                    (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))))
              (@eq_refl (@AST.stmt C)
                 (@AST.Loop C var
                    (@translate_expr C
                       (fun name : string =>
                        match
                          @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name
                        with
                        | Some _ => true
                        | None => false
                        end) start) count' (translate_stmt_list' body))) CallOk20
            = Callset.callset_descend_loop_body eq_refl CallOk20).
  { apply PropExtensionality.proof_irrelevance. }

  assert (FixCount10: @L10.Callset.callset_descend_fixed_count_loop_body C
                       (@AST.FixedCountLoop C var start count' body) body var start count'
                       (@L10.Callset.decl_callset C
                          (@fun_decl C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd
                             (S smaller_call_depth_bound) fc))
                       (@eq_refl (@L10.AST.stmt C) (@AST.FixedCountLoop C var start count' body))
                       CallOk10
                     =
                    L10.Callset.callset_descend_fixed_count_loop_body eq_refl CallOk10).
  { apply PropExtensionality.proof_irrelevance. }

  fold interpret_stmt_list'.
  fold interpret_stmt_list' in IHn.
  fold translate_stmt_list' in IHn.

  destruct result'; subst lhs rhs. 3:{ trivial. }
  { (* successful iteration *)
    assert (IHn' := IHn count' eq_refl CallOk10 CallOk20 CountOk 
                        world' loc' value' NextWeakMainLoopEq).
    rewrite FixCount10 in IHn'.
    rewrite FixCount20 in IHn'.

    assert (NZ: n = 0 \/ n <> 0) by lia.
    destruct NZ. { now destruct n. }
    (* XXX dup from above *)
    assert (ValueOk: Z_of_uint256 value' = Z.succ (Z_of_uint256 value)).
    {
      unfold value'.
      rewrite uint256_ok.
      apply Z.mod_small.
      subst cap.
      split.
      { (* 0 <= Z.succ (Z_of_uint256 value)) *)
        apply Z.le_le_succ_r.
        apply (proj1 (uint256_range _)).
      }
      (* Heqn: S (S n) = Z.to_nat (Z_of_uint256 count) *)
      lia.
    }
    rewrite<- ValueOk.
    apply IHn'.
  }
  (* iteration aborted *)
  destruct a; try easy.
  (* continue (XXX dup from above) *)
  assert (IHn' := IHn count' eq_refl CallOk10 CallOk20 CountOk 
                        world' loc' value' NextWeakMainLoopEq).
  rewrite FixCount10 in IHn'.
  rewrite FixCount20 in IHn'.

  assert (NZ: n = 0 \/ n <> 0) by lia.
  destruct NZ. { now destruct n. }
  (* XXX dup from above *)
  assert (ValueOk: Z_of_uint256 value' = Z.succ (Z_of_uint256 value)).
  {
    unfold value'.
    rewrite uint256_ok.
    apply Z.mod_small.
    subst cap.
    split.
    { (* 0 <= Z.succ (Z_of_uint256 value)) *)
      apply Z.le_le_succ_r.
      apply (proj1 (uint256_range _)).
    }
    (* Heqn: S (S n) = Z.to_nat (Z_of_uint256 count) *)
    lia.
  }
  rewrite<- ValueOk.
  apply IHn'.
}
(* fixed range loop *)
cbn.
fold interpret_stmt_list'. fold translate_stmt_list'.
remember (match start with
          | Some x => x
          | None => zero256
          end) as start_u.
remember (match start with
          | Some x => Z_of_uint256 x
          | None => 0%Z
          end) as start_z.
assert (U: start_z = Z_of_uint256 start_u).
{
  subst. destruct start. { trivial. }
  unfold zero256. now rewrite uint256_ok.
}
repeat rewrite<- U.
destruct (map_lookup loc var). { trivial. }
remember (Z_of_uint256 stop <=? start_z)%Z as loop_is_bad.
destruct loop_is_bad. { unfold zero256. now rewrite uint256_ok. }
symmetry in Heqloop_is_bad. apply Z.leb_gt in Heqloop_is_bad.
assert (StopMinusStart:
          (Z_of_uint256 (uint256_of_Z (Z_of_uint256 stop - start_z))
            =
           Z_of_uint256 stop - start_z)%Z).
{
  rewrite U.
  assert (StartRange := uint256_range start_u).
  assert (StopRange := uint256_range stop).
  rewrite uint256_ok.
  rewrite Z.mod_small; lia.
}
repeat rewrite StopMinusStart.

assert (EmptyLoopCheckPassed: (Z_of_uint256 stop - start_z =? 0)%Z = false).
{
  apply Z.eqb_neq.
  lia.
}
rewrite EmptyLoopCheckPassed.
assert (OverflowCheckPassed: (Z_of_uint256
     (uint256_of_Z (start_z + (Z_of_uint256 stop - start_z) - 1)) =?
   start_z + (Z_of_uint256 stop - start_z) - 1)%Z = true).
{
  rewrite uint256_ok.
  assert (StartRange := uint256_range start_u).
  assert (StopRange := uint256_range stop).
  rewrite Z.mod_small. { now apply Z.eqb_eq. }
  lia.
}
rewrite OverflowCheckPassed.

(* induction *)
remember (Z.to_nat (Z_of_uint256 stop - start_z)) as n.
clear Heqstart_z Heqstart_u.
clear NotVarDecl.

assert (MainLoopEquation: Z.of_nat n = (Z_of_uint256 stop - start_z)%Z).
{
  subst n. 
  rewrite Z2Nat.id. { trivial. }
  rewrite uint256_ok in StopMinusStart.
  rewrite Z.mod_small_iff in StopMinusStart. { lia. }
  discriminate.
}

assert (StartNonneg: (0 <= start_z)%Z).
{
  assert (StartRange := uint256_range start_u).
  lia.
}
revert MainLoopEquation StartNonneg CallOk10 CallOk20 world loc.
clear U EmptyLoopCheckPassed OverflowCheckPassed Heqn Heqloop_is_bad.
revert start_z StopMinusStart.
induction n. { easy. }  (* --- induction --- *)
intros.

(* first iteration *)
assert (G: let _ := string_set_impl in
           FSet.is_subset (Callset.stmt_callset (translate_stmt_list is_private_call body))
             (Callset.decl_callset (fun_decl (translate_fun_ctx fc eq_refl))) = true).
{ rewrite<- P. apply (L20.Callset.callset_descend_loop_body eq_refl CallOk20). }

assert (L: AllOk body).
{
  unfold AllOk.
  rewrite List.Forall_forall.
  rewrite List.Forall_forall in H.
  intros.
  now apply H.
}
mark.
assert (W := weak_stmt_list_ok eq_refl builtins fc DoCallOk world
             (map_insert loc var (uint256_of_Z start_z))
             G
             (L10.Callset.callset_descend_fixed_range_loop_body eq_refl CallOk10)
             L).

fold is_private_call in W. 
fold translate_stmt_list' in Heqlhs.
rewrite interpret_stmt_list_alt in Heqrhs.
destruct L10.Stmt.interpret_stmt_list as ((world', loc'), result').

(* This hairball is copied from Heqlhs.
   It looks like [
               Stmt.interpret_stmt eq_refl (translate_fun_ctx fc eq_refl) do_call_20 builtins world
               (map_insert loc var (uint256_of_Z start_z)) (translate_stmt_list' body)
               (Callset.callset_descend_loop_body eq_refl CallOk20)
  ] but if I write just that then it doesn't match. *)
assert (V: @Stmt.interpret_stmt C (S smaller_call_depth_bound) smaller_call_depth_bound
               (@eq_refl nat (S smaller_call_depth_bound)) (@translate_calldag C cd)
               (@translate_fun_ctx C (S smaller_call_depth_bound) cd fc (@translate_calldag C cd)
                  (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))) do_call_20 builtins world
               (@map_insert C (@uint256 C) loc var (@uint256_of_Z C start_z))
               (translate_stmt_list' body)
               (@Callset.callset_descend_loop_body C
                  (@AST.Loop C var (@AST.Const C start_u)
                     (@uint256_of_Z C (@Z_of_uint256 C stop - start_z)) (translate_stmt_list' body))
                  (translate_stmt_list' body) var (@AST.Const C start_u)
                  (@uint256_of_Z C (@Z_of_uint256 C stop - start_z))
                  (@Callset.decl_callset C
                     (@cached_translated_decl C (S smaller_call_depth_bound) cd fc
                        (@translate_calldag C cd)
                        (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))))
                  (@eq_refl (@AST.stmt C)
                     (@AST.Loop C var (@AST.Const C start_u)
                        (@uint256_of_Z C (@Z_of_uint256 C stop - start_z)) 
                        (translate_stmt_list' body))) CallOk20)
           = (world', loc', result')).
{
  (* Strangely, what worked above for FixedCountLoop doesn't work here.
     Here's something else instead:
   *)
  remember (@Callset.callset_descend_loop_body C
     (@AST.Loop C var (@AST.Const C start_u) (@uint256_of_Z C (@Z_of_uint256 C stop - start_z))
        (translate_stmt_list' body)) (translate_stmt_list' body) var (@AST.Const C start_u)
     (@uint256_of_Z C (@Z_of_uint256 C stop - start_z))
     (@Callset.decl_callset C
        (@cached_translated_decl C (S smaller_call_depth_bound) cd fc (@translate_calldag C cd)
           (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))))
     (@eq_refl (@AST.stmt C)
        (@AST.Loop C var (@AST.Const C start_u) (@uint256_of_Z C (@Z_of_uint256 C stop - start_z))
           (translate_stmt_list' body))) CallOk20) as F.
  rewrite<- W. clear W Heqlhs Heqrhs HeqF.
  revert G F. rewrite<- translate_stmt_list_alt. intros.
  assert (E: F = G).
  { apply PropExtensionality.proof_irrelevance. }
  subst F. trivial.
}
rewrite V in Heqlhs.
clear V W G.

pose (start_z' := Z.succ start_z).
assert (NextMainLoopEquation: Z.of_nat n = (Z_of_uint256 stop - start_z')%Z) by lia.

fold interpret_stmt_list'.
fold interpret_stmt_list' in IHn.
fold translate_stmt_list' in IHn.

assert (NextStopMinusStart:
          (Z_of_uint256 (uint256_of_Z (Z_of_uint256 stop - start_z'))
            =
           Z_of_uint256 stop - start_z')%Z).
{
  rewrite uint256_ok.
  apply Z.mod_small.
  split. { lia. }
  assert (StopRange := uint256_range stop).
  lia.
}

assert (NextStartNonneg: (0 <= start_z')%Z) by lia.

assert (IHn' := IHn start_z' NextStopMinusStart NextMainLoopEquation NextStartNonneg
                    CallOk10 CallOk20).
assert (Fix20:
  @Callset.callset_descend_loop_body C
              (@AST.Loop C var (@AST.Const C start_u)
                 (@uint256_of_Z C (@Z_of_uint256 C stop - start_z')) (translate_stmt_list' body))
              (translate_stmt_list' body) var (@AST.Const C start_u)
              (@uint256_of_Z C (@Z_of_uint256 C stop - start_z'))
              (@Callset.decl_callset C
                 (@cached_translated_decl C (S smaller_call_depth_bound) cd fc
                    (@translate_calldag C cd)
                    (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))))
              (@eq_refl (@AST.stmt C)
                 (@AST.Loop C var (@AST.Const C start_u)
                    (@uint256_of_Z C (@Z_of_uint256 C stop - start_z')) (translate_stmt_list' body)))
              CallOk20
  =
 @Callset.callset_descend_loop_body C
                    (@AST.Loop C var (@AST.Const C start_u)
                       (@uint256_of_Z C (@Z_of_uint256 C stop - start_z)) 
                       (translate_stmt_list' body)) (translate_stmt_list' body) var
                    (@AST.Const C start_u) (@uint256_of_Z C (@Z_of_uint256 C stop - start_z))
                    (@Callset.decl_callset C
                       (@cached_translated_decl C (S smaller_call_depth_bound) cd fc
                          (@translate_calldag C cd)
                          (@eq_refl (@Descend.calldag C) (@translate_calldag C cd))))
                    (@eq_refl (@AST.stmt C)
                       (@AST.Loop C var (@AST.Const C start_u)
                          (@uint256_of_Z C (@Z_of_uint256 C stop - start_z))
                          (translate_stmt_list' body))) CallOk20).
{ apply PropExtensionality.proof_irrelevance. }
rewrite Fix20 in IHn'.

(* looking at the result of the first iteration *)
destruct result'; subst lhs rhs. 3:{ trivial. }
{
  (* successful first iteration *)
  apply IHn'.
}
(* first iteration aborted *)
now destruct a.
Qed.

(* We can now strengthen weak_stmt_list_ok to remove ItemsOk assumption. *)
Lemma interpret_translated_stmt_list {C: VyperConfig}
                  {bigger_call_depth_bound smaller_call_depth_bound: nat}
                  (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                  {cd: L10.Descend.calldag}
                  (builtins: string -> option builtin)
                  (fc: fun_ctx cd bigger_call_depth_bound)
                  {do_call_10: forall
                        (fc': fun_ctx cd smaller_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256),
                      world_state * expr_result uint256}
                  {do_call_20: forall
                        (fc': fun_ctx (translate_calldag cd) smaller_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256),
                      world_state * expr_result uint256}
                  (DoCallOk: forall fc' world arg_values,
                               do_call_20 (translate_fun_ctx fc' eq_refl) world arg_values
                                =
                               do_call_10 fc' world arg_values)
                  (world: world_state)
                  (loc: string_map uint256)
                  {list10: list L10.AST.stmt}
                  (CallOk20: let _ := string_set_impl in 
                             let is_private_call := fun name: string =>
                                      match cd_declmap cd name with
                                      | Some _ => true
                                      | _ => false
                                      end in
                           FSet.is_subset (L20.Callset.stmt_callset
                                            (translate_stmt_list is_private_call list10))
                                          (L20.Callset.decl_callset
                                             (fun_decl
                                               (translate_fun_ctx fc eq_refl)))
                     = true)
                  (CallOk10: let _ := string_set_impl in 
                     FSet.is_subset (L10.Callset.stmt_list_callset list10)
                                    (L10.Callset.decl_callset
                                      (fun_decl fc))
                     = true):
  let is_private_call := fun name: string =>
                            match cd_declmap cd name with
                            | Some _ => true
                            | _ => false
                            end in
  L20.Stmt.interpret_stmt Ebound (translate_fun_ctx fc eq_refl) do_call_20 builtins world loc
    (translate_stmt_list is_private_call list10) CallOk20
   =
  L10.Stmt.interpret_stmt_list Ebound fc do_call_10 builtins world loc list10 CallOk10.
Proof.
apply weak_stmt_list_ok. { apply DoCallOk. }
(* we're doing ItemsOk argument from weak_stmt_list_ok *)
rewrite List.Forall_forall.
intro s.
intro foo; clear foo. (* s is in list *)
clear CallOk20 CallOk10 world loc.
intros is_private_call NotVarDecl CallOk20 CallOk10 world loc.
apply interpret_translated_stmt. { apply DoCallOk. }
trivial.
Qed.