From Coq Require Import String ZArith Eqdep_dec Lia.

From Coq Require PropExtensionality.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L10.Expr L20.AST L10.Interpret L20.Interpret.

From Vyper.From10To20 Require Import Translate Callset FunCtx Expr Stmt.

Lemma interpret_translated_call {C: VyperConfig}
                                (builtins: string -> option builtin)
                                {cd: L10.Descend.calldag}
                                {call_depth_bound: nat}
                                (fc: fun_ctx cd call_depth_bound)
                                {cd2: L20.Descend.calldag}
                                (ok: cd2 = translate_calldag cd)
                                (world: world_state)
                                (arg_values: list uint256):
  L20.Interpret.interpret_call builtins (translate_fun_ctx fc ok) world arg_values
   =
  L10.Interpret.interpret_call builtins fc world arg_values.
Proof.
revert world arg_values. induction call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))). }
pose (is_private_call := fun name: string =>
          match cd_declmap cd name with
          | Some _ => true
          | _ => false
          end).
assert(F: cached_translated_decl fc ok
           = 
          translate_decl is_private_call (fun_decl fc)).
{
  clear IHcall_depth_bound.
  unfold translate_fun_ctx in *. cbn in *.
  unfold cached_translated_decl in *.
  remember (FunCtx.translate_fun_ctx_fun_decl_helper fc ok) as foo. clear Heqfoo.
  remember (cd_declmap cd2 (fun_name fc)) as d.
  destruct d. 2:{ contradiction. }
  subst. rewrite translate_calldag_ok in Heqd.
  remember (cd_declmap cd (fun_name fc)) as x.
  destruct x. 2:{ discriminate. }
  inversion Heqd. unfold is_private_call.
  f_equal. inversion Heqx.
  assert (D := fun_decl_ok fc).
  rewrite D in *. inversion H1. (* XXX *)
  trivial.
}
intros.
cbn.
remember (fun name arg_names body 
              (E: cached_translated_decl fc ok = AST.FunDecl name arg_names body) =>
            match Interpret.bind_args arg_names arg_values with
            | inl err => (world, expr_error err)
            | inr loc =>
                let
                '(world', _, result) :=
                 Stmt.interpret_stmt eq_refl (translate_fun_ctx fc ok) (Interpret.interpret_call builtins)
                   builtins world loc body (Interpret.interpret_call_helper E) in
                 (world',
                 match result with
                 | StmtSuccess => ExprSuccess zero256
                 | StmtAbort a => ExprAbort a
                 | StmtReturnFromFunction x => ExprSuccess x
                 end)
            end) as branch_20.
remember (fun name arg_names body
              (E : fun_decl fc = L10.AST.FunDecl name arg_names body) =>
            match Interpret.bind_args arg_names arg_values with
            | inl err => (world, expr_error err)
            | inr loc =>
                let
                '(world', _, result) :=
                 Stmt.interpret_stmt_list eq_refl fc (L10.Interpret.interpret_call builtins) builtins world
                   loc body (L10.Interpret.interpret_call_helper E) in
                 (world',
                 match result with
                 | StmtSuccess => ExprSuccess zero256
                 | StmtAbort a => ExprAbort a
                 | StmtReturnFromFunction x => ExprSuccess x
                 end)
            end) as branch_10.
assert (B: forall name arg_names body20 body10 E20 E10,
             branch_20 name arg_names body20 E20 = branch_10 name arg_names body10 E10).
{
  intros. subst.
  destruct (Interpret.bind_args arg_names arg_values) as [err|loc]. { trivial. }
  rewrite E10 in F. 
  assert (B20: body20 = translate_stmt_list is_private_call body10).
  { rewrite F in E20. now inversion E20. }
  subst body20.
  rewrite<- (interpret_translated_stmt_list eq_refl builtins fc IHcall_depth_bound world loc
                                            (L20.Interpret.interpret_call_helper E20)
                                            (L10.Interpret.interpret_call_helper E10)).
  fold is_private_call.
  destruct L20.Stmt.interpret_stmt as ((world', _), result).
  trivial.
}
clear Heqbranch_10. clear Heqbranch_20.
destruct (fun_decl fc); cbn in F; destruct cached_translated_decl; try discriminate.
{ now subst. }
inversion F; subst.
apply B.
Qed.

Lemma make_fun_ctx_and_bound_ok {C: VyperConfig}
                                (cd: L10.Descend.calldag)
                                (fun_name: string):
   make_fun_ctx_and_bound (translate_calldag cd) fun_name
    =
   match make_fun_ctx_and_bound cd fun_name with
   | Some (existT _ bound fc) => Some (existT _ bound (translate_fun_ctx fc eq_refl))
   | None => None
   end.
Proof.
(* this is too complicated due to destructing convoys *)
unfold make_fun_ctx_and_bound.
remember (fun d (Ed : cd_declmap (translate_calldag cd) fun_name = Some d) =>
    match
      cd_depthmap (translate_calldag cd) fun_name as depth'
      return
        (cd_depthmap (translate_calldag cd) fun_name = depth' ->
         option {bound : nat & fun_ctx (translate_calldag cd) bound})
    with
    | Some depth =>
        fun Edepth : cd_depthmap (translate_calldag cd) fun_name = Some depth =>
        Some
          (existT (fun bound : nat => fun_ctx (translate_calldag cd) bound) 
             (S depth)
             {|
             fun_name := fun_name;
             fun_depth := depth;
             fun_depth_ok := Edepth;
             fun_decl := d;
             fun_decl_ok := Ed;
             fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |})
    | None =>
        fun Edepth : cd_depthmap (translate_calldag cd) fun_name = None =>
        False_rect (option {bound : nat & fun_ctx (translate_calldag cd) bound})
          (Calldag.make_fun_ctx_helper Ed Edepth)
    end eq_refl) as lhs_some_branch.
remember (fun d (Ed : cd_declmap cd fun_name = Some d) =>
      match
        cd_depthmap cd fun_name as depth'
        return (cd_depthmap cd fun_name = depth' -> option {bound : nat & fun_ctx cd bound})
      with
      | Some depth =>
          fun Edepth : cd_depthmap cd fun_name = Some depth =>
          Some
            (existT (fun bound : nat => fun_ctx cd bound) (S depth)
               {|
               fun_name := fun_name;
               fun_depth := depth;
               fun_depth_ok := Edepth;
               fun_decl := d;
               fun_decl_ok := Ed;
               fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |})
      | None =>
          fun Edepth : cd_depthmap cd fun_name = None =>
          False_rect (option {bound : nat & fun_ctx cd bound}) (Calldag.make_fun_ctx_helper Ed Edepth)
      end eq_refl) as rhs_some_branch.
assert (SomeBranchOk: forall d Ed' Ed,
                        lhs_some_branch
                          (translate_decl
                             (fun name : string => match cd_declmap cd name with
                                                   | Some _ => true
                                                   | None => false
                                                   end) d) Ed'
                         =
                        match rhs_some_branch d Ed with
                        | Some (existT _ bound fc) =>
                            Some
                              (existT _ bound
                                 (translate_fun_ctx fc eq_refl))
                        | None => None
                        end).
{
  subst. cbn.
  intros.
  (* This is even more messed up than usual because just the implicit arguments weren't enough. *)
  remember (fun depth
         (Edepth : @eq (option nat)
                    (@cd_depthmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd fun_name)
                    (@Some nat depth)) =>
       @Some
         (@sigT nat
            (fun bound : nat =>
             @fun_ctx C (@AST.decl C) (@Callset.decl_callset C) false (@translate_calldag C cd) bound))
         (@existT nat
            (fun bound : nat =>
             @fun_ctx C (@AST.decl C) (@Callset.decl_callset C) false (@translate_calldag C cd) bound)
            (S depth)
            (Build_fun_ctx C (@AST.decl C) (@Callset.decl_callset C) false (@translate_calldag C cd)
               (S depth) fun_name depth Edepth
               (@translate_decl C
                  (fun name : string =>
                   match
                     @cd_declmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd name return bool
                   with
                   | Some _ => true
                   | None => false
                   end) d) Ed'
               (@proj2 (forall _ : @eq bool (Nat.leb depth depth) true, lt depth (S depth))
                  (forall _ : lt depth (S depth), @eq bool (Nat.leb depth depth) true)
                  (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth)))))
    as depth_lhs_some_branch.
  remember (fun (depth: nat)
          (Edepth : @eq (option nat)
                     (@cd_depthmap C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd fun_name)
                     (@Some nat depth)) =>
        @Some
          (@sigT nat
             (fun bound : nat => @fun_ctx C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd bound))
          (@existT nat
             (fun bound : nat => @fun_ctx C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd bound)
             (S depth)
             (Build_fun_ctx C (@L10.AST.decl C) (@L10.Callset.decl_callset C) true cd
                (S depth) fun_name depth Edepth d Ed
                (@proj2 (forall _ : @eq bool (Nat.leb depth depth) true, lt depth (S depth))
                   (forall _ : lt depth (S depth), @eq bool (Nat.leb depth depth) true)
                   (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth)))))
    as depth_rhs_some_branch.
  assert (A: forall depth E,
            depth_lhs_some_branch depth E
             =
            match depth_rhs_some_branch depth E with
            | Some (existT _ bound fc) =>
                Some
                  (existT (fun bound0 : nat => fun_ctx (translate_calldag cd) bound0) bound
                     (translate_fun_ctx fc eq_refl))
            | None => None
            end).
  {
    intros. subst.
    f_equal. f_equal.
    unfold translate_fun_ctx. cbn.
    assert (D: translate_decl
                (fun name : string => match cd_declmap cd name with
                                      | Some _ => true
                                      | None => false
                                      end) d
               =
              cached_translated_decl
                {|
                fun_name := fun_name;
                fun_depth := depth;
                fun_depth_ok := E;
                fun_decl := d;
                fun_decl_ok := Ed;
                fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |} eq_refl).
    {
      unfold cached_translated_decl.
      cbn.
      assert (X: forall false_branch,
                translate_decl
          (fun name : string => match cd_declmap cd name with
                                | Some _ => true
                                | None => false
                                end) d =
        match
          cd_declmap (translate_calldag cd) fun_name as d'
          return (cd_declmap (translate_calldag cd) fun_name = d' -> AST.decl)
        with
        | Some f =>
            fun _ => f
        | None => false_branch
        end eq_refl).
      { rewrite translate_calldag_ok. now rewrite Ed. }
      apply X.
    }
    assert (FunCtxEq: forall name1 depth depth_ok1 decl1 decl_ok1 bound_ok1
                             name2       depth_ok2 decl2 decl_ok2 bound_ok2
                             (Name: name1 = name2)
                             (Decl: decl1 = decl2),
      ({| fun_name := name1
        ; fun_depth := depth
        ; fun_depth_ok := depth_ok1
        ; fun_decl := decl1
        ; fun_decl_ok := decl_ok1
        ; fun_bound_ok := bound_ok1 |}: fun_ctx (translate_calldag cd) (S depth))
       =
      {| fun_name := name2
       ; fun_depth := depth
       ; fun_depth_ok := depth_ok2
       ; fun_decl := decl2
       ; fun_decl_ok := decl_ok2
       ; fun_bound_ok := bound_ok2 |}).
    {
      intros. subst.
      assert (depth_ok1 = depth_ok2) by apply PropExtensionality.proof_irrelevance.
      assert (decl_ok1 = decl_ok2) by apply PropExtensionality.proof_irrelevance.
      assert (bound_ok1 = bound_ok2) by apply PropExtensionality.proof_irrelevance.
      subst.
      trivial.
    }
    apply FunCtxEq. { (* name: *) trivial. }
    apply D.
  }
  clear Heqdepth_lhs_some_branch Heqdepth_rhs_some_branch.
  (* Unfortunately remembering the none branches doesn't work. Here's another way to go. *)
  assert (Oops := Calldag.make_fun_ctx_helper Ed).
  assert (K: forall foo bar,
  match
    cd_depthmap cd fun_name as depth'
    return
      (cd_depthmap cd fun_name = depth' -> option {bound : nat & fun_ctx (translate_calldag cd) bound})
  with
  | Some x => depth_lhs_some_branch x
  | None => foo
  end eq_refl =
  match
    match
      cd_depthmap cd fun_name as depth'
      return (cd_depthmap cd fun_name = depth' -> option {bound : nat & fun_ctx cd bound})
    with
    | Some x => depth_rhs_some_branch x
    | None => bar
    end eq_refl
  with
  | Some (existT _ bound fc) =>
      Some
        (existT (fun bound0 : nat => fun_ctx (translate_calldag cd) bound0) bound
           (translate_fun_ctx fc eq_refl))
  | None => None
  end).
  {
    intros.
    destruct (cd_depthmap cd fun_name).
    { apply A. }
    tauto.
  }
  apply K.
}
cbn in *.
remember (fun _: _ = None => None) as lhs_none_branch.
assert (NoneBranchOk: forall E, lhs_none_branch E = None).
{ subst. trivial. }
clear Heqlhs_some_branch Heqrhs_some_branch Heqlhs_none_branch.
assert (T := translate_calldag_ok cd fun_name).
destruct (cd_declmap cd fun_name); destruct (cd_declmap (translate_calldag cd) fun_name);
  try easy.
inversion T.
now subst.
Qed.

Theorem translate_ok {C: VyperConfig}
                     (builtins: string -> option builtin)
                     (cd: L10.Descend.calldag)
                     (fun_name: string)
                     (world: world_state)
                     (arg_values: list uint256):
  L20.Interpret.interpret builtins (translate_calldag cd) fun_name world arg_values
   =
  L10.Interpret.interpret builtins cd fun_name world arg_values.
Proof.
unfold L10.Interpret.interpret. unfold L20.Interpret.interpret.
rewrite make_fun_ctx_and_bound_ok.
destruct (make_fun_ctx_and_bound cd fun_name) as [(bound, fc)|]; cbn.
{ apply interpret_translated_call. }
trivial.
Qed.