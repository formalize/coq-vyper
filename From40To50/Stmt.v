From Coq Require Import String NArith ZArith DecimalString List Lia Eqdep_dec.

From Vyper Require Import Config Logic2 NaryFun.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require AST.
From Vyper.L50 Require AST.
From Vyper.L50 Require Import Types Expr Stmt.

From Vyper.L40Metered Require Import Interpret.

From Vyper.From40To50 Require Import Translate Proto Mangle Expr.

(* We always return exactly one value from every function.
 *)
Definition StmtResultsAgree {C: VyperConfig}
                (r40: world_state * memory * option (stmt_result uint256))
                (r50: world_state * string_map dynamic_value * option (stmt_result (list dynamic_value)))
                (varcap: N)
: Prop
:= let '(w40, m40, v40) := r40 in
   let '(w50, m50, v50) := r50 in
   LocalVarsAgree m40 m50 varcap
    /\
   match v40, v50 with
   | Some s40, Some s50 =>
        match s40, s50 with
        | StmtSuccess, StmtSuccess
        | StmtAbort AbortBreak, StmtAbort AbortBreak
        | StmtAbort AbortContinue, StmtAbort AbortContinue
            => w40 = w50

        | StmtAbort a40, StmtAbort a50 =>
            get_world_except_memory w40 = get_world_except_memory w50
             /\
            a40 = a50
        | StmtReturnFromFunction x40, StmtReturnFromFunction x50 =>
               w40 = w50
                /\
               x50 = existT _ U256 (yul_uint256 x40) :: nil
        | _, _ => False
        end
   | None, None => True
   | _, _ => False
   end.

(** We have to demand that [mstore()] doesn't change anything except memory
    otherwise the world changes in an unspecified way and everything is lost.
 *)
Definition BuiltinsSupportMstore {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
:= match b "mstore"%string with
   | None => False
   | Some mstore =>
      L50.Builtins.b_input_types mstore = U256 :: U256 :: nil
       /\
      L50.Builtins.b_output_types mstore = nil
       /\
      forall world addr value ArityOk,
        match fst (nary_call (L50.Builtins.b_fun mstore world) (addr :: value :: nil) ArityOk) with
        | (w, ExprSuccess nil) =>
             mload w addr = value
              /\
             get_world_except_memory w = get_world_except_memory world
        | _ => False (* mstore can't fail *)
        end
   end.

(** [call_builtin] has a nasty dependent match inside for typechecking,
    so this is less straightforward than it should be.
 *)
Lemma BuiltinsSupportMstore' {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
                             (Ok: BuiltinsSupportMstore b):
   match b "mstore"%string with
   | None => False
   | Some mstore =>
      forall world addr value,
          match L50.Builtins.call_builtin mstore world
           (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 addr)
            :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 value) :: nil) 
          with
          | (w, ExprSuccess nil) =>
               mload w addr = value
                /\
               get_world_except_memory w = get_world_except_memory world
          | _ => False (* mstore can't fail *)
          end
   end.
Proof.
unfold BuiltinsSupportMstore in Ok.
destruct (b "mstore"%string). 2:assumption.
intros world addr value.
unfold L50.Builtins.call_builtin.
destruct Ok as (InputOk, (OutputOk, FunOk)).
assert (TC: Builtins.mass_typecheck
                (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 addr)
                 :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 value) :: nil)
                (Builtins.b_input_types y)
              = L50.Builtins.MassTypecheckOk)
  by now rewrite InputOk.
rewrite L50.Builtins.mass_typecheck_ok_rewrite with (Ok := TC). cbn.
remember (Builtins.call_builtin_helper _ _ _) as foo. clear Heqfoo.
assert (F := FunOk world addr value foo).
destruct nary_call as ((w', e), rest).
destruct e as [out | ab]; cbn in F. 2:contradiction.
destruct out. 2:contradiction. now rewrite OutputOk.
Qed.

(** Here [revert()] is used to signal exceptions ([AbortException])
    and to implement Fe's revert statement ([AbortRevert]).
    The magical distinction between [revert(_, 0)] and [revert(_, 1)]
    is unnatural from the EVM viewpoint but here we'll pretend that EVM
    cares about Fe's raises and reverts.
 *)
Definition BuiltinsSupportRevert {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
:= match b "revert"%string with
   | None => False
   | Some revert =>
      L50.Builtins.b_input_types revert = U256 :: U256 :: nil
       /\
      L50.Builtins.b_output_types revert = nil
       /\
      (forall world addr ArityOk,
        match fst (nary_call (L50.Builtins.b_fun revert world) (addr :: zero256 :: nil) ArityOk) with
        | (w, ExprAbort AbortRevert) =>
              w = world
        | _ => False
        end)
       /\
      forall world addr ArityOk,
        match fst (nary_call (L50.Builtins.b_fun revert world) (addr :: one256 :: nil) ArityOk) with
        | (w, ExprAbort (AbortException e)) =>
              e = mload world addr /\ w = world
        | _ => False
        end
   end.

(* dup of BuiltinsSupportMstore' *)
Lemma BuiltinsSupportRevert0 {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
                             (Ok: BuiltinsSupportRevert b):
   match b "revert"%string with
   | None => False
   | Some revert =>
      forall world addr,
          match L50.Builtins.call_builtin revert world
           (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 addr)
            :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 zero256) :: nil) 
          with
          | (w, ExprAbort AbortRevert) => w = world
          | _ => False
          end
   end.
Proof.
unfold BuiltinsSupportRevert in Ok.
destruct (b "revert"%string). 2:assumption.
intros world addr.
unfold L50.Builtins.call_builtin.
destruct Ok as (InputOk, (OutputOk, (FunOk, _))).
assert (TC: Builtins.mass_typecheck
                (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 addr)
                 :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 zero256) :: nil)
                (Builtins.b_input_types y)
              = L50.Builtins.MassTypecheckOk)
  by now rewrite InputOk.
rewrite L50.Builtins.mass_typecheck_ok_rewrite with (Ok := TC). cbn.
remember (Builtins.call_builtin_helper _ _ _) as foo. clear Heqfoo.
assert (F := FunOk world addr foo).
destruct nary_call as ((w', e), rest).
destruct e as [out | ab]; cbn in F. { contradiction. }
now destruct ab.
Qed.

Lemma BuiltinsSupportRevert1 {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
                             (Ok: BuiltinsSupportRevert b):
   match b "revert"%string with
   | None => False
   | Some revert =>
      forall world addr,
          match L50.Builtins.call_builtin revert world
           (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 addr)
            :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 one256) :: nil) 
          with
          | (w, ExprAbort (AbortException e)) => e = mload world addr /\ w = world
          | _ => False 
          end
   end.
Proof.
unfold BuiltinsSupportRevert in Ok.
destruct (b "revert"%string). 2:assumption.
intros world addr.
unfold L50.Builtins.call_builtin.
destruct Ok as (InputOk, (OutputOk, (_, FunOk))).
assert (TC: Builtins.mass_typecheck
                (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 addr)
                 :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 zero256) :: nil)
                (Builtins.b_input_types y)
              = L50.Builtins.MassTypecheckOk)
  by now rewrite InputOk.
rewrite L50.Builtins.mass_typecheck_ok_rewrite with (Ok := TC). cbn.
remember (Builtins.call_builtin_helper _ _ _) as foo. clear Heqfoo.
assert (F := FunOk world addr foo).
destruct nary_call as ((w', e), rest).
destruct e as [out | ab]; cbn in F.  contradiction.
now destruct ab.
Qed.

Definition BuiltinsSupportStop {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
:= match b "stop"%string with
   | None => False
   | Some stop =>
      L50.Builtins.b_input_types stop = nil
       /\
      L50.Builtins.b_output_types stop = nil
       /\
      forall world ArityOk,
        match fst (nary_call (L50.Builtins.b_fun stop world) nil ArityOk) with
        | (w, ExprAbort AbortReturnFromContract) => w = world
        | _ => False
        end
   end.

Lemma BuiltinsSupportStop' {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
                           (Ok: BuiltinsSupportStop b):
   match b "stop"%string with
   | None => False
   | Some stop =>
      forall world,
          match L50.Builtins.call_builtin stop world nil with
          | (w, ExprAbort AbortReturnFromContract) => w = world
          | _ => False
          end
   end.
Proof.
unfold BuiltinsSupportStop in Ok.
destruct (b "stop"%string). 2:assumption.
intros world.
unfold L50.Builtins.call_builtin.
destruct Ok as (InputOk, (OutputOk, FunOk)).
assert (TC: Builtins.mass_typecheck nil (Builtins.b_input_types y)
              = L50.Builtins.MassTypecheckOk)
  by now rewrite InputOk.
rewrite L50.Builtins.mass_typecheck_ok_rewrite with (Ok := TC). cbn.
remember (Builtins.call_builtin_helper _ _ _) as foo. clear Heqfoo.
assert (F := FunOk world foo).
destruct nary_call as ((w', e), rest).
destruct e as [out | ab]; cbn in F.  contradiction.
now destruct ab.
Qed.

Definition BuiltinsSupportPop {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
:= match b "pop"%string with
   | None => False
   | Some pop =>
      L50.Builtins.b_input_types pop = U256 :: nil
       /\
      L50.Builtins.b_output_types pop = nil
       /\
      forall world value ArityOk,
        match fst (nary_call (L50.Builtins.b_fun pop world) (value :: nil) ArityOk) with
        | (w, ExprSuccess nil) => w = world
        | _ => False
        end
   end.

Lemma BuiltinsSupportPop' {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
                          (Ok: BuiltinsSupportPop b):
   match b "pop"%string with
   | None => False
   | Some pop =>
      forall world value,
          match L50.Builtins.call_builtin pop world
                   (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 value) :: nil) with
          | (w, ExprSuccess nil) => w = world
          | _ => False
          end
   end.
Proof.
unfold BuiltinsSupportPop in Ok.
destruct (b "pop"%string). 2:assumption.
intros world value.
unfold L50.Builtins.call_builtin.
destruct Ok as (InputOk, (OutputOk, FunOk)).
assert (TC: Builtins.mass_typecheck 
                (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 value) :: nil) 
                (Builtins.b_input_types y)
              = L50.Builtins.MassTypecheckOk)
  by now rewrite InputOk.
rewrite L50.Builtins.mass_typecheck_ok_rewrite with (Ok := TC). cbn.
remember (Builtins.call_builtin_helper _ _ _) as foo. clear Heqfoo.
assert (F := FunOk world value foo).
destruct nary_call as ((w', e), rest).
destruct e as [out | ab]; cbn in F. 2:contradiction.
destruct out. 2:contradiction.
now rewrite OutputOk.
Qed.

Definition BuiltinsSupportBasics {C: VyperConfig} (b: string -> option L50.Builtins.yul_builtin)
:= BuiltinsSupportMstore b
    /\
   BuiltinsSupportRevert b
    /\
   BuiltinsSupportStop b
    /\
   BuiltinsSupportPop b.

Record SecondaryVarsOk {C: VyperConfig} (loop_info: list L40.Expr.loop_ctx)
                       (loc: string_map dynamic_value)
:= { sv_result_declared:
           (* The local var dictionary contains [$$result] of type [u256].
            All translated functions declare [$$result] as the output variable
            and interpret_call binds all outputs to zeros. 
           *)
           match map_lookup loc "$$result" with
           | Some (existT _ (IntType I256 false (* that's U256 *) ) _) => True
           | _ => False
           end;
     sv_offsets_agree: LoopOffsetsAgree loop_info loc;
     sv_cursors_agree: LoopCursorsAgree loop_info loc;
     sv_offsets_undeclared: forall k, List.length loop_info <= k ->
                              map_lookup loc (make_var_name "offset" (N.of_nat k)) = None;
     sv_cursors_undeclared: forall k, List.length loop_info <= k ->
                              map_lookup loc (make_var_name "cursor" (N.of_nat k)) = None;
   }.
Arguments sv_result_declared {_ _ _}.
Arguments sv_offsets_agree {_ _ _}.
Arguments sv_cursors_agree {_ _ _}.
Arguments sv_offsets_undeclared {_ _ _}.
Arguments sv_cursors_undeclared {_ _ _}.

Lemma interpret_translated_small_stmt {C: VyperConfig}
                                      {B: builtin_names_config}
                                      {protos: string_map proto}
                                      {ss40: L40.AST.small_stmt}
                                      {s50: list L50.AST.stmt}
                                      {loop_depth: N}
                                      {max_loop_iterations: nat}
                                      (call40: forall
                                                    (decl: L40.AST.decl)
                                                    (world: world_state)
                                                    (arg_values: list uint256),
                                                  world_state * option (expr_result uint256))
                                      (call50: forall
                                                    (decl: L50.AST.fun_decl)
                                                    (world: world_state)
                                                    (arg_values: list dynamic_value),
                                                  world_state * option (expr_result (list dynamic_value)))
                                      (CallsOk: forall (decl40: L40.AST.decl)
                                                       (decl50: L50.AST.fun_decl)
                                                       (Ok: translate_fun_decl B protos decl40 = inr decl50)
                                                       (world: world_state)
                                                       (args40: list uint256)
                                                       (args50: list dynamic_value)
                                                       (ArgsOk: args50 = map (fun x : uint256 => existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x)) args40),
                                                   ResultsAgree (call40 decl40 world args40)
                                                                (call50 decl50 world args50) 1%N)
                                      (decls40: string_map L40.AST.decl)
                                      (decls50: string_map L50.AST.fun_decl)
                                      (this_fun_decl40: option L40.AST.decl)
                                      (this_fun_decl50: option L50.AST.fun_decl)
                                      (FunDeclOk: match this_fun_decl40, this_fun_decl50 with
                                                  | Some d40, Some d50 =>
                                                      translate_fun_decl B protos d40 = inr d50
                                                  | None, None => True
                                                  | _, _ => False
                                                  end)
                                      (Ok: translate_small_stmt (match this_fun_decl50 with
                                                                 | Some _ => true
                                                                 | None => false
                                                                 end) protos ss40 loop_depth = inr s50)
                                      (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
                                      (builtins40: string -> option builtin)
                                      (builtins50: string -> option L50.Builtins.yul_builtin)
                                      (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
                                      (BuiltinsBasics: BuiltinsSupportBasics builtins50)
                                      (BuiltinsSafe: forall x,
                                                       builtins50 ("$" ++ x)%string = None)
                                      (ProtosOk: ProtosAgree (map_lookup protos) builtins50)
                                      (world: world_state)
                                      (loc40: memory)
                                      (loc50: string_map dynamic_value)
                                      (varcap: N)
                                      (VarcapOk: (L40.AST.var_cap_small_stmt ss40 <= varcap)%N)
                                      (LocalVarsOk: LocalVarsAgree loc40 loc50 varcap)
                                      (loop_info: list L40.Expr.loop_ctx)
                                      (LoopDepthOk: length loop_info = N.to_nat loop_depth)
                                      (SV: SecondaryVarsOk loop_info loc50):
  let '(w, l, result50) :=
    interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50) 
                        this_fun_decl50 call50 world loc50 s50
  in
    StmtResultsAgree
      (interpret_small_stmt_metered decls40 call40 builtins40 world loc40 loop_info ss40)
      (w, l, result50)
      varcap
     /\
    SecondaryVarsOk loop_info l.
Proof.
destruct BuiltinsBasics as (SupportMstore, (SupportRevert, (SupportStop, SupportPop))).
destruct ss40; cbn.
{ (* abort *)
  destruct ab; inversion Ok; subst s50; clear Ok; cbn.
  { (* exception *)
    (* do mstore *)
    assert (SupportMstore' := BuiltinsSupportMstore' builtins50 SupportMstore).
    destruct (builtins50 "mstore"%string) as [mstore|]. 2:contradiction.
    rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "mstore" eq_refl).
    assert (SupportMstore'' := SupportMstore' world zero256 data).
    destruct L50.Builtins.call_builtin as (w, [out | ab]). 2:contradiction.
    destruct out. 2:contradiction.
    (* do revert *)
    assert (SupportRevert' := BuiltinsSupportRevert1 builtins50 SupportRevert).
    destruct (builtins50 "revert"%string) as [revert|]. 2:contradiction.
    rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "revert" eq_refl).
    assert (SupportRevert'' := SupportRevert' w zero256).
    destruct L50.Builtins.call_builtin as (w', [out | ab]). { contradiction. }
    destruct ab; try contradiction.
    destruct SupportRevert'' as (RevertDataOk, RevertWorldOk).
    destruct SupportMstore'' as (MstoreDataOk, MstoreWorldOk).
    symmetry in MstoreWorldOk.
    now subst.
  }
  { (* break *) easy. }
  { (* continue *) easy. }
  { (* return from contract *)
    assert (SupportStop' := BuiltinsSupportStop' builtins50 SupportStop).
    destruct (builtins50 "stop"%string) as [stop|]. 2:contradiction.
    rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "stop" eq_refl).
    assert (SupportStop'' := SupportStop' world).
    destruct L50.Builtins.call_builtin as (w', [out | ab]). { contradiction. }
    destruct ab; try contradiction. now subst.
  }
  { (* revert *)
    assert (SupportRevert' := BuiltinsSupportRevert0 builtins50 SupportRevert).
    destruct (builtins50 "revert"%string) as [revert|]. 2:contradiction.
    rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "revert" eq_refl).
    assert (SupportRevert'' := SupportRevert' world zero256).
    destruct L50.Builtins.call_builtin as (w', [out | ab]). { contradiction. }
    destruct ab; try contradiction. now subst.
  }
}
{ (* return from function *)
  destruct this_fun_decl50 as [this_fd|]. 2:easy. (* returns only allowed within functions *)
  cbn in Ok.
  remember (translate_expr protos e loop_depth) as e'.
  destruct e' as [|(e', n')]. { easy. }
  destruct n' as [|p].
  {
    (* return with a builtin that produces 0 values - legal in Fe *)
    inversion Ok; subst s50; clear Ok; cbn.
    symmetry in Heqe'.
    assert (ReturnValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                                             builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                                             ProtosOk world loc40 loc50
                                                             (local_vars_agree_weaken VarcapOk LocalVarsOk)
                                                             loop_info LoopDepthOk
                                                             (sv_offsets_agree SV) (sv_cursors_agree SV)).
    unfold ResultsAgree in ReturnValueOk.
    destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
    destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e') as (w50, r50).
    destruct r40 as [r40|], r50 as [r50|]; try easy. (* dealing with None (out of limits) *)
    unfold ExprResultsAgree in ReturnValueOk.
    destruct ReturnValueOk as (W, ReturnValueOk). subst w40.
    destruct r40 as [v40|ab40], r50 as [v50|ab50]; try easy.
    destruct v50. 2:{
      destruct v50. 2:tauto. assert (Bad: 0%N = 1%N) by tauto. discriminate.
    }

    (* pass the check that $$result is declared at all *)
    assert (ResultDeclared := sv_result_declared SV).
    destruct (map_lookup loc50 "$$result") as [(result_type, _)|]. 2:contradiction.
    destruct result_type; try contradiction.
    destruct size; try contradiction.
    destruct signed; try contradiction.
    destruct yul_type_eq_dec; try easy.

    (* fetch the declaration of $$result *)
    destruct this_fun_decl40 as [this_fd40|]. 2:contradiction.
    unfold translate_fun_decl in FunDeclOk.
    destruct this_fd40 as (this_fun_name, this_fun_arity, this_fun_body40).
    remember (translate_block true B protos this_fun_body40 0) as this_fun_body50.
    destruct this_fun_body50 as [|(this_fun_body50)]. 1:discriminate.
    inversion FunDeclOk; subst this_fd; clear FunDeclOk. cbn.

    (* finally we can load $$result. *)
    unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
    destruct string_dec. 2:contradiction. cbn.
    destruct ReturnValueOk as (V, _).
    split.
    {
      split. 2:now subst.
      cbn in LocalVarsOk.

      (* we need to prove that setting $$result doesn't disturb LocalVarsAgree. *)
      unfold LocalVarsAgree in *.
      intros k L. assert (A := LocalVarsOk k L).
      unfold map_lookup in *. rewrite Map.insert_ok.
      destruct (string_dec "$$result" (make_var_name "var" k)) as [E|NE]. 2:assumption.
      exfalso. cbn in E. discriminate.
    }
    split.
    {
      unfold map_lookup. rewrite Map.insert_ok.
      now destruct string_dec.
    }
    {
      unfold LoopOffsetsAgree. intros k L.
      unfold map_lookup. rewrite Map.insert_ok.
      destruct (string_dec "$$result" (make_var_name "offset" (N.of_nat k))) as [E|NE].
      2:exact (sv_offsets_agree SV k L).
      exfalso. cbn in E. discriminate.
    }
    {
      unfold LoopCursorsAgree. intros k L.
      unfold map_lookup. rewrite Map.insert_ok.
      destruct (string_dec "$$result" (make_var_name "cursor" (N.of_nat k))) as [E|NE].
      2:exact (sv_cursors_agree SV k L).
      exfalso. cbn in E. discriminate.
    }
    {
      intros k GE. unfold map_lookup.
      rewrite Map.insert_ok.
      destruct (string_dec "$$result" (make_var_name "offset" (N.of_nat k))) as [E|NE].
      2:exact (sv_offsets_undeclared SV k GE).
      exfalso. cbn in E. discriminate.
    }
    intros k GE. unfold map_lookup.
    rewrite Map.insert_ok.
    destruct (string_dec "$$result" (make_var_name "cursor" (N.of_nat k))) as [E|NE].
    2:exact (sv_cursors_undeclared SV k GE).
    exfalso. cbn in E. discriminate.
    subst ab50. now destruct ab40.
  }
  (* normal return with something that produces a value *)
  (* dup *)
  destruct p; try discriminate.
  inversion Ok; subst s50; clear Ok; cbn.
  symmetry in Heqe'.
  assert (ReturnValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                                           builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                                           ProtosOk world loc40 loc50
                                                           (local_vars_agree_weaken VarcapOk LocalVarsOk)
                                                           loop_info LoopDepthOk
                                                           (sv_offsets_agree SV) (sv_cursors_agree SV)).
  unfold ResultsAgree in ReturnValueOk.
  destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
  destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e') as (w50, r50).
  destruct r40 as [r40|], r50 as [r50|]; try easy. (* dealing with None (out of limits) *)
  unfold ExprResultsAgree in ReturnValueOk.
  destruct ReturnValueOk as (W, ReturnValueOk). subst w40.
  destruct r40 as [v40|ab40], r50 as [v50|ab50]; try easy.
  destruct v50 as [|v]. { destruct ReturnValueOk as (_, A). discriminate. }
  destruct v50. 2:tauto.

  (* pass the check that $$result is declared at all *)
  assert (ResultDeclared := sv_result_declared SV).
  destruct (map_lookup loc50 "$$result") as [(result_type, _)|]. 2:contradiction.
  destruct result_type; try contradiction.
  destruct size; try contradiction.
  destruct signed; try contradiction.
  destruct ReturnValueOk as (V, _). subst v.
  destruct yul_type_eq_dec; try easy.

  (* fetch the declaration of $$result *)
  destruct this_fun_decl40 as [this_fd40|]. 2:contradiction.
  unfold translate_fun_decl in FunDeclOk.
  destruct this_fd40 as (this_fun_name, this_fun_arity, this_fun_body40).
  remember (translate_block true B protos this_fun_body40 0) as this_fun_body50.
  destruct this_fun_body50 as [|(this_fun_body50)]. 1:discriminate.
  inversion FunDeclOk; subst this_fd; clear FunDeclOk. cbn.

  (* finally we can load $$result. *)
  unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
  destruct string_dec. 2:contradiction. cbn.
  split.
  {
    split. 2:now subst.
    cbn in LocalVarsOk.

    (* we need to prove that setting $$result doesn't disturb LocalVarsAgree. *)
    unfold LocalVarsAgree in *.
    intros k L. assert (A := LocalVarsOk k L).
    unfold map_lookup in *. rewrite Map.insert_ok.
    destruct (string_dec "$$result" (make_var_name "var" k)) as [E|NE]. 2:assumption.
    exfalso. cbn in E. discriminate.
  }
  split.
  {
    unfold map_lookup. rewrite Map.insert_ok.
    now destruct string_dec.
  }
  {
    unfold LoopOffsetsAgree. intros k L.
    unfold map_lookup. rewrite Map.insert_ok.
    destruct (string_dec "$$result" (make_var_name "offset" (N.of_nat k))) as [E|NE].
    2:exact (sv_offsets_agree SV k L).
    exfalso. cbn in E. discriminate.
  }
  {
    unfold LoopCursorsAgree. intros k L.
    unfold map_lookup. rewrite Map.insert_ok.
    destruct (string_dec "$$result" (make_var_name "cursor" (N.of_nat k))) as [E|NE].
    2:exact (sv_cursors_agree SV k L).
    exfalso. cbn in E. discriminate.
  }
  {
    intros k GE. unfold map_lookup.
    rewrite Map.insert_ok.
    destruct (string_dec "$$result" (make_var_name "offset" (N.of_nat k))) as [E|NE].
    2:exact (sv_offsets_undeclared SV k GE).
    exfalso. cbn in E. discriminate.
  }
  intros k GE. unfold map_lookup.
  rewrite Map.insert_ok.
  destruct (string_dec "$$result" (make_var_name "cursor" (N.of_nat k))) as [E|NE].
  2:exact (sv_cursors_undeclared SV k GE).
  exfalso. cbn in E. discriminate.
  subst ab50. now destruct ab40.
}
{ (* raise *)
  cbn in Ok. remember (translate_expr protos e loop_depth) as e'.
  destruct e' as [err|(e50, n')]. 1:discriminate. symmetry in Heqe'.
  destruct n' as [|p].
  { (* 0 results *)
    inversion Ok; subst s50; clear Ok. cbn.

    (* ensure that both sides evaluate to 0 *)
    assert (RaisedValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                                             builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                                             ProtosOk world loc40 loc50
                                                             (local_vars_agree_weaken VarcapOk LocalVarsOk)
                                                             loop_info LoopDepthOk
                                                             (sv_offsets_agree SV) (sv_cursors_agree SV)).
    unfold ResultsAgree in RaisedValueOk.
    destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
    destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e50) as (w50, r50).
    destruct r40 as [r40|], r50 as [r50|]; try easy.
    destruct RaisedValueOk as (W, RaisedValuesAgree). subst w40.
    unfold ExprResultsAgree in RaisedValuesAgree.
    destruct r40 as [val40 | ab40], r50 as [val50 | ab50]; try contradiction.
    2:{ subst ab50. subst. now destruct ab40. }
    destruct val50.
    2:{ destruct val50. { assert (Bad: 0%N = 1%N) by tauto. discriminate. } contradiction. }
    destruct RaisedValuesAgree as (V, _). subst val40.

    (* dup from abort above - doing mstore *)
    assert (SupportMstore' := BuiltinsSupportMstore' builtins50 SupportMstore).
    destruct (builtins50 "mstore"%string) as [mstore|]. 2:contradiction.
    rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "mstore" eq_refl).
    assert (SupportMstore'' := SupportMstore' w50 zero256 zero256).
    destruct L50.Builtins.call_builtin as (w, [out | ab]). 2:contradiction.
    destruct out. 2:contradiction.
    (* do revert *)
    assert (SupportRevert' := BuiltinsSupportRevert1 builtins50 SupportRevert).
    destruct (builtins50 "revert"%string) as [revert|]. 2:contradiction.
    rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "revert" eq_refl).
    assert (SupportRevert'' := SupportRevert' w zero256).
    destruct L50.Builtins.call_builtin as (w', [out | ab]). { contradiction. }
    destruct ab; try contradiction.
    destruct SupportMstore'' as (MstoreDataOk, MstoreWorldOk).
    destruct SupportRevert'' as (RevertDataOk, RevertWorldOk).
    rewrite MstoreDataOk in RevertDataOk. subst.
    now unfold StmtResultsAgree.
  }
  (* raising 1 value; massive dup of course. *)
  destruct p; try discriminate.
  inversion Ok; subst s50; clear Ok; cbn.
  assert (RaisedValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                                             builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                                             ProtosOk world loc40 loc50
                                                             (local_vars_agree_weaken VarcapOk LocalVarsOk)
                                                             loop_info LoopDepthOk
                                                             (sv_offsets_agree SV) (sv_cursors_agree SV)).
  unfold ResultsAgree in RaisedValueOk.
  destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
  destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e50) as (w50, r50).
  destruct r40 as [r40|], r50 as [r50|]; try easy.
  2:{
    (* both computations resulted in out of limits error *)
    (* we still have to check for mstore *)
    assert (SupportMstore' := BuiltinsSupportMstore' builtins50 SupportMstore).
    destruct (builtins50 "mstore"%string) as [mstore|]. 2:contradiction.
    cbn. rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "mstore" eq_refl).
    tauto.
  }
  unfold StmtResultsAgree.
  destruct RaisedValueOk as (W, RaisedValuesAgree). subst w40.
  unfold ExprResultsAgree in RaisedValuesAgree.

  (* doing mstore - 1*)
  assert (SupportMstore' := BuiltinsSupportMstore' builtins50 SupportMstore).
  destruct (builtins50 "mstore"%string) as [mstore|]. 2:contradiction.
  rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "mstore" eq_refl).

  destruct r40 as [val40 | ab40], r50 as [val50 | ab50]; try easy.
  2:{ subst ab50. now destruct ab40. }
  cbn.
  destruct val50.
  { assert (Bad: 1%N = 0%N) by tauto. discriminate. }
  destruct val50. 2: contradiction.
  destruct RaisedValuesAgree as (V, _). subst.

  (* doing mstore - 2 *)
  assert (SupportMstore'' := SupportMstore' w50 zero256 val40).
  destruct L50.Builtins.call_builtin as (w, [out | ab]). 2:contradiction.
  destruct out. 2:contradiction.

  (* do revert *)
  assert (SupportRevert' := BuiltinsSupportRevert1 builtins50 SupportRevert).
  destruct (builtins50 "revert"%string) as [revert|]. 2:contradiction.
  rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "revert" eq_refl).
  assert (SupportRevert'' := SupportRevert' w zero256).
  destruct L50.Builtins.call_builtin as (w', [out | ab]). { contradiction. }
  destruct ab; try contradiction.
  destruct SupportMstore'' as (MstoreDataOk, MstoreWorldOk).
  destruct SupportRevert'' as (RevertDataOk, RevertWorldOk).
  rewrite MstoreDataOk in RevertDataOk. subst.
  now unfold StmtResultsAgree.
}
{ (* assign *)
  cbn in Ok. remember (translate_expr protos rhs loop_depth) as rhs'.
  destruct rhs' as [err|(rhs50, n')]. 1:discriminate. symmetry in Heqrhs'.
  destruct n' as [|p].
  { (* 0 results *)
    cbn in Ok. inversion Ok; subst s50; clear Ok. cbn. cbn in LocalVarsOk. cbn in VarcapOk.
    assert (AssignedValueOk := interpret_translated_expr Heqrhs' call40 call50 CallsOk decls40 decls50 DeclsOk
                                                         builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                                         ProtosOk world loc40 loc50
                                                         (local_vars_agree_weaken_right
                                                           (local_vars_agree_weaken VarcapOk LocalVarsOk))
                                                         loop_info LoopDepthOk
                                                         (sv_offsets_agree SV) (sv_cursors_agree SV)).
    unfold ResultsAgree in AssignedValueOk.
    destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info rhs) as (w40, r40).
    destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 rhs50) as (w50, r50).
    destruct AssignedValueOk as (W, AssignedValueOk). subst w40.
    destruct r40 as [r40 | ], r50 as [r50 | ]; try easy.
    unfold ExprResultsAgree in AssignedValueOk.

    destruct r40 as [val40 | ab40], r50 as [val50 | ab50]; try easy. 
    2:{ subst ab50. now destruct ab40. }
    cbn.
    destruct val50.
    2:{ destruct val50. { assert (Bad: 0%N = 1%N) by tauto. discriminate. } contradiction. }
    destruct AssignedValueOk as (V, _). subst.
    assert (LhsOk := local_vars_agree_weaken_left (local_vars_agree_weaken VarcapOk LocalVarsOk) lhs (N.lt_succ_diag_r _)).
    unfold LocalVarsAgree in LhsOk.
    cbn in LhsOk. rewrite LhsOk.
    destruct (yul_type_eq_dec U256 U256) as [E|]. 2:contradiction. clear E.
    cbn.

    split.
    {
      split. 2:trivial.
      (* goal: LocalVarsAgree between OpenArray.put and Map.insert *)
      intros k L.
      unfold map_lookup. unfold map_insert. rewrite Map.insert_ok. rewrite OpenArray.put_ok.
      remember (lhs =? k)%N as q. symmetry in Heqq. destruct q.
      { (* lhs = k *)
        apply N.eqb_eq in Heqq. subst lhs.
        destruct string_dec as [_|NE]; trivial. cbn in NE. tauto.
      }
      (* lhs <> k *)
      destruct string_dec as [E|_]; trivial.
      {
        rewrite N.eqb_neq in Heqq.
        assert (M := make_var_name_inj' "var" lhs k Heqq).
        easy.
      }
      apply (LocalVarsOk k L).
    }
    split.
    {
      unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
      destruct string_dec as [E|NE]. { discriminate. }
      apply (sv_result_declared SV).
    }
    {
      unfold LoopOffsetsAgree. intros k L.
      unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
      destruct string_dec as [E|NE].
      2:exact (sv_offsets_agree SV k L).
      exfalso. cbn in E. discriminate.
    } 
    {
      unfold LoopOffsetsAgree. intros k L.
      unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
      destruct string_dec as [E|NE].
      2:exact (sv_cursors_agree SV k L).
      exfalso. cbn in E. discriminate.
    }
    {
      intros k GE. unfold map_lookup. unfold map_insert.
      rewrite Map.insert_ok.
      destruct string_dec as [E|NE].
      2:exact (sv_offsets_undeclared SV k GE).
      exfalso. cbn in E. discriminate.
    }
    intros k GE. unfold map_lookup. unfold map_insert.
    rewrite Map.insert_ok.
    destruct string_dec as [E|NE].
    2:exact (sv_cursors_undeclared SV k GE).
    exfalso. cbn in E. discriminate.
  }
  destruct p; try discriminate.
  (* 1 result, of course dup from 0 results *)
  cbn in Ok. inversion Ok; subst s50; clear Ok. cbn. cbn in LocalVarsOk. cbn in VarcapOk.
  assert (AssignedValueOk := interpret_translated_expr Heqrhs' call40 call50 CallsOk decls40 decls50 DeclsOk
                                                       builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                                       ProtosOk world loc40 loc50 
                                                       (local_vars_agree_weaken_right
                                                         (local_vars_agree_weaken VarcapOk LocalVarsOk))
                                                       loop_info LoopDepthOk
                                                       (sv_offsets_agree SV) (sv_cursors_agree SV)).
  unfold ResultsAgree in AssignedValueOk.
  destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info rhs) as (w40, r40).
  destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 rhs50) as (w50, r50).
  destruct AssignedValueOk as (W, AssignedValueOk). subst w40.
  unfold StmtResultsAgree.
  destruct r40 as [r40 | ], r50 as [r50 | ]; try easy.
  unfold ExprResultsAgree in AssignedValueOk.

  destruct r40 as [val40 | ab40], r50 as [val50 | ab50]; try easy. 
  2:{ subst ab50. now destruct ab40. }
  cbn.
  destruct val50. { assert (Bad: 1%N = 0%N) by tauto. discriminate. }
  destruct val50. 2:contradiction.
  destruct AssignedValueOk as (V, _). subst.
  assert (LhsOk := local_vars_agree_weaken_left (local_vars_agree_weaken VarcapOk LocalVarsOk) lhs (N.lt_succ_diag_r _)).
  unfold LocalVarsAgree in LhsOk.
  cbn in LhsOk. 
  cbn.
  rewrite LhsOk.
  destruct (yul_type_eq_dec U256 U256) as [E|]. 2:contradiction. clear E.
  cbn.

  split.
  {
    split. 2:trivial.
    (* goal: LocalVarsAgree between OpenArray.put and Map.insert *)
    intros k L.
    unfold map_lookup. unfold map_insert. rewrite Map.insert_ok. rewrite OpenArray.put_ok.
    remember (lhs =? k)%N as q. symmetry in Heqq. destruct q.
    { (* lhs = k *)
      apply N.eqb_eq in Heqq. subst lhs.
      destruct string_dec as [_|NE]; trivial. cbn in NE. tauto.
    }
    (* lhs <> k *)
    destruct string_dec as [E|_]; trivial.
    {
      rewrite N.eqb_neq in Heqq.
      assert (M := make_var_name_inj' "var" lhs k Heqq).
      easy.
    }
    apply (LocalVarsOk k L).
  }
  split.
  {
    unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
    destruct string_dec as [E|NE]. { discriminate. }
    apply (sv_result_declared SV).
  }
  {
    unfold LoopOffsetsAgree. intros k L.
    unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
    destruct string_dec as [E|NE].
    2:exact (sv_offsets_agree SV k L).
    exfalso. cbn in E. discriminate.
  } 
  {
    unfold LoopOffsetsAgree. intros k L.
    unfold map_lookup. unfold map_insert. rewrite Map.insert_ok.
    destruct string_dec as [E|NE].
    2:exact (sv_cursors_agree SV k L).
    exfalso. cbn in E. discriminate.
  }
  {
    intros k GE. unfold map_lookup. unfold map_insert.
    rewrite Map.insert_ok.
    destruct string_dec as [E|NE].
    2:exact (sv_offsets_undeclared SV k GE).
    exfalso. cbn in E. discriminate.
  }
  intros k GE. unfold map_lookup. unfold map_insert.
  rewrite Map.insert_ok.
  destruct string_dec as [E|NE].
  2:exact (sv_cursors_undeclared SV k GE).
  exfalso. cbn in E. discriminate.
}
(* expr *)
cbn in Ok. remember (translate_expr protos e loop_depth) as e'.
destruct e' as [err|(e50, n')]. 1:discriminate. symmetry in Heqe'.
destruct n' as [|p].
{ (* 0 results *)
  cbn in Ok. inversion Ok; subst s50; clear Ok. cbn. cbn in LocalVarsOk.
  assert (ValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                               builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                               ProtosOk world loc40 loc50
                                               (local_vars_agree_weaken VarcapOk LocalVarsOk)
                                               loop_info LoopDepthOk
                                               (sv_offsets_agree SV) (sv_cursors_agree SV)).
  unfold ResultsAgree in ValueOk.
  destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
  destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e50) as (w50, r50).
  destruct ValueOk as (W, ValueOk). subst w40.
  unfold StmtResultsAgree.

  destruct r40 as [r40 | ], r50 as [r50 | ]; try easy.
  unfold ExprResultsAgree in ValueOk.
  destruct r40 as [val40 | ab40], r50 as [val50 | ab50]; try easy.
  2:{ subst ab50. now destruct ab40. }
  cbn.
  destruct val50.
  2:{ destruct val50. { assert (Bad: 0%N = 1%N) by tauto. discriminate. } contradiction. }
  destruct ValueOk as (V, _). subst.
  cbn. now split.
}
destruct p; try discriminate.
(* 1 result *)
cbn in Ok. inversion Ok; subst s50; clear Ok. cbn. cbn in LocalVarsOk.
assert (ValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                             builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                             ProtosOk world loc40 loc50
                                             (local_vars_agree_weaken VarcapOk LocalVarsOk)
                                             loop_info LoopDepthOk
                                             (sv_offsets_agree SV) (sv_cursors_agree SV)).
unfold ResultsAgree in ValueOk.
destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e50) as (w50, r50).
destruct ValueOk as (W, ValueOk). subst w40.

(* do pop *)
assert (SupportPop' := BuiltinsSupportPop' builtins50 SupportPop).
destruct (builtins50 "pop"%string) as [pop|]. 2:contradiction.
rewrite (unmangled_names_are_not_translated decls40 decls50 DeclsOk "pop" eq_refl).

unfold StmtResultsAgree.
unfold ExprResultsAgree in ValueOk.
destruct r40 as [r40 | ], r50 as [r50 | ]; try easy.
cbn.
destruct r40 as [val40 | ab40], r50 as [val50 | ab50]; try easy.
2:{ subst ab50. now destruct ab40. }
cbn.
destruct val50. { assert (Bad: 1%N = 0%N) by tauto. discriminate. }
destruct val50. 2:contradiction.
destruct ValueOk as (V, _). subst.
assert (SupportPop'' := SupportPop' w50 val40).
destruct (Builtins.call_builtin pop) as (w, [out | ab]). 2:contradiction.
destruct out. 2:contradiction.
subst w50. cbn.
now split.
Qed.

Lemma lookup_unbind {C: VyperConfig}
                    (loc50: string_map dynamic_value)
                    (vars: list L50.AST.typename)
                    (name: string):
  map_lookup (LocalVars.unbind_vars vars loc50) name
   =
  if ListSet.set_mem string_dec name (List.map snd vars)
    then None
    else map_lookup loc50 name.
Proof.
revert loc50. induction vars as [|head]; intros. { easy. }
unfold map_lookup in *. cbn.
rewrite IHvars. unfold map_remove.
rewrite Map.remove_ok.
destruct (string_dec name (snd head)) as [E|NE];
  destruct (string_dec (snd head) name) as [E'|NE'];
  destruct (ListSet.set_mem string_dec name (map snd vars));
  try easy;
  try symmetry in E; try contradiction;
  try symmetry in E'; try contradiction.
Qed.

Lemma local_vars_agree_erase_unbind {C: VyperConfig}
                                    (loc40: memory)
                                    (loc50: string_map dynamic_value)
                                    (vars: list L50.AST.typename)
                                    (varcap: N)
    (Ok: LocalVarsAgree loc40 (L50.LocalVars.unbind_vars vars loc50) varcap):
  LocalVarsAgree loc40 loc50 varcap.
Proof.
intros k L.
assert (OkK := Ok k L).
rewrite lookup_unbind in OkK.
destruct (ListSet.set_mem string_dec (make_var_name "var" k) (map snd vars)).
{ discriminate. }
exact OkK.
Qed.

Lemma stmt_results_agree_erase_unbind {C: VyperConfig}
                                      (w40 w50: world_state)
                                      (loc40: memory)
                                      (loc50: string_map dynamic_value)
                                      (result40: option (stmt_result uint256))
                                      (result50: option (stmt_result (list dynamic_value)))
                                      (vars: list L50.AST.typename)
                                      (varcap: N)
   (Ok: StmtResultsAgree (w40, loc40, result40)
                         (w50, L50.LocalVars.unbind_vars vars loc50, result50)
                         varcap):
  StmtResultsAgree (w40, loc40, result40) (w50, loc50, result50) varcap.
Proof.
unfold StmtResultsAgree in *.
split. 2:tauto.
destruct Ok as (Ok, _).
apply local_vars_agree_erase_unbind in Ok.
exact Ok.
Qed.


Lemma translated_stmt_declares_nothing  {C: VyperConfig}
                                        {B: builtin_names_config}
                                        {loop_depth: N}
                                        {protos: string_map proto}
                                        {s40: L40.AST.stmt}
                                        {s50: list L50.AST.stmt}
                                        {this_fun_decl50: option L50.AST.fun_decl}
                                        (Ok: translate_stmt (match this_fun_decl50 with
                                                             | Some _ => true
                                                             | None => false
                                                             end) B protos s40 loop_depth = inr s50):
  stmt_list_has_top_level_var_decls s50 = false.
Proof.
destruct s40; cbn in Ok.
{ (* small *)
  destruct ss; cbn in Ok;
    try (destruct translate_expr as [|(e', n)]; [| destruct n as [|p]]);
    try destruct p;
    try (inversion Ok; subst);
    try easy;
    try (destruct ab; cbn in Ok; inversion Ok; now subst);
    try destruct this_fun_decl50;
    inversion Ok; subst; easy.
}
{ (* switch *)
  destruct (_ cases) as [err | cases']. { easy. }
  destruct default as [default|].
  {
    destruct translate_block as [err | default']. { easy. }
    destruct translate_expr as [|(e', n)]; [| destruct n as [|p]];
      try easy.
    { inversion Ok; now subst. }
    destruct p; try easy. inversion Ok; now subst.
  }
  destruct translate_expr as [|(e', n)]; [| destruct n as [|p]];
    try easy.
  { inversion Ok; now subst. }
  destruct p; try easy. inversion Ok; now subst.
}
(* loop *)
destruct translate_block as [err | body']. { easy. }
inversion Ok. now subst.
Qed.


Lemma translated_block_declares_nothing  {C: VyperConfig}
                                         {B: builtin_names_config}
                                         {loop_depth: N}
                                         {protos: string_map proto}
                                         {b40: L40.AST.block}
                                         {b50: L50.AST.block}
                                         {this_fun_decl50: option L50.AST.fun_decl}
                                         (Ok: translate_block (match this_fun_decl50 with
                                                               | Some _ => true
                                                               | None => false
                                                               end) B protos b40 loop_depth = inr b50):
  let '(L50.AST.Block s50) := b50 in
  stmt_list_has_top_level_var_decls s50 = false.
Proof.
destruct b40 as (s40).
destruct b50 as (s50).
revert s50 Ok. induction s40 as [|head40]; intros; cbn in Ok. { now inversion Ok. }
remember (translate_stmt match this_fun_decl50 with
                         | Some _ => true
                         | None => false
                         end B protos head40 loop_depth) as head'.
destruct head' as [|head50]. discriminate. symmetry in Heqhead'.
cbn in Ok. cbn in IHs40.
remember (_ s40) as tail50.
destruct tail50 as [|tail50]. 1:easy.
inversion Ok; subst.
rewrite stmt_list_has_top_level_var_decls_app.
rewrite (translated_stmt_declares_nothing Heqhead').
now rewrite (IHs40 tail50 eq_refl).
Qed.

(* to Arith2 *)
Lemma max_lub_lt_l {a b c : N} (H: (N.max a b < c)%N):
  (a < c)%N.
Proof. exact (proj1 (proj1 (N.max_lub_lt_iff _ _ _) H)). Qed.
Lemma max_lub_lt_r {a b c : N} (H: (N.max a b < c)%N):
  (b < c)%N.
Proof. exact (proj2 (proj1 (N.max_lub_lt_iff _ _ _) H)). Qed.

(** Blocks are interpreted correctly provided that statements are interpreted correctly. *)
Local Lemma interpret_translated_block_weak
    {C: VyperConfig}
    {B: builtin_names_config}
    {protos: string_map proto}
    {loop_depth: N}
    {max_loop_iterations: nat}
    (call40: forall
                  (decl: L40.AST.decl)
                  (world: world_state)
                  (arg_values: list uint256),
                world_state * option (expr_result uint256))
    (call50: forall
                  (decl: L50.AST.fun_decl)
                  (world: world_state)
                  (arg_values: list dynamic_value),
                world_state * option (expr_result (list dynamic_value)))
    (CallsOk: forall (decl40: L40.AST.decl)
                     (decl50: L50.AST.fun_decl)
                     (Ok: translate_fun_decl B protos decl40 = inr decl50)
                     (world: world_state)
                     (args40: list uint256)
                     (args50: list dynamic_value)
                     (ArgsOk: args50 = map (fun x : uint256 => existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x)) args40),
                 ResultsAgree (call40 decl40 world args40)
                              (call50 decl50 world args50) 1%N)
    (decls40: string_map L40.AST.decl)
    (decls50: string_map L50.AST.fun_decl)
    (this_fun_decl40: option L40.AST.decl)
    (this_fun_decl50: option L50.AST.fun_decl)
    (FunDeclOk: match this_fun_decl40, this_fun_decl50 with
                | Some d40, Some d50 =>
                    translate_fun_decl B protos d40 = inr d50
                | None, None => True
                | _, _ => False
                end)
    (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
    (builtins40: string -> option builtin)
    (builtins50: string -> option L50.Builtins.yul_builtin)
    (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
    (BuiltinsBasics: BuiltinsSupportBasics builtins50)
    (BuiltinsSafe: forall x,
                     builtins50 ("$" ++ x)%string = None)
    (ProtosOk: ProtosAgree (map_lookup protos) builtins50)
    (world: world_state)
    (loc40: memory)
    (loc50: string_map dynamic_value)
    (loop_info: list L40.Expr.loop_ctx)
    (LoopDepthOk: length loop_info = N.to_nat loop_depth)
    (SV: SecondaryVarsOk loop_info loc50)
    (b40: L40.AST.block)
    (b50: L50.AST.block)
    (Ok: translate_block (match this_fun_decl50 with
                          | Some _ => true
                          | None => false
                          end) B protos b40 loop_depth = inr b50)
    (varcap: N)
    (VarcapOk: (L40.AST.var_cap_block b40 <= varcap)%N)
    (LocalVarsOk: LocalVarsAgree loc40 loc50 varcap)
    (EnoughIterations:
      (L40.AST.max_loop_count_block b40 < N.of_nat max_loop_iterations)%N)
    (OkB: match b40 with
          | L40.AST.Block body =>
             Forall
               (fun s : L40.AST.stmt =>
                (AST.var_cap_stmt s <= varcap)%N ->
                (AST.max_loop_count_stmt s < N.of_nat max_loop_iterations)%N ->
                forall (loop_depth : N) (s50 : list AST.stmt),
                translate_stmt match this_fun_decl50 with
                               | Some _ => true
                               | None => false
                               end B protos s loop_depth = inr s50 ->
                forall (world : world_state) (loc40 : memory) (loc50 : string_map dynamic_value),
                LocalVarsAgree loc40 loc50 varcap ->
                forall loop_info : list Expr.loop_ctx,
                Datatypes.length loop_info = N.to_nat loop_depth ->
                SecondaryVarsOk loop_info loc50 ->
                let '(w, l, result) := interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50)
                                                           this_fun_decl50 call50
                                                            world loc50 s50 in
                StmtResultsAgree
                  (interpret_stmt_metered decls40 call40 builtins40 world loc40 loop_info s)
                  (w, l, result)
                  varcap
                 /\
                SecondaryVarsOk loop_info l)
               body
      end):
  let '(L50.AST.Block body50) := b50 in
  let '(w, l, result) := interpret_stmt_list max_loop_iterations builtins50 
                                             (map_lookup decls50) this_fun_decl50
                                             call50 world loc50 body50 in
  StmtResultsAgree
    (interpret_block_metered decls40 call40 builtins40 world loc40 loop_info b40)
    (w, l, result)
    varcap
   /\
  SecondaryVarsOk loop_info l.
Proof.
destruct b40 as (s40). destruct b50 as (s50).
revert world loc40 loc50 s50 Ok LocalVarsOk SV.
induction s40 as [|head40]; intros; cbn in Ok.
{ (* base *) inversion Ok. subst s50. clear Ok. cbn. cbn in LocalVarsOk. tauto. }
remember (translate_stmt _ B protos head40 loop_depth) as head'.
destruct head' as [|head50]. { discriminate. } symmetry in Heqhead'.
remember ((fix translate_stmt_list (l : list L40.AST.stmt) : string + list AST.stmt := _) s40) as tail'.
destruct tail' as [|tail50]. { discriminate. }
inversion Ok. subst s50. clear Ok. cbn.
cbn in EnoughIterations. cbn in LocalVarsOk.
assert (T: translate_block (match this_fun_decl50 with
                            | Some _ => true
                            | None => false
                            end) B protos (L40.AST.Block s40) loop_depth 
            =
           inr (L50.AST.Block tail50)).
{ cbn. now rewrite<- Heqtail'. }
rewrite interpret_stmt_list_app.
2: apply (translated_stmt_declares_nothing Heqhead').
2:{
  apply (translated_block_declares_nothing T).
}
cbn in VarcapOk.

assert (OkHead := Forall_inv OkB (N.max_lub_l _ _ _ VarcapOk) (max_lub_lt_l EnoughIterations)
                             loop_depth head50 Heqhead'
                             world loc40 loc50
                             LocalVarsOk
                             loop_info LoopDepthOk SV).
(*
assert (OkHead := Forall_inv OkB (N.max_lub_l _ _ _ VarcapOk)
                             (N.max_lub_l _ _ _ EnoughIterations) head50 Heqhead'
                             world loc40 loc50
                             (local_vars_agree_weaken_left (local_vars_agree_weaken VarcapOk LocalVarsOk))
                             ResultDeclared loop_info LoopDepthOk OffsetsOk CursorsOk).
*)
destruct (interpret_stmt_metered decls40 call40 builtins40 world loc40 loop_info head40)
  as ((w', loc40'), result40).
destruct (interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50) 
              this_fun_decl50 call50 world loc50 head50)
  as ((w50', loc50'), result50).
destruct result40 as [result40|], result50 as [result50|]; cbn in OkHead; try easy.
destruct result40, result50; try easy.
2:{ now destruct a. }
destruct OkHead as ((LocalVarsOk', W), SV').
subst w50'.
assert (X := IHs40 (N.max_lub_r _ _ _ VarcapOk)
                   (max_lub_lt_r EnoughIterations)
                   (Forall_inv_tail OkB)
                   w' loc40' loc50' tail50 T LocalVarsOk'
                   SV').
destruct (interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50) this_fun_decl50 call50 w' loc50' tail50)
  as ((world'', loc''), result'').
apply X.
Qed.

(** A separate lemma for switches because of many different ways switches can go
    (with/without default, with 0 or 1 value).
    This lemma starts with the value to switch on being already known.
    This is straightforward because switches work in exactly the same way in L40 and L50.
 *)

Local Lemma interpret_translated_switch
    {C: VyperConfig}
    {B: builtin_names_config}
    {protos: string_map proto}
    {loop_depth: N}
    {max_loop_iterations: nat}
    (call40: forall
                  (decl: L40.AST.decl)
                  (world: world_state)
                  (arg_values: list uint256),
                world_state * option (expr_result uint256))
    (call50: forall
                  (decl: L50.AST.fun_decl)
                  (world: world_state)
                  (arg_values: list dynamic_value),
                world_state * option (expr_result (list dynamic_value)))
    (CallsOk: forall (decl40: L40.AST.decl)
                     (decl50: L50.AST.fun_decl)
                     (Ok: translate_fun_decl B protos decl40 = inr decl50)
                     (world: world_state)
                     (args40: list uint256)
                     (args50: list dynamic_value)
                     (ArgsOk: args50 = map (fun x : uint256 => existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x)) args40),
                 ResultsAgree (call40 decl40 world args40)
                              (call50 decl50 world args50) 1%N)
    (decls40: string_map L40.AST.decl)
    (decls50: string_map L50.AST.fun_decl)
    (this_fun_decl40: option L40.AST.decl)
    (this_fun_decl50: option L50.AST.fun_decl)
    (FunDeclOk: match this_fun_decl40, this_fun_decl50 with
                | Some d40, Some d50 =>
                    translate_fun_decl B protos d40 = inr d50
                | None, None => True
                | _, _ => False
                end)
    (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
    (builtins40: string -> option builtin)
    (builtins50: string -> option L50.Builtins.yul_builtin)
    (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
    (BuiltinsBasics: BuiltinsSupportBasics builtins50)
    (BuiltinsSafe: forall x,
                     builtins50 ("$" ++ x)%string = None)
    (ProtosOk: ProtosAgree (map_lookup protos) builtins50)
    (world: world_state)
    (loc40: memory)
    (loc50: string_map dynamic_value)
    (loop_info: list L40.Expr.loop_ctx)
    (LoopDepthOk: length loop_info = N.to_nat loop_depth)
    (SV: SecondaryVarsOk loop_info loc50)
    (cases40: list L40.AST.case)
    (cases50: list L50.AST.case)
    (OkCases:  (fix translate_cases (l: list L40.AST.case): string + list AST.case :=
                   match l with
                   | nil => inr nil
                   | L40.AST.Case guard body :: t =>
                       match
                         translate_block match this_fun_decl50 with
                                         | Some _ => true
                                         | None => false
                                         end B protos body loop_depth
                       with
                       | inl err => inl err
                       | inr body' =>
                           match translate_cases t with
                           | inl err => inl err
                           | inr t' => inr (AST.Case U256 (yul_uint256 guard) body' :: t')
                           end
                       end
                   end) cases40 = inr cases50)
    (default40: option L40.AST.block)
    (default50: option L50.AST.block)
    (OkDefault:
      match default40, default50 with
      | None, None => True
      | Some d40, Some d50 => translate_block match this_fun_decl50 with
                                              | Some _ => true
                                              | None => false
                                              end B protos d40 loop_depth = inr d50
      | _, _ => False
      end)
    (varcap: N)
    (VarcapOk: ((N.max
                 ((fix var_cap_cases (l : list L40.AST.case) : N :=
                     match l with
                     | nil => 0
                     | L40.AST.Case _ body :: t => N.max (AST.var_cap_block body) (var_cap_cases t)
                     end) cases40) 
                 (match default40 with
                  | None => 0%N
                  | Some d => L40.AST.var_cap_block d
                  end)) <= varcap)%N)
    (LocalVarsOk: LocalVarsAgree loc40 loc50 varcap)
    (EnoughIterations:
      (let
        fix max_loop_count_cases (l : list L40.AST.case) : N :=
          match l with
          | nil => 0%N
          | L40.AST.Case _ body :: t => N.max (L40.AST.max_loop_count_block body)
                                              (max_loop_count_cases t)
          end in
        let d := match default40 with
               | Some b => L40.AST.max_loop_count_block b
               | None => 0%N
               end in
      N.max (max_loop_count_cases cases40) d <
        N.of_nat max_loop_iterations)%N)
    (CasesWork: Forall
                  (fun case: L40.AST.case =>
                   match case with
                   | L40.AST.Case _ (L40.AST.Block body) =>
                       Forall
                         (fun s : L40.AST.stmt =>
                          (AST.var_cap_stmt s <= varcap)%N ->
                          (AST.max_loop_count_stmt s < N.of_nat max_loop_iterations)%N ->
                          forall (loop_depth : N) (s50 : list AST.stmt),
                          translate_stmt match this_fun_decl50 with
                                         | Some _ => true
                                         | None => false
                                         end B protos s loop_depth = inr s50 ->
                          forall (world : world_state) (loc40 : memory) (loc50 : string_map dynamic_value),
                          LocalVarsAgree loc40 loc50 varcap ->
                          forall loop_info : list Expr.loop_ctx,
                          Datatypes.length loop_info = N.to_nat loop_depth ->
                          SecondaryVarsOk loop_info loc50 ->
                          let
                          '(w, l, result) :=
                           interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50) this_fun_decl50 call50
                             world loc50 s50 in
                           StmtResultsAgree (interpret_stmt_metered decls40 call40 builtins40 world loc40 loop_info s)
                             (w, l, result) varcap /\
                           SecondaryVarsOk loop_info l) body
                   end) cases40)
    (DefaultWorks: match default40 with
                   | Some (L40.AST.Block d) =>
                       Forall
                         (fun s : L40.AST.stmt =>
                          (AST.var_cap_stmt s <= varcap)%N ->
                          (AST.max_loop_count_stmt s < N.of_nat max_loop_iterations)%N ->
                          forall (loop_depth : N) (s50 : list AST.stmt),
                          translate_stmt match this_fun_decl50 with
                                         | Some _ => true
                                         | None => false
                                         end B protos s loop_depth = inr s50 ->
                          forall (world : world_state) (loc40 : memory) (loc50 : string_map dynamic_value),
                          LocalVarsAgree loc40 loc50 varcap  ->
                          forall loop_info : list Expr.loop_ctx,
                          Datatypes.length loop_info = N.to_nat loop_depth ->
                          SecondaryVarsOk loop_info loc50 ->
                          let
                          '(w, l, result) :=
                           interpret_stmt_list max_loop_iterations builtins50 (map_lookup decls50) this_fun_decl50 call50
                             world loc50 s50 in
                           StmtResultsAgree (interpret_stmt_metered decls40 call40 builtins40 world loc40 loop_info s)
                             (w, l, result) varcap /\
                           SecondaryVarsOk loop_info l)
                         d
                    | None => True
                    end)
    (value: uint256):
  let fix dispatch50 (l: list L50.AST.case)
       : world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
       := match l with
          | (L50.AST.Case guard_type guard body) :: tail =>
              if yul_type_eq_dec U256 guard_type
                then if (Z_of_uint256 value
                          =?
                         Z_of_uint256 (uint256_of_yul_value guard))%Z
                        then L50.Stmt.interpret_block max_loop_iterations
                                                      builtins50 (map_lookup decls50) this_fun_decl50 call50
                                                      world loc50 nop body
                        else dispatch50 tail
                else (world, loc50, Some (stmt_error (L50.DynError.string_of_dynamic_error
                                                      (L50.DynError.DE_TypeMismatch guard_type U256))))
          | nil =>
                   match default50 with
                   | Some body =>
                        L50.Stmt.interpret_block max_loop_iterations
                                                 builtins50 (map_lookup decls50) this_fun_decl50 call50
                                                 world loc50 nop body
                   | None => (world, loc50, Some StmtSuccess)
                   end
          end in
  let '(w, l, result) := dispatch50 cases50 in
  StmtResultsAgree
    (let fix dispatch40 (l: list L40.AST.case)
         : world_state * memory * option (stmt_result uint256)
         := match l with
            | cons (L40.AST.Case guard block) t =>
                if (Z_of_uint256 value =? Z_of_uint256 guard)%Z
                  then interpret_block_metered decls40 call40 builtins40
                                               world loc40 loop_info block
                  else dispatch40 t
            | nil => match default40 with
                     | Some block =>
                          interpret_block_metered decls40 call40 builtins40
                                                  world loc40 loop_info block
                     | None => (world, loc40, Some StmtSuccess)
                     end
            end
     in dispatch40 cases40)
    (w, l, result)
    varcap
     /\
    SecondaryVarsOk loop_info l.
Proof.
revert cases50 OkCases. induction cases40 as [|head]; intros.
{
  inversion OkCases. subst cases50. cbn.
  destruct default40 as [d40|], default50 as [d50|]; try easy.
  destruct d50 as (d50). rewrite interpret_stmt_list_ok.
  apply (interpret_translated_block_weak call40 call50 CallsOk decls40 decls50
                                         this_fun_decl40 this_fun_decl50 FunDeclOk
                                         DeclsOk builtins40 builtins50 BuiltinsOk
                                         BuiltinsBasics BuiltinsSafe ProtosOk
                                         world loc40 loc50
                                         loop_info LoopDepthOk SV
                                         d40 (L50.AST.Block d50) OkDefault varcap (N.max_lub_r _ _ _ VarcapOk)
                                         LocalVarsOk (max_lub_lt_r EnoughIterations) DefaultWorks).
}
destruct head as (guard, body).
remember (translate_block match this_fun_decl50 with
                          | Some _ => true
                          | None => false
                          end B protos body loop_depth) as head'.
destruct head' as [|head50]. { discriminate. }
remember ((fix translate_cases (l : list L40.AST.case) : string + list AST.case := _) cases40) as tail'.
destruct tail' as [|tail50]. { discriminate. }
inversion OkCases; subst cases50; clear OkCases.
cbn.
destruct (Z_of_uint256 value =? Z_of_uint256 guard)%Z.
{ (* taking the case *)
  destruct head50 as (head50). rewrite interpret_stmt_list_ok.
  apply (interpret_translated_block_weak call40 call50 CallsOk decls40 decls50
                                         this_fun_decl40 this_fun_decl50 FunDeclOk
                                         DeclsOk builtins40 builtins50 BuiltinsOk
                                         BuiltinsBasics BuiltinsSafe ProtosOk
                                         world loc40 loc50
                                         loop_info LoopDepthOk SV
                                         body (L50.AST.Block head50) (eq_sym Heqhead')
                                         varcap (N.max_lub_l _ _ _  (N.max_lub_l _ _ _ VarcapOk))
                                         LocalVarsOk (max_lub_lt_l (max_lub_lt_l EnoughIterations))
                                         (Forall_inv CasesWork)).
}
(* not taking the case *)
cbn in EnoughIterations.
apply (IHcases40 (N.max_lub _ _ _ (N.max_lub_r _ _ _  (N.max_lub_l _ _ _ VarcapOk))
                                  (N.max_lub_r _ _ _ VarcapOk))
                 (N.max_lub_lt _ _ _ (max_lub_lt_r (max_lub_lt_l EnoughIterations))
                                     (max_lub_lt_r EnoughIterations))
                 (Forall_inv_tail CasesWork)
                 tail50 eq_refl).
Qed.

Lemma interpret_translated_stmt {C: VyperConfig}
                                {B: builtin_names_config}
                                {protos: string_map proto}
                                {s40: L40.AST.stmt}
                                {s50: list L50.AST.stmt}
                                {loop_depth: N}
                                {max_loop_iterations: nat}
                                (call40: forall
                                              (decl: L40.AST.decl)
                                              (world: world_state)
                                              (arg_values: list uint256),
                                            world_state * option (expr_result uint256))
                                (call50: forall
                                              (decl: L50.AST.fun_decl)
                                              (world: world_state)
                                              (arg_values: list dynamic_value),
                                            world_state * option (expr_result (list dynamic_value)))
                                (CallsOk: forall (decl40: L40.AST.decl)
                                                 (decl50: L50.AST.fun_decl)
                                                 (Ok: translate_fun_decl B protos decl40 = inr decl50)
                                                 (world: world_state)
                                                 (args40: list uint256)
                                                 (args50: list dynamic_value)
                                                 (ArgsOk: args50 = map (fun x : uint256 => existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x)) args40),
                                             ResultsAgree (call40 decl40 world args40)
                                                          (call50 decl50 world args50) 1%N)
                                (decls40: string_map L40.AST.decl)
                                (decls50: string_map L50.AST.fun_decl)
                                (this_fun_decl40: option L40.AST.decl)
                                (this_fun_decl50: option L50.AST.fun_decl)
                                (FunDeclOk: match this_fun_decl40, this_fun_decl50 with
                                            | Some d40, Some d50 =>
                                                translate_fun_decl B protos d40 = inr d50
                                            | None, None => True
                                            | _, _ => False
                                            end)
                                (Ok: translate_stmt (match this_fun_decl50 with
                                                     | Some _ => true
                                                     | None => false
                                                     end) B protos s40 loop_depth = inr s50)
                                (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
                                (builtins40: string -> option builtin)
                                (builtins50: string -> option L50.Builtins.yul_builtin)
                                (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
                                (BuiltinsBasics: BuiltinsSupportBasics builtins50)
                                (BuiltinsSafe: forall x,
                                                 builtins50 ("$" ++ x)%string = None)
                                (BuiltinsHaveArith: BuiltinsSupportUInt256 B builtins40)
                                (ProtosOk: ProtosAgree (map_lookup protos) builtins50)
                                (KnownProtosOk: check_known_protos B (map_lookup protos) = true)
                                (world: world_state)
                                (loc40: memory)
                                (loc50: string_map dynamic_value)
                                (varcap: N)
                                (VarcapOk: (L40.AST.var_cap_stmt s40 <= varcap)%N)
                                (EnoughIterations:
                                  (L40.AST.max_loop_count_stmt s40 < N.of_nat max_loop_iterations)%N)
                                (LocalVarsOk: LocalVarsAgree loc40 loc50 varcap)
                                (loop_info: list L40.Expr.loop_ctx)
                                (LoopDepthOk: length loop_info = N.to_nat loop_depth)
                                (SV: SecondaryVarsOk loop_info loc50):
  let '(w, l, result) := L50.Stmt.interpret_stmt_list max_loop_iterations builtins50
                                                      (map_lookup decls50)
                                                      this_fun_decl50 call50
                                                      world loc50 s50
  in
  StmtResultsAgree
    (interpret_stmt_metered decls40 call40 builtins40 world loc40 loop_info s40)
    (w, l, result)
    varcap
   /\
  SecondaryVarsOk loop_info l.
Proof.
revert loop_depth s50 Ok world loc40 loc50 LocalVarsOk loop_info LoopDepthOk SV.
induction s40 using L40.AST.stmt_ind'; intros.
{ (* small stmt *)
  apply (interpret_translated_small_stmt call40 call50 CallsOk decls40 decls50
                                         this_fun_decl40 this_fun_decl50 FunDeclOk Ok DeclsOk
                                         builtins40 builtins50 BuiltinsOk BuiltinsBasics BuiltinsSafe
                                         ProtosOk world loc40 loc50 varcap VarcapOk LocalVarsOk
                                         loop_info
                                         LoopDepthOk SV).
}
{ (* switch without default *)
  cbn in Ok.
  remember (translate_expr protos e loop_depth) as e'. symmetry in Heqe'.
  destruct e' as [|(e', n)]. { now destruct (_ cases). }
  cbn in LocalVarsOk, VarcapOk.
  assert (ValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                               builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                               ProtosOk world loc40 loc50
                                               (local_vars_agree_weaken_left
                                                 (local_vars_agree_weaken VarcapOk LocalVarsOk))
                                               loop_info LoopDepthOk 
                                               (sv_offsets_agree SV) (sv_cursors_agree SV)).
  unfold ResultsAgree in ValueOk.
  remember ((fix translate_cases (l : list L40.AST.case) : string + list AST.case := _) cases) as cases'.
  destruct cases' as [|cases50]. { discriminate. }
  destruct n as [|p].
  { (* 0 values *)
    inversion Ok. subst s50. clear Ok.

    (* dance around cbn's horrors *)
    cbn delta iota.
    unfold L50.Stmt.interpret_stmt_list.
    cbn delta iota.
    remember (L50.DynError.string_of_dynamic_error) as stringify.
    remember yul_type_eq_dec as yt_eq.
    cbn.

    destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
    destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e') as (w50, r50).
    destruct ValueOk as (W, ValueOk). subst w40.
    destruct r40 as [r40|], r50 as [r50|]; try easy.
    destruct r40 as [val40|ab40], r50 as [val50|ab50]; try easy.
    destruct val50. 2:{ cbn in ValueOk. now destruct val50. }
    assert (X := interpret_translated_switch call40 call50 CallsOk decls40 decls50
                                             this_fun_decl40 this_fun_decl50 FunDeclOk
                                             DeclsOk builtins40 builtins50 BuiltinsOk
                                             BuiltinsBasics BuiltinsSafe ProtosOk
                                             w50 loc40 loc50
                                             loop_info LoopDepthOk SV
                                             cases cases50 (eq_sym Heqcases')
                                             None None I
                                             varcap (N.max_lub_r _ _ _ VarcapOk)
                                             LocalVarsOk EnoughIterations H I val40).
    rewrite<- Heqstringify in X.
    rewrite<- Heqyt_eq in X.
    cbn in X.
    cbn in ValueOk. destruct ValueOk as (V, _). subst val40.
    destruct ((fix dispatch50 (l : list L50.AST.case) := _) cases50) as ((ww50, l50), result50).
    destruct (((fix dispatch40 (l : list L40.AST.case) : world_state * memory * option (stmt_result uint256) :=
          match l with
          | nil => (w50, loc40, Some StmtSuccess)
          | L40.AST.Case guard block :: t =>
              if (Z_of_uint256 zero256 =? Z_of_uint256 guard)%Z
              then interpret_block_metered decls40 call40 builtins40 w50 loc40 loop_info block
              else dispatch40 t
          end) cases)) as ((w40, l40), result40).
    destruct result50 as [result50|]. 2:tauto. { now destruct result50. }
    cbn in ValueOk. subst ab40. now destruct ab50.
  }
  (* 1 value *)
  destruct p; try discriminate.
  inversion Ok. subst s50. clear Ok.

  (* dance around cbn's horrors *)
  cbn delta iota.
  unfold L50.Stmt.interpret_stmt_list.
  cbn delta iota.
  remember (L50.DynError.string_of_dynamic_error) as stringify.
  remember yul_type_eq_dec as yt_eq.
  cbn.

  destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
  destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e') as (w50, r50).
  destruct ValueOk as (W, ValueOk). subst w40.
  destruct r40 as [r40|], r50 as [r50|]; try easy.
  destruct r40 as [val40|ab40], r50 as [val50|ab50]; try easy.
  2:{ cbn in ValueOk. subst ab40. now destruct ab50. }

  unfold ExprResultsAgree in ValueOk.
  destruct val50 as [|val50]. { cbn in ValueOk. assert (Bad: 1%N = 0%N) by tauto. discriminate. }
  destruct val0 (* how to rename it? *). 2:contradiction.
  destruct ValueOk as (V, _). subst val50.
  assert (X := interpret_translated_switch call40 call50 CallsOk decls40 decls50
                                           this_fun_decl40 this_fun_decl50 FunDeclOk
                                           DeclsOk builtins40 builtins50 BuiltinsOk
                                           BuiltinsBasics BuiltinsSafe ProtosOk
                                           w50 loc40 loc50
                                           loop_info LoopDepthOk SV
                                           cases cases50 (eq_sym Heqcases')
                                           None None I
                                           varcap (N.max_lub_r _ _ _ VarcapOk)
                                           LocalVarsOk EnoughIterations H I val40).
  rewrite<- Heqstringify in X.
  rewrite<- Heqyt_eq in X.
  cbn in X.
  destruct ((fix dispatch50 (l : list L50.AST.case) := _) cases50) as ((ww50, l50), result50).
  destruct (((fix dispatch40 (l : list L40.AST.case) : world_state * memory * option (stmt_result uint256) :=
        match l with
        | nil => (w50, loc40, Some StmtSuccess)
        | L40.AST.Case guard block :: t =>
            if (Z_of_uint256 zero256 =? Z_of_uint256 guard)%Z
            then interpret_block_metered decls40 call40 builtins40 w50 loc40 loop_info block
            else dispatch40 t
        end) cases)) as ((w40, l40), result40).
  destruct result50 as [result50|]. 2:tauto. now destruct result50.
}
{ (* switch with default (of course massive dup) *)
  cbn in Ok.
  remember (translate_expr protos e loop_depth) as e'. symmetry in Heqe'.
  destruct e' as [|(e', n)].
  {
    destruct (_ cases) as [|cases']. { discriminate. }
    now destruct (_ default).
  }
  cbn in LocalVarsOk, VarcapOk.
  assert (ValueOk := interpret_translated_expr Heqe' call40 call50 CallsOk decls40 decls50 DeclsOk
                                               builtins40 builtins50 BuiltinsOk BuiltinsSafe
                                               ProtosOk world loc40 loc50
                                               (local_vars_agree_weaken_left
                                                 (local_vars_agree_weaken VarcapOk LocalVarsOk))
                                               loop_info LoopDepthOk
                                               (sv_offsets_agree SV) (sv_cursors_agree SV)).
  unfold ResultsAgree in ValueOk.
  remember ((fix translate_cases (l : list L40.AST.case) : string + list AST.case := _) cases)
    as cases'.
  destruct cases' as [|cases50]. { discriminate. }
  remember ((fix translate_stmt_list (l : list L40.AST.stmt) : string + list AST.stmt := _) default)
    as default'.
  destruct default' as [|default50]. { discriminate. }
  destruct n as [|p].
  { (* 0 values *)
    inversion Ok. subst s50. clear Ok.

    (* dance around cbn's horrors *)
    cbn delta iota.
    unfold L50.Stmt.interpret_stmt_list.
    cbn delta iota.
    remember (L50.DynError.string_of_dynamic_error) as stringify.
    remember yul_type_eq_dec as yt_eq.
    cbn.

    destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
    destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e') as (w50, r50).
    destruct ValueOk as (W, ValueOk). subst w40.
    destruct r40 as [r40|], r50 as [r50|]; try easy.
    destruct r40 as [val40|ab40], r50 as [val50|ab50]; try easy.
    2:{ cbn in ValueOk. subst ab40. now destruct ab50. }
    destruct val50. 2:{ cbn in ValueOk. now destruct val50. }
    assert (DefaultsOk: translate_block
                          match this_fun_decl50 with
                          | Some _ => true
                          | None => false
                          end
                          B protos (L40.AST.Block default) loop_depth = inr (AST.Block default50)).
    { cbn. now rewrite<- Heqdefault'. }
    assert (X := interpret_translated_switch call40 call50 CallsOk decls40 decls50
                                             this_fun_decl40 this_fun_decl50 FunDeclOk
                                             DeclsOk builtins40 builtins50 BuiltinsOk
                                             BuiltinsBasics BuiltinsSafe ProtosOk
                                             w50 loc40 loc50
                                             loop_info LoopDepthOk SV
                                             cases cases50 (eq_sym Heqcases')
                                             (Some (L40.AST.Block default)) (Some (L50.AST.Block default50))
                                             DefaultsOk
                                             varcap (N.max_lub_r _ _ _ VarcapOk)
                                             LocalVarsOk EnoughIterations H H0 val40).
    rewrite<- Heqstringify in X.
    rewrite<- Heqyt_eq in X.
    cbn in X.
    cbn in ValueOk. destruct ValueOk as (V, _). subst val40.
    destruct ((fix dispatch50 (l : list L50.AST.case) := _) cases50) as ((ww50, l50), result50).
    destruct (((fix dispatch40 (l : list L40.AST.case) : world_state * memory * option (stmt_result uint256) :=
          match l with
          | nil => (w50, loc40, Some StmtSuccess)
          | L40.AST.Case guard block :: t =>
              if (Z_of_uint256 zero256 =? Z_of_uint256 guard)%Z
              then interpret_block_metered decls40 call40 builtins40 w50 loc40 loop_info block
              else dispatch40 t
          end) cases)) as ((w40, l40), result40).
    destruct result50 as [result50|]. 2:tauto. now destruct result50.
  }
  (* 1 value *)
  destruct p; try discriminate.
  inversion Ok. subst s50. clear Ok.

  (* dance around cbn's horrors *)
  cbn delta iota.
  unfold L50.Stmt.interpret_stmt_list.
  cbn delta iota.
  remember (L50.DynError.string_of_dynamic_error) as stringify.
  remember yul_type_eq_dec as yt_eq.
  cbn.

  destruct (interpret_expr_metered decls40 call40 builtins40 world loc40 loop_info e) as (w40, r40).
  destruct (interpret_expr builtins50 (map_lookup decls50) call50 world loc50 e') as (w50, r50).
  destruct ValueOk as (W, ValueOk). subst w40.
  destruct r40 as [r40|], r50 as [r50|]; try easy.
  destruct r40 as [val40|ab40], r50 as [val50|ab50]; try easy.
  2:{ cbn in ValueOk. subst ab40. now destruct ab50. }

  unfold ExprResultsAgree in ValueOk.
  destruct val50 as [|val50]. { cbn in ValueOk. assert (Bad: 1%N = 0%N) by tauto. discriminate. }
  destruct val0 (* how to rename it? *). 2:contradiction.
  destruct ValueOk as (V, _). subst val50.
  assert (DefaultsOk: translate_block
                        match this_fun_decl50 with
                        | Some _ => true
                        | None => false
                        end
                        B protos (L40.AST.Block default) loop_depth = inr (AST.Block default50)).
  { cbn. now rewrite<- Heqdefault'. }
  assert (X := interpret_translated_switch call40 call50 CallsOk decls40 decls50
                                           this_fun_decl40 this_fun_decl50 FunDeclOk
                                           DeclsOk builtins40 builtins50 BuiltinsOk
                                           BuiltinsBasics BuiltinsSafe ProtosOk
                                           w50 loc40 loc50
                                           loop_info LoopDepthOk SV
                                           cases cases50 (eq_sym Heqcases')
                                           (Some (L40.AST.Block default)) (Some (L50.AST.Block default50))
                                           DefaultsOk
                                           varcap (N.max_lub_r _ _ _ VarcapOk)
                                           LocalVarsOk EnoughIterations H H0 val40).
  rewrite<- Heqstringify in X.
  rewrite<- Heqyt_eq in X.
  cbn in X.
  destruct ((fix dispatch50 (l : list L50.AST.case) := _) cases50) as ((ww50, l50), result50).
  destruct (((fix dispatch40 (l : list L40.AST.case) : world_state * memory * option (stmt_result uint256) :=
        match l with
        | nil => (w50, loc40, Some StmtSuccess)
        | L40.AST.Case guard block :: t =>
            if (Z_of_uint256 zero256 =? Z_of_uint256 guard)%Z
            then interpret_block_metered decls40 call40 builtins40 w50 loc40 loop_info block
            else dispatch40 t
        end) cases)) as ((w40, l40), result40).
  destruct result50 as [result50|]. 2:tauto. now destruct result50.
}
(********************************** loop **********************************)
cbn delta iota in Ok.
remember (make_var_name "var") as var_name. (* prevent cbn horrors *)
remember (make_var_name "offset") as offset_name.
remember (make_var_name "cursor") as cursor_name.
cbn in Ok.
remember ((fix translate_stmt_list (l : list L40.AST.stmt) : string + list AST.stmt := _) body) as body'.
destruct body' as [|body50]. { discriminate. }
inversion Ok. subst s50. clear Ok.
cbn in EnoughIterations.

(* remembering everything away from cbn *)
remember (AST.VarDecl ((U256, cursor_name loop_depth) :: nil) None :: nil) as cursor_decl.
remember ((AST.FunCall (builtin_name_uint256_lt B)
           (AST.LocVar (cursor_name loop_depth) :: AST.Const U256 (yul_uint256 count) :: nil)))
  as cond_expr.
remember (AST.Block
           (AST.Assign (cursor_name loop_depth :: nil)
              (AST.FunCall (builtin_name_uint256_add B)
                 (AST.LocVar (cursor_name loop_depth) :: AST.Const U256 (yul_uint256 one256) :: nil))
            :: nil))
  as increment.
remember (AST.Block body50) as bodyblock50.
remember (L40.AST.Block body) as bodyblock40.
cbn. (* it still opens yul_type_eq_dec :( *)
remember (fix iterate
            (count0 : nat) (world0 : world_state) (loc : string_map dynamic_value) {struct count0} :
              world_state * string_map dynamic_value * option (stmt_result (list dynamic_value)) := _)
  as iterate50.
remember (fix do_loop (world0 : world_state) (loc : memory) (countdown : nat) {struct countdown} :
            world_state * memory * option (stmt_result uint256) := _) as iterate40.

(* load the variable with the offset value *)
cbn in VarcapOk.
assert (InitVarUnderCap: (var < varcap)%N) by lia.
assert (InitVarOk := LocalVarsOk var InitVarUnderCap).
unfold map_lookup in InitVarOk. rewrite<- Heqvar_name in InitVarOk.
rewrite InitVarOk. cbn.

(* ensure that our offset variable isn't declared yet *)
assert (OffsetUndeclared := sv_offsets_undeclared SV (N.to_nat loop_depth)
                                                     (Nat.eq_le_incl _ _ LoopDepthOk)).
rewrite<-Heqoffset_name in OffsetUndeclared. rewrite N2Nat.id in OffsetUndeclared.
rewrite OffsetUndeclared.

(* declare cursor *)
subst cursor_decl. cbn.
assert (CursorUndeclared := sv_cursors_undeclared SV (N.to_nat loop_depth)
                                                     (Nat.eq_le_incl _ _ LoopDepthOk)).
unfold map_lookup in *. unfold map_insert in *.
rewrite<-Heqcursor_name in CursorUndeclared. rewrite N2Nat.id in CursorUndeclared.
rewrite Map.insert_ok.
destruct string_dec. { subst. discriminate. }
rewrite CursorUndeclared.

(* we obtain the varmap with new offset and cursor variables *)
remember (@Map.insert string string_dec (@dynamic_value C) (@string_map C (@dynamic_value C))
             (@string_map_impl C (@dynamic_value C))
             (@Map.insert string string_dec (@dynamic_value C) (@string_map C (@dynamic_value C))
                (@string_map_impl C (@dynamic_value C)) loc50 (offset_name loop_depth)
                (@existT yul_type (fun t : yul_type => @yul_value C t) U256
                   (@yul_uint256 C
                      (@OpenArray.get (@uint256 C) (@uint256_of_Z C 0) (@memory C) 
                         (@memory_impl C) loc40 var)))) (cursor_name loop_depth)
             (@existT yul_type (fun t : yul_type => @yul_value C t) U256 (@int_zero_value C I256 false)))
  as current_loc50.

assert (CurrentLocalVarsOk: LocalVarsAgree loc40 current_loc50 varcap).
{
  intros k L.
  subst current_loc50.
  unfold map_lookup.
  subst offset_name cursor_name.
  repeat rewrite Map.insert_ok.
  destruct string_dec. { discriminate. }
  destruct string_dec. { discriminate. }
  apply (LocalVarsOk k L).
}

assert (CondExprWorks: forall w l cursor,
         map_lookup l (cursor_name loop_depth) = Some (existT _ U256 (yul_uint256 cursor))
          ->
         interpret_expr builtins50 (map_lookup decls50) call50 w l cond_expr
          =
         (w, Some (ExprSuccess
               ((if (Z_of_uint256 cursor <? Z_of_uint256 count)%Z
                    then existT _ U256 (yul_uint256 one256)
                    else existT _ U256 (yul_uint256 zero256))
                  :: nil)))).
{
  assert (LtProtoChecked: check_proto (map_lookup protos (builtin_name_uint256_lt B)) 2 1 = true).
  {
    unfold check_known_protos in KnownProtosOk.
    unfold map_lookup.
    destruct (check_proto (Map.lookup protos (builtin_name_uint256_lt B)) 2 1). { trivial. }
    repeat rewrite Bool.andb_false_r in KnownProtosOk.
    repeat rewrite Bool.andb_false_l in KnownProtosOk.
    discriminate.
  }
  unfold BuiltinsSupportUInt256 in BuiltinsHaveArith.
  assert (LtSupported: BuiltinsSupportBinop builtins40 (builtin_name_uint256_lt B) UInt256.uint256_lt)
    by tauto.
  assert (LtSpec := binop_to_yul BuiltinsOk ProtosOk LtProtoChecked LtSupported).
  intros w l cursor Q.
  subst cond_expr. cbn.
  assert (DeclsMangled := translated_decls_start_with_dollar decls40 decls50 DeclsOk (builtin_name_uint256_lt B)).
  assert (LtNotMangled := proj1 (mangled_safety_equiv builtins50) BuiltinsSafe 
                                (builtin_name_uint256_lt B)).
  unfold map_lookup in *.
  destruct (builtins50 (builtin_name_uint256_lt B)) as [b|]. 2:contradiction.
  destruct (Map.lookup decls50 (builtin_name_uint256_lt B)).
  {
    assert (F: forall {T} (x: T), Some x <> None) by discriminate.
    assert (M := DeclsMangled (F _ _)).
    assert (N := LtNotMangled (F _ _)).
    rewrite M in N. discriminate.
  }
  unfold dynamic_value. rewrite Q.
  cbn. rewrite LtSpec. unfold UInt256.uint256_lt.
  now destruct (Z_of_uint256 cursor <? Z_of_uint256 count)%Z.
}
clear Heqcond_expr.

assert (IncrementWorks: forall w l cursor,
         map_lookup l (cursor_name loop_depth) = Some (existT _ U256 (yul_uint256 cursor))
          ->
         interpret_block max_loop_iterations builtins50 (map_lookup decls50) this_fun_decl50 call50 w l nop increment
          =
         (w,
          map_insert l (cursor_name loop_depth)
             (existT _ U256 (yul_uint256 (uint256_of_Z (Z_of_uint256 cursor + 1%Z)))),
          Some StmtSuccess)).
{
  assert (AddProtoChecked: check_proto (map_lookup protos (builtin_name_uint256_add B)) 2 1 = true).
  {
    unfold check_known_protos in KnownProtosOk.
    unfold map_lookup.
    destruct (check_proto (Map.lookup protos (builtin_name_uint256_add B)) 2 1). { trivial. }
    repeat rewrite Bool.andb_false_r in KnownProtosOk.
    repeat rewrite Bool.andb_false_l in KnownProtosOk.
    discriminate.
  }
  unfold BuiltinsSupportUInt256 in BuiltinsHaveArith.
  assert (AddSupported: BuiltinsSupportBinop builtins40 (builtin_name_uint256_add B) CheckedArith.uint256_add)
    by tauto.  (* XXX: CheckedArith.uint256_add is actually unchecked modulo - needs to be renamed! *)
  assert (AddSpec := binop_to_yul BuiltinsOk ProtosOk AddProtoChecked AddSupported).
  intros w l cursor Q.
  subst increment. cbn.
  assert (DeclsMangled := translated_decls_start_with_dollar decls40 decls50 DeclsOk (builtin_name_uint256_add B)).
  assert (AddNotMangled := proj1 (mangled_safety_equiv builtins50) BuiltinsSafe 
                                 (builtin_name_uint256_add B)).
  unfold map_lookup in *.
  destruct (builtins50 (builtin_name_uint256_add B)) as [b|]. 2:contradiction.
  destruct (Map.lookup decls50 (builtin_name_uint256_add B)).
  {
    assert (F: forall {T} (x: T), Some x <> None) by discriminate.
    assert (M := DeclsMangled (F _ _)).
    assert (N := AddNotMangled (F _ _)).
    rewrite M in N. discriminate.
  }
  unfold dynamic_value. rewrite Q.
  cbn. rewrite AddSpec. unfold CheckedArith.uint256_add. cbn.
  unfold nop. repeat f_equal.
  unfold one256. now rewrite uint256_ok.
}
clear Heqincrement.

assert (LocalVarsUndeclare: forall l40 l50 vc,
  LocalVarsAgree l40 l50 vc
   ->
  LocalVarsAgree l40 (map_remove (map_remove l50
                                             (cursor_name loop_depth))
                                 (offset_name loop_depth))
                 vc).
{
  intros l40 l50 vc LVA k L.
  rewrite<- (LVA k L).
  unfold map_remove. unfold map_lookup.
  repeat rewrite Map.remove_ok.
  repeat rewrite Map.insert_ok.
  subst offset_name cursor_name.
  destruct string_dec. { discriminate. }
  destruct string_dec. { discriminate. }
  trivial.
}

assert (StmtResultsUndeclare: forall w40 w50 l40 l50 r40 r50 vc,
  StmtResultsAgree (w40, l40, r40) (w50, l50, r50) vc
   ->
  StmtResultsAgree (w40, l40, r40)
                   (w50,
                    map_remove (map_remove l50
                                           (cursor_name loop_depth))
                               (offset_name loop_depth),
                    r50) vc).
{
  unfold StmtResultsAgree.
  intros w40 w50 l40 l50 r40 r50 vc SRA.
  destruct SRA as (LVA, SRA). split. { apply (LocalVarsUndeclare l40 l50 vc LVA). }
  assumption.
}

assert (UndeclareSV: forall ctx l,
  SecondaryVarsOk (ctx :: loop_info) l
   ->
  SecondaryVarsOk loop_info (map_remove (map_remove l
                                                    (cursor_name loop_depth))
                                        (offset_name loop_depth))).
{
  intros ctx l SV'.
  unfold map_remove.
  split; unfold LoopOffsetsAgree; unfold LoopCursorsAgree; unfold map_lookup;
         repeat rewrite Map.remove_ok;
         repeat rewrite Map.insert_ok;
         try rewrite Heqoffset_name; try rewrite Heqcursor_name.
  { apply (sv_result_declared SV'). }
  {
    intros k L.
    assert (LO := sv_offsets_agree SV' k (Nat.lt_lt_succ_r _ _ L)). unfold LoopOffsetsAgree in LO.
    unfold map_lookup in LO.
    repeat rewrite Map.remove_ok.
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    destruct string_dec. { discriminate. }
    rewrite<- Heqoffset_name in LO. cbn in LO.
    replace (Datatypes.length loop_info - 0 - k) with (S (Datatypes.length loop_info - 1 - k))
      in LO by lia.
    cbn in LO. subst offset_name.
    apply LO; assumption.
  }
  {
    intros k L.
    assert (LC := sv_cursors_agree SV' k (Nat.lt_lt_succ_r _ _ L)). unfold LoopOffsetsAgree in LC.
    unfold map_lookup in LC.
    repeat rewrite Map.remove_ok.
    destruct string_dec. { discriminate. }
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    rewrite<- Heqcursor_name in LC. cbn in LC.
    replace (Datatypes.length loop_info - 0 - k) with (S (Datatypes.length loop_info - 1 - k))
      in LC by lia.
    cbn in LC. subst cursor_name.
    apply LC; assumption.
  }
  {
    intros k L. repeat rewrite Map.remove_ok.
    destruct string_dec. { trivial. }
    destruct string_dec. { discriminate. }
    apply le_lt_or_eq in L.
    destruct L as [L|E]. { apply (sv_offsets_undeclared SV' k L). }
    assert (K: loop_depth = N.of_nat k) by lia.
    subst loop_depth. contradiction.
  }
  {
    intros k L. repeat rewrite Map.remove_ok.
    destruct string_dec. { discriminate. }
    destruct string_dec. { trivial. }
    apply le_lt_or_eq in L.
    destruct L as [L|E]. { apply (sv_cursors_undeclared SV' k L). }
    assert (K: loop_depth = N.of_nat k) by lia.
    subst loop_depth. contradiction.
  }
}

(* check the special zero loop case *)
remember (Z.to_nat (Z_of_uint256 count)) as c.
destruct c.
{ (* count = 0 *)
  subst iterate40.
  assert (W: iterate50 max_loop_iterations world current_loc50 
              =
             (world, current_loc50, Some StmtSuccess)).
  {
    subst iterate50.
    destruct max_loop_iterations. { now apply N.nlt_0_r in EnoughIterations. }
    cbn. unfold map_lookup in *. rewrite CondExprWorks with (cursor := zero256).
    {
      replace (Z_of_uint256 zero256 <? Z_of_uint256 count)%Z with false.
      { cbn. unfold zero256. rewrite uint256_ok. easy. }
      unfold zero256. rewrite uint256_ok.
      rewrite<- (Z2Nat.id (Z_of_uint256 count)). { now rewrite<- Heqc. }
      apply (proj1 (uint256_range count)).
    }
    subst current_loc50. rewrite Map.insert_ok.
    destruct string_dec as [|NE]. 2:{ contradiction. }
    unfold int_zero_value. unfold yul_uint256.
    repeat f_equal.
    apply Eqdep_dec.eq_proofs_unicity.
    decide equality.
  }
  rewrite W.

  split.
  {
    cbn. split. 2:trivial.
    apply LocalVarsUndeclare. assumption.
  }
  subst current_loc50.
  split; unfold LoopOffsetsAgree; unfold LoopCursorsAgree; unfold map_lookup; unfold map_remove; intros;
         repeat rewrite Map.remove_ok;
         repeat rewrite Map.insert_ok;
         subst offset_name cursor_name.
  {
    destruct string_dec. { discriminate. }
    destruct string_dec. { discriminate. }
    apply (sv_result_declared SV).
  }
  {
    assert (LO := sv_offsets_agree SV). unfold LoopOffsetsAgree in LO. 
    unfold map_lookup in LO.
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    destruct string_dec. { discriminate. }
    apply LO; assumption.
  }
  {
    assert (LC := sv_cursors_agree SV). unfold LoopCursorsAgree in LC. 
    unfold map_lookup in LC.
    destruct string_dec. { discriminate. }
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    apply LC; assumption.
  }
  {
    destruct string_dec. { trivial. }
    destruct string_dec. { discriminate. }
    apply (sv_offsets_undeclared SV); assumption.
  }
  {
    destruct string_dec. { discriminate. }
    destruct string_dec. { trivial. }
    apply (sv_cursors_undeclared SV); assumption.
  }
}
(* now c = count - 1 and we can form a context *)
pose (current_ctx := {| L40.Expr.loop_offset := let _ := memory_impl in OpenArray.get loc40 var
                      ; L40.Expr.loop_count := count
                      ; L40.Expr.loop_countdown := c
                     |}).
cbn in current_ctx.
assert (PreloopSV: SecondaryVarsOk (current_ctx :: loop_info) current_loc50).
{
  subst current_loc50.
  split; unfold map_lookup.
  {
    repeat rewrite Map.insert_ok. subst offset_name cursor_name.
    destruct string_dec. { discriminate. }
    destruct string_dec. { discriminate. }
    apply (sv_result_declared SV).
  }
  {
    intros k L. rewrite<- Heqoffset_name. cbn.
    rewrite Nat.sub_0_r.
    remember (Datatypes.length loop_info - k) as i.
    cbn in L. destruct i; cbn.
    {
      assert (K: k = List.length loop_info) by lia.
      unfold map_lookup. repeat rewrite Map.insert_ok.
      subst offset_name cursor_name.
      destruct string_dec. { discriminate. }
      destruct string_dec. { trivial. }
      subst k. rewrite LoopDepthOk in *.
      rewrite N2Nat.id in *. contradiction.
    }
    assert (L': k < Datatypes.length loop_info) by lia.
    assert (A := sv_offsets_agree SV k L').
    replace i with (Datatypes.length loop_info - 1 - k) by lia.
    subst offset_name.
    unfold map_lookup in *. repeat rewrite Map.insert_ok.
    destruct string_dec. { subst. discriminate. }
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    apply A.
  }
  {
    intros k L. rewrite<- Heqcursor_name. cbn.
    rewrite Nat.sub_0_r.
    remember (Datatypes.length loop_info - k) as i.
    cbn in L. destruct i; cbn.
    {
      assert (K: k = List.length loop_info) by lia.
      unfold map_lookup. repeat rewrite Map.insert_ok.
      subst offset_name cursor_name.
      destruct string_dec.
      {
        subst current_ctx. unfold get_cursor. cbn.
        replace (Z_of_uint256 count - 1 - Z.of_nat c)%Z with 0%Z by lia.
        repeat f_equal. unfold int_zero_value. unfold yul_uint256. unfold zero256.
        f_equal. apply eq_proofs_unicity. decide equality.
      }
      destruct string_dec. { discriminate. }
      subst k. rewrite LoopDepthOk in *.
      rewrite N2Nat.id in *. contradiction.
    }
    assert (L': k < Datatypes.length loop_info) by lia.
    assert (A := sv_cursors_agree SV k L').
    replace i with (Datatypes.length loop_info - 1 - k) by lia.
    subst cursor_name.
    unfold map_lookup in *. repeat rewrite Map.insert_ok.
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    destruct string_dec. { subst. discriminate. }
    apply A.
  }
  {
    intros k Bound. cbn in Bound.
    repeat rewrite Map.insert_ok.
    subst offset_name cursor_name.
    destruct string_dec. { discriminate. }
    destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
    apply (sv_offsets_undeclared SV k). lia.
  }
  intros k Bound. cbn in Bound.
  repeat rewrite Map.insert_ok.
  subst offset_name cursor_name.
  destruct string_dec as [E|]. { apply make_var_name_inj in E. lia. }
  destruct string_dec. { discriminate. }
  apply (sv_cursors_undeclared SV k). lia.
}

assert (G: forall ctx l,
             LoopCursorsAgree (ctx :: loop_info) l
              ->
             map_lookup l (cursor_name loop_depth)
              =
             Some (existT _ U256 (yul_uint256 (get_cursor ctx)))).
{
  intros ctx l LCA.
  assert (L := LCA (List.length loop_info) (Nat.lt_succ_diag_r _)).
  rewrite<- Heqcursor_name in L.
  cbn in L.
  rewrite Nat.sub_0_r in L.
  rewrite Nat.sub_diag in L.
  cbn in L. rewrite LoopDepthOk in L.
  rewrite N2Nat.id in L.
  exact L.
}

assert (IncrementSV: forall offset l m,
                       let ctx := {| L40.Expr.loop_offset := offset
                                   ; L40.Expr.loop_count := count
                                   ; L40.Expr.loop_countdown := S m
                                  |} in
                       (Z.of_nat (S m) < Z_of_uint256 count)%Z
                        ->
                       SecondaryVarsOk (ctx :: loop_info) l
                        ->
                       SecondaryVarsOk
                         ({| L40.Expr.loop_offset := offset
                           ; L40.Expr.loop_count := count
                           ; L40.Expr.loop_countdown := m
                          |} :: loop_info)
                          (map_insert l (cursor_name loop_depth)
                             (existT _ U256 (yul_uint256
                                              (uint256_of_Z (Z_of_uint256 (get_cursor ctx) + 1%Z)))))).
{
  cbn.
  intros offset l m Bound SV'.
  split; unfold map_lookup in *; unfold map_insert in *; unfold map_remove in *;
    repeat rewrite Map.insert_ok.
  {
    subst offset_name cursor_name.
    destruct string_dec. { discriminate. }
    apply (sv_result_declared SV').
  }
  {
    intros k L. rewrite<- Heqoffset_name. cbn.
    unfold map_insert. unfold map_lookup. rewrite Map.insert_ok.
    destruct string_dec. { subst. discriminate. }
    assert (X := sv_offsets_agree SV' k L).
    subst. apply X.
  }
  {
    intros k L. rewrite<- Heqcursor_name. cbn.
    unfold map_insert. unfold map_lookup. rewrite Map.insert_ok.
    destruct string_dec as [E|NE].
    {
      subst. apply make_var_name_inj in E. subst loop_depth.
      rewrite Nat2N.id in LoopDepthOk. subst k.
      rewrite Nat.sub_0_r.
      rewrite Nat.sub_diag.
      cbn.
      unfold get_cursor. cbn.
      f_equal. f_equal. f_equal. f_equal.
      rewrite uint256_ok.
      replace (((Z_of_uint256 count - 1 - Z.pos (Pos.of_succ_nat m))) + 1)%Z
        with (Z_of_uint256 count - 1 - Z.of_nat m)%Z
        by lia.
      assert (R := uint256_range count).
      rewrite Z.mod_small; lia.
    }
    assert (X := sv_cursors_agree SV' k L).
    rewrite<- Heqcursor_name in X. cbn in X.
    remember (Datatypes.length loop_info - 0 - k) as i.
    destruct i.
    {
      cbn in L.
      now replace loop_depth with (N.of_nat k) in NE by lia.
    }
    cbn.
    apply X.
  }
  {
    intros k L.
    rewrite Map.insert_ok. subst cursor_name.
    destruct string_dec. { discriminate. }
    apply (sv_offsets_undeclared SV' k L).
  }
  intros k L.
  rewrite Map.insert_ok. subst offset_name.
  destruct string_dec as [E|NE].
  {
    subst cursor_name. apply make_var_name_inj in E.
    cbn in L. lia.
  }
  apply (sv_cursors_undeclared SV' k L).
}

assert (EnoughIterationsForBody: (AST.max_loop_count_block bodyblock40 
                                   <
                                  N.of_nat max_loop_iterations)%N).
{ subst. cbn. apply (max_lub_lt_r EnoughIterations). }
subst bodyblock40 bodyblock50.
assert (T: translate_block match this_fun_decl50 with
           | Some _ => true
           | None => false
           end B protos (L40.AST.Block body) (N.succ loop_depth) = inr (AST.Block body50)).
{ cbn. now rewrite<- Heqbody'. }

(* ------------------------------- induction ---------------------------- *)
clear Heqcurrent_loc50.
remember (S c) as sc.
assert (CBound: (Z.of_nat c < Z_of_uint256 count)%Z) by lia.
assert (M: sc < max_loop_iterations) by lia.
clear Heqc.
unfold current_ctx in *.
assert (CurrentSV: match sc with
                   | O => True
                   | S x => SecondaryVarsOk ({|
                                              Expr.loop_offset := let _ := memory_impl in
                                                                  OpenArray.get loc40 var;
                                              Expr.loop_count := count;
                                              Expr.loop_countdown := x
                                             |} :: loop_info) current_loc50
                   end).
{
  subst sc.
  apply PreloopSV.
}
clear PreloopSV.
clear LocalVarsOk.
remember (_ loc40 var) as offset. clear Heqoffset.
revert loc40 c CBound Heqsc current_ctx current_loc50 CurrentSV CurrentLocalVarsOk world.
remember max_loop_iterations as fixed_max_loop_iterations.
rewrite Heqfixed_max_loop_iterations in M.
rewrite Heqfixed_max_loop_iterations. clear Heqfixed_max_loop_iterations.
revert max_loop_iterations M.
induction sc; intros. { discriminate. }
inversion Heqsc; subst sc; clear Heqsc.

assert (LoopDepthOk': List.length (current_ctx :: loop_info) = N.to_nat (N.succ loop_depth)).
{ cbn. rewrite LoopDepthOk. lia. }
assert (BodyWorks := interpret_translated_block_weak call40 call50 CallsOk decls40 decls50
                                                     this_fun_decl40 this_fun_decl50 FunDeclOk
                                                     DeclsOk builtins40 builtins50 BuiltinsOk
                                                     BuiltinsBasics BuiltinsSafe ProtosOk
                                                     world loc40 current_loc50
                                                     (current_ctx :: loop_info) LoopDepthOk' CurrentSV
                                                     (L40.AST.Block body) (L50.AST.Block body50)
                                                     T varcap (N.max_lub_r _ _ _ VarcapOk)
                                                     CurrentLocalVarsOk EnoughIterationsForBody
                                                     H).

subst iterate40 iterate50.
fold current_ctx.

destruct max_loop_iterations. { exfalso. apply (Nat.nlt_0_r _ M). }
cbn.
assert (CondRewrite := CondExprWorks world current_loc50 (get_cursor current_ctx)
                                     (G current_ctx current_loc50 (sv_cursors_agree CurrentSV))).
unfold map_lookup in CondRewrite. rewrite CondRewrite. clear CondRewrite.
assert (ShouldProceed: (Z_of_uint256 (get_cursor current_ctx) <? Z_of_uint256 count)%Z = true).
{
  apply Z.ltb_lt.
  unfold get_cursor.
  unfold current_ctx.
  cbn.
  rewrite uint256_ok. 
  assert (R := uint256_range count).
  rewrite Z.mod_small; lia.
}
rewrite ShouldProceed. unfold one256. cbn. rewrite uint256_ok. cbn.
cbn in BodyWorks.
rewrite<- interpret_stmt_list_ok in BodyWorks.
cbn in BodyWorks.
destruct (_ world current_loc50 body50) as ((world50', loc50'), result50').
destruct (_ world loc40 (current_ctx :: loop_info) body) as ((world40', loc40'), result40').
destruct BodyWorks as (PostIterResultsAgree, PostIterSV).
unfold StmtResultsAgree in PostIterResultsAgree.
destruct PostIterResultsAgree as (PostIterLocalVarsOk, PostIterResultsAgree).

(* apply increment *)
assert (IncRewrite := IncrementWorks world50' loc50' (get_cursor current_ctx)
                                     (G current_ctx loc50' (sv_cursors_agree PostIterSV))).
unfold map_lookup in IncRewrite. rewrite IncRewrite. clear IncRewrite.
remember (map_insert loc50' (cursor_name loop_depth)
           (existT (fun t : yul_type => yul_value t) U256
              (yul_uint256 (uint256_of_Z (Z_of_uint256 (get_cursor current_ctx) + 1)))))
  as postinc_loc50.
assert (NextSV:
     match c with
     | 0 => True
     | S x =>
         SecondaryVarsOk
           ({|
              Expr.loop_offset := offset;
              Expr.loop_count := count;
              Expr.loop_countdown := x
            |} :: loop_info) postinc_loc50
     end).
{
  destruct c as [|x]. { trivial. }
  cbn. subst postinc_loc50.
  apply (IncrementSV _ loc50' x CBound PostIterSV).
}
assert (StopNowSV := UndeclareSV current_ctx loc50' PostIterSV).
destruct result40' as [result40'|], result50' as [result50'|]; try contradiction.
2:{
  (* just undeclare the offset and cursor *)
  split. { apply StmtResultsUndeclare. cbn. tauto. }
  apply StopNowSV.
}

assert (EquivSV: forall ctx loc1 loc2,
                   (forall name, map_lookup loc1 name = map_lookup loc2 name)
                    ->
                   SecondaryVarsOk ctx loc1
                    ->
                   SecondaryVarsOk ctx loc2).
{
  intros ctx loc1 loc2 E SV1.
  split.
  { rewrite<- E. apply (sv_result_declared SV1). }
  { intros k L. rewrite<- E. apply (sv_offsets_agree SV1 k L). }
  { intros k L. rewrite<- E. apply (sv_cursors_agree SV1 k L). }
  { intros k L. rewrite<- E. apply (sv_offsets_undeclared SV1 k L). }
  intros k L. rewrite<- E. apply (sv_cursors_undeclared SV1 k L).
}

assert (StopNowSV':
  SecondaryVarsOk loop_info
    (map_remove
       (map_remove
          (map_insert loc50' (cursor_name loop_depth)
             (existT (fun t : yul_type => yul_value t) U256
                (yul_uint256 (uint256_of_Z (Z_of_uint256 (uint256_of_Z (Z_of_uint256 count - 1 - 0)) + 1)))))
          (cursor_name loop_depth)) (offset_name loop_depth))).
{
  refine (EquivSV _ _ _ _ StopNowSV).
  intro name. unfold map_lookup; unfold map_remove; unfold map_insert.
  repeat rewrite Map.remove_ok. repeat rewrite Map.insert_ok.
  destruct string_dec; try easy; destruct string_dec; easy.
}

assert (StopNowLVA:
  LocalVarsAgree loc40' (map_remove (map_remove loc50' (cursor_name loop_depth)) (offset_name loop_depth))
    varcap).
{ now apply LocalVarsUndeclare. }

assert (StopNowLVA':
  LocalVarsAgree loc40'
    (map_remove
       (map_remove
          (map_insert loc50' (cursor_name loop_depth)
             (existT (fun t : yul_type => yul_value t) U256
                (yul_uint256 (uint256_of_Z (Z_of_uint256 (uint256_of_Z (Z_of_uint256 count - 1 - 0)) + 1)))))
          (cursor_name loop_depth)) (offset_name loop_depth)) varcap).
{
  apply LocalVarsUndeclare.
  intros k L. unfold map_insert. unfold map_lookup. rewrite Map.insert_ok.
  subst cursor_name. destruct string_dec. { discriminate. }
  apply (PostIterLocalVarsOk k L).
}

destruct c as [|c'].
{
  (* we finish it *)
  cbn.
  destruct max_loop_iterations. { lia. } (* we pay for a whole iteration just to check the condition! *)
  cbn.
  assert (PostincCursor: map_lookup postinc_loc50 (cursor_name loop_depth) 
              =
             Some
               (existT (fun t : yul_type => yul_value t) U256
                  (yul_uint256 (uint256_of_Z (Z_of_uint256 (get_cursor current_ctx) + 1))))).
  {
    unfold map_lookup. subst postinc_loc50. unfold map_insert.
    rewrite Map.insert_ok. now destruct string_dec.
  }

  assert (CondRewrite := CondExprWorks world50' postinc_loc50 
                                       (uint256_of_Z (Z_of_uint256 (get_cursor current_ctx) + 1))
                                       PostincCursor).
  unfold map_lookup in CondRewrite.
  subst postinc_loc50.
  unfold dynamic_value in CondRewrite.
  rewrite CondRewrite. clear CondRewrite.

  unfold current_ctx. unfold get_cursor. cbn.
  replace (Z_of_uint256
                 (uint256_of_Z (Z_of_uint256 (uint256_of_Z (Z_of_uint256 count - 1 - 0)) + 1)))%Z
    with (Z_of_uint256 count).
  2:{
    assert (R := uint256_range count).
    repeat rewrite uint256_ok.
    rewrite Z.mod_small; rewrite Z.mod_small; lia.
  }
  replace (Z_of_uint256 count <? Z_of_uint256 count)%Z with false.
  2:{ symmetry. apply Z.ltb_ge. lia. }
  unfold zero256. cbn. rewrite uint256_ok. cbn.
  destruct result40' as [|a40|x40], result50' as [|a50|x50]; try destruct a40; try destruct a50;
    try easy; split; try assumption; split; assumption.
} (* c = 0 *)

assert (C'Bound: (Z.of_nat c' < Z_of_uint256 count)%Z) by lia.
assert (PostIncLVA: LocalVarsAgree loc40' postinc_loc50 varcap).
{
  intros k L. unfold map_lookup. subst postinc_loc50. unfold map_insert. 
  rewrite Map.insert_ok.
  subst. destruct string_dec; try discriminate.
  apply (PostIterLocalVarsOk k L).
}
assert (IH := IHsc max_loop_iterations (lt_S_n _ _ M)
              loc40' c' C'Bound eq_refl postinc_loc50 NextSV PostIncLVA world50'). clear IHsc.
cbn.
cbn in IH.
unfold dynamic_value in *.
subst postinc_loc50.
remember (fix interpret_stmt_list_metered
            (world0 : world_state) (loc : memory) (loops : list Expr.loop_ctx) (l0 : list L40.AST.stmt)
            {struct l0} : world_state * memory * option (stmt_result uint256) := _)
  as interpret_stmt_list40.
remember (fix do_loop (world0 : world_state) (loc : memory) (countdown : nat) {struct countdown} :
               world_state * memory * option (stmt_result uint256) := _) as iterate40.
remember (fix iterate
              (count0 : nat) (world0 : world_state) (loc : string_map {t : yul_type & yul_value t})
              {struct count0} :
                world_state * string_map {t : yul_type & yul_value t} *
                option (stmt_result (list {t : yul_type & yul_value t})) := _) as iterate50.

destruct result40' as [|a40|x40], result50' as [|a50|x50]; try contradiction;
  try destruct a40; try destruct a50; try easy;
  try subst world40'; try apply IH.
Qed.
