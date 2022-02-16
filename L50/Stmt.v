From Coq Require Import String Arith ZArith.

From Vyper Require Import Config Map Logic2.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types AST Builtins Expr LocalVars DynError.

Local Open Scope list_scope.

Local Lemma var_decl_helper {C: VyperConfig} {s: stmt} {vars init}
                            (NotVarDecl: is_var_decl s = false)
                            (E: s = VarDecl vars init):
  False.
Proof.
now subst.
Qed.

(* This is needed for the [preproc] argument in interpret_block which is needed for for-loop inits blocks. *)
Definition nop {C: VyperConfig} (world: world_state) (loc: string_map dynamic_value)
: world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
:= (world, loc, Some StmtSuccess).

Fixpoint interpret_stmt {C: VyperConfig}
                        (max_loop_iterations: nat)
                        (builtins: string -> option yul_builtin)
                        (funs: string -> option fun_decl)
                        (this_fun_decl: option fun_decl)
                        (do_call: fun_decl -> world_state -> list dynamic_value ->
                                    world_state * option (expr_result (list dynamic_value)))
                        (world: world_state)
                        (loc: string_map dynamic_value)
                        (s: stmt)
                        (NotVarDecl: is_var_decl s = false)
{struct s}
: world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
:= match s as s' return s = s' -> _ with
   | Break => fun _ => (world, loc, Some (StmtAbort AbortBreak))
   | Continue => fun _ => (world, loc, Some (StmtAbort AbortContinue))
   | Leave => fun _ =>
              match this_fun_decl with
              | None => (world, loc, Some (stmt_error (string_of_dynamic_error DE_LeaveWithoutFunction)))
              | Some f => match get_vars_by_typenames (fd_outputs f) loc with
                          | inl err => (world, loc, Some (stmt_error (string_of_dynamic_error err)))
                          | inr outputs => (world, loc, Some (StmtReturnFromFunction outputs))
                          end
              end
   | BlockStmt b => fun _ => interpret_block max_loop_iterations
                                             builtins funs this_fun_decl do_call
                                             world loc nop b
   | VarDecl _ _ => fun E => match var_decl_helper NotVarDecl E with end
   | Assign names rhs => fun _ =>
            match interpret_expr builtins funs do_call world loc rhs
            with
            | (world', Some (ExprSuccess values)) =>
                match rebind_vars_to_values names values loc with
                | inl err => (world', loc, Some (stmt_error (string_of_dynamic_error err)))
                | inr loc' => (world', loc', Some StmtSuccess)
                end
            | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab))
            | (world', None) => (world', loc, None)
            end
   | If cond yes => fun _ =>
           match interpret_expr builtins funs do_call world loc cond
           with
           (* Apparently the actual Yul does not require boolean conditions in if and for.
           | (world', Some (ExprSuccess (existT _ BoolType (BoolValue _ b _) :: nil))) =>
               if b
                 then interpret_block max_loop_iterations
                                      builtins funs this_fun_decl do_call
                                      world' loc nop yes
                 else (world', loc, Some StmtSuccess)
           *)
           | (world', Some (ExprSuccess (b :: nil))) =>
               if (Z_of_uint256 (uint256_of_dynamic_value b) =? 0)%Z
                 then (world', loc, Some StmtSuccess)
                 else interpret_block max_loop_iterations
                                      builtins funs this_fun_decl do_call
                                      world' loc nop yes
           | (world', Some (ExprSuccess _)) =>
                (world', loc, Some (stmt_error (string_of_dynamic_error DE_SingleBooleanExpected)))
           | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab))
           | (world', None) => (world', loc, None)
           end
   | Expr e => fun _ =>
               match interpret_expr builtins funs do_call world loc e
               with
               | (world', Some (ExprSuccess nil)) => (world', loc, Some StmtSuccess)
               | (world', Some (ExprSuccess _)) =>
                    (world', loc, Some (stmt_error (string_of_dynamic_error DE_LeftoverValuesInExpression)))
               | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab))
               | (world', None) => (world', loc, None)
               end
   | Switch e cases default => fun _ =>
       let (world', result) := interpret_expr builtins funs do_call world loc e
       in match result with
          | Some (ExprSuccess (existT _ value_type value :: nil)) =>
              (fix dispatch (l: list case)
               : world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
               := match l with
                  | (Case guard_type guard body) :: tail =>
                      if yul_type_eq_dec value_type guard_type
                        then if (Z_of_uint256 (uint256_of_yul_value value)
                                  =?
                                 Z_of_uint256 (uint256_of_yul_value guard))%Z
                                then interpret_block max_loop_iterations
                                                     builtins funs this_fun_decl do_call
                                                     world' loc nop body
                                else dispatch tail
                        else (world', loc, Some (stmt_error (string_of_dynamic_error
                                                              (DE_TypeMismatch guard_type value_type))))
                  | nil =>
                           match default with
                           | Some body =>
                                interpret_block max_loop_iterations
                                                builtins funs this_fun_decl do_call
                                                world' loc nop body
                           | None => (world', loc, Some StmtSuccess)
                           end
                  end) cases
          | Some (ExprSuccess _) =>
              (world', loc, Some (stmt_error (string_of_dynamic_error DE_SingleValueExpected)))
          | Some (ExprAbort ab) => (world', loc, Some (StmtAbort ab))
          | None => (world', loc, None)
          end
   | For init cond after body => fun _ =>
        let fix iterate (count: nat) (world: world_state) (loc: string_map dynamic_value)
            : world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
            := match count with
               | O => (world, loc, None)
               | S count' =>
                   match interpret_expr builtins funs do_call world loc cond
                   with
                   (* as in If, I removed the check that the condition is actually a boolean
                      because the actual implementation never enforces that.
                    *)
                   | (world', Some (ExprSuccess (b :: nil))) =>
                       if (Z_of_uint256 (uint256_of_dynamic_value b) =? 0)%Z
                         then (world', loc, Some StmtSuccess)
                         else match interpret_block max_loop_iterations
                                                    builtins funs this_fun_decl do_call
                                                    world' loc nop body
                              with
                              | (world'', loc', Some (StmtAbort AbortBreak)) =>
                                  (world'', loc', Some StmtSuccess)
                              | (world'', loc', Some (StmtAbort AbortContinue))
                              | (world'', loc', Some StmtSuccess) =>
                                  match interpret_block max_loop_iterations
                                                        builtins funs this_fun_decl do_call
                                                        world'' loc' nop after
                                  with
                                  | (world''', loc'', Some (StmtAbort AbortBreak))
                                  | (world''', loc'', Some (StmtAbort AbortContinue)) =>
                                      (world''', loc'', Some (stmt_error
                                                          (string_of_dynamic_error
                                                            DE_BreakContinueDisallowed)))
                                  | (world''', loc'', Some StmtSuccess) =>
                                      iterate count' world''' loc''
                                  | x => x
                                  end
                              | x => x
                              end
                   | (world', Some (ExprSuccess _)) =>
                        (world', loc, Some (stmt_error (string_of_dynamic_error DE_SingleBooleanExpected)))
                   | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab))
                   | (world', None) => (world', loc, None)
                   end
               end
        in match interpret_block max_loop_iterations
                                 builtins funs this_fun_decl do_call
                                 world loc (iterate max_loop_iterations) init
           with
           | (world', loc', Some (StmtAbort AbortBreak))
           | (world', loc', Some (StmtAbort AbortContinue)) =>
               (world', loc', Some (stmt_error (string_of_dynamic_error DE_BreakContinueDisallowed)))
           | x => x
           end
   end eq_refl
with interpret_block {C: VyperConfig}
                     (max_loop_iterations: nat)
                     (builtins: string -> option yul_builtin)
                     (funs: string -> option fun_decl)
                     (this_fun_decl: option fun_decl)
                     (do_call: fun_decl -> world_state -> list dynamic_value ->
                                 world_state * option (expr_result (list dynamic_value)))
                     (world: world_state)
                     (loc: string_map dynamic_value)
                     (postproc: world_state -> string_map dynamic_value ->
                                world_state * string_map dynamic_value * option (stmt_result (list dynamic_value)))
                     (b: block)
: world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
:= let fix interpret_stmt_list (world: world_state)
                               (loc: string_map dynamic_value)
                               (stmts: list stmt)
        {struct stmts}
        : world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
        := match stmts as stmts' return stmts = stmts' -> _ with
           | nil => fun _ => postproc world loc
           | h :: t => fun E =>
              (if is_var_decl h as h_is_var_decl return _ = h_is_var_decl -> _
                 then fun Evar =>
                   match var_decl_unpack h Evar with
                   | (names, Some init) =>
                        match interpret_expr builtins funs do_call world loc init
                        with
                        | (world', Some (ExprSuccess values)) =>
                            match bind_vars_to_values names values loc with
                            | inl err => (world', loc, Some (stmt_error (string_of_dynamic_error err)))
                            | inr loc' =>
                                let '(world'', loc'', result) := interpret_stmt_list world' loc' t in
                                (world'', unbind_vars names loc'', result)
                            end
                        | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab))
                        | (world', None) => (world', loc, None)
                        end
                   | (names, None) =>
                       match bind_vars_to_zeros names loc with
                       | inl err => (world, loc, Some (stmt_error (string_of_dynamic_error err)))
                       | inr loc' =>
                           let '(world', loc'', result) := interpret_stmt_list world loc' t in
                           (world', unbind_vars names loc'', result)
                       end
                   end
                 else fun Evar =>
                   let '(world', loc', result) := interpret_stmt max_loop_iterations
                                                                 builtins funs this_fun_decl do_call
                                                                 world loc h Evar
                   in match result with
                      | Some StmtSuccess => interpret_stmt_list world' loc' t
                      | _ => (world', loc', result)
                      end) eq_refl
           end eq_refl
    in let '(Block stmts) := b in interpret_stmt_list world loc stmts.

(** In all cases except for-loops' init blocks we don't need the stupid postproc hook.
  Here's a cleaner hook-free version.
 *)
Fixpoint interpret_stmt_list {C: VyperConfig}
                             (max_loop_iterations: nat)
                             (builtins: string -> option yul_builtin)
                             (funs: string -> option fun_decl)
                             (this_fun_decl: option fun_decl)
                             (do_call: fun_decl -> world_state -> list dynamic_value ->
                                         world_state * option (expr_result (list dynamic_value)))
                             (world: world_state)
                             (loc: string_map dynamic_value)
                             (stmts: list stmt)
{struct stmts}
: world_state * string_map dynamic_value * option (stmt_result (list dynamic_value))
:= match stmts as stmts' return stmts = stmts' -> _ with
   | nil => fun _ => (world, loc, Some StmtSuccess)
   | h :: t => fun E =>
      (if is_var_decl h as h_is_var_decl return _ = h_is_var_decl -> _
         then fun Evar =>
           match var_decl_unpack h Evar with
           | (names, Some init) =>
                match interpret_expr builtins funs do_call world loc init
                with
                | (world', Some (ExprSuccess values)) =>
                    match bind_vars_to_values names values loc with
                    | inl err => (world', loc, Some (stmt_error (string_of_dynamic_error err)))
                    | inr loc' =>
                        let '(world'', loc'', result) := 
                            interpret_stmt_list max_loop_iterations builtins funs this_fun_decl do_call
                                                world' loc' t in
                        (world'', unbind_vars names loc'', result)
                    end
                | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab))
                | (world', None) => (world', loc, None)
                end
           | (names, None) =>
               match bind_vars_to_zeros names loc with
               | inl err => (world, loc, Some (stmt_error (string_of_dynamic_error err)))
               | inr loc' =>
                   let '(world', loc'', result) := interpret_stmt_list max_loop_iterations builtins
                                                                       funs this_fun_decl do_call
                                                                       world loc' t 
                   in (world', unbind_vars names loc'', result)
               end
           end
         else fun Evar =>
           let '(world', loc', result) := interpret_stmt max_loop_iterations
                                                         builtins funs this_fun_decl do_call
                                                         world loc h Evar
           in match result with
              | Some StmtSuccess => interpret_stmt_list max_loop_iterations builtins
                                                        funs this_fun_decl do_call
                                                        world' loc' t
              | _ => (world', loc', result)
              end) eq_refl
   end eq_refl.

(** The standalone definition of [interpret_stmt_list] corresponds to interpret_block. *)
Lemma interpret_stmt_list_ok {C: VyperConfig}
                             (max_loop_iterations: nat)
                             (builtins: string -> option yul_builtin)
                             (funs: string -> option fun_decl)
                             (this_fun_decl: option fun_decl)
                             (do_call: fun_decl -> world_state -> list dynamic_value ->
                                         world_state * option (expr_result (list dynamic_value)))
                             (world: world_state)
                             (loc: string_map dynamic_value)
                             (stmts: list stmt):
  interpret_block max_loop_iterations builtins funs this_fun_decl do_call world loc nop (Block stmts)
   =
  interpret_stmt_list max_loop_iterations builtins funs this_fun_decl do_call world loc stmts.
Proof.
cbn. (* open interpret_block *)
revert world loc. induction stmts as [|head]; intros. { easy. }
cbn.
pose (x := is_var_decl head). remember x as head_is_var_decl. symmetry in Heqhead_is_var_decl.
destruct head_is_var_decl; subst x.
{
  repeat rewrite if_yes with (E := Heqhead_is_var_decl).
  destruct (var_decl_unpack head Heqhead_is_var_decl) as (names, inits).
  destruct inits as [inits|].
  {
    destruct (interpret_expr builtins funs do_call world loc inits) as (world', init_result).
    destruct init_result as [init_result|]. 2:easy.
    destruct init_result as [values|ab]. 2:easy.
    destruct (bind_vars_to_values names values loc). { easy. }
    rewrite IHstmts. trivial.
  }
  destruct (bind_vars_to_zeros names loc). { easy. }
  rewrite IHstmts. trivial.
}
repeat rewrite if_no with (E := Heqhead_is_var_decl).
destruct interpret_stmt as ((world', loc'), head_result).
destruct head_result as [head_result|]. 2:trivial.
now destruct head_result.
Qed.

(** This version of [interpret_stmt_list] doesn't unbind the declared local variables,
    instead it returns a list of them.
    This is necessary to reason about interpreting a list of the form [a ++ b].
 *)
Fixpoint interpret_stmt_list_no_unbind {C: VyperConfig}
                                       (max_loop_iterations: nat)
                                       (builtins: string -> option yul_builtin)
                                       (funs: string -> option fun_decl)
                                       (this_fun_decl: option fun_decl)
                                       (do_call: fun_decl -> world_state -> list dynamic_value ->
                                                   world_state * option (expr_result (list dynamic_value)))
                                       (world: world_state)
                                       (loc: string_map dynamic_value)
                                       (stmts: list stmt)
{struct stmts}
: world_state * string_map dynamic_value * option (stmt_result (list dynamic_value)) * list typename
:= match stmts as stmts' return stmts = stmts' -> _ with
   | nil => fun _ => (world, loc, Some StmtSuccess, nil)
   | h :: t => fun E =>
      (if is_var_decl h as h_is_var_decl return _ = h_is_var_decl -> _
         then fun Evar =>
           match var_decl_unpack h Evar with
           | (names, Some init) =>
                match interpret_expr builtins funs do_call world loc init
                with
                | (world', Some (ExprSuccess values)) =>
                    match bind_vars_to_values names values loc with
                    | inl err => (world', loc, Some (stmt_error (string_of_dynamic_error err)), nil)
                    | inr loc' =>
                        let '(world'', loc'', result, vars) :=
                            interpret_stmt_list_no_unbind max_loop_iterations builtins
                                                          funs this_fun_decl do_call
                                                          world' loc' t
                        in (world'', loc'', result, vars ++ names)
                    end
                | (world', Some (ExprAbort ab)) => (world', loc, Some (StmtAbort ab), nil)
                | (world', None) => (world', loc, None, nil)
                end
           | (names, None) =>
               match bind_vars_to_zeros names loc with
               | inl err => (world, loc, Some (stmt_error (string_of_dynamic_error err)), nil)
               | inr loc' =>
                   let '(world', loc'', result, vars) :=
                            interpret_stmt_list_no_unbind max_loop_iterations builtins
                                                          funs this_fun_decl do_call
                                                          world loc' t
                   in (world', loc'', result, vars ++ names)
               end
           end
         else fun Evar =>
           let '(world', loc', result) := interpret_stmt max_loop_iterations
                                                         builtins funs this_fun_decl do_call
                                                         world loc h Evar
           in match result with
              | Some StmtSuccess => interpret_stmt_list_no_unbind max_loop_iterations builtins
                                                                  funs this_fun_decl do_call
                                                                  world' loc' t
              | _ => (world', loc', result, nil)
              end) eq_refl
   end eq_refl.

(** [interpret_stmt_list_no_unbind] followed by [unbind_vars] does the same thing
    as [interpret_stmt_list].
 *)
Lemma interpret_stmt_list_unbind_later {C: VyperConfig}
                                       (max_loop_iterations: nat)
                                       (builtins: string -> option yul_builtin)
                                       (funs: string -> option fun_decl)
                                       (this_fun_decl: option fun_decl)
                                       (do_call: fun_decl -> world_state -> list dynamic_value ->
                                                   world_state * option (expr_result (list dynamic_value)))
                                       (world: world_state)
                                       (loc: string_map dynamic_value)
                                       (stmts: list stmt):
  interpret_stmt_list max_loop_iterations builtins funs this_fun_decl do_call world loc stmts
   =
  let '(world', loc', result, vars) :=
    interpret_stmt_list_no_unbind max_loop_iterations builtins funs this_fun_decl do_call
                                  world loc stmts
  in (world', unbind_vars vars loc', result).
Proof.
revert world loc. induction stmts as [|head]; intros. { easy. }
cbn.
pose (x := is_var_decl head). remember x as head_is_var_decl. symmetry in Heqhead_is_var_decl.
destruct head_is_var_decl; subst x.
{
  repeat rewrite if_yes with (E := Heqhead_is_var_decl).
  destruct (var_decl_unpack head Heqhead_is_var_decl) as (names, inits).
  destruct inits as [inits|].
  {
    destruct (interpret_expr builtins funs do_call world loc inits) as (world', init_result).
    destruct init_result as [init_result|]. 2:easy.
    destruct init_result as [values|ab]. 2:easy.
    destruct (bind_vars_to_values names values loc). { easy. }
    rewrite IHstmts.
    destruct interpret_stmt_list_no_unbind as (((w, l), r), v).
    rewrite unbind_vars_app. trivial.
  }
  destruct (bind_vars_to_zeros names loc). { easy. }
  rewrite IHstmts.
  destruct interpret_stmt_list_no_unbind as (((w, l), r), v).
  rewrite unbind_vars_app. trivial.
}
repeat rewrite if_no with (E := Heqhead_is_var_decl).
destruct interpret_stmt as ((world', loc'), head_result).
destruct head_result as [head_result|]. 2:trivial.
now destruct head_result.
Qed.

(** Interpreting [a ++ b].
    (This lemma is the reason for interpret_stmt_list_no_unbind).
 *)
Lemma interpret_stmt_list_no_unbind_app {C: VyperConfig}
                                        (max_loop_iterations: nat)
                                        (builtins: string -> option yul_builtin)
                                        (funs: string -> option fun_decl)
                                        (this_fun_decl: option fun_decl)
                                        (do_call: fun_decl -> world_state -> list dynamic_value ->
                                                    world_state * option (expr_result (list dynamic_value)))
                                        (world: world_state)
                                        (loc: string_map dynamic_value)
                                        (a b: list stmt):
  interpret_stmt_list_no_unbind max_loop_iterations builtins funs this_fun_decl do_call
                                world loc (a ++ b)
   =
  let '(world', loc', result', vars') :=
    interpret_stmt_list_no_unbind max_loop_iterations builtins funs this_fun_decl do_call
                                  world loc a
  in match result' with
     | Some StmtSuccess =>
        let '(world'', loc'', result'', vars'') :=
             interpret_stmt_list_no_unbind max_loop_iterations builtins funs this_fun_decl do_call
                                           world' loc' b
        in (world'', loc'', result'', vars'' ++ vars')
     | _ => (world', loc', result', vars')
     end.
Proof.
revert world loc. induction a as [|head]; intros.
{
  rewrite List.app_nil_l. cbn.
  destruct interpret_stmt_list_no_unbind as (((w, l), r), v).
  now rewrite List.app_nil_r.
}
cbn.
pose (x := is_var_decl head). remember x as head_is_var_decl. symmetry in Heqhead_is_var_decl.
destruct head_is_var_decl; subst x.
{
  repeat rewrite if_yes with (E := Heqhead_is_var_decl).
  destruct (var_decl_unpack head Heqhead_is_var_decl) as (names, inits).
  destruct inits as [inits|].
  {
    destruct (interpret_expr builtins funs do_call world loc inits) as (world', init_result).
    destruct init_result as [init_result|]. 2:easy.
    destruct init_result as [values|ab]. 2:easy.
    destruct (bind_vars_to_values names values loc). { easy. }
    rewrite IHa.
    destruct interpret_stmt_list_no_unbind as (((w, l), r), v).
    destruct r as [r|]. 2:easy. destruct r; try easy.
    destruct interpret_stmt_list_no_unbind as (((w', l'), r'), v').
    now rewrite List.app_assoc.
  }
  destruct (bind_vars_to_zeros). { easy. }
  rewrite IHa.
  destruct interpret_stmt_list_no_unbind as (((w, l), r), v).
  destruct r as [r|]. 2:easy. destruct r; try easy.
  destruct interpret_stmt_list_no_unbind as (((w', l'), r'), v').
  now rewrite List.app_assoc.
}
repeat rewrite if_no with (E := Heqhead_is_var_decl).
destruct interpret_stmt as ((w, l), r).
destruct r as [r|]. 2:easy. now destruct r.
Qed.

Fixpoint stmt_list_has_top_level_var_decls {C: VyperConfig}
                                           (l: list stmt)
:= match l with
   | nil => false
   | h :: t => (is_var_decl h  ||  stmt_list_has_top_level_var_decls t)%bool
   end.

Lemma stmt_list_has_top_level_var_decls_app {C: VyperConfig}
                                            (a b: list L50.AST.stmt):
   stmt_list_has_top_level_var_decls (a ++ b)
    =
   (stmt_list_has_top_level_var_decls a ||
    stmt_list_has_top_level_var_decls b)%bool.
Proof.
induction a as [|ha]. { easy. }
cbn.
rewrite<- Bool.orb_assoc. f_equal.
assumption.
Qed.

Lemma interpret_stmt_list_no_unbind_no_vars
                                       {C: VyperConfig}
                                       (max_loop_iterations: nat)
                                       (builtins: string -> option yul_builtin)
                                       (funs: string -> option fun_decl)
                                       (this_fun_decl: option fun_decl)
                                       (do_call: fun_decl -> world_state -> list dynamic_value ->
                                                   world_state * option (expr_result (list dynamic_value)))
                                       (world: world_state)
                                       (loc: string_map dynamic_value)
                                       (stmts: list stmt)
                                       (NoVars: stmt_list_has_top_level_var_decls stmts = false):
  let '(_, _, _, vars) := interpret_stmt_list_no_unbind max_loop_iterations builtins funs
                                                        this_fun_decl do_call
                                                        world loc stmts
  in vars = nil.
Proof.
revert world loc. induction stmts as [|head]; intros. { easy. }
cbn in NoVars. apply Bool.orb_false_elim in NoVars. destruct NoVars as (NoVarsHead, NoVarsTail).
cbn.
rewrite if_no with (E := NoVarsHead).
destruct interpret_stmt as ((world', loc'), result).
destruct result as [result|]. 2:easy.
destruct result; try easy. apply IHstmts. assumption.
Qed.

(** Interpreting [a ++ b] when neither [a] nor [b] contain local variable declarations.
 *)
Lemma interpret_stmt_list_app {C: VyperConfig}
                              (max_loop_iterations: nat)
                              (builtins: string -> option yul_builtin)
                              (funs: string -> option fun_decl)
                              (this_fun_decl: option fun_decl)
                              (do_call: fun_decl -> world_state -> list dynamic_value ->
                                          world_state * option (expr_result (list dynamic_value)))
                              (world: world_state)
                              (loc: string_map dynamic_value)
                              (a b: list stmt)
                              (NoVarsA: stmt_list_has_top_level_var_decls a = false)
                              (NoVarsB: stmt_list_has_top_level_var_decls b = false):
  interpret_stmt_list max_loop_iterations builtins funs this_fun_decl do_call
                      world loc (a ++ b)
   =
  let '(world', loc', result') :=
    interpret_stmt_list max_loop_iterations builtins funs this_fun_decl do_call
                        world loc a
  in match result' with
     | Some StmtSuccess =>
        let '(world'', loc'', result'') :=
             interpret_stmt_list max_loop_iterations builtins funs this_fun_decl do_call
                                 world' loc' b
        in (world'', loc'', result'')
     | _ => (world', loc', result')
     end.
Proof.
repeat rewrite interpret_stmt_list_unbind_later.
rewrite interpret_stmt_list_no_unbind_app.
assert (V_A := interpret_stmt_list_no_unbind_no_vars max_loop_iterations builtins funs
                                                     this_fun_decl do_call
                                                     world loc a NoVarsA).
destruct (interpret_stmt_list_no_unbind max_loop_iterations builtins funs this_fun_decl do_call world loc a)
  as (((world', loc'), result'), vars'). subst vars'.
destruct result' as [result'|]; try easy.
destruct result'; try easy.
cbn.
assert (V_B := interpret_stmt_list_no_unbind_no_vars max_loop_iterations builtins funs
                                                     this_fun_decl do_call
                                                     world' loc' b NoVarsB).
rewrite interpret_stmt_list_unbind_later.
destruct (interpret_stmt_list_no_unbind max_loop_iterations builtins funs this_fun_decl do_call world' loc' b)
  as (((world'', loc''), result''), vars''). now subst vars''.
Qed.
