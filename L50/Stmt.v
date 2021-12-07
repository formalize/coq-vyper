From Coq Require Import String Arith ZArith.

From Vyper Require Import Config Map.
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
           | (world', Some (ExprSuccess (existT _ BoolType (BoolValue _ b _) :: nil))) =>
               if b
                 then interpret_block max_loop_iterations
                                      builtins funs this_fun_decl do_call
                                      world loc nop yes
                 else (world', loc, Some StmtSuccess)
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
                                                     world loc nop body
                                else dispatch tail
                        else (world', loc, Some (stmt_error (string_of_dynamic_error
                                                              (DE_TypeMismatch guard_type value_type))))
                  | nil =>
                           match default with
                           | Some body =>
                                interpret_block max_loop_iterations
                                                builtins funs this_fun_decl do_call
                                                world loc nop body
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
                   | (world', Some (ExprSuccess (existT _ BoolType (BoolValue _ b _) :: nil))) =>
                       if b
                         then match interpret_block max_loop_iterations
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
                         else (world', loc, Some StmtSuccess)
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