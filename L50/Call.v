From Coq Require Import String Arith ZArith.

From Vyper Require Import Config Map.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types AST Builtins Expr LocalVars DynError Stmt.



Fixpoint interpret_call {C: VyperConfig}
                        (max_call_depth: nat)
                        (max_loop_iterations: nat)
                        (builtins: string -> option yul_builtin)
                        (funs: string -> option fun_decl)
                        (f: fun_decl)
                        (world: world_state)
                        (arg_values: list dynamic_value)
{struct max_call_depth}
: world_state * option (expr_result (list dynamic_value))
:= let _ := string_map_impl in
   match max_call_depth with
   | O => (world, None)
   | S new_max_call_depth =>
        match bind_vars_to_values (fd_inputs f) arg_values Map.empty with
        | inl err =>
            (* since L10-L40 produce a slightly better error message than "too few values",
               namely "function called with too few arguments", it's better to repeat it here.
             *)
            (world, Some (expr_error
                            match err with
                            | DE_TooFewValues => "function called with too few arguments"
                            | DE_TooManyValues => "function called with too many arguments"
                            | _ => string_of_dynamic_error err
                            end))
        | inr loc_with_args_only =>
            match bind_vars_to_zeros (fd_outputs f) loc_with_args_only with
            | inl err => (world, Some (expr_error (string_of_dynamic_error err)))
            | inr loc =>
                let '(world', loc', result) :=
                        interpret_block max_loop_iterations builtins funs (Some f)
                                        (interpret_call new_max_call_depth max_loop_iterations 
                                                        builtins funs)
                                        world loc nop (fd_body f)
                in (world', match result with
                            | None => None
                            | Some StmtSuccess =>
                                match get_vars_by_typenames (fd_outputs f) loc' with
                                | inl err => Some (expr_error (string_of_dynamic_error err))
                                | inr outputs => Some (ExprSuccess outputs)
                                end
                            | Some (StmtAbort AbortBreak)
                            | Some (StmtAbort AbortContinue) =>
                                Some (expr_error (string_of_dynamic_error DE_BreakContinueDisallowed))
                            | Some (StmtAbort a) => Some (ExprAbort a)
                            | Some (StmtReturnFromFunction x) => Some (ExprSuccess x)
                            end)
            end
        end
   end.

Definition interpret {C: VyperConfig}
                     (max_call_depth: nat)
                     (max_loop_iterations: nat)
                     (builtins: string -> option yul_builtin)
                     (funs: string -> option fun_decl)
                     (fun_name: string)
                     (world: world_state)
                     (args: list dynamic_value)
: world_state * option (expr_result (list dynamic_value))
:= match funs fun_name with
   | Some f => interpret_call max_call_depth max_loop_iterations builtins funs f world args
   | None => (world, Some (expr_error "declaration not found"))
   end.