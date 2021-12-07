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
        | inl err => (world, Some (expr_error (string_of_dynamic_error err)))
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
                                match get_vars_by_typenames (fd_outputs f) loc with
                                | inl err => Some (expr_error (string_of_dynamic_error err))
                                | inr outputs => Some (ExprSuccess outputs)
                                end
                            | Some (StmtAbort a) => Some (ExprAbort a)
                            | Some (StmtReturnFromFunction x) => Some (ExprSuccess x)
                            end)
            end
        end
   end.