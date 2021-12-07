From Coq Require Import String Arith.

From Vyper Require Import Config Map.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types AST Builtins.

(**
    Prepend a newly computed result to a tuple of computed values.
    The newly computed result must contain exactly one value,
    otherwise [DE_ExactlyOneValueExpected] will be "thrown".
 *)
Definition cons_eval_results {C: VyperConfig}
                             (head: option (expr_result (list dynamic_value)))
                             (tail: list dynamic_value)
: option (expr_result (list dynamic_value))
:= match head with
   | None | Some (ExprAbort _) => head
   | Some (ExprSuccess h_values) =>
      match h_values with
      | (v :: nil)%list => Some (ExprSuccess (v :: tail)%list)
      | _ => Some (expr_error "exactly one value expected")
      end
   end.

Fixpoint interpret_expr {C: VyperConfig}
                        (builtins: string -> option yul_builtin)
                        (funs: string -> option fun_decl)
                        (do_call: fun_decl -> world_state -> list dynamic_value ->
                                    world_state * option (expr_result (list dynamic_value)))
                        (world: world_state)
                        (loc: string_map dynamic_value)
                        (e: expr)
{struct e}
: world_state * option (expr_result (list dynamic_value))
:= let fix interpret_expr_list (world: world_state)
                               (loc: string_map dynamic_value)
                               (args: list expr)
    {struct args}
    : world_state * option (expr_result (list dynamic_value))
    := match args with
       | nil => (world, Some (ExprSuccess nil))
       | cons head tail =>
           (* Arguments are evaluated right-to-left. *)
           let tail_result := interpret_expr_list world loc tail
           in match tail_result with
              | (_, Some (ExprAbort _)) | (_, None) => tail_result
              | (world', Some (ExprSuccess tail_values)) =>
                 let '(world'', head_result) := interpret_expr builtins funs do_call
                                                               world' loc head
                  in (world'', cons_eval_results head_result tail_values)
              end
   end in
   match e with
   | Const type val => (world, Some (ExprSuccess (existT _ type val :: nil)%list))
   | LocVar id =>
          let _ := string_map_impl in
          match Map.lookup loc id with
          | None => (world, Some (expr_error "cannot resolve variable"))
          | Some value =>
              (world, Some (ExprSuccess (value :: nil)%list))
          end
   | FunCall name args =>
      match builtins name with
      | Some b =>
          match funs name with
          | Some f => (world, Some (expr_error "a function shadows a builtin"))
          | None => (* call builtin *)
             match interpret_expr_list world loc args with
             | (world', Some (ExprSuccess arg_values)) =>
                  let '(world'', result) := call_builtin b world' arg_values in
                  (world'', Some result)
             | _ as result => result
             end
          end
      | None =>
          match funs name with
          | None => (world, Some (expr_error "can't resolve function name"))
          | Some f => (* call function *)
               match interpret_expr_list world loc args with
               | (world', Some (ExprSuccess arg_values)) => do_call f world' arg_values
               | _ as result => result
               end
          end
      end
  end.
