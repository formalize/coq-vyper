From Coq Require Import ZArith String.

From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import Base.

From Vyper.L40 Require Import AST Callset Descend.


Record loop_ctx {C: VyperConfig} := {
  loop_offset: uint256;
  loop_count: uint256;
  loop_countdown: nat; (* count - 1 down to 0 *)
}.

Fixpoint interpret_expr {C: VyperConfig}
                        {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        {cd: calldag}
                        (fc: fun_ctx cd bigger_call_depth_bound)
                        (do_call: forall
                                      (fc': fun_ctx cd smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256)
                        (builtins: string -> option builtin)
                        (world: world_state)
                        (loc: memory)
                        (loops: list loop_ctx)
                        (e: expr)
                        (CallOk: let _ := string_set_impl in 
                                   FSet.is_subset (expr_callset e)
                                                  (decl_callset (fun_decl fc))
                                   = true)
{struct e}
: world_state * expr_result uint256
:= let fix interpret_expr_list (world: world_state)
                               (loc: memory)
                               (e: list expr)
                               (CallOk: let _ := string_set_impl in 
                                        FSet.is_subset (expr_list_callset e)
                                                       (decl_callset (fun_decl fc))
                                        = true)
      {struct e}
      : world_state * expr_result (list uint256)
      := match e as e' return e = e' -> _ with
         | nil => fun _ => (world, ExprSuccess nil)
         | (h :: t)%list => fun E =>
             (* right-to-left evaluation order *)
             let (world', result_t) := interpret_expr_list world loc t
                                                           (callset_descend_tail E CallOk)
             in match result_t with
                | ExprAbort ab => (world', ExprAbort ab)
                | ExprSuccess values_t =>
                   let (world'', result_h) := interpret_expr Ebound fc do_call builtins
                                                             world' loc loops h
                                                             (callset_descend_head E CallOk)
                   in (world'', match result_h with
                                | ExprAbort ab => ExprAbort ab
                                | ExprSuccess value_h => ExprSuccess (value_h :: values_t)%list
                                end)
                 end
         end eq_refl
    in match e as e' return e = e' -> _ with
       | Const val => fun _ => (world, ExprSuccess val)
       | LocalVar index => fun _ =>
           let _ := memory_impl in
           (world, ExprSuccess (OpenArray.get loc index))
       | LoopOffset => fun _ =>
           (world, match loops with
                   | (loop :: _)%list =>  ExprSuccess (loop_offset loop)
                   | nil => expr_error "loop index higher than the nesting level"
                   end)
       | LoopCursor => fun _ =>
           (world, match loops with
                   | (loop :: _)%list => 
                      ExprSuccess (uint256_of_Z (Z_of_uint256 (loop_count loop) - 1 -
                                                   Z.of_nat (loop_countdown loop)))%Z
                   | nil => expr_error "loop index higher than the nesting level"
                   end)
       | PrivateCall name args => fun E =>
           let (world', result_args) :=
             interpret_expr_list world loc args
                                 (callset_descend_args E CallOk)
           in match result_args with
              | ExprAbort ab => (world', ExprAbort ab)
              | ExprSuccess arg_values =>
                  match fun_ctx_descend fc CallOk Ebound E with
                  | None => (* can't resolve the function, maybe it's a builtin *)
                            (world', expr_error "can't resolve function name")
                  | Some new_fc => do_call new_fc world' arg_values
                  end
              end
       | BuiltinCall name args => fun E =>
           let (world', result_args) :=
             interpret_expr_list world loc args
                                 (callset_descend_builtin_args E CallOk)
           in match result_args with
              | ExprAbort ab => (world', ExprAbort ab)
              | ExprSuccess arg_values =>
                match builtins name with
                | Some (existT _ arity b) =>
                   (if (arity =? List.length arg_values)%nat as arity_ok 
                    return _ = arity_ok -> _
                        then fun Earity =>
                               call_builtin arg_values Earity (b world')
                        else fun _ => (world', expr_error "builtin with wrong arity"))
                      eq_refl
                | None => (world', expr_error "can't resolve function name")
                end
              end
       end eq_refl.