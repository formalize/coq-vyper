From Coq Require Import ZArith String.

From Vyper Require Import Config Calldag.

From Vyper.L10 Require Import Base.

From Vyper.L20 Require Import AST Callset Descend.


Definition storage_var_is_declared {C: VyperConfig}
                                   (cd: calldag)
                                   (name: string)
: bool
:= match cd_declmap cd name with
   | Some (StorageVarDecl _) => true
   | _ => false
   end.


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
                        (loc: string_map uint256)
                        (e: expr)
                        (CallOk: let _ := string_set_impl in 
                                   FSet.is_subset (expr_callset e)
                                                  (decl_callset (fun_decl fc))
                                   = true)
{struct e}
: world_state * expr_result uint256
:= let fix interpret_expr_list (world: world_state)
                               (loc: string_map uint256)
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
             let (world', result_h) := interpret_expr Ebound fc do_call builtins
                                                      world loc h
                                                      (callset_descend_head E CallOk)
             in match result_h with
                | ExprAbort ab => (world', ExprAbort ab)
                | ExprSuccess x =>
                   let (world'', result_t) := interpret_expr_list world' loc t
                                                                  (callset_descend_tail E CallOk)
                   in (world'', match result_t with
                                | ExprAbort _ => result_t
                                | ExprSuccess y => ExprSuccess (x :: y)%list
                                end)
                 end
         end eq_refl
    in match e as e' return e = e' -> _ with
       | Const val => fun _ => (world, ExprSuccess val)
       | LocalVar name => fun _ =>
           (world, match map_lookup loc name with
                   | Some val => ExprSuccess val
                   | None => expr_error "undeclared local variable"
                   end)
       | StorageVar name => fun _ =>
           if storage_var_is_declared cd name
              then (world, ExprSuccess (match storage_lookup world name with
                                        | None => zero256
                                        | Some x => x
                                        end))
              else (world, expr_error "undeclared global variable")
       | UnOp op a => fun E =>
           let (world', result) := interpret_expr Ebound fc do_call builtins
                                                  world loc a
                                                  (callset_descend_unop E CallOk)
           in (world', match result with
                       | ExprSuccess val => interpret_unop op val
                       | ExprAbort _ => result
                       end)
       | BinOp op a b => fun E =>
           let (world', result_a) := interpret_expr Ebound fc do_call builtins
                                                    world loc a
                                                    (callset_descend_binop_left E CallOk)
           in match result_a with
           | ExprAbort _ => (world', result_a)
           | ExprSuccess x =>
             let (world'', result_b) := interpret_expr Ebound fc do_call builtins
                                                       world' loc b
                                                       (callset_descend_binop_right E CallOk)
             in (world'', match result_b with
                          | ExprAbort _ => result_b
                          | ExprSuccess y => interpret_binop op x y
                          end)
           end
       | IfThenElse cond yes no => fun E =>
           let (world', result_cond) := interpret_expr Ebound fc do_call builtins
                                                       world loc cond
                                                       (callset_descend_if_cond E CallOk)
           in match result_cond with
              | ExprAbort _ => (world', result_cond)
              | ExprSuccess cond_value =>
                  if (Z_of_uint256 cond_value =? 0)%Z
                    then interpret_expr Ebound fc do_call builtins
                                        world' loc no
                                        (callset_descend_if_else E CallOk)
                    else interpret_expr Ebound fc do_call builtins
                                        world' loc yes
                                        (callset_descend_if_then E CallOk)
              end
       | LogicalAnd a b => fun E =>
           let (world', result_a) := interpret_expr Ebound fc do_call builtins
                                                    world loc a
                                                    (callset_descend_and_left E CallOk)
           in match result_a with
              | ExprAbort _ => (world', result_a)
              | ExprSuccess a_value =>
                  if (Z_of_uint256 a_value =? 0)%Z
                    then (world', result_a)
                    else interpret_expr Ebound fc do_call builtins
                                        world' loc b
                                        (callset_descend_and_right E CallOk)
              end
       | LogicalOr a b => fun E =>
           let (world', result_a) := interpret_expr Ebound fc do_call builtins
                                                    world loc a
                                                    (callset_descend_or_left E CallOk)
           in match result_a with
              | ExprAbort msg => (world', result_a)
              | ExprSuccess a_value =>
                  if (Z_of_uint256 a_value =? 0)%Z
                    then interpret_expr Ebound fc do_call builtins
                                        world' loc b
                                        (callset_descend_or_right E CallOk)
                    else (world', result_a)
              end
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
