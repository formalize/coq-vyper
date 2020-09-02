From Coq Require Import ZArith String.

From Vyper Require Import Config Calldag.

From Vyper.L10 Require Import Base.

From Vyper.L20 Require Import AST Callset Descend Expr.

Section Stmt.
Context {C: VyperConfig}.

Definition interpret_small_stmt {bigger_call_depth_bound smaller_call_depth_bound: nat}
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
                                (s: small_stmt)
                                (CallOk: let _ := string_set_impl in 
                                         FSet.is_subset (small_stmt_callset s)
                                                        (decl_callset (fun_decl fc))
                                         = true)
: world_state * string_map uint256 * stmt_result uint256
:= match s as s' return s = s' -> _ with
   | Pass     => fun _ => (world, loc, StmtSuccess)
   | Abort ab => fun _ => (world, loc, StmtAbort ab)
   | Return e => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc e
                                               (callset_descend_return E CallOk)
        in (world', loc, match result with
                         | ExprSuccess value => StmtReturnFromFunction value
                         | ExprAbort ab => StmtAbort ab
                         end)
   | Raise e => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc e
                                               (callset_descend_raise E CallOk)
        in (world', loc, StmtAbort (match result with
                                    | ExprSuccess value => AbortException value
                                    | ExprAbort ab      => ab
                                    end))
   | Assign lhs rhs => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc rhs
                                               (callset_descend_assign_rhs E CallOk)
        in do_assign world' loc lhs result
   | ExprStmt e => fun E =>
                   let (world', result) := interpret_expr Ebound fc do_call builtins
                                                          world loc e
                                                          (callset_descend_expr_stmt E CallOk)
                   in (world', loc, match result with
                                    | ExprSuccess a => StmtSuccess
                                    | ExprAbort ab => StmtAbort ab
                                    end)
   end eq_refl.

Fixpoint interpret_stmt {bigger_call_depth_bound smaller_call_depth_bound: nat}
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
                        (s: stmt)
                        (CallOk: let _ := string_set_impl in 
                                 FSet.is_subset (stmt_callset s)
                                                (decl_callset (fun_decl fc)) = true)
 {struct s}
 : world_state * string_map uint256 * stmt_result uint256
 := match s as s' return s = s' -> _ with
    | Semicolon a b => fun E =>
         let '(world', loc', result_a) :=
                interpret_stmt Ebound fc do_call builtins
                               world loc a
                               (callset_descend_semicolon_left E CallOk) in
         match result_a with
         | StmtSuccess =>
             interpret_stmt Ebound fc do_call builtins
                            world' loc' b
                            (callset_descend_semicolon_right E CallOk)
         | _ => (world', loc', result_a)
         end
    | SmallStmt ss => fun E => interpret_small_stmt Ebound fc do_call builtins
                                                    world loc ss
                                                    (callset_descend_small_stmt E CallOk)
    | LocalVarDecl name init scope => fun E =>
         match map_lookup loc name with
         | Some _ => (world, loc, StmtAbort (AbortError "local variable already exists"))
         | None =>
           let '(world', result) :=
                  interpret_expr Ebound fc do_call builtins
                                 world loc init
                                 (callset_descend_var_init E CallOk)
           in match result with
              | ExprSuccess value =>
                  let '(world2, loc2, result2) :=
                    interpret_stmt Ebound fc do_call builtins
                                   world (map_insert loc name value) scope
                                   (callset_descend_var_scope E CallOk)
                  in (world2, map_remove loc2 name, result2)
              | ExprAbort ab =>
                  (world', loc, StmtAbort ab)
              end
         end
    | IfElseStmt cond yes no => fun E => 
        let (world', result_cond) := interpret_expr
                                       Ebound fc do_call builtins
                                       world loc cond
                                       (callset_descend_stmt_if_cond E CallOk)
        in match result_cond with
           | ExprAbort ab => (world', loc, StmtAbort ab)
           | ExprSuccess cond_value =>
               if (Z_of_uint256 cond_value =? 0)%Z
                 then interpret_stmt Ebound fc do_call builtins
                                     world' loc no
                                     (callset_descend_stmt_if_else E CallOk)
                 else interpret_stmt Ebound fc do_call builtins
                                     world' loc yes
                                     (callset_descend_stmt_if_then E CallOk)
           end
    | Loop var start count fc_body => fun E =>
        let (world', result_start) :=
              interpret_expr Ebound fc do_call builtins
                             world loc start
                             (callset_descend_loop_start E CallOk)
        in match result_start with
           | ExprAbort ab => (world', loc, StmtAbort ab)
           | ExprSuccess start_value =>
              let fix interpret_loop_rec (world: world_state)
                                         (loc: string_map uint256)
                                         (cursor: Z)
                                         (countdown: nat)
                                         (name: string)
                                         (CallOk: let _ := string_set_impl in 
                                                  FSet.is_subset (stmt_callset fc_body)
                                                                 (decl_callset (fun_decl fc)) = true)
                 {struct countdown}
                 : world_state * string_map uint256 * stmt_result uint256
                 := match countdown with
                    | O => (world, loc, StmtSuccess)
                    | S new_countdown =>
                          let loc' := map_insert loc name (uint256_of_Z cursor) in
                          let '(world', loc'', result) :=
                                interpret_stmt Ebound fc do_call builtins world loc' fc_body CallOk
                          in match result with
                             | StmtSuccess | StmtAbort AbortContinue =>
                                 interpret_loop_rec world' loc''
                                                    (Z.succ cursor) new_countdown name CallOk
                             | StmtAbort AbortBreak =>
                                 (world', loc'', StmtSuccess)
                             | _ => (world', loc'', result)
                             end
                    end
               in match map_lookup loc var with
               | Some _ => (world', loc, StmtAbort (AbortError "loop var already exists"))
               | None => let count_z := Z_of_uint256 count in
                         let count_nat := Z.to_nat count_z in
                         let start_z := Z_of_uint256 start_value in
                         let last := (start_z + count_z - 1)%Z in
                         if (Z_of_uint256 (uint256_of_Z last) =? last)%Z
                           then
                             interpret_loop_rec
                               world' loc start_z count_nat var
                               (callset_descend_loop_body E CallOk)
                           else (world, loc, StmtAbort (AbortError "loop range overflows"))
               end
           end
    end eq_refl.

End Stmt.