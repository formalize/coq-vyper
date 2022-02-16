From Coq Require Import ZArith String.

From Vyper Require Import Config Calldag.

From Vyper.L10 Require Import Base UInt256.

From Vyper.L40 Require Import AST Callset Descend Expr.

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
                                (loc: memory)
                                (loops: list loop_ctx)
                                (ss: small_stmt)
                                (CallOk: let _ := string_set_impl in 
                                         FSet.is_subset (small_stmt_callset ss)
                                                        (decl_callset (fun_decl fc))
                                         = true)
: world_state * memory * stmt_result uint256
:= match ss as ss' return ss = ss' -> _ with
   | Abort ab => fun _ => (world, loc, StmtAbort ab)
   | Return e => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc loops e
                                               (callset_descend_return E CallOk)
        in (world', loc, match result with
                         | ExprSuccess value => StmtReturnFromFunction value
                         | ExprAbort ab => StmtAbort ab
                         end)
   | Raise e => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc loops e
                                               (callset_descend_raise E CallOk)
        in (world', loc, StmtAbort (match result with
                                    | ExprSuccess value => AbortException value
                                    | ExprAbort ab      => ab
                                    end))
   | Assign lhs rhs => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc loops rhs
                                               (callset_descend_assign_rhs E CallOk)
        in let _ := memory_impl
        in match result with
           | ExprSuccess value => (world', OpenArray.put loc lhs value, StmtSuccess)
           | ExprAbort ab => (world', loc, StmtAbort ab)
           end
   | ExprStmt e => fun E =>
                   let (world', result) := interpret_expr Ebound fc do_call builtins
                                                          world loc loops e
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
                        (loc: memory)
                        (loops: list loop_ctx) (* the head is the innermost *)
                        (s: stmt)
                        (CallOk: let _ := string_set_impl in 
                                 FSet.is_subset (stmt_callset s)
                                                (decl_callset (fun_decl fc))
                                 = true)
{struct s}
: world_state * memory * stmt_result uint256
:= match s as s' return s = s' -> _ with
   | SmallStmt ss => fun E => interpret_small_stmt Ebound fc do_call builtins
                                                   world loc loops ss
                                                   (callset_descend_small_stmt E CallOk)
   | Switch e cases default => fun E =>
       let (world', result) := interpret_expr Ebound fc do_call builtins
                                              world loc loops e
                                              (callset_descend_switch_expr E CallOk)
       in match result with
          | ExprAbort ab => (world', loc, StmtAbort ab)
          | ExprSuccess value =>
              (fix dispatch (l: list case) (Ok: let _ := string_set_impl in 
                                                FSet.is_subset (case_list_callset l)
                                                               (decl_callset (fun_decl fc))
                                                = true)
               : world_state * memory * stmt_result uint256
               := match l as l' return l = l' -> _ with
                  | cons (Case guard block) t => fun El =>
                      if (Z_of_uint256 value =? Z_of_uint256 guard)%Z
                        then interpret_block Ebound fc do_call builtins
                                             world' loc loops block (callset_descend_cases_head El Ok)
                        else dispatch t (callset_descend_cases_tail El Ok)
                  | nil => fun _ =>
                           match default as default' return default = default' -> _ with
                           | Some block => fun Edefault =>
                                interpret_block Ebound fc do_call builtins
                                                world' loc loops block
                                                (callset_descend_cases_default
                                                  (eq_ind default (fun x => s = Switch e cases x)
                                                          E (Some _) Edefault)
                                                  CallOk)
                           | None => fun _ => (world', loc, StmtSuccess)
                           end eq_refl
                  end eq_refl) cases (callset_descend_cases E CallOk)
          end
   | Loop var count body => fun E =>
              let _ := memory_impl in
              let offset := OpenArray.get loc var in
              let fix do_loop (world: world_state)
                              (loc: memory)
                              (countdown: nat)
              {struct countdown}
              := match countdown with
                 | O => (world, loc, StmtSuccess)
                 | S k =>
                     let '(world', loc', result)
                     := interpret_block Ebound fc do_call builtins
                                        world loc
                                        ({| loop_offset := let _ := memory_impl in offset
                                          ; loop_count := count
                                          ; loop_countdown := k
                                         |} :: loops)%list
                                        body
                                        (callset_descend_loop_body E CallOk)
                     in match result with
                        | StmtSuccess | StmtAbort AbortContinue => do_loop world' loc' k
                        | StmtAbort AbortBreak => (world', loc', StmtSuccess)
                        | _ => (world', loc', result)
                        end
                 end
              in do_loop world loc (Z.to_nat (Z_of_uint256 count))
   end eq_refl
with interpret_block {bigger_call_depth_bound smaller_call_depth_bound: nat}
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
                     (b: block)
                     (CallOk: let _ := string_set_impl in 
                              FSet.is_subset (block_callset b)
                                             (decl_callset (fun_decl fc))
                              = true)
: world_state * memory * stmt_result uint256
:= match b as b' return b = b' -> _ with
   | Block stmts => fun Eb =>
      (fix interpret_stmt_list (world: world_state)
                               (loc: memory)
                               (loops: list loop_ctx)
                               (l: list stmt)
                               (Ok: let _ := string_set_impl in 
                                    FSet.is_subset (stmt_list_callset l)
                                                   (decl_callset (fun_decl fc))
                                    = true)
       {struct l}
       : world_state * memory * stmt_result uint256
       := match l as l' return l = l' -> _ with
          | nil => fun _ => (world, loc, StmtSuccess)
          | cons h t => fun El =>
              let '(world', loc', result) := interpret_stmt Ebound fc do_call builtins
                                                            world loc loops h
                                                            (callset_descend_stmts_head El Ok)
              in match result with
                 | StmtSuccess => interpret_stmt_list world' loc' loops t
                                                      (callset_descend_stmts_tail El Ok)
                 | _ => (world', loc', result)
                 end
          end eq_refl) world loc loops stmts (callset_descend_block Eb CallOk)
   end eq_refl.

End Stmt.
