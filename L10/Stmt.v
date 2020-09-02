From Coq Require Import String Arith NArith ZArith Eqdep_dec.

From Vyper Require Import Config Calldag.
From Vyper Require FSet Map UInt256.

From Vyper.L10 Require Import AST Base Callset Descend Expr.

Local Open Scope list_scope.
Local Open Scope string_scope.

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
   | Break    => fun _ => (world, loc, StmtAbort AbortBreak)
   | Continue => fun _ => (world, loc, StmtAbort AbortContinue)
   | Revert   => fun _ => (world, loc, StmtAbort AbortRevert)
   | Return None => fun _ => (world, loc, StmtReturnFromFunction zero256)
   | Return (Some e) => fun E =>
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
                                    | ExprAbort ab => ab
                                    end))
   | Assert cond maybe_e => fun E =>
        let (world', result_cond) := interpret_expr Ebound fc do_call builtins
                                                    world loc cond
                                                    (callset_descend_assert_cond E CallOk)
        in match result_cond with
           | ExprAbort ab => (world', loc, StmtAbort ab)
           | ExprSuccess value =>
              if (Z_of_uint256 value =? 0)%Z
                then match maybe_e as maybe_e' return maybe_e = maybe_e' -> _ with
                     | None => fun _ => (world', loc, StmtAbort (AbortException zero256))
                     | Some e => fun Ee =>
                        let (world'', result_e) :=
                           interpret_expr Ebound fc do_call builtins
                                          world' loc e
                                          (callset_descend_assert_error E Ee CallOk)
                        in match result_e with
                           | ExprSuccess value =>
                                             (world'', loc, StmtAbort (AbortException value))
                           | ExprAbort ab => (world'', loc, StmtAbort ab)
                           end
                     end eq_refl
                else (world', loc, StmtSuccess)
           end
   | Assign lhs rhs => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc rhs
                                               (callset_descend_assign_rhs E CallOk)
        in do_assign world' loc lhs result
   | BinOpAssign lhs op rhs => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc rhs
                                               (callset_descend_binop_assign_rhs E CallOk)
        in do_binop_assign world' loc lhs op result
   | ExprStmt e => fun E =>
                   let (world', result) := 
                      interpret_expr Ebound fc do_call builtins
                                            world loc e
                                            (callset_descend_expr_stmt E CallOk)
                   in (world', loc, match result with
                                    | ExprSuccess a => StmtSuccess
                                    | ExprAbort ab => StmtAbort ab
                                    end)
   end eq_refl.

Lemma interpret_small_stmt_fun_ctx_irrel {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                         (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                         {cd: calldag}
                                         {fc1 fc2: fun_ctx cd bigger_call_depth_bound}
                                         (FcOk: fun_name fc1 = fun_name fc2)
                                         (do_call: forall
                                                       (fc': fun_ctx cd smaller_call_depth_bound)
                                                       (world: world_state)
                                                       (arg_values: list uint256),
                                                     world_state * expr_result uint256)
                                         (builtins: string -> option builtin)
                                         (world: world_state)
                                         (loc: string_map uint256)
                                         (ss: small_stmt)
                                         (CallOk1: let _ := string_set_impl in 
                                                      FSet.is_subset (small_stmt_callset ss)
                                                                     (decl_callset (fun_decl fc1))
                                                      = true)
                                         (CallOk2: let _ := string_set_impl in 
                                                      FSet.is_subset (small_stmt_callset ss)
                                                                     (decl_callset (fun_decl fc2))
                                                      = true):
  interpret_small_stmt Ebound fc1 do_call builtins world loc ss CallOk1
   =
  interpret_small_stmt Ebound fc2 do_call builtins world loc ss CallOk2.
Proof.
revert world loc.
destruct ss; intros; cbn; try easy; try destruct result;
  try destruct_interpret_expr_irrel; trivial;
  try destruct_let_pair.
(* assert *)
destruct e. 2:{ trivial. }
destruct (Z_of_uint256 value =? 0)%Z. 2:{ trivial. }
destruct error. 2:{ trivial. }
destruct_interpret_expr_irrel.
trivial.
Qed.


Local Lemma var_decl_helper {s: stmt} {name init}
                            (NotVarDecl: is_local_var_decl s = false)
                            (E: s = LocalVarDecl name init):
  False.
Proof.
now subst.
Qed.


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
                        (NotVarDecl: is_local_var_decl s = false)
                        (CallOk: let _ := string_set_impl in 
                                 FSet.is_subset (stmt_callset s) 
                                                (decl_callset (fun_decl fc)) = true)
{struct s}
: world_state * string_map uint256 * stmt_result uint256
:= let fix interpret_stmt_list (world: world_state)
                               (loc: string_map uint256)
                               (stmts: list stmt)
                               (CallOk: let _ := string_set_impl in 
                                        FSet.is_subset (stmt_list_callset stmts)
                                                       (decl_callset (fun_decl fc)) = true)
       {struct stmts}
       : world_state * string_map uint256 * stmt_result uint256
       := match stmts as stmts' return stmts = stmts' -> _ with
          | nil => fun _ => (world, loc, StmtSuccess)
          | h :: t => fun E =>
              (if is_local_var_decl h as h_is_var_decl return _ = h_is_var_decl -> _
                 then fun Evar =>
                   let name_init := var_decl_unpack h Evar in
                   let name := fst name_init in
                   let init := snd name_init in
                   match map_lookup loc name with
                   | Some _ => (world, loc, StmtAbort (AbortError "local variable already exists"))
                   | None =>
                       match init as init' return init = init' -> _ with
                       | None => fun _ =>
                           let '(world', loc', result) :=
                             interpret_stmt_list world (map_insert loc name zero256) t
                                                       (callset_descend_stmt_tail E CallOk)
                           in (world', map_remove loc' name, result)
                       | Some init_expr => fun Einit =>
                           let '(world', result) := 
                                  interpret_expr Ebound fc do_call builtins
                                                 world loc init_expr
                                                 (callset_descend_init_expr E Evar Einit CallOk)
                           in match result with
                              | ExprSuccess value =>
                                  let '(world2, loc2, result2) :=
                                    interpret_stmt_list world (map_insert loc name value) t
                                                        (callset_descend_stmt_tail E CallOk)
                                  in (world2, map_remove loc2 name, result2)
                              | ExprAbort ab => (world', loc, StmtAbort ab)
                              end
                       end eq_refl
                   end
                 else fun Evar =>
                   let '(world', loc', result) := 
                     interpret_stmt Ebound fc do_call builtins
                                    world loc h Evar
                                    (callset_descend_stmt_head E CallOk)
                   in match result with
                      | StmtSuccess => interpret_stmt_list world' loc' t
                                                           (callset_descend_stmt_tail E CallOk)
                      | _ => (world', loc', result)
                      end) eq_refl
          end eq_refl
  in match s as s' return s = s' -> _ with
  | SmallStmt ss => fun E => interpret_small_stmt Ebound fc do_call builtins
                                         world loc ss
                                         (callset_descend_small_stmt E CallOk)
  | LocalVarDecl _ _ => fun E => False_rect _ (var_decl_helper NotVarDecl E)
  | IfElseStmt cond yes no => fun E => 
      let (world', result_cond) := interpret_expr
                                     Ebound fc do_call builtins
                                     world loc cond
                                     (callset_descend_stmt_if_cond E CallOk)
      in match result_cond with
         | ExprAbort ab => (world', loc, StmtAbort ab)
         | ExprSuccess cond_value =>
             if (Z_of_uint256 cond_value =? 0)%Z
               then match no as no' return no = no' -> _ with
                    | None => fun _ => (world', loc, StmtSuccess)
                    | Some n => fun Eno =>
                        interpret_stmt_list
                          world' loc n
                          (callset_descend_stmt_if_else E Eno CallOk)
                    end eq_refl
               else interpret_stmt_list world' loc yes
                                        (callset_descend_stmt_if_then E CallOk)
         end
  | FixedRangeLoop var start stop body => fun E =>
     let fix interpret_loop_rec (world: world_state)
                                (loc: string_map uint256)
                                (cursor: Z)
                                (countdown: nat)
          {struct countdown}
          : world_state * string_map uint256 * stmt_result uint256
          := match countdown with
             | O => (world, loc, StmtSuccess)
             | S new_countdown =>
                   let loc' := map_insert loc var (uint256_of_Z cursor) in
                   let '(world', loc'', result) :=
                          interpret_stmt_list world loc' body
                                              (callset_descend_fixed_range_loop_body E CallOk)
                   in match result with
                      | StmtSuccess | StmtAbort AbortContinue =>
                          interpret_loop_rec world' loc''
                                             (Z.succ cursor) new_countdown
                      | StmtAbort AbortBreak => (world', loc'', StmtSuccess)
                      | _ => (world', loc'', result)
                      end
             end
     in let start_z := match start with
                       | Some x => Z_of_uint256 x
                       | None => 0%Z
                       end
     in let stop_z := Z_of_uint256 stop in
     match map_lookup loc var with
     | Some _ => (world, loc, StmtAbort (AbortError "loop var already exists"))
     | None => if (stop_z <=? start_z)%Z
                 then (* ... with STOP being a greater value than START ...
                         https://vyper.readthedocs.io/en/stable/control-structures.html#for-loops
                      *)
                      (world, loc, StmtAbort (AbortError "empty fixed range loop"))
                 else let '(world', loc', result) :=
                             interpret_loop_rec world loc start_z
                                                (Z.to_nat (stop_z - start_z)%Z)
                      in (world', map_remove loc' var, result)
     end
  | FixedCountLoop var start count body => fun E =>
     let fix interpret_loop_rec (world: world_state)  (* almost dup from FixedRangeLoop branch *)
                                (loc: string_map uint256)
                                (cursor: Z)
                                (countdown: nat)
          {struct countdown}
          : world_state * string_map uint256 * stmt_result uint256
          := match countdown with
             | O => (world, loc, StmtSuccess)
             | S new_countdown =>
                   let loc' := map_insert loc var (uint256_of_Z cursor) in
                   let '(world', loc'', result) :=
                          interpret_stmt_list world loc' body
                                              (callset_descend_fixed_count_loop_body E CallOk)
                   in match result with
                      | StmtSuccess | StmtAbort AbortContinue =>
                          interpret_loop_rec world' loc''
                                             (Z.succ cursor) new_countdown
                      | StmtAbort AbortBreak => (world', loc'', StmtSuccess)
                      | _ => (world', loc'', result)
                      end
             end
      in match map_lookup loc var with
         | Some _ => (world, loc, StmtAbort (AbortError "loop var already exists"))
         | None => let (world', result_start) :=
                      interpret_expr Ebound fc do_call builtins
                                     world loc start
                                     (callset_descend_fixed_count_loop_start E CallOk)
                   in match result_start with
                   | ExprAbort ab => (world', loc, StmtAbort ab)
                   | ExprSuccess start_value =>
                       let count_z := Z_of_uint256 count in
                       let count_nat := Z.to_nat count_z in
                       let start_z := Z_of_uint256 start_value in
                       let last := (start_z + count_z - 1)%Z in
                       if (Z_of_uint256 (uint256_of_Z last) =? last)%Z
                         then
                           let '(world', loc', result) :=
                             interpret_loop_rec
                               world' loc start_z count_nat
                           in (world', map_remove loc var, result)
                         else (world, loc, StmtAbort (AbortError "loop range overflows"))
                   end
         end
  end eq_refl.

Fixpoint interpret_stmt_list {bigger_call_depth_bound smaller_call_depth_bound: nat}
                             (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                             {cd: calldag}
                             (fc: fun_ctx cd bigger_call_depth_bound)
                             (do_call: forall
                                          (fc': fun_ctx cd smaller_call_depth_bound)
                                          (world: world_state)
                                          (arg_values: list uint256),
                                        world_state * expr_result uint256)
                             (builtins: string -> option builtin)
                             (world: world_state) (* XXX this is a huge dup from interpret_stmt! *)
                             (loc: string_map uint256)
                             (stmts: list stmt)
                             (CallOk: let _ := string_set_impl in 
                                      FSet.is_subset (stmt_list_callset stmts)
                                                     (decl_callset (fun_decl fc)) = true)
{struct stmts}
: world_state * string_map uint256 * stmt_result uint256
:= match stmts as stmts' return stmts = stmts' -> _ with
   | nil => fun _ => (world, loc, StmtSuccess)
   | h :: t => fun E =>
      (if is_local_var_decl h as h_is_var_decl return _ = h_is_var_decl -> _
         then fun Evar =>
           let name_init := var_decl_unpack h Evar in
           let name := fst name_init in
           let init := snd name_init in
           match map_lookup loc name with
           | Some _ => (world, loc, StmtAbort (AbortError "local variable already exists"))
           | None =>
               match init as init' return init = init' -> _ with
               | None => fun _ =>
                   let '(world', loc', result) :=
                     interpret_stmt_list Ebound fc do_call builtins
                                         world (map_insert loc name zero256) t
                                         (callset_descend_stmt_tail E CallOk)
                   in (world', map_remove loc' name, result)
               | Some init_expr => fun Einit =>
                   let '(world', result) := 
                          interpret_expr Ebound fc do_call builtins
                                         world loc init_expr
                                         (callset_descend_init_expr E Evar Einit CallOk)
                   in match result with
                      | ExprSuccess value =>
                          let '(world2, loc2, result2) :=
                            interpret_stmt_list Ebound fc do_call builtins
                                                world (map_insert loc name value) t
                                                (callset_descend_stmt_tail E CallOk)
                          in (world2, map_remove loc2 name, result2)
                      | ExprAbort ab => (world', loc, StmtAbort ab)
                      end
               end eq_refl
           end
         else fun Evar =>
           let '(world', loc', result) := 
             interpret_stmt Ebound fc do_call builtins
                            world loc h Evar
                            (callset_descend_stmt_head E CallOk)
           in match result with
              | StmtSuccess => interpret_stmt_list Ebound fc do_call builtins
                                                   world' loc' t
                                                   (callset_descend_stmt_tail E CallOk)
              | _ => (world', loc', result)
              end) eq_refl
   end eq_refl.


(*

Lemma interpret_stmt_fun_ctx_irrel {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                   (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                   {cd: calldag}
                                   {fc1 fc2: fun_ctx cd bigger_call_depth_bound}
                                   (FcOk: fun_name fc1 = fun_name fc2)
                                   (do_call: forall
                                                 (fc': fun_ctx cd smaller_call_depth_bound)
                                                 (world: world_state)
                                                 (arg_values: list uint256),
                                               world_state * expr_result uint256)
                                   (builtins: string -> option builtin)
                                   (world: world_state)
                                   (loc: string_map uint256)
                                   (s: stmt)
                                   (NotLocVar: is_local_var_decl s = false)
                                   (CallOk1: let _ := string_set_impl in 
                                                FSet.is_subset (stmt_callset s)
                                                               (decl_callset (fun_decl fc1))
                                                = true)
                                   (CallOk2: let _ := string_set_impl in 
                                                FSet.is_subset (stmt_callset s)
                                                               (decl_callset (fun_decl fc2))
                                                = true):
  interpret_stmt Ebound fc1 do_call builtins world loc s NotLocVar CallOk1
   =
  interpret_stmt Ebound fc2 do_call builtins world loc s NotLocVar CallOk2.
Proof.
*)


End Stmt.