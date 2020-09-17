From Coq Require Import ZArith String.

From Vyper Require Import Config Calldag.
From Vyper Require OpenArray.

From Vyper.L10 Require Import Base.

From Vyper.L30 Require Import AST Callset Descend.

Definition interpret_small_stmt {C: VyperConfig}
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
                                (ss: small_stmt)
                                (CallOk: let _ := string_set_impl in 
                                         FSet.is_subset (small_stmt_callset ss)
                                                        (decl_callset (fun_decl fc))
                                         = true)
: world_state * memory * stmt_result uint256
:= let _ := memory_impl in
   match ss as ss' return ss = ss' -> _ with
   | Pass       => fun _ => (world, loc, StmtSuccess)
   | Abort ab   => fun _ => (world, loc, StmtAbort ab)
   | Return src => fun _ => (world, loc, StmtReturnFromFunction (OpenArray.get loc src))
   | Raise src  => fun _ => (world, loc, StmtAbort (AbortException (OpenArray.get loc src)))
   | Const dst val => fun _ => (world, OpenArray.put loc dst val, StmtSuccess)
   | Copy dst src => fun _ => (world, OpenArray.put loc dst (OpenArray.get loc src), StmtSuccess)
   | StorageGet dst name => fun _ =>
        (world,
         OpenArray.put loc dst
                  (match storage_lookup world name with
                   | Some val => val
                   | None => zero256
                   end),
         StmtSuccess)
   | StoragePut name src => fun _ =>
        (storage_insert world name (OpenArray.get loc src), loc, StmtSuccess)
   | UnOp op dst src => fun _ =>
        match interpret_unop op (OpenArray.get loc src) with
        | ExprSuccess result => (world, OpenArray.put loc dst result, StmtSuccess)
        | ExprAbort ab => (world, loc, StmtAbort ab)
        end
   | BinOp op dst src1 src2 => fun _ =>
        match interpret_binop op (OpenArray.get loc src1) (OpenArray.get loc src2) with
        | ExprSuccess result => (world, OpenArray.put loc dst result, StmtSuccess)
        | ExprAbort ab => (world, loc, StmtAbort ab)
        end
   | PrivateCall dst name args_offset args_count => fun E =>
        match fun_ctx_descend fc CallOk Ebound E with
        | None => (world, loc, StmtAbort (AbortError "can't resolve function name"))
        | Some new_fc => let arg_values := OpenArray.view loc args_offset args_count in
                         let (world', call_result) := do_call new_fc world arg_values in
                         match call_result with
                         | ExprSuccess result =>
                            (world', OpenArray.put loc dst result, StmtSuccess)
                         | ExprAbort ab => (world', loc, StmtAbort ab)
                         end
        end
   | BuiltinCall dst name args_offset args_count => fun _ =>
        let arg_values := OpenArray.view loc args_offset args_count in
        match builtins name with
        | Some (existT _ arity b) => 
            (if (arity =? List.length arg_values)%nat as arity_ok
             return _ = arity_ok -> _
                then fun Earity =>
                  let (world', call_result) := call_builtin arg_values Earity (b world) in
                         match call_result with
                         | ExprSuccess result =>
                            (world', OpenArray.put loc dst result, StmtSuccess)
                         | ExprAbort ab => (world', loc, StmtAbort ab)
                         end
                else fun _ => (world, loc, StmtAbort (AbortError "builtin with wrong arity")))
              eq_refl
        | None => (world, loc, StmtAbort (AbortError "can't resolve function name"))
        end
   end eq_refl.

Fixpoint interpret_stmt {C: VyperConfig}
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
                        (s: stmt)
                        (CallOk: let _ := string_set_impl in 
                                 FSet.is_subset (stmt_callset s)
                                                (decl_callset (fun_decl fc)) = true)
 {struct s}
 : world_state * memory * stmt_result uint256
 := let _ := memory_impl in
    match s as s' return s = s' -> _ with
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
    | IfElseStmt cond yes no => fun E =>
        if (Z_of_uint256 (OpenArray.get loc cond) =? 0)%Z
             then interpret_stmt Ebound fc do_call builtins
                                 world loc no
                                 (callset_descend_stmt_if_else E CallOk)
             else interpret_stmt Ebound fc do_call builtins
                                 world loc yes
                                 (callset_descend_stmt_if_then E CallOk)
    | Loop var count body => fun E =>
        if (Z_of_uint256 count =? 0)%Z
          then (world, loc, StmtAbort (AbortError "empty loop not allowed"))
          else  let fix interpret_loop_rec (world: world_state)
                                           (loc: memory)
                                           (cursor: Z)
                                           (countdown: nat)
                                           (var: N)
                                           (CallOk: let _ := string_set_impl in 
                                                    FSet.is_subset (stmt_callset body)
                                                                   (decl_callset (fun_decl fc)) = true)
                   {struct countdown}
                   : world_state * memory * stmt_result uint256
                   := match countdown with
                      | O => (world, loc, StmtSuccess)
                      | S new_countdown =>
                            let loc' := OpenArray.put loc var (uint256_of_Z cursor) in
                            let '(world', loc'', result) :=
                                  interpret_stmt Ebound fc do_call builtins world loc' body CallOk
                            in match result with
                               | StmtSuccess | StmtAbort AbortContinue =>
                                   interpret_loop_rec world' loc''
                                                      (Z.succ cursor) new_countdown var CallOk
                               | StmtAbort AbortBreak =>
                                   (world', loc'', StmtSuccess)
                               | _ => (world', loc'', result)
                               end
                      end
                 in let count_z := Z_of_uint256 count in
                     let count_nat := Z.to_nat count_z in
                     let start_z := Z_of_uint256 (OpenArray.get loc var) in
                     let last := (start_z + count_z - 1)%Z in
                     if (Z_of_uint256 (uint256_of_Z last) =? last)%Z
                       then interpret_loop_rec
                                     world loc start_z count_nat var
                                     (callset_descend_loop_body E CallOk)
                       else (world, loc, StmtAbort (AbortError "loop range overflows"))
    end eq_refl.