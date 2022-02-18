From Coq Require Import String Arith ZArith.

From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require Import AST Descend Expr Stmt.

(** This is an alternative interpreter for L40 that does away with all the CallOk crap
   and treats running out of max call depth as a special exception.
 *)

Fixpoint interpret_expr_metered {C: VyperConfig}
                                (decls: string_map L40.AST.decl)
                                (do_call: forall
                                              (decl: L40.AST.decl)
                                              (world: world_state)
                                              (arg_values: list uint256),
                                            world_state * option (expr_result uint256))
                                (builtins: string -> option builtin)
                                (world: world_state)
                                (loc: memory)
                                (loops: list loop_ctx)
                                (e: expr)
{struct e}
: world_state * option (expr_result uint256)
:= let fix interpret_expr_list (world: world_state)
                               (loc: memory)
                               (e: list expr)
      {struct e}
      : world_state * option (expr_result (list uint256))
      := match e as e' return e = e' -> _ with
         | nil => fun _ => (world, Some (ExprSuccess nil))
         | (h :: t)%list => fun E =>
             (* right-to-left evaluation order *)
             let (world', result_t) := interpret_expr_list world loc t
             in match result_t with
                | Some (ExprSuccess values_t) =>
                   let (world'', result_h) :=
                          interpret_expr_metered decls do_call builtins
                                                 world' loc loops h
                   in (world'', match result_h with
                                | Some (ExprSuccess value_h) =>
                                    Some (ExprSuccess (value_h :: values_t)%list)
                                | Some (ExprAbort ab) => Some (ExprAbort ab)
                                | None => None
                                end)
                | _ => (world', result_t)
                end
         end eq_refl
    in match e as e' return e = e' -> _ with
       | Const val => fun _ => (world, Some (ExprSuccess val))
       | LocalVar index => fun _ =>
           let _ := memory_impl in
           (world, Some (ExprSuccess (OpenArray.get loc index)))
       | LoopOffset => fun _ =>
           (world, Some (match loops with
                         | (loop :: _)%list => ExprSuccess (loop_offset loop)
                         | nil => expr_error "loop index higher than the nesting level"
                         end))
       | LoopCursor => fun _ =>
           (world, Some (match loops with
                         | (loop :: _)%list => 
                            ExprSuccess (uint256_of_Z (Z_of_uint256 (loop_count loop) - 1 -
                                                         Z.of_nat (loop_countdown loop)))%Z
                         | nil => expr_error "loop index higher than the nesting level"
                         end))
       | PrivateCall name args => fun E =>
           match map_lookup decls name with
           | None => (* can't resolve the function, maybe it's a builtin *)
                     (world, Some (expr_error "can't resolve function name"))
           | Some decl =>
               let (world', result_args) :=
                 interpret_expr_list world loc args
               in match result_args with
                  | Some (ExprSuccess arg_values) => do_call decl world' arg_values
                  | Some (ExprAbort ab) => (world', Some (ExprAbort ab))
                  | None => (world', None)
                  end
           end
       | BuiltinCall name args => fun E =>
           let (world', result_args) :=
             interpret_expr_list world loc args
           in match result_args with
              | Some (ExprSuccess arg_values) =>
                match builtins name with
                | Some (existT _ arity b) =>
                   (if (arity =? List.length arg_values)%nat as arity_ok
                    return _ = arity_ok -> _
                        then fun Earity =>
                               let '(world'', result) := 
                                      call_builtin arg_values Earity (b world')
                               in (world'', Some result)
                        else fun _ => (world', Some (expr_error "builtin with wrong arity")))
                      eq_refl
                | None => (world', Some (expr_error "can't resolve function name"))
                end
              | Some (ExprAbort ab) => (world', Some (ExprAbort ab))
              | None => (world', None)
              end
       end eq_refl.



Definition interpret_small_stmt_metered {C: VyperConfig}
                                        (decls: string_map L40.AST.decl)
                                        (do_call: forall
                                                      (decl: L40.AST.decl)
                                                      (world: world_state)
                                                      (arg_values: list uint256),
                                                    world_state * option (expr_result uint256))
                                        (builtins: string -> option builtin)
                                        (world: world_state)
                                        (loc: memory)
                                        (loops: list loop_ctx)
                                        (ss: small_stmt)
: world_state * memory * option (stmt_result uint256)
:= match ss as ss' return ss = ss' -> _ with
   | Abort ab => fun _ => (world, loc, Some (StmtAbort ab))
   | Return e => fun E =>
        let (world', result) := interpret_expr_metered decls do_call builtins
                                                       world loc loops e
        in (world', loc, match result with
                         | Some (ExprSuccess value) => Some (StmtReturnFromFunction value)
                         | Some (ExprAbort ab) => Some (StmtAbort ab)
                         | None => None
                         end)
   | Raise e => fun E =>
        let (world', result) := interpret_expr_metered decls do_call builtins
                                                       world loc loops e
        in (world', loc, (match result with
                          | Some (ExprSuccess value) => Some (StmtAbort (AbortException value))
                          | Some (ExprAbort ab)      => Some (StmtAbort ab)
                          | None => None
                          end))
   | Assign lhs rhs => fun E =>
         let (world', result) := interpret_expr_metered decls do_call builtins
                                                       world loc loops rhs
        in let _ := memory_impl
        in match result with
           | Some (ExprSuccess value) => (world', OpenArray.put loc lhs value, Some StmtSuccess)
           | Some (ExprAbort ab) => (world', loc, Some (StmtAbort ab))
           | None => (world', loc, None)
           end
   | ExprStmt e => fun E =>
                   let (world', result) := interpret_expr_metered decls do_call builtins
                                                                  world loc loops e
                   in (world', loc, match result with
                                    | Some (ExprSuccess a) => Some StmtSuccess
                                    | Some (ExprAbort ab) => Some (StmtAbort ab)
                                    | None => None
                                    end)
   end eq_refl.


Fixpoint interpret_stmt_metered {C: VyperConfig}
                                (decls: string_map L40.AST.decl)
                                (do_call: forall
                                              (decl: L40.AST.decl)
                                              (world: world_state)
                                              (arg_values: list uint256),
                                            world_state * option (expr_result uint256))
                                (builtins: string -> option builtin)
                                (world: world_state)
                                (loc: memory)
                                (loops: list loop_ctx)
                                (s: stmt)
{struct s}
: world_state * memory * option (stmt_result uint256)
:= match s as s' return s = s' -> _ with
   | SmallStmt ss => fun E => interpret_small_stmt_metered decls do_call builtins
                                                           world loc loops ss
   | Switch e cases default => fun E =>
       let (world', result) := interpret_expr_metered decls do_call builtins
                                                      world loc loops e
       in match result with
          | None => (world', loc, None)
          | Some (ExprAbort ab) => (world', loc, Some (StmtAbort ab))
          | Some (ExprSuccess value) =>
              (fix dispatch (l: list case)
               : world_state * memory * option (stmt_result uint256)
               := match l  with
                  | cons (Case guard block) t =>
                      if (Z_of_uint256 value =? Z_of_uint256 guard)%Z
                        then interpret_block_metered decls do_call builtins
                                                     world' loc loops block
                        else dispatch t
                  | nil => match default with
                           | Some block =>
                                interpret_block_metered decls do_call builtins
                                                        world' loc loops block
                           | None => (world', loc, Some StmtSuccess)
                           end
                  end) cases
          end
   | Loop var count body => fun E =>
              let _ := memory_impl in
              let offset := OpenArray.get loc var in
              let fix do_loop (world: world_state)
                              (loc: memory)
                              (countdown: nat)
              {struct countdown}
              := match countdown with
                 | O => (world, loc, Some StmtSuccess)
                 | S k =>
                     let '(world', loc', result)
                     := interpret_block_metered decls do_call builtins
                                                world loc
                                                ({| loop_offset := let _ := memory_impl in offset
                                                  ; loop_count := count
                                                  ; loop_countdown := k
                                                 |} :: loops)%list
                                                body
                     in match result with
                        | Some StmtSuccess | Some (StmtAbort AbortContinue) => do_loop world' loc' k
                        | Some (StmtAbort AbortBreak) => (world', loc', Some StmtSuccess)
                        | _ => (world', loc', result)
                        end
                 end
              in do_loop world loc (Z.to_nat (Z_of_uint256 count))
   end eq_refl
with interpret_block_metered {C: VyperConfig}
                             (decls: string_map L40.AST.decl)
                             (do_call: forall
                                           (decl: L40.AST.decl)
                                           (world: world_state)
                                           (arg_values: list uint256),
                                         world_state * option (expr_result uint256))
                             (builtins: string -> option builtin)
                             (world: world_state)
                             (loc: memory)
                             (loops: list loop_ctx)
                             (b: block)
: world_state * memory * option (stmt_result uint256)
:= match b as b' return b = b' -> _ with
   | Block stmts => fun Eb =>
      (fix interpret_stmt_list_metered (world: world_state)
                                       (loc: memory)
                                       (loops: list loop_ctx)
                                       (l: list stmt)
       {struct l}
       : world_state * memory * option (stmt_result uint256)
       := match l as l' return l = l' -> _ with
          | nil => fun _ => (world, loc, Some StmtSuccess)
          | cons h t => fun El =>
              let '(world', loc', result) := interpret_stmt_metered decls do_call builtins
                                                                    world loc loops h
              in match result with
                 | Some StmtSuccess => interpret_stmt_list_metered world' loc' loops t
                 | _ => (world', loc', result)
                 end
          end eq_refl) world loc loops stmts
   end eq_refl.



Fixpoint interpret_call_metered {C: VyperConfig}
                                (max_call_depth: nat)
                                (decls: string_map L40.AST.decl)
                                (builtins: string -> option builtin)
                                (d: L40.AST.decl)
                                (world: world_state)
                                (arg_values: list uint256)
{struct max_call_depth}
: world_state * option (expr_result uint256)
:= let _ := memory_impl in
   match max_call_depth with
   | O => (world, None)
   | S new_max_call_depth =>
        let '(FunDecl _ arity body) := d in
            if (List.length arg_values =? N.to_nat arity)%nat
              then let loc := OpenArray.from_list arg_values in
                   let '(world', loc', result) 
                        := interpret_block_metered 
                            decls
                            (interpret_call_metered new_max_call_depth decls builtins)
                            builtins world loc nil body
                   in (world', match result with
                               | Some StmtSuccess => Some (ExprSuccess zero256)
                               | Some (StmtReturnFromFunction x) => Some (ExprSuccess x)
                               | Some (StmtAbort a) => Some (ExprAbort a)
                               | None => None
                               end)
              else (world, Some (expr_error
                            (if (List.length arg_values <? N.to_nat arity)%nat
                               then "function called with too few arguments"
                               else "function called with too many arguments")))
   end.

Definition interpret_metered {C: VyperConfig}
                             (max_call_depth: nat)
                             (decls: string_map L40.AST.decl)
                             (builtins: string -> option builtin)
                             (fun_name: string)
                             (world: world_state)
                             (arg_values: list uint256)
: world_state * option (expr_result uint256)
:= match map_lookup decls fun_name with
   | Some d => interpret_call_metered max_call_depth decls builtins d world arg_values
   | None => (world, Some (expr_error "declaration not found"))
   end.
