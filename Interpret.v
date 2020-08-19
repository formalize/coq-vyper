From Coq Require Import String Arith NArith ZArith.
Require Import Config UntypedAST Callset.
Require FSet Map UInt256.

Local Open Scope list_scope.
Local Open Scope string_scope.

Section Interpret.

Context {C: VyperConfig}.

Inductive abort
:= AbortError (msg: string)
 | AbortException (data: uint256)
 | AbortBreak
 | AbortContinue
 | AbortReturnFromContract
 | AbortRevert.

Inductive expr_result (type: Type)
:= ExprSuccess (value: type)
 | ExprAbort (a: abort).
Arguments ExprSuccess {type}.
Arguments ExprAbort {type}.

Inductive stmt_result (return_type: Type)
:= StmtSuccess
 | StmtAbort (a: abort)
 | StmtReturnFromFunction (value: return_type).
Arguments StmtSuccess {_}.
Arguments StmtAbort {_}.
Arguments StmtReturnFromFunction {_}.

Definition expr_error {type: Type} (msg: string) := @ExprAbort type (AbortError msg).

Definition interpret_unop (op: unop) (a: uint256)
: expr_result uint256
:= match UInt256.interpret_unop op a with
   | Some result => ExprSuccess result
   | None => expr_error "arithmetic error"
   end.

Definition interpret_binop (op: binop) (a b: uint256)
: expr_result uint256
:= match UInt256.interpret_binop op a b with
   | Some result => ExprSuccess result
   | None => expr_error "arithmetic error"
   end.

Record calldag := {
  cd_declmap:  string -> option decl;
  cd_depthmap: string -> option nat;
  cd_depthmap_ok:
    forall name: string,
      match cd_declmap name with
      | None => True
      | Some decl =>
          match cd_depthmap name with
          | None => False
          | Some x =>
              let _ := string_set_impl in
              FSet.for_all (decl_callset decl)
                           (fun callee => match cd_depthmap callee with
                                          | None => false
                                          | Some y => y <? x
                                          end)
               = true
            end
      end;
}.

(** Initialize a map of local variables with argument names and argument values. *)
Fixpoint bind_args (names: list string) (values: list uint256)
: string + string_map uint256
:= let _ := string_map_impl in
   match names with
   | nil => match values with
            | nil => inr Map.empty
            | _ => inl "function called with too many arguments"
            end
   | hn :: tn => match values with
                 | nil => inl "function called with too few arguments"
                 | hv :: tv =>
                     match bind_args tn tv with
                     | inl err => inl err
                     | inr bindings =>
                        match Map.lookup bindings hn with
                        | Some _ => inl "error: duplicate variable name"
                        | None => inr (Map.insert bindings hn hv)
                        end
                     end
                 end
   end.

Local Lemma interpret_call_helper {this_decl: decl}
                                  {fun_name: string}
                                  {arg_names: list string}
                                  {body: small_stmt} (* list stmt *)
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let _ := string_set_impl in FSet.is_subset (small_stmt_callset body) (decl_callset this_decl) = true.
Proof.
subst this_decl. unfold decl_callset. apply FSet.is_subset_refl.
Qed.

Lemma call_descend {call_depth_bound new_call_depth_bound current_fun_depth: nat}
                   (DepthOk : current_fun_depth < call_depth_bound)
                   (cd : calldag)
                   (this_fun_name: string)
                   (this_decl: decl)
                   (this_decl_ok: cd_declmap cd this_fun_name = Some this_decl)
                   (current_fun_depth_ok:
                     cd_depthmap cd this_fun_name = Some current_fun_depth)
                   (e: expr)
                   (CallOk : let _ := string_set_impl in
                             FSet.is_subset (expr_callset e) (decl_callset this_decl) = true)
                   (Ebound : call_depth_bound = S new_call_depth_bound)
                   (name : string)
                   (args : list expr)
                   (E : e = PrivateOrBuiltinCall name args)
                   {depth: nat}
                   (Edepth: cd_depthmap cd name = Some depth):
  depth < new_call_depth_bound.
Proof.
subst e. cbn in CallOk.
assert(HasName: let _ := string_set_impl in FSet.has (decl_callset this_decl) name = true).
{
  cbn.
  apply (FSet.is_subset_if CallOk name).
  apply FSet.add_has.
}
clear CallOk. cbn in HasName.
assert (K := cd_depthmap_ok cd this_fun_name).
rewrite this_decl_ok in K.
rewrite current_fun_depth_ok in K.
cbn in K.
rewrite FSet.for_all_ok in K.
assert (L := K name HasName). clear K.
subst call_depth_bound.
apply lt_n_Sm_le in DepthOk.
rewrite Edepth in L.
destruct current_fun_depth. { discriminate. }
rewrite Nat.leb_le in L.
rewrite Nat.le_succ_l in DepthOk.
apply (Nat.le_lt_trans _ _ _ L DepthOk).
Qed.

Record fun_ctx (cd: calldag) (bound: nat) := {
  fun_name: string;
  fun_depth: nat;
  fun_depth_ok: cd_depthmap cd fun_name = Some fun_depth;
  fun_decl: decl;
  fun_decl_ok: cd_declmap cd fun_name = Some fun_decl;
  fun_bound_ok: fun_depth < bound;
}.
Arguments fun_name     {_ _}.
Arguments fun_depth    {_ _}.
Arguments fun_depth_ok {_ _}.
Arguments fun_decl     {_ _}.
Arguments fun_decl_ok  {_ _}.
Arguments fun_bound_ok {_ _}.

Local Lemma fun_ctx_descend_helper {cd: calldag}
                                   {name: string}
                                   {d: decl}
                                   (Edecl : cd_declmap cd name = Some d):
  cd_depthmap cd name <> None.
Proof.
assert (D := cd_depthmap_ok cd name).
rewrite Edecl in D.
intro H.
rewrite H in D.
exact D.
Qed.

(** Make a callee context from a caller context and a call expression, 
  The None result means that no declaration with the given name is found.
  No check is made that the callee context is indeed a function.
  The max stack depth bound is reduced by 1.
 *)
Definition fun_ctx_descend {call_depth_bound new_call_depth_bound}
                           {cd: calldag}
                           {e: expr}
                           {name: string}
                           {args: list expr}

                           (fc: fun_ctx cd call_depth_bound)
                           (CallOk: let _ := string_set_impl in
                                       FSet.is_subset (expr_callset e)
                                                      (decl_callset (fun_decl fc))
                                        = true)
                           (Ebound: call_depth_bound = S new_call_depth_bound)
                           (E: e = PrivateOrBuiltinCall name args)
: option (fun_ctx cd new_call_depth_bound)
:= match cd_declmap cd name as maybe_decl return _ = maybe_decl -> _ with
   | None => fun _ =>
       (* no declaration found - could be a builtin *)
       None
   | Some d => fun Edecl =>
       match cd_depthmap cd name as maybe_depth return _ = maybe_depth -> _ with
       | None => fun Edepth => False_rect _ (fun_ctx_descend_helper Edecl Edepth)
       | Some depth => fun Edepth =>
           Some {| fun_name := name
                 ; fun_depth := depth
                 ; fun_depth_ok := Edepth
                 ; fun_decl := d
                 ; fun_decl_ok := Edecl
                 ; fun_bound_ok := call_descend (fun_bound_ok fc) cd (fun_name fc)
                                                (fun_decl fc) (fun_decl_ok fc)
                                                (fun_depth_ok fc) e CallOk Ebound 
                                                name args E Edepth
                |}
       end eq_refl
   end eq_refl.

(*************************************************************************************************)

Definition do_assign {return_type: Type} 
                     (world: world_state) (loc: string_map uint256)
                     (lhs: assignable)
                     (computed_rhs: expr_result uint256)
: world_state * string_map uint256 * stmt_result return_type
:= let _ := string_map_impl in
   match computed_rhs with
   | ExprAbort ab => (world, loc, StmtAbort ab)
   | ExprSuccess a =>
       match lhs with
       | AssignableLocalVar name =>
           match Map.lookup loc name with
           | None => (world, loc, StmtAbort (AbortError "undeclared local variable"))
           | Some _ => (world, Map.insert loc name a, StmtSuccess)
           end
       | AssignableStorageVar name =>
           match storage_lookup world name with
           | None => (world, loc, StmtAbort (AbortError "undeclared global variable"))
           | Some _ => (storage_insert world name a, loc, StmtSuccess)
           end
       end
   end.

Definition do_binop_assign {return_type: Type} 
                           (world: world_state) (loc: string_map uint256)
                           (lhs: assignable)
                           (op: binop)
                           (computed_rhs: expr_result uint256)
: world_state * string_map uint256 * stmt_result return_type
:= let _ := string_map_impl in
   match computed_rhs with
   | ExprAbort ab => (world, loc, StmtAbort ab)
   | ExprSuccess a =>
       match lhs with
       | AssignableLocalVar name =>
           match Map.lookup loc name with
           | None => (world, loc, StmtAbort (AbortError "undeclared local variable"))
           | Some old_val =>
                match interpret_binop op old_val a with
                | ExprSuccess new_val => (world, Map.insert loc name new_val, StmtSuccess)
                | ExprAbort ab => (world, loc, StmtAbort ab)
                end
           end
       | AssignableStorageVar name =>
           match storage_lookup world name with
           | None => (world, loc, StmtAbort (AbortError "undeclared global variable"))
           | Some old_val =>
                match interpret_binop op old_val a with
                | ExprSuccess new_val => (storage_insert world name new_val, loc, StmtSuccess)
                | ExprAbort ab => (world, loc, StmtAbort ab)
                end
           end
       end
   end.

Definition map_lookup {Value} (m: string_map Value) := let _ := string_map_impl in Map.lookup m.
Definition map_insert {Value} (m: string_map Value) := let _ := string_map_impl in Map.insert m.
Definition map_remove {Value} (m: string_map Value) := let _ := string_map_impl in Map.remove m.

Local Lemma var_decl_helper {s: stmt} {name init}
                            (NotVarDecl: is_local_var_decl s = false)
                            (E: s = LocalVarDecl name init):
  False.
Proof.
now subst.
Qed.

Fixpoint interpret_call {call_depth_bound: nat}
                        {cd: calldag}
                        (fc: fun_ctx cd call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256)
{struct call_depth_bound}
: world_state * expr_result uint256
:= let interpret_expr 
   := fix interpret_expr
         (world: world_state)
         (loc: string_map uint256)
         (e: expr)
         (CallOk: let _ := string_set_impl in 
                  FSet.is_subset (expr_callset e) (decl_callset (fun_decl fc)) = true)
      {struct e}
      : world_state * expr_result uint256
      := let interpret_expr_list
         := fix interpret_expr_list (world: world_state)
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
                   let (world', result_h) := interpret_expr world loc h
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
         in match call_depth_bound as call_depth_bound' return _ = call_depth_bound' -> _ with
            | O => fun Ebound => False_rect _ (Nat.nlt_0_r (fun_depth fc)
                                                           (eq_ind _ _ (fun_bound_ok fc) _ Ebound))
            | S new_call_depth_bound => fun Ebound =>

                 match e as e' return e = e' -> _ with
                 | Const val => fun _ => (world, ExprSuccess val)
                 | LocalVar name => fun _ =>
                     (world, match map_lookup loc name with
                             | Some val => ExprSuccess val
                             | None => expr_error "Local variable not found"
                             end)
                 | StorageVar name => fun _ => 
                     (world, match storage_lookup world name with
                             | Some val => ExprSuccess val
                             | None => expr_error "Storage variable not found"
                             end)
                 | UnOp op a => fun E =>
                     let (world', result) := interpret_expr world loc a
                                                            (callset_descend_unop E CallOk)
                     in (world', match result with
                                 | ExprSuccess val => interpret_unop op val
                                 | ExprAbort _ => result
                                 end)
                 | BinOp op a b => fun E =>
                     let (world', result_a) := interpret_expr world loc a
                                                              (callset_descend_binop_left E CallOk)
                     in match result_a with
                     | ExprAbort _ => (world', result_a)
                     | ExprSuccess x =>
                       let (world'', result_b) := interpret_expr world' loc b
                                                                 (callset_descend_binop_right E CallOk)
                       in (world'', match result_b with
                                    | ExprAbort _ => result_b
                                    | ExprSuccess y => interpret_binop op x y
                                    end)
                     end
                 | IfThenElse cond yes no => fun E =>
                     let (world', result_cond) := interpret_expr world loc cond
                                                                 (callset_descend_if_cond E CallOk)
                     in match result_cond with
                        | ExprAbort _ => (world', result_cond)
                        | ExprSuccess cond_value =>
                            if (Z_of_uint256 cond_value =? 0)%Z
                              then interpret_expr world' loc no
                                                  (callset_descend_if_else E CallOk)
                              else interpret_expr world' loc yes
                                                  (callset_descend_if_then E CallOk)
                        end
                 | LogicalAnd a b => fun E =>
                     let (world', result_a) := interpret_expr world loc a
                                                              (callset_descend_and_left E CallOk)
                     in match result_a with
                        | ExprAbort _ => (world', result_a)
                        | ExprSuccess a_value =>
                            if (Z_of_uint256 a_value =? 0)%Z
                              then (world', result_a)
                              else interpret_expr world' loc b
                                                  (callset_descend_and_right E CallOk)
                        end
                 | LogicalOr a b => fun E =>
                     let (world', result_a) := interpret_expr world loc a
                                                              (callset_descend_or_left E CallOk)
                     in match result_a with
                        | ExprAbort msg => (world', result_a)
                        | ExprSuccess a_value =>
                            if (Z_of_uint256 a_value =? 0)%Z
                              then interpret_expr world' loc b
                                                  (callset_descend_or_right E CallOk)
                              else (world', result_a)
                        end
                 | PrivateOrBuiltinCall name args => fun E =>
                     let (world', result_args) :=
                       interpret_expr_list world loc args
                                           (callset_descend_args E CallOk)
                     in match result_args with
                        | ExprAbort ab => (world', ExprAbort ab)
                        | ExprSuccess arg_values =>
                            match fun_ctx_descend fc CallOk Ebound E with
                            | None => (* can't resolve the function, maybe it's a builtin *)
                                      (world', expr_error "can't resolve function name")
                            | Some new_fc => interpret_call new_fc world' arg_values
                            end
                        end
                 end eq_refl
         end eq_refl
     in let interpret_small_stmt (world: world_state)
                                 (loc: string_map uint256)
                                 (s: small_stmt)
                                 (CallOk: let _ := string_set_impl in 
                                          FSet.is_subset (small_stmt_callset s)
                                                         (decl_callset (fun_decl fc))
                                           =
                                          true)
        : world_state * string_map uint256 * stmt_result uint256
        := match s as s' return s = s' -> _ with
           | Pass     => fun _ => (world, loc, StmtSuccess)
           | Break    => fun _ => (world, loc, StmtAbort AbortBreak)
           | Continue => fun _ => (world, loc, StmtAbort AbortContinue)
           | Revert   => fun _ => (world, loc, StmtAbort AbortRevert)
           | Return None => fun _ => (world, loc, StmtReturnFromFunction zero256)
           | Return (Some e) => fun E =>
                let (world', result) := interpret_expr world loc e
                                                       (callset_descend_return E CallOk)
                in (world', loc, match result with
                                 | ExprSuccess value => StmtReturnFromFunction value
                                 | ExprAbort ab => StmtAbort ab
                                 end)
           | Raise e => fun E =>
                let (world', result) := interpret_expr world loc e
                                                       (callset_descend_raise E CallOk)
                in (world', loc, StmtAbort (match result with
                                            | ExprSuccess value => AbortException value
                                            | ExprAbort ab => ab
                                            end))
           | Assert cond maybe_e => fun E =>
                let (world', result_cond) := interpret_expr world loc cond
                                                            (callset_descend_assert_cond E CallOk)
                in match result_cond with
                   | ExprAbort ab => (world', loc, StmtAbort ab)
                   | ExprSuccess value =>
                      if (Z_of_uint256 value =? 0)%Z
                        then match maybe_e as maybe_e' return maybe_e = maybe_e' -> _ with
                             | None => fun _ => (world', loc, StmtAbort (AbortException zero256))
                             | Some e => fun Ee =>
                                let (world'', result_e) := interpret_expr world loc e
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
                let (world', result) := interpret_expr world loc rhs
                                                       (callset_descend_assign_rhs E CallOk)
                in do_assign world' loc lhs result
           | BinOpAssign lhs op rhs => fun E =>
                let (world', result) := interpret_expr world loc rhs
                                        (callset_descend_binop_assign_rhs E CallOk)
                in do_binop_assign world' loc lhs op result
           | ExprStmt e => fun E =>
                           let (world', result) := interpret_expr world loc e
                                                   (callset_descend_expr_stmt E CallOk)
                           in (world', loc, match result with
                                            | ExprSuccess a => StmtSuccess
                                            | ExprAbort ab => StmtAbort ab
                                            end)
           end eq_refl
     in let interpret_stmt
        := fix interpret_stmt (world: world_state)
                              (loc: string_map uint256)
                              (s: stmt)
                              (NotVarDecl: is_local_var_decl s = false)
                              (CallOk: let _ := string_set_impl in 
                                       FSet.is_subset (stmt_callset s) 
                                                      (decl_callset (fun_decl fc)) = true)
           {struct s}
           : world_state * string_map uint256 * stmt_result uint256
           := let interpret_stmt_list
              := fix interpret_stmt_list (world: world_state)
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
                                            interpret_expr world loc init_expr
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
                               interpret_stmt world loc h Evar
                                                    (callset_descend_stmt_head E CallOk)
                             in match result with
                                | StmtSuccess => interpret_stmt_list world' loc' t
                                                                     (callset_descend_stmt_tail E CallOk)
                                | _ => (world', loc', result)
                                end) eq_refl
                    end eq_refl
          in let interpret_loop_rec
             :=  fix interpret_loop_rec (world: world_state)
                                        (loc: string_map uint256)
                                        (body: list stmt)
                                        (cursor: Z)
                                        (countdown: nat)
                                        (name: string)
                                        (CallOk: let _ := string_set_impl in 
                                                 FSet.is_subset (stmt_list_callset body)
                                                                (decl_callset (fun_decl fc)) = true)
                  {struct countdown}
                  : world_state * string_map uint256 * stmt_result uint256
                  := match countdown with
                     | O => (world, loc, StmtSuccess)
                     | S new_countdown =>
                           let loc' := map_insert loc name (uint256_of_Z cursor) in
                           let '(world', loc'', result) := interpret_stmt_list world loc' body CallOk
                           in match result with
                              | StmtSuccess | StmtAbort AbortContinue =>
                                  interpret_loop_rec world' loc'' body
                                                     (Z.succ cursor) new_countdown name CallOk
                              | StmtAbort AbortBreak => (world', loc'', StmtSuccess)
                              | _ => (world', loc'', result)
                              end
                     end
           in let interpret_loop (world: world_state)
                                 (loc: string_map uint256)
                                 (body: list stmt)
                                 (start: uint256)
                                 (stop: Z)
                                 (name: string)
                                 (CallOk: let _ := string_set_impl in 
                                          FSet.is_subset (stmt_list_callset body)
                                                         (decl_callset (fun_decl fc)) = true)
                 : world_state * string_map uint256 * stmt_result uint256
                 := match map_lookup loc name with
                    | Some _ => (world, loc, StmtAbort (AbortError "loop var already exists"))
                    | None => if (Z_of_uint256 (uint256_of_Z stop) =? stop)%Z
                                then let cursor := Z_of_uint256 start in
                                     if (cursor <? stop)%Z
                                       then let '(world', loc', result) :=
                                                   interpret_loop_rec world loc body cursor
                                                                      (Z.to_nat (stop - cursor)%Z)
                                                                      name CallOk
                                            in (world', map_remove loc' name, result)
                                       else (world, loc, StmtSuccess)
                                else (world, loc, StmtAbort (AbortError "loop range overflows"))
                    end
          in match s as s' return s = s' -> _ with
          | SmallStmt ss => fun E => interpret_small_stmt world loc ss
                                                 (callset_descend_small_stmt E CallOk)
          | LocalVarDecl _ _ => fun E => False_rect _ (var_decl_helper NotVarDecl E)
          | IfElseStmt cond yes no => fun E => 
              let (world', result_cond) := interpret_expr
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
       (*   | FixedRangeLoop var start stop fr_body => fun E =>
              interpret_loop world loc fr_body (match start with
                                                | Some x => x
                                                | None => zero256
                                                end)
                             (Z_of_uint256 stop) var
                             (callset_descend_fixed_range_loop_body E CallOk)
          | FixedCountLoop var start count fc_body => fun E =>
              let (world', result_start) :=
                    interpret_expr world loc start
                                   (callset_descend_fixed_count_loop_start E CallOk)
              in match result_start with
                 | ExprAbort ab => (world', loc, StmtAbort ab)
                 | ExprSuccess start_value =>
                      interpret_loop world' loc fc_body start_value
                             (Z_of_uint256 start_value + Z_of_uint256 count)%Z
                             var (callset_descend_fixed_count_loop_body E CallOk)
                 end *)
          end eq_refl
   in match fun_decl fc as d return _ = d -> _ with
      | FunDecl _ arg_names body => fun E =>
          match bind_args arg_names arg_values with
          | inl err => (world, expr_error err)
          | inr loc =>
              let '(world', loc', result) := interpret_small_stmt world loc body 
                                                                  (interpret_call_helper E)
              in (world', match result with
                          | StmtSuccess => ExprSuccess zero256
                          | StmtReturnFromFunction x => ExprSuccess x
                          | StmtAbort a => ExprAbort a
                          end)
          end
      | _ => fun _ => (world, expr_error "a declaration is found but it's not a function")
      end eq_refl.

Local Lemma make_fun_ctx_helper {cd: calldag}
                          {name: string}
                          {d : decl}
                          (Ed : cd_declmap cd name = Some d)
                          (Edepth : cd_depthmap cd name = None):
  False.
Proof.
assert (W := cd_depthmap_ok cd name).
rewrite Ed in W. rewrite Edepth in W. exact W.
Qed.

Definition make_fun_ctx_and_bound (cd: calldag)
                                  (name: string)
: option { bound: nat & fun_ctx cd bound }
:= match cd_declmap cd name as maybe_d return _ = maybe_d -> _ with
   | None => fun _ => None
   | Some d => fun Ed =>
      match cd_depthmap cd name as depth' return _ = depth' -> _ with
      | None => fun Edepth => False_rect _ (make_fun_ctx_helper Ed Edepth)
      | Some depth => fun Edepth => Some (existT _
                                                 (S depth)
                                                 {| fun_name := name
                                                  ; fun_decl := d
                                                  ; fun_decl_ok := Ed
                                                  ; fun_depth := depth
                                                  ; fun_depth_ok := Edepth
                                                  ; fun_bound_ok := Nat.lt_succ_diag_r _
                                                 |})
      end eq_refl
   end eq_refl.

(** This is a simplified interface to interpret_call that takes care of creating a function context. *)
Definition interpret (cd: calldag)
                     (function_name: string)
                     (world: world_state)
                     (arg_values: list uint256)
: world_state * expr_result uint256
:= match make_fun_ctx_and_bound cd function_name with
   | None => (world, expr_error "declaration not found")
   | Some (existT _ bound fc) => interpret_call fc world arg_values
   end.

End Interpret.