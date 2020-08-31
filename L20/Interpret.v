From Coq Require Import String Arith NArith ZArith.
From Vyper Require Import Config L20.AST L20.Callset.
From Vyper Require FSet Map L10.AST L10.UInt256.

Local Open Scope list_scope.
Local Open Scope string_scope.

Section Interpret.

Context {C: VyperConfig}.

Definition abort := L10.Interpret.abort.
Definition expr_result := L10.Interpret.expr_result.
Definition stmt_result := L10.Interpret.stmt_result.
Definition expr_error {type: Type} := @L10.Interpret.expr_error C type.

Definition calldag := L10.Interpret.generic_calldag decl decl_callset.
Definition cd_declmap {C decl_type callset} := @L10.Interpret.cd_declmap C decl_type callset.
Definition cd_depthmap {C decl_type callset} := @L10.Interpret.cd_depthmap C decl_type callset.
Definition cd_depthmap_ok {C decl_type callset} := @L10.Interpret.cd_depthmap_ok C decl_type callset.


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
                                  {body: stmt}
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let _ := string_set_impl in FSet.is_subset (stmt_callset body) (decl_callset this_decl) = true.
Proof.
subst this_decl. unfold decl_callset. apply FSet.is_subset_refl.
Qed.

(* XXX dup from L10 except PrivateOrBuiltinCall becomes PrivateCall *)
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
                   (E : e = PrivateCall name args)
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
unfold cd_declmap in this_decl_ok. rewrite this_decl_ok in K.
unfold cd_depthmap in current_fun_depth_ok. rewrite current_fun_depth_ok in K.
cbn in K.
rewrite FSet.for_all_ok in K.
assert (L := K name HasName). clear K.
subst call_depth_bound.
apply lt_n_Sm_le in DepthOk.
unfold cd_depthmap in Edepth.
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
unfold cd_declmap in Edecl.
rewrite Edecl in D.
intro H.
unfold cd_depthmap in H.
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
                           (E: e = PrivateCall name args)
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

Definition map_lookup {Value} (m: string_map Value) := let _ := string_map_impl in Map.lookup m.
Definition map_insert {Value} (m: string_map Value) := let _ := string_map_impl in Map.insert m.
Definition map_remove {Value} (m: string_map Value) := let _ := string_map_impl in Map.remove m.

Fixpoint interpret_expr {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        {cd: calldag}
                        (fc: fun_ctx cd bigger_call_depth_bound)
                        (do_call: forall
                                      (fc': fun_ctx cd smaller_call_depth_bound)
                                      (world: world_state)
                                      (arg_values: list uint256),
                                    world_state * expr_result uint256)
                        (builtins: string -> option L10.Interpret.builtin)
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
         | nil => fun _ => (world, L10.Interpret.ExprSuccess _ nil)
         | (h :: t)%list => fun E =>
             let (world', result_h) := interpret_expr Ebound fc do_call builtins
                                                      world loc h
                                                      (callset_descend_head E CallOk)
             in match result_h with
                | L10.Interpret.ExprAbort _ ab => (world', L10.Interpret.ExprAbort _ ab)
                | L10.Interpret.ExprSuccess _ x =>
                   let (world'', result_t) := interpret_expr_list world' loc t
                                                                  (callset_descend_tail E CallOk)
                   in (world'', match result_t with
                                | L10.Interpret.ExprAbort _ _ => result_t
                                | L10.Interpret.ExprSuccess _ y => 
                                    L10.Interpret.ExprSuccess _ (x :: y)%list
                                end)
                 end
         end eq_refl
    in match e as e' return e = e' -> _ with
       | Const val => fun _ => (world, L10.Interpret.ExprSuccess _ val)
       | LocalVar name => fun _ =>
           (world, match map_lookup loc name with
                   | Some val => L10.Interpret.ExprSuccess _ val
                   | None => expr_error "Local variable not found"
                   end)
       | StorageVar name => fun _ => 
           (world, match storage_lookup world name with
                   | Some val => L10.Interpret.ExprSuccess _ val
                   | None => expr_error "Storage variable not found"
                   end)
       | UnOp op a => fun E =>
           let (world', result) := interpret_expr Ebound fc do_call builtins
                                                  world loc a
                                                  (callset_descend_unop E CallOk)
           in (world', match result with
                       | L10.Interpret.ExprSuccess _ val => L10.Interpret.interpret_unop op val
                       | L10.Interpret.ExprAbort _ _ => result
                       end)
       | BinOp op a b => fun E =>
           let (world', result_a) := interpret_expr Ebound fc do_call builtins
                                                    world loc a
                                                    (callset_descend_binop_left E CallOk)
           in match result_a with
           | L10.Interpret.ExprAbort _ _ => (world', result_a)
           | L10.Interpret.ExprSuccess _ x =>
             let (world'', result_b) := interpret_expr Ebound fc do_call builtins
                                                       world' loc b
                                                       (callset_descend_binop_right E CallOk)
             in (world'', match result_b with
                          | L10.Interpret.ExprAbort _ _ => result_b
                          | L10.Interpret.ExprSuccess _ y => L10.Interpret.interpret_binop op x y
                          end)
           end
       | IfThenElse cond yes no => fun E =>
           let (world', result_cond) := interpret_expr Ebound fc do_call builtins
                                                       world loc cond
                                                       (callset_descend_if_cond E CallOk)
           in match result_cond with
              | L10.Interpret.ExprAbort _ _ => (world', result_cond)
              | L10.Interpret.ExprSuccess _ cond_value =>
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
              | L10.Interpret.ExprAbort _ _ => (world', result_a)
              | L10.Interpret.ExprSuccess _ a_value =>
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
              | L10.Interpret.ExprAbort _ msg => (world', result_a)
              | L10.Interpret.ExprSuccess _ a_value =>
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
              | L10.Interpret.ExprAbort _ ab => (world', L10.Interpret.ExprAbort _ ab)
              | L10.Interpret.ExprSuccess _ arg_values =>
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
              | L10.Interpret.ExprAbort _ ab => (world', L10.Interpret.ExprAbort _ ab)
              | L10.Interpret.ExprSuccess _ arg_values =>
                match builtins name with
                | Some (existT _ arity b) =>
                   (if (arity =? List.length arg_values)%nat as arity_ok 
                    return _ = arity_ok -> _
                        then fun Earity =>
                               L10.Interpret.call_builtin arg_values Earity (b world')
                        else fun _ => (world', expr_error "builtin with wrong arity"))
                      eq_refl
                | None => (world', expr_error "can't resolve function name")
                end
              end
       end eq_refl.

Definition interpret_small_stmt {bigger_call_depth_bound smaller_call_depth_bound: nat}
                                (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                                {cd: calldag}
                                (fc: fun_ctx cd bigger_call_depth_bound)
                                (do_call: forall
                                              (fc': fun_ctx cd smaller_call_depth_bound)
                                              (world: world_state)
                                              (arg_values: list uint256),
                                            world_state * expr_result uint256)
                                (builtins: string -> option L10.Interpret.builtin)
                                (world: world_state)
                                (loc: string_map uint256)
                                (s: small_stmt)
                                (CallOk: let _ := string_set_impl in 
                                         FSet.is_subset (small_stmt_callset s)
                                                        (decl_callset (fun_decl fc))
                                         = true)
: world_state * string_map uint256 * stmt_result uint256
:= match s as s' return s = s' -> _ with
   | Pass     => fun _ => (world, loc, L10.Interpret.StmtSuccess _)
   | Abort ab => fun _ => (world, loc, L10.Interpret.StmtAbort _ ab)
   | Return e => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc e
                                               (callset_descend_return E CallOk)
        in (world', loc, match result with
                         | L10.Interpret.ExprSuccess _ value =>
                              L10.Interpret.StmtReturnFromFunction _ value
                         | L10.Interpret.ExprAbort _ ab =>
                              L10.Interpret.StmtAbort _ ab
                         end)
   | Raise e => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc e
                                               (callset_descend_raise E CallOk)
        in (world', loc, L10.Interpret.StmtAbort _
                           (match result with
                            | L10.Interpret.ExprSuccess _ value =>
                                L10.Interpret.AbortException value
                            | L10.Interpret.ExprAbort _ ab => ab
                            end))
   | Assign lhs rhs => fun E =>
        let (world', result) := interpret_expr Ebound fc do_call builtins
                                               world loc rhs
                                               (callset_descend_assign_rhs E CallOk)
        in L10.Interpret.do_assign world' loc lhs result
   | ExprStmt e => fun E =>
                   let (world', result) := interpret_expr Ebound fc do_call builtins
                                                          world loc e
                                                          (callset_descend_expr_stmt E CallOk)
                   in (world', loc, match result with
                                    | L10.Interpret.ExprSuccess _ a =>
                                        L10.Interpret.StmtSuccess _
                                    | L10.Interpret.ExprAbort _ ab =>
                                        L10.Interpret.StmtAbort _ ab
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
                        (builtins: string -> option L10.Interpret.builtin)
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
         | L10.Interpret.StmtSuccess _ =>
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
         | Some _ => (world, loc,
                        L10.Interpret.StmtAbort _
                          (L10.Interpret.AbortError "local variable already exists"))
         | None =>
           let '(world', result) :=
                  interpret_expr Ebound fc do_call builtins
                                 world loc init
                                 (callset_descend_var_init E CallOk)
           in match result with
              | L10.Interpret.ExprSuccess _ value =>
                  let '(world2, loc2, result2) :=
                    interpret_stmt Ebound fc do_call builtins
                                   world (map_insert loc name value) scope
                                   (callset_descend_var_scope E CallOk)
                  in (world2, map_remove loc2 name, result2)
              | L10.Interpret.ExprAbort _ ab =>
                  (world', loc, L10.Interpret.StmtAbort _ ab)
              end
         end
    | IfElseStmt cond yes no => fun E => 
        let (world', result_cond) := interpret_expr
                                       Ebound fc do_call builtins
                                       world loc cond
                                       (callset_descend_stmt_if_cond E CallOk)
        in match result_cond with
           | L10.Interpret.ExprAbort _ ab => (world', loc, L10.Interpret.StmtAbort _ ab)
           | L10.Interpret.ExprSuccess _ cond_value =>
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
           | L10.Interpret.ExprAbort _ ab => (world', loc, L10.Interpret.StmtAbort _ ab)
           | L10.Interpret.ExprSuccess _ start_value =>
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
                    | O => (world, loc, L10.Interpret.StmtSuccess _)
                    | S new_countdown =>
                          let loc' := map_insert loc name (uint256_of_Z cursor) in
                          let '(world', loc'', result) :=
                                interpret_stmt Ebound fc do_call builtins world loc' fc_body CallOk
                          in match result with
                             | L10.Interpret.StmtSuccess _
                             | L10.Interpret.StmtAbort _ L10.Interpret.AbortContinue =>
                                 interpret_loop_rec world' loc''
                                                    (Z.succ cursor) new_countdown name CallOk
                             | L10.Interpret.StmtAbort _ L10.Interpret.AbortBreak =>
                                 (world', loc'', L10.Interpret.StmtSuccess _)
                             | _ => (world', loc'', result)
                             end
                    end
               in match map_lookup loc var with
               | Some _ => (world', loc,
                             L10.Interpret.StmtAbort _
                               (L10.Interpret.AbortError "loop var already exists"))
               | None => let count_z := Z_of_uint256 count in
                         let count_nat := Z.to_nat count_z in
                         let start_z := Z_of_uint256 start_value in
                         let last := (start_z + count_z - 1)%Z in
                         if (Z_of_uint256 (uint256_of_Z last) =? last)%Z
                           then
                             interpret_loop_rec
                               world' loc start_z count_nat var
                               (callset_descend_loop_body E CallOk)
                           else (world, loc,
                                  L10.Interpret.StmtAbort _
                                    (L10.Interpret.AbortError "loop range overflows"))
               end
           end
    end eq_refl.

Fixpoint interpret_call {call_depth_bound: nat}
                        {cd: calldag}
                        (builtins: string -> option L10.Interpret.builtin)
                        (fc: fun_ctx cd call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256)
{struct call_depth_bound}
: world_state * expr_result uint256
:= match call_depth_bound as call_depth_bound' return _ = call_depth_bound' -> _ with
   | O => fun Ebound => False_rect _ (Nat.nlt_0_r (fun_depth fc)
                                                  (eq_ind _ _ (fun_bound_ok fc) _ Ebound))
   | S new_call_depth_bound => fun Ebound =>
        match fun_decl fc as d return _ = d -> _ with
        | FunDecl _ arg_names body => fun E =>
            match bind_args arg_names arg_values with
            | inl err => (world, expr_error err)
            | inr loc =>
                let '(world', loc', result) := interpret_stmt Ebound fc (interpret_call builtins)
                                                              builtins world loc body 
                                                              (interpret_call_helper E)
                in (world', match result with
                            | L10.Interpret.StmtSuccess _ => L10.Interpret.ExprSuccess _ zero256
                            | L10.Interpret.StmtReturnFromFunction _ x => L10.Interpret.ExprSuccess _ x
                            | L10.Interpret.StmtAbort _ a => L10.Interpret.ExprAbort _ a
                            end)
            end
        | _ => fun _ => (world, expr_error "a declaration is found but it's not a function")
        end eq_refl
   end eq_refl.

Local Lemma make_fun_ctx_helper {cd: calldag}
                          {name: string}
                          {d : decl}
                          (Ed : cd_declmap cd name = Some d)
                          (Edepth : cd_depthmap cd name = None):
  False.
Proof.
assert (W := cd_depthmap_ok cd name).
unfold cd_declmap in Ed.
rewrite Ed in W.
unfold cd_depthmap in Edepth.
rewrite Edepth in W. exact W.
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
Definition interpret (builtins: string -> option L10.Interpret.builtin)
                     (cd: calldag)
                     (function_name: string)
                     (world: world_state)
                     (arg_values: list uint256)
: world_state * expr_result uint256
:= match make_fun_ctx_and_bound cd function_name with
   | None => (world, expr_error "declaration not found")
   | Some (existT _ bound fc) => interpret_call builtins fc world arg_values
   end.

End Interpret.