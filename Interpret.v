From Coq Require Import String Arith NArith.
Require Import Config UntypedAST Callset.
Require FSet Map.

Local Open Scope list_scope.
Local Open Scope string_scope.

Inductive expr_result {C: VyperConfig} (result_type: Type)
:= ExprSuccess (result: result_type)
 | ExprError (msg: string).
Arguments ExprSuccess {_ _}.
Arguments ExprError {_ _}.

Inductive stmt_abort (return_type: Type)
:= AbortError (msg: string)
 | AbortBreak
 | AbortContinue
 | AbortReturnFromFunction
 | AbortReturnFromContract
 | AbortRevert.

Inductive stmt_result {C: VyperConfig} (return_type: Type)
:= StmtSuccess
 | StmtAbort (a: stmt_abort return_type).
Arguments StmtSuccess {_ _}.
Arguments StmtAbort {_ _}.

(** XXX *)
Definition interpret_unop {C: VyperConfig} (op: unop) (a: uint256)
: expr_result uint256
:= ExprSuccess a.

(** XXX *)
Definition interpret_binop {C: VyperConfig} (op: binop) (a b: uint256)
: expr_result uint256
:= ExprSuccess a.

Record calldag {C: VyperConfig} := {
  cd_declmap:  string -> option decl;
  cd_depthmap: string -> option N;
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
                                          | Some y => (y <? x)%N
                                          end)
               = true
            end
      end;
}.

Fixpoint bind_args {C: VyperConfig} (names: list string) (values: list uint256)
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

Local Lemma interpret_call_helper {C: VyperConfig}
                                  {this_decl: decl}
                                  {fun_name: string}
                                  {arg_names: list string}
                                  {body: expr}
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let H := string_set_impl in FSet.is_subset (expr_callset body) (decl_callset this_decl) = true.
Proof.
subst this_decl. unfold decl_callset. apply FSet.is_subset_refl.
Qed.

Lemma call_descend {C: VyperConfig}
                   {call_depth_bound new_call_depth_bound current_fun_depth: nat}
                   (DepthOk : current_fun_depth < call_depth_bound)
                   (cd : calldag)
                   (this_fun_name: string)
                   (this_decl: decl)
                   (this_decl_ok: cd_declmap cd this_fun_name = Some this_decl)
                   (current_fun_depth_ok:
                     cd_depthmap cd this_fun_name = Some (N.of_nat current_fun_depth))
                   (e : expr)
                   (CallOk : let _ := string_set_impl in
                             FSet.is_subset (expr_callset e) (decl_callset this_decl) = true)
                   (Ebound : call_depth_bound = S new_call_depth_bound)
                   (name : string)
                   (args : list expr)
                   (E : e = PrivateOrBuiltinCall name args):
  match cd_depthmap cd name with
    | Some y => (y <? N.of_nat new_call_depth_bound)%N
    | None => false
    end = true.
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
destruct (cd_depthmap cd name). 2:{ assumption. }
rewrite N.ltb_lt. rewrite N.ltb_lt in L.
refine (N.lt_le_trans _ _ _ L _).
rewrite<- N.compare_le_iff.
rewrite<- Nat2N.inj_compare.
rewrite Nat.compare_le_iff.
exact DepthOk.
Qed.

Fixpoint interpret_call {C: VyperConfig}
                        (CALL_depth_bound: nat)
                        (call_depth_bound: nat)
                        (current_fun_depth: nat)
                        (DepthOk: current_fun_depth < call_depth_bound)
                        (cd: calldag)
                        (world: world_state)
                        (fun_name: string)
                        (arg_values: list uint256)
: world_state * expr_result uint256
:= match cd_declmap cd fun_name with
   | Some this_decl =>
      match this_decl as this_decl' return this_decl = this_decl' -> _ with
      | FunDecl _ arg_names body => fun E =>
          match bind_args arg_names arg_values with
          | inl err => (world, ExprError err)
          | inr loc => interpret_expr CALL_depth_bound call_depth_bound
                                      current_fun_depth DepthOk
                                      cd this_decl
                                      world loc body
                                      (interpret_call_helper E)
          end
     | _ => fun _ => (world, ExprError "a declaration is found but it's not a function")
     end eq_refl
   | None => (world, ExprError "declaration not found") (* XXX: builtins *)
   end
with interpret_expr {C: VyperConfig}
                    (CALL_depth_bound: nat)
                    (call_depth_bound: nat)
                    (current_fun_depth: nat)
                    (DepthOk: current_fun_depth < call_depth_bound)
                    (cd: calldag)
                    (this_decl: decl)
                    (world: world_state)
                    (loc: string_map uint256)
                    (e: expr)
                    (CallOk: let _ := string_set_impl in 
                             FSet.is_subset (expr_callset e) (decl_callset this_decl) = true)
: world_state * expr_result uint256
:= let interpret_expr_list := 
     fix interpret_expr_list {C: VyperConfig}
                             (CALL_depth_bound: nat)
                             (call_depth_bound: nat)
                             (current_fun_depth: nat)
                             (DepthOk: current_fun_depth < call_depth_bound)
                             (cd: calldag)
                             (this_decl: decl)
                             (world: world_state)
                             (loc: string_map uint256)
                             (e: list expr)
                             (CallOk: let _ := string_set_impl in 
                                      FSet.is_subset (expr_list_callset e) (decl_callset this_decl) = true)
     {struct e}
     : world_state * expr_result (list uint256)
     := match e as e' return e = e' -> _ with
        | nil => fun _ => (world, ExprSuccess nil)
        | (h :: t)%list => fun E =>
            let (world', result_h) := interpret_expr CALL_depth_bound call_depth_bound
                                                     current_fun_depth DepthOk
                                                     cd this_decl
                                                     world loc h
                                                     (callset_descend_head E CallOk)
            in match result_h with
               | ExprError msg => (world', ExprError msg)
               | ExprSuccess x =>
                  let (world'', result_t) := interpret_expr_list CALL_depth_bound call_depth_bound
                                                                 current_fun_depth DepthOk
                                                                 cd this_decl
                                                                 world' loc t
                                                                 (callset_descend_tail E CallOk)
                  in (world'', match result_t with
                               | ExprError _ => result_t
                               | ExprSuccess y => ExprSuccess (x :: y)%list
                               end)
                end
        end eq_refl
   in match CALL_depth_bound as CALL_depth_bound' return CALL_depth_bound = CALL_depth_bound' -> _
   with
   | O => fun _ => (world, ExprError "Max CALL stack depth exceeded")
   | S new_CALL_depth_bound => fun _ =>
        match call_depth_bound as call_depth_bound'
          return call_depth_bound = call_depth_bound' -> _
        with
        | O => fun E => False_rect _ (Nat.nlt_0_r current_fun_depth
                                                  (eq_ind _ _ DepthOk _ E))
        | S new_call_depth_bound => fun _ =>

            match e as e' return e = e' -> _ with
               | Const val => fun _ => (world, ExprSuccess val)
               | LocalVar name => fun _ =>
                   let _ := string_map_impl in
                   (world, match Map.lookup loc name with
                           | Some val => ExprSuccess val
                           | None => ExprError "Local variable not found"
                           end)
               | StorageVar name => fun _ => 
                   let _ := string_map_impl in
                   (world, match storage_lookup world name with
                           | Some val => ExprSuccess val
                           | None => ExprError "Storage variable not found"
                           end)
               | UnOp op a => fun E =>
                   let (world', result) := interpret_expr CALL_depth_bound call_depth_bound
                                                          current_fun_depth DepthOk cd
                                                          this_decl world loc a
                                                          (callset_descend_unop E CallOk)
                   in (world', match result with
                               | ExprSuccess val => interpret_unop op val
                               | ExprError msg => result
                               end)
               | BinOp op a b => fun E =>
                   let (world', result_a) := interpret_expr CALL_depth_bound call_depth_bound
                                                            current_fun_depth DepthOk cd
                                                            this_decl world loc a
                                                            (callset_descend_binop_left E CallOk)
                   in match result_a with
                   | ExprError msg => (world', result_a)
                   | ExprSuccess x =>
                     let (world'', result_b) := interpret_expr CALL_depth_bound call_depth_bound
                                                               current_fun_depth DepthOk cd
                                                               this_decl world' loc b
                                                               (callset_descend_binop_right E CallOk)
                     in (world'', match result_b with
                                  | ExprError msg => result_b
                                  | ExprSuccess y => interpret_binop op x y
                                  end)
                   end
               (* | IfThenElse cond yes no => fun E =>
                   _ *)
               | PrivateOrBuiltinCall name args => fun E =>
                   let (world', result_args) :=
                     interpret_expr_list CALL_depth_bound call_depth_bound
                                         current_fun_depth DepthOk cd
                                         this_decl world loc args
                                         (callset_descend_args E CallOk)
                   in match result_args with
                      | ExprError msg => (world', ExprError msg)
                      | ExprSuccess arg_values =>
                          _
(*
                          interpret_call CALL_depth_bound new_call_depth_bound
                                         XXX
                        (current_fun_depth: nat)
                        (DepthOk: current_fun_depth < call_depth_bound)
                        (cd: calldag)
                        (world: world_state)
                        (fun_name: string)
                        (arg_values: list uint256) *)
                      end
               end eq_refl
        end eq_refl
   end eq_refl.


Definition interpret_expr {C: VyperConfig}
                          (CALL_depth_bound: nat)
                          (call_depth_bound: nat)
                          (current_fun_depth: nat)
                          (DepthOk: current_fun_depth < call_depth_bound)
                          (cd: calldag)
                          (allowed_calls: string_set)
                          (world: world_state)
                          (loc: string_map uint256)
                          (e: expr)
                          (CallOk: let _ := string_set_impl in 
                                   FSet.is_subset (expr_callset e) allowed_calls = true)
: world_state * expr_result uint256. admit. Admitted.

Definition stmt_is_local_var_decl {C: VyperConfig} (s: stmt)
:= match s with
   | LocalVarDecl _ _ => true
   | _ => false
   end.

Fixpoint interpret_call {C: VyperConfig}
                        (call_depth_bound: nat)
                        (cd: calldag)
                        (fun_name: string)
                        (allowed_calls: string_set)
                        (world: world_state)


Fixpoint interpret_stmt {C: VyperConfig}
                        (CALL_depth_bound: nat)
                        (call_depth_bound: nat)
                        (current_fun_depth: nat)
                        (DepthOk: current_fun_depth < call_depth_bound)
                        (cd: calldag)
                        (allowed_calls: string_set)
                        (world: world_state)
                        (loc: string_map uint256)
                        (return_type: Type)
                        (s: stmt)
                        (NotVarDecl: stmt_is_local_var_decl s = false)
                        (CallOk: let _ := string_set_impl in 
                                 FSet.is_subset (stmt_callset s) allowed_calls = true)
: world_state * string_map uint256 * stmt_result return_type
:= let interpret_loop := fix interpret_loop 
   match s as s' return s = s' -> _ with
   | SmallStmt ss => interpret_small_stmt XXXX
   | LocalVarDecl _ _ => False_rect _ _
   | IfElseStmt cond yes no =>
      let (world', result_cond) := interpret_expr XXXXX
   | FixedRangeLoop var start stop body =>
      (* Range checks *)
   | FixedCountLoop var start count body =>
      (* Range checks *)
   end eq_refl.
Fixpoint interpret_stmt_list {C: VyperConfig}
                             (CALL_depth_bound: nat)
                             (call_depth_bound: nat)
                             (current_fun_depth: nat)
                             (DepthOk: current_fun_depth < call_depth_bound)
                             (cd: calldag)
                             (allowed_calls: string_set)
                             (world: world_state)
                             (loc: string_map uint256)
                             (return_type: Type)
                             (s: list stmt)
                             (CallOk: let _ := string_set_impl in 
                                      FSet.is_subset (stmt_list_callset s) allowed_calls = true)
: world_state * string_map uint256 * stmt_result return_type
:= match s with
   | nil => (world, loc, StmtSuccess)
   | LocalVarDecl name maybe_init :: rest =>
      match Map.lookup loc name with
      | Some _ => (world, StmtAbort (ErrorAbort "local variable shadowing"))
      | None => _
      end
   | IfElseStmt cond yes no =>
      
   | FixedRangeLoop (var: string) (start: option uint256) (stop: uint256) (body: list stmt)
   | FixedCountLoop (var: string) (start: string) (count: uint256) (body: list stmt).
   end.

Definition interpret 