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

Section Interpret.

Context {C: VyperConfig}.

Inductive stmt_result (return_type: Type)
:= StmtSuccess
 | StmtAbort (a: stmt_abort return_type).
Arguments StmtSuccess {_}.
Arguments StmtAbort {_}.

(** XXX *)
Definition interpret_unop (op: unop) (a: uint256)
: expr_result uint256
:= ExprSuccess a.

(** XXX *)
Definition interpret_binop (op: binop) (a b: uint256)
: expr_result uint256
:= ExprSuccess a.

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
                                  {body: expr}
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let H := string_set_impl in FSet.is_subset (expr_callset body) (decl_callset this_decl) = true.
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
                   (e : expr)
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
                           {cd : calldag}
                           {e : expr}
                           {name : string}
                           {args : list expr}

                           (fc: fun_ctx cd call_depth_bound)
                           (CallOk : let _ := string_set_impl in
                                       FSet.is_subset (expr_callset e)
                                                      (decl_callset (fun_decl fc))
                                        = true)
                           (Ebound : call_depth_bound = S new_call_depth_bound)
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
                      | ExprError msg => (world', ExprError msg)
                      | ExprSuccess x =>
                         let (world'', result_t) := interpret_expr_list world' loc t
                                                                        (callset_descend_tail E CallOk)
                         in (world'', match result_t with
                                      | ExprError _ => result_t
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
                     let (world', result) := interpret_expr world loc a
                                                            (callset_descend_unop E CallOk)
                     in (world', match result with
                                 | ExprSuccess val => interpret_unop op val
                                 | ExprError msg => result
                                 end)
                 | BinOp op a b => fun E =>
                     let (world', result_a) := interpret_expr world loc a
                                                              (callset_descend_binop_left E CallOk)
                     in match result_a with
                     | ExprError msg => (world', result_a)
                     | ExprSuccess x =>
                       let (world'', result_b) := interpret_expr world' loc b
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
                       interpret_expr_list world loc args
                                           (callset_descend_args E CallOk)
                     in match result_args with
                        | ExprError msg => (world', ExprError msg)
                        | ExprSuccess arg_values =>
                            match fun_ctx_descend fc CallOk Ebound E with
                            | None => (* can't resolve the function, maybe it's a builtin *)
                                      (world', ExprError "can't resolve function name")
                            | Some new_fc => interpret_call new_fc world' arg_values
                            end
                        end
                 end eq_refl
         end eq_refl
   in match fun_decl fc as d return _ = d -> _ with
      | FunDecl _ arg_names body => fun E =>
          match bind_args arg_names arg_values with
          | inl err => (world, ExprError err)
          | inr loc => interpret_expr world loc body (interpret_call_helper E)
          end
      | _ => fun _ => (world, ExprError "a declaration is found but it's not a function")
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
   | None => (world, ExprError "declaration not found")
   | Some (existT _ bound fc) => interpret_call fc world arg_values
   end.

(*
Definition stmt_is_local_var_decl {C: VyperConfig} (s: stmt)
:= match s with
   | LocalVarDecl _ _ => true
   | _ => false
   end.


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
*)

End Interpret.