From Coq Require Import String Arith NArith ZArith Eqdep_dec.
From Vyper Require Import Config L10.AST L10.Callset NaryFun Some.
From Vyper Require FSet Map UInt256.

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

Record generic_calldag (decl_type: Type) (callset: decl_type -> string_set) := {
  cd_declmap:  string -> option decl_type;
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
              FSet.for_all (callset decl)
                           (fun callee => match cd_depthmap callee with
                                          | None => false
                                          | Some y => y <? x
                                          end)
               = true
            end
      end;
}.
Arguments cd_declmap {decl_type callset}.
Arguments cd_depthmap {decl_type callset}.
Arguments cd_depthmap_ok {decl_type callset}.

Definition calldag := generic_calldag decl decl_callset.

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
                                  {body: list stmt}
                                  (E: this_decl = FunDecl fun_name arg_names body):
  let _ := string_set_impl in FSet.is_subset (stmt_list_callset body) (decl_callset this_decl) = true.
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
                   (CallOk: let _ := string_set_impl in
                             FSet.is_subset (expr_callset e) (decl_callset this_decl) = true)
                   (Ebound: call_depth_bound = S new_call_depth_bound)
                   {name: string}
                   {args: list expr}
                   (E: e = PrivateOrBuiltinCall name args)
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

(**
  A functional context is the result of looking up a function by name.
  
 *)
Record fun_ctx {decl_type: Type}
               {decl_callset: decl_type -> string_set}
               (cd: generic_calldag decl_type decl_callset)
               (bound: nat) := {
  fun_name: string;
  fun_depth: nat;
  fun_depth_ok: cd_depthmap cd fun_name = Some fun_depth;
  fun_decl: decl_type;
  fun_decl_ok: cd_declmap cd fun_name = Some fun_decl;
  fun_bound_ok: fun_depth <? bound = true;
}.
Arguments fun_name     {_ _ _ _}.
Arguments fun_depth    {_ _ _ _}.
Arguments fun_depth_ok {_ _ _ _}.
Arguments fun_decl     {_ _ _ _}.
Arguments fun_decl_ok  {_ _ _ _}.
Arguments fun_bound_ok {_ _ _ _}.


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

Local Lemma call_descend' {call_depth_bound new_call_depth_bound}
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
                          {d: decl}
                          (Edecl: cd_declmap cd name = Some d)
                          {depth: nat}
                          (Edepth: cd_depthmap cd name = Some depth):
  (depth <? new_call_depth_bound) = true.
Proof.
exact (proj2 (Nat.ltb_lt _ _)
         (call_descend (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))
                       cd (fun_name fc)
                       (fun_decl fc) (fun_decl_ok fc)
                       (fun_depth_ok fc) e CallOk Ebound 
                       E Edepth)).
Qed.

(* The inner part of fun_ctx_descend is here separately because
   it's too difficult to destruct [cd_depthmap cd name] otherwise. 
 *)
Local Definition fun_ctx_descend_inner {call_depth_bound new_call_depth_bound}
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
                           {d: decl}
                           (Edecl: cd_declmap cd name = Some d)
:= match cd_depthmap cd name as maybe_depth return _ = maybe_depth -> _ with
   | None => fun Edepth => False_rect _ (fun_ctx_descend_helper Edecl Edepth)
   | Some depth => fun Edepth =>
       Some {| fun_name := name
             ; fun_depth := depth
             ; fun_depth_ok := Edepth
             ; fun_decl := d
             ; fun_decl_ok := Edecl
             ; fun_bound_ok := call_descend' fc CallOk Ebound E Edecl Edepth
            |}
   end eq_refl.

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
   | Some d => fun Edecl => fun_ctx_descend_inner fc CallOk Ebound E Edecl
   end eq_refl.

Lemma fun_ctx_descend_irrel {call_depth_bound new_call_depth_bound}
                            {cd: calldag}
                            {e: expr}
                            {name: string}
                            {args: list expr}
                            (fc1 fc2: fun_ctx cd call_depth_bound)
                            (CallOk1: let _ := string_set_impl in
                                        FSet.is_subset (expr_callset e)
                                                       (decl_callset (fun_decl fc1))
                                         = true)
                            (CallOk2: let _ := string_set_impl in
                                        FSet.is_subset (expr_callset e)
                                                       (decl_callset (fun_decl fc2))
                                         = true)
                            (Ebound: call_depth_bound = S new_call_depth_bound)
                            (E: e = PrivateOrBuiltinCall name args):
  fun_ctx_descend fc1 CallOk1 Ebound E = fun_ctx_descend fc2 CallOk2 Ebound E.
Proof.
unfold fun_ctx_descend.
assert (InnerOk: forall (d: decl) (Edecl: cd_declmap cd name = Some d),
                   fun_ctx_descend_inner fc1 CallOk1 Ebound E Edecl
                    =
                   fun_ctx_descend_inner fc2 CallOk2 Ebound E Edecl).
{
  intros. unfold fun_ctx_descend_inner.
  remember (fun (depth: nat) (Edepth: cd_depthmap cd name = Some depth) => Some {|
      fun_name := name;
      fun_depth := depth;
      fun_depth_ok := Edepth;
      fun_decl := d;
      fun_decl_ok := Edecl;
      fun_bound_ok := call_descend' fc1 CallOk1 Ebound E Edecl Edepth |}) as some_branch1.
  remember (fun (depth: nat) (Edepth: cd_depthmap cd name = Some depth) => Some {|
      fun_name := name;
      fun_depth := depth;
      fun_depth_ok := Edepth;
      fun_decl := d;
      fun_decl_ok := Edecl;
      fun_bound_ok := call_descend' fc2 CallOk2 Ebound E Edecl Edepth |}) as some_branch2.
  assert(SomeBranchOk: forall (depth: nat) (Edepth: cd_depthmap cd name = Some depth),
                         some_branch1 depth Edepth = some_branch2 depth Edepth).
  {
    intros. subst. f_equal. f_equal.
    apply eq_proofs_unicity. decide equality.
  }
  clear Heqsome_branch1 Heqsome_branch2.
  remember fun_ctx_descend_helper as foo. clear Heqfoo. revert foo.
  revert CallOk1 CallOk2.
  destruct (cd_depthmap cd name).
  { intros. apply SomeBranchOk. }
  trivial.
}
remember fun_ctx_descend_inner as inner. clear Heqinner. revert inner CallOk1 CallOk2 InnerOk.
destruct (cd_declmap cd name). (* this is why fun_ctx_descend_inner exists *)
{ intros. apply InnerOk. }
trivial.
Qed.

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

Definition builtin := { arity: nat
                      & world_state -> nary_fun uint256 arity (world_state * expr_result uint256) 
                      }.

Definition call_builtin {arity: nat}
                        (args: list uint256)
                        (ArityOk: (arity =? List.length args)%nat = true)
                        (callable: nary_fun uint256 arity (world_state * expr_result uint256))
: world_state * expr_result uint256
:= fst (nary_call callable args (Nat.eq_le_incl _ _ (proj1 (Nat.eqb_eq _ _) ArityOk))).

Fixpoint interpret_expr {bigger_call_depth_bound smaller_call_depth_bound: nat}
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
               | None => expr_error "Local variable not found"
               end)
   | StorageVar name => fun _ => 
       (world, match storage_lookup world name with
               | Some val => ExprSuccess val
               | None => expr_error "Storage variable not found"
               end)
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
   | PrivateOrBuiltinCall name args => fun E =>
       let (world', result_args) :=
         interpret_expr_list world loc args
                             (callset_descend_args E CallOk)
       in match result_args with
          | ExprAbort ab => (world', ExprAbort ab)
          | ExprSuccess arg_values =>
              match fun_ctx_descend fc CallOk Ebound E with
              | Some new_fc => do_call new_fc world' arg_values
              | None => (* can't resolve the function, maybe it's a builtin *)
                 match builtins name with
                 | Some (existT _ arity b) =>
                    (if (arity =? List.length arg_values)%nat as arity_ok 
                     return _ = arity_ok -> _
                         then fun Earity => call_builtin arg_values Earity (b world')
                         else fun _ => (world', expr_error "builtin with wrong arity"))
                       eq_refl
                 | None => (world', expr_error "can't resolve function name")
                 end
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
                                          world loc e
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


Fixpoint interpret_call {call_depth_bound: nat}
                        {cd: calldag}
                        (builtins: string -> option builtin)
                        (fc: fun_ctx cd call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256)
{struct call_depth_bound}
: world_state * expr_result uint256
:= match call_depth_bound as call_depth_bound' return _ = call_depth_bound' -> _ with
   | O => fun Ebound => False_rect _ (Nat.nlt_0_r (fun_depth fc)
                                                  (eq_ind _ _
                                                          (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))
                                                          _ Ebound))
   | S new_call_depth_bound => fun Ebound =>
      match fun_decl fc as d return _ = d -> _ with
      | FunDecl _ arg_names body => fun E =>
          match bind_args arg_names arg_values with
          | inl err => (world, expr_error err)
          | inr loc =>
              let '(world', loc', result) := interpret_stmt_list Ebound fc (interpret_call builtins)
                                                                 builtins world loc body
                                                                 (interpret_call_helper E)
              in (world', match result with
                          | StmtSuccess => ExprSuccess zero256
                          | StmtReturnFromFunction x => ExprSuccess x
                          | StmtAbort a => ExprAbort a
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
                                                  ; fun_bound_ok := proj2 (Nat.ltb_lt _ _)
                                                                          (Nat.lt_succ_diag_r _)
                                                 |})
      end eq_refl
   end eq_refl.

(** This is a simplified interface to interpret_call that takes care of creating a function context. *)
Definition interpret (builtins: string -> option builtin)
                     (cd: calldag)
                     (function_name: string)
                     (world: world_state)
                     (arg_values: list uint256)
: world_state * expr_result uint256
:= match make_fun_ctx_and_bound cd function_name with
   | None => (world, expr_error "declaration not found")
   | Some (existT _ bound fc) => interpret_call builtins fc world arg_values
   end.

Ltac destruct_let_pair
:= match goal with
   |- (let (_, _) := ?x in _) = let (_, _) := ?x in _ =>
     destruct x
   end.
Ltac destruct_if
:= match goal with
   |- (if ?x then _ else _) = (if ?x then _ else _) =>
     destruct x
   end.

(* An alternative to this #$@% would be to have proper Leibnitz equality on fun_ctx
   or give up and bring in the proof irrelevance axiom.
   Part of the problem is that there's no equality predicate on uint256s so far
   because they can be represented by Zs.
   There goes the hope for having an equality predicate on exprs/stmts/decls as well.
   But this is an easy practice for induction on expr, so whatever.
 *)
Lemma interpret_expr_fun_ctx_irrel {bigger_call_depth_bound smaller_call_depth_bound: nat}
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
                                   (e: expr)
                                   (CallOk1: let _ := string_set_impl in 
                                                FSet.is_subset (expr_callset e)
                                                               (decl_callset (fun_decl fc1))
                                                = true)
                                   (CallOk2: let _ := string_set_impl in 
                                                FSet.is_subset (expr_callset e)
                                                               (decl_callset (fun_decl fc2))
                                                = true):
  interpret_expr Ebound fc1 do_call builtins world loc e CallOk1
   =
  interpret_expr Ebound fc2 do_call builtins world loc e CallOk2.
Proof.
revert world loc.
induction e using expr_ind'; cbn; intros.
{ trivial. }
{ trivial. }
{ trivial. }
{ (* unop *)
  now rewrite IHe with (CallOk2 := callset_descend_unop eq_refl CallOk2).
}
{ (* binop *)
  rewrite IHe1 with (CallOk2 := callset_descend_binop_left eq_refl CallOk2).
  destruct_let_pair.
  destruct e. 2:{ trivial. }
  rewrite IHe2 with (CallOk2 := callset_descend_binop_right eq_refl CallOk2).
  destruct_let_pair.
  trivial.
}
{ (* if *)
  rewrite IHe1 with (CallOk2 := callset_descend_if_cond eq_refl CallOk2).
  destruct_let_pair.
  destruct e. 2:{ trivial. }
  destruct_if.
  { now rewrite IHe3 with (CallOk2 := callset_descend_if_else eq_refl CallOk2). }
  now rewrite IHe2 with (CallOk2 := callset_descend_if_then eq_refl CallOk2).
}
{ (* and *)
  rewrite IHe1 with (CallOk2 := callset_descend_and_left eq_refl CallOk2).
  destruct_let_pair.
  destruct e. 2:{ trivial. }
  now destruct_if.
}
{ (* or *)
  rewrite IHe1 with (CallOk2 := callset_descend_or_left eq_refl CallOk2).
  destruct_let_pair.
  destruct e. 2:{ trivial. }
  now destruct_if.
}
(* call *)
remember (fix interpret_expr_list world loc (e: list expr) CallOk := _) as interpret_expr_list1.
remember (fix interpret_expr_list world loc (e: list expr) 
                                  (CallOk: FSet.is_subset (expr_list_callset e)
                                           (decl_callset (fun_decl fc2)) 
                                           = true) := _) as interpret_expr_list2.
assert (L: interpret_expr_list1 world loc args (callset_descend_args eq_refl CallOk1)
            =
           interpret_expr_list2 world loc args (callset_descend_args eq_refl CallOk2)).
{
  remember (callset_descend_args eq_refl CallOk1) as ListCallOk1.
  remember (callset_descend_args eq_refl CallOk2) as ListCallOk2.
  clear HeqListCallOk1 HeqListCallOk2 CallOk1 CallOk2.
  revert world loc ListCallOk1 ListCallOk2.
  induction args; intros. { now subst. }
  rewrite Heqinterpret_expr_list1. rewrite Heqinterpret_expr_list2. cbn.
  rewrite (List.Forall_inv H 
            (callset_descend_head eq_refl ListCallOk1) 
            (callset_descend_head eq_refl ListCallOk2)).
  destruct_let_pair.
  destruct e. 2:{ trivial. }
  rewrite<- Heqinterpret_expr_list1.
  rewrite<- Heqinterpret_expr_list2.
  rewrite (IHargs (List.Forall_inv_tail H) w loc
            (callset_descend_tail eq_refl ListCallOk1)
            (callset_descend_tail eq_refl ListCallOk2)).
  now destruct_let_pair.
}
clear Heqinterpret_expr_list1 Heqinterpret_expr_list2.
rewrite L.
destruct_let_pair.
destruct e. 2:{ trivial. }
assert (F: fun_ctx_descend fc1 CallOk1 Ebound eq_refl
            =
           fun_ctx_descend fc2 CallOk2 Ebound eq_refl).
{ apply fun_ctx_descend_irrel. }
rewrite F.
now destruct (fun_ctx_descend fc2 CallOk2 Ebound eq_refl).
Qed.

Ltac destruct_interpret_expr_irrel
:= match goal with
   H: fun_name ?fc1 = fun_name ?fc2 
   |- (let (_, _) := interpret_expr ?Ebound ?fc1 ?do_call ?builtins ?world ?loc ?e ?c1 in _)
       =
      (let (_, _) := interpret_expr ?Ebound ?fc2 ?do_call ?builtins ?world ?loc ?e ?c2 in _)
       =>
      rewrite (interpret_expr_fun_ctx_irrel Ebound H do_call builtins
                                            world loc e c1 c2);
      destruct_let_pair
   end.

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

End Interpret.