From Coq Require Import String Arith NArith ZArith Eqdep_dec.

From Vyper Require FSet Map UInt256.

From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import AST Base Callset Descend.

Local Open Scope list_scope.
Local Open Scope string_scope.


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


Section Expr.
Context {C: VyperConfig}.

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

(* This is not needed as PropExtensionality covers it.
   But this is an example of induction on expr.
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

End Expr.

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