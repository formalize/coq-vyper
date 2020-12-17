From Coq Require Import String Arith NArith ZArith Eqdep_dec.
From Vyper Require Import Config NaryFun Calldag.
From Vyper.L10 Require Import AST Callset.
From Vyper Require FSet Map UInt256.

Local Open Scope list_scope.
Local Open Scope string_scope.

Section Descend.
Context {C: VyperConfig}.

Definition calldag := generic_calldag decl_callset true.


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
unfold cd_declmap in this_decl_ok.
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

Lemma fun_ctx_descend_none {call_depth_bound new_call_depth_bound}
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
                           (E: e = PrivateOrBuiltinCall name args):
  fun_ctx_descend fc CallOk Ebound E = None
   <->
  cd_declmap cd name = None.
Proof.
unfold fun_ctx_descend.
assert (InnerOk: forall (d: decl) (Edecl: cd_declmap cd name = Some d),
                   fun_ctx_descend_inner fc CallOk Ebound E Edecl = None
                    <->
                   cd_declmap cd name = None).
{
  intros. unfold fun_ctx_descend_inner.
  assert (Ok := cd_depthmap_ok cd name).
  remember (fun (depth: nat) (Edepth: cd_depthmap cd name = Some depth) =>
    Some
      {|
      fun_name := name;
      fun_depth := depth;
      fun_depth_ok := Edepth;
      fun_decl := d;
      fun_decl_ok := Edecl;
      fun_bound_ok := call_descend' fc CallOk Ebound E Edecl Edepth |}) as some_branch.
  remember (fun Edepth : cd_depthmap cd name = None =>
              False_rect (option (fun_ctx cd new_call_depth_bound))
                         (fun_ctx_descend_helper Edecl Edepth))
    as none_branch.
  assert (SomeBranchOk: forall (depth: nat) (Edepth: cd_depthmap cd name = Some depth),
                          some_branch depth Edepth <> None).
  { now subst. }
  assert (NoneBranchOk: forall (Edepth: cd_depthmap cd name = None),
                          none_branch Edepth = None).
  { intro. exfalso. exact (fun_ctx_descend_helper Edecl Edepth). }
  clear Heqsome_branch Heqnone_branch.
  unfold cd_declmap in *.
  rewrite Edecl in *.
  destruct (cd_depthmap cd name). 2:{ contradiction. }
  assert (S := SomeBranchOk n eq_refl).
  split. { contradiction. }
  intro. discriminate.
} (* InnerOk *)
remember fun_ctx_descend_inner as inner. clear Heqinner. revert inner InnerOk.
destruct cd_declmap.
{ intros. apply InnerOk. }
intros. tauto.
Qed.

End Descend.