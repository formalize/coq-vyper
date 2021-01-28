From Coq Require Import Arith NArith ZArith Lia String Eqdep_dec.

From Vyper Require Import Logic2.
From Vyper Require Import Config L10.Base Calldag.
From Vyper Require OpenArray.
From Vyper Require Import UInt256.
From Vyper.CheckArith Require Import CheckedArith Translate Builtins.
From Vyper.L30 Require Import AST Stmt Callset VarCap.

(** Two open arrays have the same [count] first elements. *)
Definition MemoryPrefixAgree {C: VyperConfig} (mem1 mem2: memory) (count: N)
:= let _ := memory_impl in
   forall n: N,
     (n < count)%N
      ->
     OpenArray.get mem1 n = OpenArray.get mem2 n.


(** Replace [ view ... ... 1 ] with [get ... :: nil].
    This is basically the same as [rewrite OpenArray.view1],
    except it avoids the annoying "metavariable has several occurences" error.
 *)
Ltac view1
:= let a := fresh "a" in
   let v := fresh "v" in
   let LenOk := fresh "LenOk" in
   let Eqn := fresh "Eqn" in
   let OkA := fresh "OkA" in
   match goal with
   |- context [ @OpenArray.view ?ValueType ?Zero ?MemType ?MemClass ?memory ?offset 1%N ] =>
       remember (OpenArray.view memory offset 1%N) as v eqn:Eqn;
       assert (LenOk := @OpenArray.view_len ValueType Zero MemType MemClass memory offset 1%N);
       destruct v as [|a]; try discriminate;
       destruct v; try discriminate;
       clear LenOk;
       (* Eqn is now [a :: nil = view ... ... 1] *)
       assert (OkA := @OpenArray.view_ok ValueType Zero MemType MemClass memory offset 1 0 N.lt_0_1);
       rewrite<- Eqn in OkA; clear Eqn;
       rewrite N.add_0_r in OkA;
       replace (List.nth_error (a :: nil) (N.to_nat 0)) with (Some a) in OkA by trivial;
       inversion OkA; subst a; clear OkA
   end.

(** Replace [ view ... ... 2 ] with [get ... :: get ... :: nil].
    This is basically the same as [rewrite OpenArray.view2],
    except it avoids the annoying "metavariable has several occurences" error.
 *)
Ltac view2
:= let a := fresh "a" in
   let b := fresh "b" in
   let v := fresh "v" in
   let LenOk := fresh "LenOk" in
   let Eqn := fresh "Eqn" in
   let OkA := fresh "OkA" in
   let OkB := fresh "OkB" in
   match goal with
   |- context [ @OpenArray.view ?ValueType ?Zero ?MemType ?MemClass ?memory ?offset 2%N ] =>
       remember (OpenArray.view memory offset 2%N) as v eqn:Eqn;
       assert (LenOk := @OpenArray.view_len ValueType Zero MemType MemClass memory offset 2%N);
       destruct v as [|a]; try discriminate;
       destruct v as [|b]; try discriminate;
       destruct v; try discriminate;
       clear LenOk;
       (* Eqn is now [a :: b :: nil = view ... ... 2] *)
       assert (OkA := @OpenArray.view_ok ValueType Zero MemType MemClass memory offset 2 0 N.lt_0_2);
       assert (OkB := @OpenArray.view_ok ValueType Zero MemType MemClass memory offset 2 1 N.lt_1_2);
       rewrite<- Eqn in OkA; rewrite<- Eqn in OkB; clear Eqn;
       rewrite N.add_0_r in OkA; rewrite N.add_1_r in OkB;
       replace (List.nth_error (a :: b :: nil) (N.to_nat 0)) with (Some a) in OkA by trivial;
       replace (List.nth_error (a :: b :: nil) (N.to_nat 1)) with (Some b) in OkB by trivial;
       inversion OkA; subst a; inversion OkB; subst b; clear OkA OkB
   end.


(* Convert a BuiltinsSupportBinop clause into BuiltinIsBinop;
   pass the arity check and rewrite the builtin call.
   Example: open_binop builtin_name_uint256_add binop_add.
   Invoke after reducing the interpreted code to (builtins ...)
*)
Ltac do_binop selector newname
:= let op_name := fresh newname in
   let A := fresh "A" in
   let arity := fresh "arity" in
   let CondOk := fresh "CondOk" in
   match goal with
   | H: @BuiltinsSupportBinop ?C ?builtins (selector ?B) (?op ?C) |- _ =>
      unfold BuiltinsSupportBinop in H;
      destruct (builtins (selector B)) as [op_name|];
      try contradiction;
      assert (A := builtin_is_binop_arity _ _ H);
      destruct op_name as (arity, op_name);
      cbn in A;
      subst arity;
      match goal with
      |- context [ 2 =? ?rhs = ?ok] =>
          assert (CondOk: 2 =? rhs = true) by now rewrite OpenArray.view_len
      end;
      rewrite if_yes with (E := CondOk);
      cbn in CondOk;
      view2;
      rewrite (builtin_is_binop_ok _ _ H);
      clear CondOk
   end.

Ltac do_binop_nocbn selector newname
:= let op_name := fresh newname in
   let A := fresh "A" in
   let arity := fresh "arity" in
   let CondOk := fresh "CondOk" in
   match goal with
   | H: @BuiltinsSupportBinop ?C ?builtins (selector ?B) (?op ?C) |- _ =>
      unfold BuiltinsSupportBinop in H;
      destruct (builtins (selector B)) as [op_name|];
      try contradiction;
      assert (A := builtin_is_binop_arity _ _ H);
      destruct op_name as (arity, op_name);
      simpl in A;
      subst arity;
      match goal with
      |- context [ 2 =? ?rhs = ?ok] =>
          assert (CondOk: 2 =? rhs = true) by now rewrite OpenArray.view_len
      end;
      rewrite if_yes with (E := CondOk);
      simpl in CondOk;
      view2;
      rewrite (builtin_is_binop_ok _ _ H);
      clear CondOk
   end.

(* example: open_unop builtin_name_uint256_not binop_not. *)
Ltac do_unop selector newname
:= let op_name := fresh newname in
   let A := fresh "A" in
   let arity := fresh "arity" in
   let CondOk := fresh "CondOk" in
   match goal with
   | H: @BuiltinsSupportUnop ?C ?builtins (selector ?B) (?op ?C) |- _ =>
      unfold BuiltinsSupportUnop in H;
      destruct (builtins (selector B)) as [op_name|];
      try contradiction;
      assert (A := builtin_is_unop_arity _ _ H);
      destruct op_name as (arity, op_name);
      cbn in A;
      subst arity;
      match goal with
      |- context [ 1 =? ?rhs = ?ok] =>
          assert (CondOk: 1 =? rhs = true) by now rewrite OpenArray.view_len
      end;
      rewrite if_yes with (E := CondOk);
      cbn in CondOk;
      view1;
      rewrite (builtin_is_unop_ok _ _ H);
      clear CondOk
   end.

Local Lemma lt_ne_helper (x y: N) (L: (x < y)%N):
  (x =? y)%N = false.
Proof. apply N.eqb_neq. lia. Qed.

Local Lemma lt_ne_helper' (x y: N) (L: (x < y)%N):
  (y =? x)%N = false.
Proof. apply N.eqb_neq. lia. Qed.

Local Lemma lt_ne1_helper (x y: N) (L: (x < y)%N):
  (x =? N.succ y)%N = false.
Proof. apply N.eqb_neq. lia. Qed.

Local Lemma lt_ne1_helper' (x y: N) (L: (x < y)%N):
  (N.succ y =? x)%N = false.
Proof. apply N.eqb_neq. lia. Qed.

Local Lemma lt_ne2_helper (x y: N) (L: (x < y)%N):
  (x =? N.succ (N.succ y))%N = false.
Proof. apply N.eqb_neq. lia. Qed.

Local Lemma lt_ne2_helper' (x y: N) (L: (x < y)%N):
  (N.succ (N.succ y) =? x)%N = false.
Proof. apply N.eqb_neq. lia. Qed.

Local Lemma noalias1 (x: N): (x =? N.succ x)%N = false.
Proof. rewrite N.eqb_neq. lia. Qed.
Local Lemma noalias2 (x: N): (x =? N.succ (N.succ x))%N = false.
Proof. rewrite N.eqb_neq. lia. Qed.
Local Lemma noalias1' (x: N): (N.succ x =? x)%N = false.
Proof. rewrite N.eqb_neq. lia. Qed.
Local Lemma noalias2' (x: N): (N.succ (N.succ x) =? x)%N = false.
Proof. rewrite N.eqb_neq. lia. Qed.

(* TODO: to Arith2 *)
Lemma Z_ltb_succ_r (n m: Z):
  ((n <? Z.succ m) = (n <=? m))%Z.
Proof.
apply (relation_quad Z.ltb_lt Z.leb_le).
apply Z.lt_succ_r.
Qed.

Lemma translate_small_stmt_ok {C: VyperConfig}
                              {bigger_call_depth_bound smaller_call_depth_bound: nat}
                              (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                              (builtins: string -> option builtin)
                              (B: builtin_names_config)
                              (scratch: N)
                              (BuiltinsOk: BuiltinsSupportUInt256 B builtins)
                              {cd: L30.Descend.calldag}
                              (fc: fun_ctx cd bigger_call_depth_bound)
                              {do_call': forall (fc': fun_ctx (translate_calldag B scratch cd)
                                                              smaller_call_depth_bound)
                                                (world: world_state)
                                                (arg_values: list uint256),
                                            world_state * expr_result uint256}
                              {do_call: forall (fc': fun_ctx cd smaller_call_depth_bound)
                                               (world: world_state)
                                               (arg_values: list uint256),
                                           world_state * expr_result uint256}
                              (DoCallOk: forall fc' world arg_values,
                                     do_call' (translate_fun_ctx B scratch fc') world arg_values
                                      =
                                     do_call fc' world arg_values)
                              (ss: small_stmt)
                              (CallOk': let _ := string_set_impl in 
                                 FSet.is_subset (stmt_callset (translate_small_stmt B scratch ss))
                                                (decl_callset
                                                   (fun_decl
                                                     (translate_fun_ctx B scratch fc)))
                                 = true)
                              (CallOk: let _ := string_set_impl in 
                                 FSet.is_subset (small_stmt_callset ss)
                                                (Callset.decl_callset (fun_decl fc))
                                 = true)
                              (world: world_state)
                              (mem' mem: memory)
                              (ScratchOk: (var_cap_small_stmt ss <= scratch)%N)
                              (Agree: MemoryPrefixAgree mem' mem scratch):
  let _ := string_map_impl in
  let _ := memory_impl in
  let '(w', m', result') := interpret_stmt Ebound (translate_fun_ctx B scratch fc)
                                                  do_call' builtins
                                                  world mem' (translate_small_stmt B scratch ss)
                                                  CallOk' in
  let '(w, m, result) := interpret_small_stmt Ebound fc do_call builtins world mem ss CallOk in
    result' = result
     /\
    w' = w
     /\
    MemoryPrefixAgree m' m scratch.
Proof.
unfold BuiltinsSupportUInt256 in BuiltinsOk.
destruct BuiltinsOk as (AddOk, (SubOk, (MulOk, (DivOk, (ModOk,
                        (PowOk, (NotOk, (IsZeroOk, (AndOk, (OrOk, (XorOk,
                         (LtOk, (EqOk, (ShlOk, ShrOk)))))))))))))).

destruct ss; simpl; simpl in ScratchOk. (* cbn hangs up *)
{ (* Pass *) easy. }
{ (* Const *)
  repeat (split; trivial).
  intros n L.
  repeat rewrite OpenArray.put_ok.
  destruct (dst =? n)%N. { trivial. }
  apply (Agree n L).
}
{ (* Copy *)
  repeat (split; trivial).
  intros n L.
  repeat rewrite OpenArray.put_ok.
  destruct (dst =? n)%N. { apply Agree. lia. }
  apply (Agree n L).
}
{ (* StorageGet *)
  assert (D := calldag_map_declmap (translate_decl B scratch)
                                   (Translate.translate_calldag_helper B scratch cd)
                                   cd name).
  destruct (cd_declmap
     (calldag_map (translate_decl B scratch) (Translate.translate_calldag_helper B scratch cd) cd)
     name) as [d'|], (cd_declmap cd name) as [d|]; try discriminate.
  2:easy. (* not found *)
  destruct d; cbn in D; inversion D; subst d'.
  2:easy. (* found but it's a function decl *)
  repeat (split; trivial).
  intros n L.
  repeat rewrite OpenArray.put_ok.
  destruct (dst =? n)%N. { trivial. }
  apply (Agree n L).
}
{ (* StoragePut *)
  assert (D := calldag_map_declmap (translate_decl B scratch)
                                   (Translate.translate_calldag_helper B scratch cd)
                                   cd name).
  destruct (cd_declmap
     (calldag_map (translate_decl B scratch) (Translate.translate_calldag_helper B scratch cd) cd)
     name) as [d'|], (cd_declmap cd name) as [d|]; try discriminate.
  2:easy. (* not found *)
  destruct d; cbn in D; inversion D; subst d'.
  2:easy. (* found but it's a function decl *)
  repeat (split; trivial).
  f_equal.
  apply Agree. lia.
}
{ (* UnOp *)
  destruct op.
  { (* ~ *)
    cbn.
    do_unop builtin_name_uint256_not unop_not.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    remember (dst =? n)%N as dst_n. symmetry in Heqdst_n.
    destruct dst_n; [f_equal|]; apply Agree; lia.
  }
  { (* logical not (iszero) *)
    cbn.
    do_unop builtin_name_uint256_iszero unop_iszero.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    remember (dst =? n)%N as dst_n. symmetry in Heqdst_n.
    destruct dst_n; [f_equal|]; apply Agree; lia.
  }
  (* unary -, the stupidest operator *)
  unfold Base.interpret_unop. rewrite<- uint256_checked_neg_ok.
  unfold uint256_checked_neg.
  cbn.
  assert (E: let _ := memory_impl in OpenArray.get mem' src = OpenArray.get mem src).
  { apply Agree. lia. }
  rewrite E.
  destruct (Z_of_uint256 (OpenArray.get mem src) =? 0)%Z.
  {
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    remember (dst =? n)%N as dst_n. symmetry in Heqdst_n.
    destruct dst_n; [f_equal|]; apply Agree; lia.
  }
  cbn.
  repeat (split; trivial).
  { now rewrite OpenArray.put_same. }
  intros n L.
  repeat rewrite OpenArray.put_ok.
  remember (scratch =? n)%N as e. symmetry in Heqe.
  destruct e. { rewrite N.eqb_eq in Heqe. lia. }
  apply (Agree n L).
}
3:{ (* BinOp *)
  unfold Base.interpret_binop.
  assert (NoAliasDstScratch: (dst =? scratch)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasDstScratch1: (dst =? N.succ scratch)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasDstScratch2: (dst =? N.succ (N.succ scratch))%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratchDst: (scratch =? dst)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratch1Dst: (N.succ scratch =? dst)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratch2Dst: (N.succ (N.succ scratch) =? dst)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasSrc1Scratch: (src1 =? scratch)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasSrc1Scratch1: (src1 =? N.succ scratch)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasSrc1Scratch2: (src1 =? N.succ (N.succ scratch))%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratchSrc1: (scratch =? src1)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratch1Src1: (N.succ scratch =? src1)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratch2Src1: (N.succ (N.succ scratch) =? src1)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasSrc2Scratch: (src2 =? scratch)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasSrc2Scratch1: (src2 =? N.succ scratch)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasSrc2Scratch2: (src2 =? N.succ (N.succ scratch))%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratchSrc2: (scratch =? src2)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratch1Src2: (N.succ scratch =? src2)%N = false) by (rewrite N.eqb_neq; lia).
  assert (NoAliasScratch2Src2: (N.succ (N.succ scratch) =? src2)%N = false) by (rewrite N.eqb_neq; lia).

  Local Ltac aliasing
  := repeat (rewrite N.eqb_refl
          || rewrite noalias1
          || rewrite noalias2
          || rewrite noalias1'
          || rewrite noalias2'
          || match goal with
             | H: (_ =? _)%N = false |- _ => rewrite H
             | H: forall x: N, (_ =? _)%N = false |- _ => rewrite H
             | H: (?a < ?b)%N |- _ => rewrite (lt_ne_helper a b H)
             | H: (?a < ?b)%N |- _ => rewrite (lt_ne1_helper a b H)
             | H: (?a < ?b)%N |- _ => rewrite (lt_ne2_helper a b H)
             | H: (?a < ?b)%N |- _ => rewrite (lt_ne_helper' a b H)
             | H: (?a < ?b)%N |- _ => rewrite (lt_ne1_helper' a b H)
             | H: (?a < ?b)%N |- _ => rewrite (lt_ne2_helper' a b H)
             end).
  assert (R1: let _ := memory_impl in OpenArray.get mem' src1 = OpenArray.get mem src1)
    by (apply Agree; lia). cbn in R1.
  assert (R2: let _ := memory_impl in OpenArray.get mem' src2 = OpenArray.get mem src2)
    by (apply Agree; lia). cbn in R2.

  destruct op.
  { (* < *)
    cbn.
    do_binop builtin_name_uint256_lt binop_lt.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    aliasing. destruct (dst =? n)%N; aliasing.
    { f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* >= *)
    cbn. rewrite uint256_le_ok.
    do_binop builtin_name_uint256_lt binop_lt.
    do_unop builtin_name_uint256_iszero unop_iszero.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal. f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* > *)
    cbn.
    do_binop builtin_name_uint256_lt binop_lt.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { rewrite uint256_gt_ok. f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* >= *)
    cbn. rewrite uint256_ge_ok.
    do_binop builtin_name_uint256_lt binop_lt.
    do_unop builtin_name_uint256_iszero unop_iszero.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal. f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* == *)
    cbn.
    do_binop builtin_name_uint256_eq binop_eq.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* != *)
    cbn. rewrite uint256_ne_ok.
    do_binop builtin_name_uint256_eq binop_eq.
    do_unop builtin_name_uint256_iszero unop_iszero.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal. f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* | *)
    cbn.
    do_binop builtin_name_uint256_or binop_or.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* & *)
    cbn. do_binop builtin_name_uint256_and binop_and.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* ^ *)
    cbn. do_binop builtin_name_uint256_xor binop_xor.
    repeat (split; trivial).
    intros n L.
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; aliasing.
    { f_equal; apply Agree; lia. }
    apply (Agree n L).
  }
  { (* << *)
    cbn.
    do_binop builtin_name_uint256_shl binop_shl.
    replace (scratch + 2)%N with (N.succ (N.succ scratch)) by lia.
    repeat rewrite OpenArray.put_ok. aliasing.
    do_binop builtin_name_uint256_shr binop_shr.
    repeat rewrite OpenArray.put_ok. aliasing.
    do_binop builtin_name_uint256_eq binop_eq.
    repeat rewrite OpenArray.put_ok. aliasing.
    assert (E := let _ := memory_impl in
                 uint256_checked_shl_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    unfold uint256_checked_shl in E.
    unfold uint256_eq. cbn in E.
    remember (Z_of_uint256
         (uint256_shr (uint256_shl (OpenArray.get mem' src1) (OpenArray.get mem' src2))
            (OpenArray.get mem' src2)) =? Z_of_uint256 (OpenArray.get mem' src1))%Z as q.
    clear Heqq. unfold one256. unfold zero256.
    destruct q; rewrite uint256_ok; cbn; rewrite<- R1; rewrite<- R2; rewrite<- E; cbn;
      repeat (split; trivial); intros n L; repeat rewrite OpenArray.put_ok; aliasing.
    1:destruct (dst =? n)%N; trivial.
    all:apply (Agree n L).
  }
  { (* >> *)
    cbn.
    do_binop builtin_name_uint256_shr binop_shr.
    assert (E := let _ := memory_impl in
                 uint256_shr_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    cbn in E. rewrite R1 in E. rewrite R2 in E. rewrite<- E.
    repeat (split; trivial); intros n L.
    repeat rewrite OpenArray.put_ok. aliasing.
    destruct (dst =? n)%N; [f_equal|]; apply Agree; lia.
  }
  { (* + *)
    cbn.
    do_binop builtin_name_uint256_add binop_add.
    do_binop builtin_name_uint256_lt binop_lt.
    replace (scratch + 2)%N with (N.succ (N.succ scratch)) by lia.
    repeat rewrite OpenArray.put_ok. aliasing.
    assert (E := let _ := memory_impl in
                 uint256_checked_add_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    unfold uint256_checked_add in E.
    cbn in E. rewrite R1 in E. rewrite R2 in E. rewrite<- E.
    unfold uint256_lt.
    rewrite Z.geb_leb.
    rewrite Z.leb_antisym.
    rewrite Bool.if_negb.
    clear E.
    rewrite R1. rewrite R2. unfold one256. unfold zero256.
    destruct (Z_of_uint256 (uint256_add (OpenArray.get mem src1) (OpenArray.get mem src2)) <?
               Z_of_uint256 (OpenArray.get mem src1))%Z; rewrite uint256_ok; cbn;
      repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
    { apply (Agree n L). }
    destruct (dst =? n)%N; [f_equal|]; apply Agree; lia.
  }
  { (* - *)
    cbn.
    do_binop builtin_name_uint256_lt binop_lt.
    repeat rewrite OpenArray.put_ok. aliasing.
    do_binop builtin_name_uint256_sub binop_sub.
    replace (scratch + 2)%N with (N.succ (N.succ scratch)) by lia.
    repeat rewrite OpenArray.put_ok. aliasing.
    assert (E := let _ := memory_impl in
                 uint256_checked_sub_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    unfold uint256_checked_sub in E.
    cbn in E. rewrite R1 in E. rewrite R2 in E. rewrite<- E. clear E.
    rewrite Z.geb_leb.
    rewrite Z.leb_antisym.
    rewrite Bool.if_negb.
    unfold uint256_lt.
    rewrite R1. rewrite R2. unfold one256. unfold zero256.
    destruct (Z_of_uint256 (OpenArray.get mem src1) <? Z_of_uint256 (OpenArray.get mem src2))%Z;
      rewrite uint256_ok; cbn;
      repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing;
      destruct (dst =? n)%N.
    3:f_equal.
    all:apply (Agree n L).
  }
  { (* * *)
    cbn.
    do_binop builtin_name_uint256_mul binop_mul.
    do_binop builtin_name_uint256_div binop_div.
    replace (scratch + 2)%N with (N.succ (N.succ scratch)) by lia.
    repeat rewrite OpenArray.put_ok. aliasing.
    do_binop builtin_name_uint256_eq binop_eq.
    repeat rewrite OpenArray.put_ok. aliasing.
    assert (E := let _ := memory_impl in
                 uint256_checked_mul_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    unfold uint256_checked_mul in E.
    cbn in E. rewrite R1 in E. rewrite R2 in E. rewrite<- E. clear E.
    unfold uint256_eq.
    rewrite R1. rewrite R2. unfold one256. unfold zero256.
    destruct (Z_of_uint256 (OpenArray.get mem src1) =? 0)%Z.
    {
      repeat (split; trivial). intros n L.
      repeat rewrite OpenArray.put_ok. aliasing.
      destruct (dst =? n)%N; trivial; apply (Agree n L).
    }
    unfold zero256. unfold one256.
    destruct (Z_of_uint256
         (uint256_div (uint256_mul (OpenArray.get mem src1) (OpenArray.get mem src2))
            (OpenArray.get mem src1)) =? Z_of_uint256 (OpenArray.get mem src2))%Z;
      rewrite uint256_ok; cbn; repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
      2:apply (Agree n L).
      destruct (dst =? n)%N; trivial; apply (Agree n L).
  }
  { (* / *)
    cbn.
    rewrite R2.
    assert (E := let _ := memory_impl in
                 uint256_checked_div_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    unfold uint256_checked_div in E.
    cbn in E. rewrite R1 in E. rewrite R2 in E. rewrite<- E. clear E.
    destruct (Z_of_uint256 (OpenArray.get mem src2) =? 0)%Z.
    {
      cbn. rewrite OpenArray.put_ok. aliasing.
      repeat (split; trivial); intros n L;
        rewrite OpenArray.put_ok; aliasing.
      apply (Agree n L).
    }
    do_binop builtin_name_uint256_div binop_div.
    repeat rewrite OpenArray.put_ok. aliasing.
    unfold uint256_eq.
    repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
    destruct (dst =? n)%N. 2:apply (Agree n L).
    now f_equal.
  }
  { (* % *)
    cbn.
    rewrite R2.
    assert (E := let _ := memory_impl in
                 uint256_checked_mod_ok (OpenArray.get mem' src1) (OpenArray.get mem' src2)).
    unfold uint256_checked_mod in E.
    cbn in E. rewrite R1 in E. rewrite R2 in E. rewrite<- E. clear E.
    destruct (Z_of_uint256 (OpenArray.get mem src2) =? 0)%Z.
    {
      cbn. rewrite OpenArray.put_ok. aliasing.
      repeat (split; trivial); intros n L;
        rewrite OpenArray.put_ok; aliasing.
      apply (Agree n L).
    }
    do_binop builtin_name_uint256_mod binop_mod.
    repeat rewrite OpenArray.put_ok. aliasing.
    unfold uint256_eq.
    repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
    destruct (dst =? n)%N. 2:apply (Agree n L).
    now f_equal.
  }
  (* ** between non-consts is not supported *)
  contradiction.
}
{ (* PowConstBase *)
  simpl in *. (* cbn hangs *)
  assert (E := let _ := memory_impl in
               uint256_checked_pow_const_base_ok base (OpenArray.get mem' exp)).
  unfold uint256_checked_pow_const_base in E.
  unfold Base.interpret_binop.
   assert (R: let _ := memory_impl in OpenArray.get mem' exp = OpenArray.get mem exp)
    by (apply Agree; lia). cbn in R.
  rewrite R in E. rewrite<- E. clear E.
  remember (Z_of_uint256 base =? 0)%Z as base0.
  destruct base0.
  { (* 0 ** _ *)
    cbn.
    do_unop builtin_name_uint256_iszero unop_iszero.
    repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
    destruct (dst =? n)%N.
    { unfold uint256_iszero. now rewrite R. }
    apply (Agree n L).
  }
  remember (Z_of_uint256 base =? 1)%Z as base1.
  destruct base1.
  { (* 1 ** _ *)
    cbn.
    repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
    destruct (dst =? n)%N; trivial.
    apply (Agree n L).
  }
  remember (Z_of_uint256 base =? 2)%Z as base2.
  destruct base2.
  { (* 2 ** _ *)
    cbn.
    do_binop builtin_name_uint256_lt binop_lt.
    replace (scratch + 2)%N with (N.succ (N.succ scratch)) by lia.
    repeat rewrite OpenArray.put_ok; aliasing.
    do_binop builtin_name_uint256_shl binop_shl.
    repeat rewrite OpenArray.put_ok; aliasing.
    unfold uint256_lt. rewrite uint256_ok. cbn.
    unfold one256. unfold zero256.
    rewrite R.
    destruct (Z_of_uint256 (OpenArray.get mem exp) <? 256)%Z;
      rewrite uint256_ok; cbn;
      repeat (split; trivial); intros n L;
      repeat rewrite OpenArray.put_ok; aliasing.
    {
      destruct (dst =? n)%N; trivial.
      apply (Agree n L).
    }
    apply (Agree n L).
  }
  (* _ ** _ *)
  assert (BaseLower: (2 < Z_of_uint256 base)%Z).
  {
    symmetry in Heqbase0. apply Z.eqb_neq in Heqbase0.
    symmetry in Heqbase1. apply Z.eqb_neq in Heqbase1.
    symmetry in Heqbase2. apply Z.eqb_neq in Heqbase2.
    assert (K := uint256_range base).
    lia.
  }
  assert (MP := uint256_max_power_ok _ BaseLower). simpl in MP.
  destruct MP as (MP, _).
  assert (PowerUpper: (uint256_max_power (Z_of_uint256 base) < 256)%Z).
  {
    assert (D := Z.lt_ge_cases (uint256_max_power (Z_of_uint256 base)) 256%Z).
    case D; clear D; intro D. { exact D. }
    exfalso.
    enough (Z.pow_pos 2 256 <= Z_of_uint256 base ^ uint256_max_power (Z_of_uint256 base))%Z by lia.
    apply (Z.le_trans _ (Z_of_uint256 base ^ 256)).
    {
      rewrite Z.pow_pos_fold.
      apply Z.pow_le_mono_l.
      lia.
    }
    apply Z.pow_le_mono_r; lia.
  }
  simpl in *.
  do_binop_nocbn builtin_name_uint256_lt binop_lt.
  replace (scratch + 2)%N with (N.succ (N.succ scratch)) by lia.
  repeat rewrite OpenArray.put_ok; aliasing.
  unfold uint256_lt.
  rewrite Z.leb_antisym.
  rewrite Bool.if_negb.
  do_binop_nocbn builtin_name_uint256_pow binop_pow.
  repeat rewrite OpenArray.put_ok; aliasing.
  replace (scratch =? exp)%N with false by (symmetry; rewrite N.eqb_neq; lia).
  rewrite R.
  rewrite uint256_ok.
  assert (PowerLower: (0 <= uint256_max_power (Z_of_uint256 base))%Z) by apply binary_search_lower.
  rewrite Z.mod_small by lia.
  unfold one256. unfold zero256.
  destruct (uint256_max_power (Z_of_uint256 base) <? Z_of_uint256 (OpenArray.get mem exp))%Z;
    rewrite uint256_ok; simpl;
    repeat (split; trivial); intros n L;
    repeat rewrite OpenArray.put_ok; aliasing.
  { apply (Agree n L). }
  destruct (dst =? n)%N; trivial.
  apply (Agree n L).
}
{ (* PowConstExp *)
  simpl in *.
  assert (E := let _ := memory_impl in
               uint256_checked_pow_const_exponent_ok (OpenArray.get mem' base) exp).
  unfold uint256_checked_pow_const_exponent in E.
  unfold Base.interpret_binop.
   assert (R: let _ := memory_impl in OpenArray.get mem' base = OpenArray.get mem base)
    by (apply Agree; lia). cbn in R.
  rewrite R in E. rewrite<- E. clear E.
  remember (Z_of_uint256 exp =? 0)%Z as exp0.
  destruct exp0.
  {
    simpl.
    repeat (split; trivial); intros n L;
    repeat rewrite OpenArray.put_ok.
    destruct (dst =? n)%N; trivial.
    apply (Agree n L).
  }
  remember (Z_of_uint256 exp =? 1)%Z as exp1.
  destruct exp1.
  {
    simpl.
    do_binop_nocbn builtin_name_uint256_pow binop_pow.
    repeat (split; trivial); intros n L;
    repeat rewrite OpenArray.put_ok. aliasing.
    destruct (dst =? n)%N; trivial.
    {
      rewrite R.
      symmetry in Heqexp1.
      apply Z.eqb_eq in Heqexp1.
      unfold uint256_pow.
      unfold one256.
      rewrite Heqexp1.
      now rewrite uint256_ok.
    }
    apply (Agree n L).
  }
  simpl.
  do_binop_nocbn builtin_name_uint256_lt binop_lt.
  repeat rewrite OpenArray.put_ok. aliasing.
  unfold uint256_lt.
  rewrite R.
  rewrite uint256_ok.
  assert (ExpLower: (2 <= Z_of_uint256 exp)%Z).
  {
    assert (K := uint256_range exp). 
    symmetry in Heqexp0. apply Z.eqb_neq in Heqexp0.
    symmetry in Heqexp1. apply Z.eqb_neq in Heqexp1.
    lia.
  }
  assert (BaseLower: (0 <= uint256_max_base (Z_of_uint256 exp))%Z) by apply binary_search_lower.
  assert (BaseUpper: (uint256_max_base (Z_of_uint256 exp) <= 2 ^ 128)%Z).
  {
    assert (MB := uint256_max_base_ok _ ExpLower). simpl in MB.
    destruct MB as (MB, _).
    rewrite Z.pow_pos_fold in MB.
    assert (D := Z.le_gt_cases (uint256_max_base (Z_of_uint256 exp)) (2 ^ 128) %Z).
    case D; clear D; intro D. { exact D. }
    exfalso.
    enough (2 ^ 256 <= uint256_max_base (Z_of_uint256 exp) ^ Z_of_uint256 exp)%Z by lia.
    replace (2 ^ 256)%Z with ((2 ^ 128) ^ 2)%Z by trivial.
    apply (Z.le_trans _ ((2 ^ 128) ^ Z_of_uint256 exp)).
    { apply Z.pow_le_mono_r; lia. }
    apply Z.lt_le_incl.
    apply Z.pow_lt_mono_l; lia.
  }
  rewrite Z.mod_small by lia.
  do_binop_nocbn builtin_name_uint256_pow binop_pow.
  repeat rewrite OpenArray.put_ok; aliasing.
  rewrite Z_ltb_succ_r.
  unfold zero256. unfold one256.
  destruct (Z_of_uint256 (OpenArray.get mem base) <=? uint256_max_base (Z_of_uint256 exp))%Z;
    repeat rewrite OpenArray.put_ok; rewrite uint256_ok; simpl; aliasing;
    repeat (split; trivial); intros n L; repeat rewrite OpenArray.put_ok; aliasing;
    destruct (dst =? n)%N; trivial; apply (Agree n L).
}
