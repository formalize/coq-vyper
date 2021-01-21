From Coq Require Import Arith NArith Lia.

From Vyper Require Import List2.

Local Open Scope list_scope.

(** An typical array container. Coq's standard [Vector] is very similar to this. *)
Class class {Value: Type} (Zero: Value) (length: N) (A: Type) := {
  get: A -> forall i: N, (i < length)%N -> Value;
  zeros: A;

  zeros_ok: forall (i: N) (Ok: (i < length)%N),
              get zeros i Ok = Zero;

  put: A -> forall (i: N) (Ok: (i < length)%N), Value -> A;

  put_ok: forall (a: A) (n: N) (OkN: (n < length)%N) (k: N) (OkK: (k < length)%N) (v: Value),
            get (put a n OkN v) k OkK
             =
            if (n =? k)%N
              then v
              else get a k OkK;

  to_list: A -> list Value;

  to_list_ok: forall (a: A) (n: N) (OkN: (n < length)%N),
                get a n OkN = List.nth (N.to_nat n) (to_list a) Zero;

  to_list_len: forall (a: A),
                 List.length (to_list a) = N.to_nat length;

  from_list: forall (l: list Value) (Ok: List.length l = N.to_nat length), A;
  from_list_ok: forall (l: list Value) (OkL: List.length l = N.to_nat length)
                       (n: N) (OkN: (n < length)%N),
                  get (from_list l OkL) n OkN = List.nth (N.to_nat n) l Zero;

  (** Given an offset and a count, convert the corresponding subarray to a list. *)
  view: A -> forall (offset count: N) (Ok: (offset + count <= length)%N), list Value;
  view_len: forall (a: A) (offset count: N) (Ok: (offset + count <= length)%N),
              List.length (view a offset count Ok) = N.to_nat count;
  view_ok: forall (a: A) (offset count: N) (Ok: (offset + count <= length)%N)
                  (n: N) (OkN: (n < count)%N) (Ok': (offset + n < length)%N),
             List.nth_error (view a offset count Ok) (N.to_nat n) = Some (get a (offset + n)%N Ok');
}.

Lemma put_same {Value: Type} {Zero: Value} {A: Type} (len: N) (C: class Zero len A)
               (a: A) (n: N) (OkN: (n < len)%N) (v: Value):
  get (put a n OkN v) n OkN = v.
Proof.
rewrite put_ok.
enough (H: (n =? n)%N = true) by now rewrite H.
now apply N.eqb_eq.
Qed.


Section ListInst.
  Context {Value: Type} (Zero: Value) (len: N).

  Definition t := { l : list Value | List.length l = N.to_nat len }.

  Definition list_get (a: t) (n: N) (Ok: (n < len)%N)
  : Value
  := List.nth (N.to_nat n) (proj1_sig a) Zero.

  Definition list_zeros
  : t
  := exist _ (List.repeat Zero (N.to_nat len)) (List.repeat_length _ _).

  Lemma list_zeros_ok (i: N) (Ok: (i < len)%N):
     list_get list_zeros i Ok = Zero.
  Proof.
  cbn. clear Ok.
  remember (N.to_nat i) as k. clear Heqk i.
  remember (N.to_nat len) as n. clear Heqn len.
  revert k.
  induction n as [|n]; intro k; destruct k as [|k]; try easy.
  cbn.
  apply IHn.
  Qed.

  Local Lemma list_put_helper (a: t) (n: N) (Ok: (n < len)%N) (v: Value):
    let i := N.to_nat n in
    let l := proj1_sig a in
    List.length (List.firstn i l ++ v :: List.skipn (S i) l) = N.to_nat len.
  Proof.
  cbn.
  assert (OkA := proj2_sig a). cbn in OkA.
  rewrite List.app_length.
  rewrite List.firstn_length_le by lia.
  cbn.
  destruct (proj1_sig a). { cbn in *. lia. }
  cbn in OkA.
  rewrite List.skipn_length. lia.
  Qed.

  Definition list_put (a: t) (n: N) (Ok: (n < len)%N) (v: Value)
  : t
  := let i := N.to_nat n in
     let l := proj1_sig a in
     exist _ (List.firstn i l ++ v :: List.skipn (S i) l) (list_put_helper a n Ok v).

  Lemma list_put_ok (a: t) (n: N) (OkN: (n < len)%N) (k: N) (OkK: (k < len)%N) (v: Value):
    list_get (list_put a n OkN v) k OkK = (if (n =? k)%N then v else list_get a k OkK).
  Proof.
  cbn.
  remember (n =? k)%N as e.
  apply N.compare_lt_iff in OkN.
  (* apply N.compare_lt_iff in OkK. <- interesting example of deptypes making a weird error *)
  rewrite N2Nat.inj_compare in OkN.
  rewrite N.eqb_compare in Heqe.
  rewrite N2Nat.inj_compare in Heqe.
  rewrite<- Nat.eqb_compare in Heqe.
  apply nat_compare_lt in OkN.
  unfold list_get.
  apply N.compare_lt_iff in OkK.
  rewrite N2Nat.inj_compare in OkK.
  apply nat_compare_lt in OkK.
  remember (N.to_nat k) as k'. clear k Heqk'. rename k' into k.
  remember (N.to_nat n) as n'. clear n Heqn'. rename n' into n.
  assert (OkA := proj2_sig a). cbn in OkA.
  destruct (proj1_sig a) as [|head]. { cbn in *. lia. } clear a.
  remember (N.to_nat len) as len'. clear len Heqlen'. rename len' into len.
  revert head len OkA n OkN k OkK e Heqe. induction l; intros; cbn.
  {
    rewrite List.skipn_nil. cbn in OkA. subst len.
    assert (n = 0) by lia; subst.
    assert (k = 0) by lia; subst.
    easy.
  }
  cbn in OkA.
  destruct n as [|n'], k as [|k']; cbn in *; subst; try easy.
  apply lt_S_n in OkN. apply lt_S_n in OkK.
  apply (IHl a (S (length l)) eq_refl n' OkN k' OkK (n' =? k') eq_refl).
  Qed.

  Definition list_view (a: t) (offset count: N)
  : list Value
  := List.firstn (N.to_nat count) (List.skipn (N.to_nat offset) (proj1_sig a)).

  Lemma list_view_len (a: t) (offset count: N) (Ok: (offset + count <= len)%N):
    List.length (list_view a offset count) = N.to_nat count.
  Proof.
  unfold list_view.
  apply List.firstn_length_le.
  rewrite List.skipn_length.
  assert (OkA := proj2_sig a). cbn in OkA.
  rewrite OkA.
  lia.
  Qed.

  Lemma list_view_ok (a: t) (offset count: N) (Ok: (offset + count <= len)%N)
                     (n: N) (OkN: (n < count)%N) (OkSum : (offset + n < len)%N):
    List.nth_error (list_view a offset count) (N.to_nat n) = Some (list_get a (offset + n) OkSum).
  Proof.
  unfold list_view. unfold list_get.
  assert (OkL := proj2_sig a). cbn in OkL.
  remember (proj1_sig a) as l. clear Heql a.

  apply N.compare_lt_iff in OkN.
  apply N.compare_lt_iff in OkSum.
  apply N.compare_le_iff in Ok.

  rewrite N2Nat.inj_compare in *.
  rewrite N2Nat.inj_add in *.
  remember (N.to_nat n) as n'. clear n Heqn'. rename n' into n.
  remember (N.to_nat count) as count'. clear count Heqcount'. rename count' into count.
  remember (N.to_nat offset) as offset'. clear offset Heqoffset'. rename offset' into offset.
  remember (N.to_nat len) as len'. clear len Heqlen'. rename len' into len.

  apply nat_compare_lt in OkSum.
  apply nat_compare_lt in OkN.
  apply nat_compare_le in Ok.

  revert len OkL offset count n Ok OkSum OkN. induction l as [|head]; intros.
  { cbn in OkL. subst. lia. }
  cbn.
  destruct count. { lia. }
  cbn.
  destruct offset; cbn.
  {
    destruct n. { easy. }
    cbn. cbn in OkL.
    rewrite List.nth_error_nth' with (d := Zero). 2:{ rewrite List.firstn_length_le; lia. }
    f_equal.
    apply nth_firstn.
    lia.
  }
  cbn in OkL.
  assert (SL := List.skipn_length offset l).
  remember (List.skipn offset l) as s.
  destruct s. { cbn in SL. lia. }
  rewrite<- (IHl (length l) eq_refl offset (S count)); try lia.
  now rewrite<- Heqs.
  Qed.

  Definition list_inst
  : class Zero len t
  := {| get := list_get
      ; zeros := list_zeros
      ; zeros_ok := list_zeros_ok
      ; put := list_put
      ; put_ok := list_put_ok
      ; to_list a := proj1_sig a
      ; to_list_ok a n OkN := eq_refl
      ; to_list_len a := proj2_sig a
      ; from_list := exist _
      ; from_list_ok a n k OkK := eq_refl
      ; view a offset count _ := list_view a offset count
      ; view_len := list_view_len
      ; view_ok := list_view_ok
     |}.

End ListInst.