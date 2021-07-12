(** 
  This file continues theories/Numbers/Cyclic/Int63/Int63.v from the standard library of Coq.
 *)

From Coq Require Import Int63 NArith ZArith Lia.

From Vyper Require Import Logic2 Arith2.

Definition uint63 := int.
Definition Z_of_uint63 := to_Z.
Definition uint63_of_Z := of_Z.

Ltac rewrite_Z_of_uint63 
:= repeat (rewrite lsl_spec
        || rewrite lsr_spec
        || rewrite land_spec'
        || rewrite lor_spec'
        || rewrite lxor_spec'
        || rewrite add_spec
        || rewrite sub_spec
        || rewrite mul_spec
        || rewrite div_spec
        || rewrite mod_spec
        || rewrite ltb_spec
        || rewrite leb_spec).

Definition N_of_uint63 (i: uint63): N
:= Z.to_N (to_Z i).
Definition uint63_of_N (n: N): uint63
:= of_Z (Z.of_N n).

Definition nat_of_uint63 (i: uint63): nat
:= N.to_nat (N_of_uint63 i).

Definition uint63_of_nat (n: nat): uint63
:= uint63_of_N (N.of_nat n).


Lemma Z_of_uint63_nonneg (i: uint63):
  (0 <= to_Z i)%Z.
Proof.
assert(B := to_Z_bounded i).
tauto.
Qed.

Lemma uint63_ltb_Z (x y: uint63):
  (x <? y)%int63 = (to_Z x <? to_Z y)%Z.
Proof.
apply (relation_quad (fun x y => iff_refl _) Z.ltb_lt).
apply ltb_spec.
Qed.

Lemma uint63_leb_Z (x y: uint63):
  (x <=? y)%int63 = (to_Z x <=? to_Z y)%Z.
Proof.
apply (relation_quad (fun x y => iff_refl _) Z.leb_le).
apply leb_spec.
Qed.

Lemma uint63_ltb_N (x y: uint63):
  (x <? y)%int63 = (N_of_uint63 x <? N_of_uint63 y)%N.
Proof.
rewrite uint63_ltb_Z.
unfold N_of_uint63.
assert (Bx := to_Z_bounded x).
assert (By := to_Z_bounded y).
destruct Bx as (Bx, _).
destruct By as (By, _).
assert (L := Z2N.inj_lt (to_Z x) (to_Z y) Bx By).
clear Bx By.
apply (relation_quad Z.ltb_lt N.ltb_lt).
apply L.
Qed.

Lemma uint63_leb_N (x y: uint63):
  (x <=? y)%int63 = (N_of_uint63 x <=? N_of_uint63 y)%N.
Proof.
rewrite uint63_leb_Z.
unfold N_of_uint63.
assert (Bx := to_Z_bounded x).
assert (By := to_Z_bounded y).
destruct Bx as (Bx, _).
destruct By as (By, _).
assert (L := Z2N.inj_le (to_Z x) (to_Z y) Bx By).
clear Bx By.
apply (relation_quad Z.leb_le N.leb_le).
apply L.
Qed.

Lemma uint63_get_high_digit (i k: uint63)
                            (B: (63 <=? k)%int63 = true):
  get_digit i k = false.
Proof.
unfold get_digit.
enough (U: (1 << k = 0)%int63).
{ 
  rewrite U.
  rewrite uint63_ltb_Z.
  rewrite land_spec'.
  rewrite to_Z_0.
  rewrite Z.land_0_r.
  trivial.
}
match goal with
|- ?lhs = ?rhs => rewrite<- (of_to_Z lhs); rewrite<- (of_to_Z rhs)
end.
f_equal.
rewrite lsl_spec.
rewrite to_Z_1. rewrite to_Z_0.
rewrite Z.mul_1_l.
rewrite uint63_leb_Z in B.
replace (to_Z 63%int63) with 63%Z in B. 2:{ trivial. }
remember (to_Z k) as n. clear i k Heqn.
remember (n - 63)%Z as m.
assert (Q: n = (m + 63)%Z). { subst. lia. }
subst n.
rewrite Z.pow_add_r; rewrite Z.leb_le in B; [ | lia | lia ].
apply Z_mod_mult.
Qed.

Lemma uint63_testbit_Z (i k: uint63):
  get_digit i k = Z.testbit (to_Z i) (to_Z k).
Proof.
remember (k <? 63)%int63 as Low. symmetry in HeqLow.
destruct Low.
{ 
  unfold get_digit.
  rewrite uint63_ltb_Z.
  rewrite land_spec'.
  rewrite lsl_spec.
  remember (to_Z i) as n.
  remember (to_Z k) as m.
  replace (to_Z 0%int63) with 0%Z. 2:{ trivial. }
  replace (to_Z 1%int63) with 1%Z. 2:{ trivial. }
  rewrite Z.mul_1_l.
  rewrite Z.mod_small.
  2:{
    split. { apply Z.pow_nonneg. rewrite<- Z.leb_le. trivial. }
    unfold wB.
    apply Z.pow_lt_mono_r.
    { rewrite<- Z.ltb_lt. trivial. }
    { rewrite<- Z.leb_le. trivial. }
    subst.
    rewrite ltb_spec in HeqLow.
    assumption.
}
symmetry.
apply Z_testbit_alt.
assert (BN := to_Z_bounded i).
subst. tauto.
assert (BM := to_Z_bounded k).
subst. tauto.
}
assert(Bk: (63 <= to_Z k)%Z).
{
  rewrite uint63_ltb_Z in HeqLow.
  replace (to_Z 63%int63) with 63%Z in HeqLow. 2:{ trivial. }
  rewrite Z.ltb_ge in HeqLow.
  assumption.
}
rewrite uint63_get_high_digit.
{
  symmetry.
  assert(Bi := to_Z_bounded i).
  apply Z_testbit_high.
  { assert(BK := to_Z_bounded k). tauto. }
  split. { tauto. }
  apply (Z.lt_le_trans _ wB _). { tauto. }
  apply Z.pow_le_mono_r. { rewrite<- Z.ltb_lt. trivial. }
  apply Bk.
}
rewrite leb_spec.
apply Bk.
Qed.

Lemma uint63_testbit_N_low_digit (n k: N)
                                  (B: (k < 63)%N):
  N.testbit n k = get_digit (uint63_of_N n) (uint63_of_N k).
Proof.
rewrite<- N2Z.inj_testbit.
rewrite uint63_testbit_Z.
unfold uint63_of_N.
repeat rewrite of_Z_spec.
rewrite (Z.mod_small (Z.of_N k)). 2:{ unfold wB. cbn. lia. }
symmetry.
apply Z.mod_pow2_bits_low.
unfold size.
lia.
Qed.

Lemma uint63_bit_get_digit (i k: uint63):
  bit i k = get_digit i k.
Proof.
rewrite bitE. rewrite uint63_testbit_Z. trivial.
Qed.

(**************************************************************************)

Lemma uint63_land_N (x y: uint63):
  N_of_uint63 (x land y)%int63 = N.land (N_of_uint63 x) (N_of_uint63 y).
Proof.
unfold N_of_uint63.
rewrite land_spec'.
apply Z_to_N_land; apply Z_of_uint63_nonneg.
Qed.

Lemma uint63_lor_N (x y: uint63):
  N_of_uint63 (x lor y)%int63 = N.lor (N_of_uint63 x) (N_of_uint63 y).
Proof.
unfold N_of_uint63.
rewrite lor_spec'.
apply Z_to_N_lor; apply Z_of_uint63_nonneg.
Qed.

Lemma uint63_lxor_N (x y: uint63):
  N_of_uint63 (x lxor y)%int63 = N.lxor (N_of_uint63 x) (N_of_uint63 y).
Proof.
unfold N_of_uint63.
rewrite lxor_spec'.
apply Z_to_N_lxor; apply Z_of_uint63_nonneg.
Qed.

(**************************************************************************)

Lemma uint63_add_sub_assoc (n m p: int):
  (n + (m - p))%int63 = (n + m - p)%int63.
Proof.
apply to_Z_inj.
repeat (rewrite add_spec || rewrite sub_spec).
rewrite Z.add_mod_idemp_r by discriminate.
repeat rewrite<- Z.add_opp_r.
rewrite Z.add_mod_idemp_l by discriminate.
now rewrite Z.add_assoc.
Qed.

Lemma uint63_add_opp_r (n m: int):
  (n + - m)%int63 = (n - m)%int63.
Proof.
apply to_Z_inj.
repeat (rewrite add_spec || rewrite sub_spec || rewrite opp_spec).
rewrite Z.add_mod_idemp_r by discriminate.
now repeat rewrite Z.add_opp_r.
Qed.

Lemma uint63_to_Z_ne_0 (n: int) (NZ: n <> 0%int63):
  to_Z n <> 0%Z.
Proof.
intro H.
rewrite<- (of_to_Z n) in NZ.
rewrite H in NZ.
cbn in NZ.
contradiction.
Qed.

Lemma uint63_dec_to_Z (n: int) (NZ: n <> 0%int63):
  to_Z (n - 1) = (to_Z n - 1)%Z.
Proof.
rewrite sub_spec.
replace (to_Z 1%int63) with 1%Z by trivial.
apply Z.mod_small.
assert (A := to_Z_bounded n).
assert (P := uint63_to_Z_ne_0 n NZ).
lia.
Qed.

(******************************************************************************************)

Lemma head0_upper (n: int):
  (to_Z (head0 n) <= 63)%Z.
Proof.
assert (Spec := head0_spec n).
assert (Spec0 := head00_spec n).
assert (Bound := to_Z_bounded n).
assert (Cases0 := Zle_lt_or_eq _ _ (proj1 Bound)). (*  0 < n  \/  0 = n  *)
case Cases0; clear Cases0.
{
  intro L. assert (B := proj2 (Spec L)).
  unfold wB in B.
  replace (Z.of_nat size) with 63%Z in B by trivial.
  assert (F: (2 ^ φ (head0 n)%int63 < 2 ^ 63)%Z) by nia.
  apply Z.pow_lt_mono_r_iff in F; lia.
}
intro E. symmetry in E. assert (G := Spec0 E).
replace (to_Z digits) with 63%Z in G by trivial.
lia.
Qed.

Lemma head0_zero (n: int):
  to_Z (head0 n) = 63%Z <-> n = 0%int63.
Proof.
split. 2:{ intro. now subst. }
intro E.
assert (Spec := head0_spec n).
assert (Spec0 := head00_spec n).
assert (Bound := to_Z_bounded n).
assert (Cases0 := Zle_lt_or_eq _ _ (proj1 Bound)). (*  0 < n  \/  0 = n  *)
case Cases0; clear Cases0.
{ (* shameless copy from head0_upper *)
  intro L. assert (B := proj2 (Spec L)).
  unfold wB in B.
  replace (Z.of_nat size) with 63%Z in B by trivial.
  assert (F: (2 ^ φ (head0 n)%int63 < 2 ^ 63)%Z) by nia.
  apply Z.pow_lt_mono_r_iff in F; lia.
}
intro H.
rewrite<- (of_to_Z n). now rewrite<- H.
Qed.

Lemma head0_single (n: int) (U: (n <? digits = true)%int63):
  head0 (lsl 1 n) = (digits - 1 - n)%int63.
Proof.
assert (Spec := head0_spec (lsl 1 n)).
assert (Q: to_Z (1 << n)%int63 = (2 ^ to_Z n)%Z).
{
  rewrite (lsl_spec 1 n).
  replace (to_Z 1) with 1%Z by trivial.
  rewrite Z.mul_1_l.
  apply Z.mod_small_iff. { discriminate. }
  left.
  split. { now apply Z.pow_nonneg. }
  apply Z.pow_lt_mono_r; try easy.
  replace (Z.of_nat size) with (to_Z digits) by trivial.
  apply ltb_spec. exact U.
}
rewrite Q in Spec. clear Q.
assert (W: (0 < 2 ^ φ (n)%int63)%Z).
{
  apply Z.pow_pos_nonneg. { easy. }
  apply to_Z_bounded.
}
apply Spec in W. clear Spec.
rewrite<- Z.pow_add_r in W by apply to_Z_bounded.
remember (to_Z (head0 (1 << n))%int63 + to_Z n)%Z as k.
assert (K: k = 62%Z).
{
  subst.
  assert (B: (0 <= to_Z (head0 (1 << n))%int63 + φ (n)%int63 < wB)%Z).
  {
    assert (H := head0_upper (1 << n)%int63).
    assert (P: (to_Z n < 63)%Z).
    {
      rewrite ltb_spec in U.
      apply U.
    }
    replace wB with (2^63)%Z by trivial.
    assert (L := to_Z_bounded (head0 (1 << n))%int63).
    assert (L' := to_Z_bounded n).
    lia.
  }
  assert (R := Z.mod_small (to_Z (head0 (1 << n))%int63 + to_Z n) wB).
  (* rewrite<- R in * by apply B doesn't work! *)
  rewrite<- R in W by apply B.
  rewrite<- R by apply B.
  clear B R.
  rewrite<- add_spec in *.
  assert (X := to_Z_bounded (head0 (1 << n) + n)%int63).
  remember (to_Z (head0 (1 << n) + n)%int63) as x.
  clear Heqx.
  replace (wB / 2)%Z with (2 ^ 62)%Z in W by trivial.
  replace wB with (2 ^ 63)%Z in W by trivial.
  destruct W as (A, B).
  rewrite<- Z.pow_le_mono_r_iff in A by lia.
  rewrite<- Z.pow_lt_mono_r_iff in B by lia.
  lia.
}
rewrite K in Heqk. subst k. clear W.
replace (digits - 1)%int63 with 62%int63 by trivial.
rewrite<- of_to_Z. rewrite<- of_to_Z at 1. f_equal.
assert (X := to_Z_bounded (head0 (1 << n))).
assert (XU := head0_upper (1 << n)%int63).
remember (to_Z (head0 (1 << n))) as x. clear Heqx.
rewrite sub_spec. replace (to_Z 62) with 62%Z by trivial.
rewrite ltb_spec in U.
assert (Y := to_Z_bounded n).
remember (to_Z n) as y. clear Heqy.
cbn in U.
rewrite Z.mod_small by lia.
lia.
Qed.

(******************************************************************************************)

(** This form of [tail0_spec] avoids [exists]. *)
Lemma tail0_spec' (x: int) (NZ: (0 < to_Z x)%Z):
  let y := Z.shiftr (to_Z x) (Z.succ (to_Z (tail0 x))) in
  to_Z x = ((2 * y + 1) * 2 ^ (to_Z (tail0 x)))%Z.
Proof.
assert (Spec := tail0_spec x NZ).
intro y. unfold y. clear y.
destruct Spec as (y, (L, Spec)).
rewrite Spec at 1. repeat f_equal.
assert (P := to_Z_bounded (tail0 x)).
remember (to_Z (tail0 x)) as p. clear Heqp.
assert (X := to_Z_bounded x).
remember (to_Z x) as n. clear Heqn. subst n.
rewrite Z.shiftr_div_pow2 by lia.
rewrite<- Z.add_1_l.
rewrite Z.pow_add_r by lia.
rewrite Z.div_mul_cancel_r by (apply pow2_nz; lia).
replace (2 ^ 1)%Z with 2%Z by trivial.
rewrite Z.mul_comm. rewrite Z.div_add_l by discriminate.
cbn. lia.
Qed.

Lemma tail0_upper (n: int):
  (to_Z (tail0 n) <= 63)%Z.
Proof.
assert (Spec := tail0_spec n).
assert (Spec0 := tail00_spec n).
assert (Bound := to_Z_bounded n).
assert (Cases0 := Zle_lt_or_eq _ _ (proj1 Bound)). (*  0 < n  \/  0 = n  *)
case Cases0; clear Cases0.
{
  intro L.
  assert (B := Spec L). destruct B as (y, (Ly, B)).
  rewrite B in Bound.
  unfold wB in Bound.
  replace (Z.of_nat size) with 63%Z in Bound by trivial.
  assert (F: (2 ^ φ (tail0 n)%int63 < 2 ^ 63)%Z) by nia.
  apply Z.pow_lt_mono_r_iff in F; lia.
}
intro E. symmetry in E. assert (G := Spec0 E).
replace (to_Z digits) with 63%Z in G by trivial.
lia.
Qed.