From Coq Require Import ZArith Lia.
From Vyper Require Import Config L10.UInt256 L10.AST.

Local Open Scope Z_scope.


(** Unchecked addition modulo [2^256]. *)
Definition uint256_add {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z_of_uint256 a + Z_of_uint256 b).

(** Checked [a + b] close to how it's compiled: [assert a + b >= a; a + b]. *)
Definition uint256_checked_add {C: VyperConfig} (a: uint256) (b: uint256)
: option uint256
:= let result := uint256_add a b in
   if Z_of_uint256 result >=? Z_of_uint256 a
     then Some result
     else None.

Lemma uint256_checked_add_ok {C: VyperConfig} (a b: uint256):
  uint256_checked_add a b = interpret_binop Add a b.
Proof.
cbn. unfold uint256_checked_add. unfold uint256_add.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
unfold maybe_uint256_of_Z.
rewrite uint256_ok.
assert (NN: 0 <= x + y) by lia.
assert (D := Z.lt_ge_cases (x + y) (2 ^ 256)).
case D; clear D; intro D.
{ (* no overflow *)
  rewrite (Z.mod_small (x + y) (2 ^ 256) (conj NN D)).
  assert (G: x <= x + y) by lia.
  rewrite<- Z.geb_le in G. rewrite G.
  now rewrite Z.eqb_refl.
}
(* overflow *)
assert (M: (x + y) mod 2 ^ 256 = x + y - 2 ^ 256).
{
  replace ((x + y) mod 2 ^ 256) with ((x + y + - 2 ^ 256) mod 2 ^ 256).
  { apply Z.mod_small. lia. }
  rewrite Z.add_mod by discriminate.
  replace (- 2 ^ 256 mod 2 ^ 256) with 0 by trivial.
  rewrite Z.add_0_r.
  apply Z.mod_mod.
  discriminate.
}
assert (F: (x + y) mod 2 ^ 256 >=? x = false).
{ rewrite Z.geb_leb. rewrite Z.leb_gt. lia. }
rewrite F.
assert (F': (x + y) mod 2 ^ 256 =? x + y = false).
{ rewrite Z.eqb_neq. lia. }
now rewrite F'.
Qed.


(** Unchecked subtraction modulo [2^256]. *)
Definition uint256_sub {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z_of_uint256 a - Z_of_uint256 b).

(** Checked [a - b] close to how it's compiled: [assert a >= b; a - b]. *)
Definition uint256_checked_sub {C: VyperConfig} (a b: uint256)
: option uint256
:= if Z_of_uint256 a >=? Z_of_uint256 b
     then Some (uint256_sub a b)
     else None.

Lemma uint256_checked_sub_ok {C: VyperConfig} (a b: uint256):
  uint256_checked_sub a b = interpret_binop Sub a b.
Proof.
cbn. unfold uint256_checked_sub. unfold uint256_sub.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
unfold maybe_uint256_of_Z.
rewrite uint256_ok.
rewrite Z.geb_leb.
assert (D := Z.lt_ge_cases x y).
case D; clear D; intro D.
{ (* overflow *)
  assert (F: (x - y) mod 2 ^ 256 =? x - y = false).
  {
    rewrite Z.eqb_neq. intro H.
    apply Z.mod_small_iff in H. 2:discriminate.
    lia.
  }
  rewrite F.
  apply Z.leb_gt in D. now rewrite D.
}
(* no overflow *)
assert (T: (x - y) mod 2 ^ 256 =? x - y = true).
{ rewrite Z.eqb_eq. apply Z.mod_small. lia. }
rewrite T.
apply Z.leb_le in D. now rewrite D.
Qed.


(** Unchecked multiplication modulo [2^256]. *)
Definition uint256_mul {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z_of_uint256 a * Z_of_uint256 b).

(** Unchecked division modulo [2^256]. *)
Definition uint256_div {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z_of_uint256 a / Z_of_uint256 b).

(** As in EVM, [x / 0 = 0]. *)
Lemma uint256_div_0_r {C: VyperConfig} (a: uint256):
  uint256_div a zero256 = zero256.
Proof.
unfold uint256_div. unfold zero256.
rewrite uint256_ok.
now rewrite Zdiv_0_r.
Qed.

(** Checked [a * b] close to how it's compiled:
     [if a == 0
        then 0
        else assert a * b / a = b;
             a * b]. *)
Definition uint256_checked_mul {C: VyperConfig} (a b: uint256)
: option uint256
:= if Z_of_uint256 a =? 0
     then Some zero256
     else let result := uint256_mul a b in
          if Z_of_uint256 (uint256_div result a) =? Z_of_uint256 b
            then Some result
            else None.

Lemma Z_div_le_l (a b: Z) (A: 0 <= a) (B: 0 <= b):
  a / b <= a.
Proof.
apply Z.lt_eq_cases in B.
case B; clear B; intro B.
{
  replace a with (a / 1) at 2 by apply Z.div_1_r.
  apply Z.div_le_compat_l; lia.
}
subst b. rewrite Zdiv_0_r. exact A.
Qed.

Lemma uint256_checked_mul_ok {C: VyperConfig} (a: uint256) (b: uint256):
  uint256_checked_mul a b = interpret_binop Mul a b.
Proof.
cbn. unfold uint256_checked_mul. unfold uint256_mul.
unfold uint256_div.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
unfold maybe_uint256_of_Z.
repeat rewrite uint256_ok.
assert (D := Z.lt_ge_cases (x * y) (2 ^ 256)).
case D; clear D; intro D.
{ (* no overflow *)
  replace ((x * y) mod 2 ^ 256) with (x * y).
  2:{ symmetry. apply Z.mod_small. lia. }
  remember (x =? 0) as x_zero. symmetry in Heqx_zero. destruct x_zero.
  {
    apply Z.eqb_eq in Heqx_zero. repeat rewrite Heqx_zero.
    now repeat rewrite Z.mul_0_r.
  }
  rewrite Z.eqb_neq in Heqx_zero.
  replace (x * y / x) with y.
  2:{ rewrite Z.mul_comm. now rewrite (Z.div_mul y x Heqx_zero). }
  replace (y mod 2 ^ 256) with y by now rewrite (Z.mod_small _ _ B).
  now repeat rewrite Z.eqb_refl.
}
(* overflow *)
remember (x =? 0) as x_zero. symmetry in Heqx_zero. destruct x_zero.
{
  apply Z.eqb_eq in Heqx_zero. rewrite Heqx_zero in D.
  rewrite Z.mul_0_l in D. contradiction.
}
rewrite Z.eqb_neq in Heqx_zero.
(* We're going to get rid of the last mod here:
    ((x * y) mod 2 ^ 256 / x) mod 2 ^ 256
*)
assert (U: (x * y) mod 2 ^ 256 / x < 2 ^ 256).
{
  apply (Z.le_lt_trans _ ((x * y) mod 2 ^ 256)).
  {
    apply Z_div_le_l. 2:tauto.
    apply Z.mod_bound_pos; lia.
  }
  apply Z.mod_bound_pos; lia.
}
assert (L: 0 <= (x * y) mod 2 ^ 256 / x).
{
  apply Z.div_pos. 2:lia.
  apply Z.mod_bound_pos; lia.
}
replace (((x * y) mod 2 ^ 256 / x) mod 2 ^ 256)
  with ((x * y) mod 2 ^ 256 / x).
2:{ symmetry. apply Z.mod_small. tauto. }

(* This is the main point of the proof. *)
assert (NE: (x * y) mod 2 ^ 256 / x <> y).
{
  intro H.
  assert (M: (x * y) mod 2 ^ 256 <= x * y - 2 ^ 256).
  {
    replace ((x * y) mod 2 ^ 256) with ((x * y + - 2 ^ 256) mod 2 ^ 256).
    2:{
      rewrite Z.add_mod by discriminate.
      replace (- 2 ^ 256 mod 2 ^ 256) with 0 by trivial.
      rewrite Z.add_0_r.
      apply Z.mod_mod.
      discriminate.
    }
    apply Z.mod_le.
    lia.
    easy.
  }
  assert (Y: (x * y) mod 2 ^ 256 < x * y - x) by lia.
  replace (x * y - x) with (x * (y - 1)) in Y by lia.
  enough (Q: (x * y) mod 2 ^ 256 / x <= x * (y - 1) / x).
  {
    replace (x * (y - 1) / x) with (y - 1) in Q. { lia. }
    rewrite Z.mul_comm.
    symmetry. apply Z.div_mul. assumption.
  }
  apply Z.div_le_mono; lia.
}
apply Z.eqb_neq in NE. rewrite NE.
enough (R: (x * y) mod 2 ^ 256 =? x * y = false) by now rewrite R.
apply Z.eqb_neq.
rewrite Z.mod_small_iff.
lia. discriminate.
Qed.

(** Checked [a / b] close to how it's compiled: [assert b; a / b] *)
Definition uint256_checked_div {C: VyperConfig} (a b: uint256)
: option uint256
:= if Z_of_uint256 b =? 0
     then None
     else Some (uint256_div a b).

(* This is almost trivial but there's an extra range check in the interpreter. *)
Lemma uint256_checked_div_ok {C: VyperConfig} (a: uint256) (b: uint256):
  uint256_checked_div a b = interpret_binop Quot a b.
Proof.
cbn. unfold uint256_checked_div. unfold uint256_div.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
remember (y =? 0) as y_zero. symmetry in Heqy_zero. destruct y_zero.
{ trivial. }
rewrite Z.eqb_neq in Heqy_zero.
unfold maybe_uint256_of_Z.
repeat rewrite uint256_ok.
enough (Q: (x / y) mod 2 ^ 256 =? x / y = true)
  by now rewrite Q.
rewrite Z.eqb_eq. apply Z.mod_small.
split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; lia.
Qed.


(** Unchecked mod. *)
Definition uint256_mod {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z_of_uint256 a mod Z_of_uint256 b).

(** As in EVM, [x % 0 = 0]. *)
Lemma uint256_mod_0_r {C: VyperConfig} (a: uint256):
  uint256_mod a zero256 = zero256.
Proof.
unfold uint256_mod. unfold zero256. rewrite uint256_ok. cbn.
now rewrite Zmod_0_r.
Qed.

(** Checked [a % b] close to how it's compiled: [assert b; a % b] *)
Definition uint256_checked_mod {C: VyperConfig} (a b: uint256)
: option uint256
:= if Z_of_uint256 b =? 0
     then None
     else Some (uint256_mod a b).

(* This is almost trivial but there's an extra range check in the interpreter. *)
Lemma uint256_checked_mod_ok {C: VyperConfig} (a: uint256) (b: uint256):
  uint256_checked_mod a b = interpret_binop Mod a b.
Proof.
cbn. unfold uint256_checked_mod. unfold uint256_mod.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
remember (y =? 0) as y_zero. symmetry in Heqy_zero. destruct y_zero.
{ trivial. }
rewrite Z.eqb_neq in Heqy_zero.
unfold maybe_uint256_of_Z.
repeat rewrite uint256_ok.
replace ((x mod y) mod 2 ^ 256) with (x mod y). { now rewrite Z.eqb_refl. }
symmetry. apply Z.mod_small.
enough (0 <= x mod y < y) by lia.
apply Z.mod_pos_bound. lia.
Qed.

(* assert a <= (~1 >> b); a << b *)