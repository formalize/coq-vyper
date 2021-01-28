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


(** Unchecked left shift modulo [2^256]. *)
Definition uint256_shl {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z.shiftl (Z_of_uint256 a) (Z_of_uint256 b)).

(** Unchecked right shift modulo [2^256]. *)
Definition uint256_shr {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z.shiftr (Z_of_uint256 a) (Z_of_uint256 b)).


(** Checked [a << b] close to how it's compiled:
     [assert (a << b) >> b = a;
      a << b]. *)
Definition uint256_checked_shl {C: VyperConfig} (a b: uint256)
: option uint256
:= let result := uint256_shl a b in
   if Z_of_uint256 (uint256_shr result b) =? Z_of_uint256 a
      then Some result
      else None.

Lemma Z_ones_nonneg (n: Z):
  0 <= n -> 0 <= Z.ones n.
Proof.
intro L.
rewrite Z.ones_equiv.
rewrite<- Z.le_succ_le_pred.
rewrite Z.le_succ_l.
now apply Z.pow_pos_nonneg.
Qed.


(* TODO: move *)
Lemma Z_shiftr_ones (a b: Z)
                    (La: 0 <= a)
                    (Lb: 0 <= b):
  Z.shiftr (Z.ones a) b = Z.ones (Z.max 0 (a - b)).
Proof.
apply Z.bits_inj. intro k.
assert (Lk := Z.neg_nonneg_cases k).
case Lk; clear Lk; intro Lk. { now repeat rewrite Z.testbit_neg_r. }
rewrite Z.shiftr_spec by exact Lk.
repeat rewrite Z.testbit_ones_nonneg by lia.
assert (D := Z.lt_ge_cases a b).
case D; clear D; intro D.
{ (* a < b *)
  assert (L: a <= k + b) by lia.
  apply Z.ltb_ge in L. rewrite L.
  replace (Z.max 0 (a - b)) with 0 by lia.
  apply Z.ltb_ge in Lk.
  exact (eq_sym Lk).
}
(* a >= b *)
replace (Z.max 0 (a - b)) with (a - b) by lia.
remember (k + b <? a) as q. symmetry. symmetry in Heqq. destruct q.
{ rewrite Z.ltb_lt in Heqq. rewrite Z.ltb_lt. lia. }
rewrite Z.ltb_ge in Heqq. rewrite Z.ltb_ge. lia.
Qed.


Lemma uint256_checked_shl_ok {C: VyperConfig} (a: uint256) (b: uint256):
  uint256_checked_shl a b = interpret_binop ShiftLeft a b.
Proof.
cbn. unfold uint256_checked_shl. unfold uint256_shl. unfold uint256_shr.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
assert (L: 0 <= Z.shiftl x y) by now apply Z.shiftl_nonneg.
unfold maybe_uint256_of_Z.
repeat rewrite uint256_ok.
assert (D := Z.lt_ge_cases (Z.shiftl x y) (2 ^ 256)).
case D; clear D; intro D.
{ (* no overflow *)
  replace ((Z.shiftl x y) mod 2 ^ 256) with (Z.shiftl x y).
  2:{ symmetry. apply Z.mod_small. tauto. }
  rewrite Z.shiftr_shiftl_l by tauto.
  rewrite Z.sub_diag.
  rewrite Z.shiftl_0_r.
  rewrite Z.eqb_refl.
  now rewrite (proj2 (Z.eqb_eq _ _) (Z.mod_small _ _ A)).
}
(* overflow *)
enough (NE: Z.shiftr (Z.shiftl x y mod 2 ^ 256) y mod 2 ^ 256 <> x).
{
  apply Z.eqb_neq in NE. rewrite NE.
  enough (M: Z.shiftl x y mod 2 ^ 256 <> Z.shiftl x y).
  { apply Z.eqb_neq in M. now rewrite M. }
  intro M. apply Z.mod_small_iff in M; lia.
}
intro E.
repeat rewrite<- Z.land_ones in E by easy.
rewrite Z.shiftr_land in E.
rewrite Z.shiftr_shiftl_l in E by tauto.
rewrite Z.sub_diag in E.
rewrite Z.shiftl_0_r in E.
rewrite<- Z.land_assoc in E.
replace (Z.land (Z.shiftr (Z.ones 256) y) (Z.ones 256)) with (Z.shiftr (Z.ones 256) y) in E.
2:{
  symmetry. apply Z.land_ones_low. {apply Z.shiftr_nonneg. now apply Z_ones_nonneg. }
  rewrite Z.log2_shiftr by easy.
  replace (Z.log2 (Z.ones 256)) with 255 by trivial.
  apply Z.max_lub_lt. { easy. }
  lia.
}
rewrite Z_shiftr_ones in E by easy.
assert (Y := Z.lt_ge_cases 256 y).
case Y; clear Y; intro Y.
{ (* big y *)
  replace (Z.max 0 (256 - y)) with 0 in E by lia. cbn in E.
  rewrite Z.land_0_r in E. rewrite<- E in *.
  now rewrite Z.shiftl_0_l in D.
}
(* small y *)
replace (Z.max 0 (256 - y)) with (256 - y) in E by lia.
rewrite Z.land_ones in E.
apply Z.mod_small_iff in E.
2:{ apply Z.pow_nonzero. { discriminate. } lia. }
2:lia.
case E; clear E; intro E.
{
  rewrite Z.shiftl_mul_pow2 in D by tauto.
  replace 256 with ((256 - y) + y) in D by lia.
  rewrite Z.pow_add_r in D by lia.
  apply Z.nlt_ge in D. apply D.
  apply Z.mul_lt_mono_pos_r. { now apply Z.pow_pos_nonneg. }
  tauto.
}
assert (X: x = 0) by lia.
rewrite X in *.
now rewrite Z.shiftl_0_l in D.
Qed.


(** There is an extra range check in [interpret_binop ShiftRight] but it will never be triggered. *)
Lemma uint256_shr_ok {C: VyperConfig} (a: uint256) (b: uint256):
  Some (uint256_shr a b) = interpret_binop ShiftRight a b.
Proof.
cbn. unfold uint256_shr. unfold maybe_uint256_of_Z.
rewrite uint256_ok.
assert (A := uint256_range a).
assert (B := uint256_range b).
remember (Z_of_uint256 a) as x.
remember (Z_of_uint256 b) as y.
replace (Z.shiftr x y mod 2 ^ 256 =? Z.shiftr x y) with true. { trivial. }
symmetry. rewrite Z.eqb_eq.
apply Z.mod_small.
rewrite Z.shiftr_div_pow2 by tauto.
split.
{
  apply Z.div_pos. { tauto. }
  now apply Z.pow_pos_nonneg.
}
apply (Z.le_lt_trans _ x _). 2:tauto.
apply Z_div_le_l. { tauto. }
now apply Z.pow_nonneg.
Qed.


(** Checked [-a] close to how it's compiled: [assert a == 0; 0] *)
Definition uint256_checked_neg {C: VyperConfig} (a: uint256)
: option uint256
:= if Z_of_uint256 a =? 0
     then Some zero256
     else None.

Lemma uint256_checked_neg_ok {C: VyperConfig} (a: uint256):
  uint256_checked_neg a = interpret_unop Neg a.
Proof.
cbn. unfold uint256_checked_neg.
assert (A := uint256_range a).
remember (Z_of_uint256 a) as x.
unfold maybe_uint256_of_Z.
rewrite uint256_ok.
remember (x =? 0) as x_zero. symmetry in Heqx_zero. destruct x_zero.
{ rewrite Z.eqb_eq in Heqx_zero. now rewrite Heqx_zero. }
rewrite Z.eqb_neq in Heqx_zero.
replace (- x mod 2 ^ 256 =? - x) with false. { trivial. }
symmetry. rewrite Z.eqb_neq.
intro H. apply Z.mod_small_iff in H; lia.
Qed.


(**********************************************************************
 Binary search
 **********************************************************************)



(* This function descends slightly slower than a normal non-Coq implementation would,
   meaning if we have 5 items to check, normally they would be split 2/3,
   but we have to do 3/3 to make the recursion happy.
 *)
Fixpoint binary_search_rec (p: Z -> bool)
                           (low: Z)
                           (n: positive)
{struct n}
: Z
:= match n with
   | xH =>
      let mid := low + 1 in
      if p mid
        then low
        else mid
   | xO half | xI half =>
      let mid := low + Z.pos half + 1 in
      if p mid
        then binary_search_rec p low half
        else binary_search_rec p mid half
   end.

Lemma binary_search_rec_lower (p: Z -> bool)
                              (low: Z)
                              (n: positive):
  low <= binary_search_rec p low n.
Proof.
revert low. induction n; intro; cbn;
  destruct p; try apply IHn;
  try refine (Z.le_trans _ _ _ _ (IHn _)); lia.
Qed.

Lemma binary_search_rec_ok (p: Z -> bool)
                           (low: Z)
                           (n: positive)
                           (Mono: forall x y, x < y -> p x = true -> p y = true)
                           (LowOk: p low = false)
                           (HighOk: p (low + Z.pos n + 1) = true):
  let m := binary_search_rec p low n in
  p m = false /\ p (Z.succ m) = true.
Proof.
revert low LowOk HighOk. induction n; intros.
{ (* 2n + 1 *)
  cbn.
  remember (p (low + Z.pos n + 1)) as p_mid; symmetry in Heqp_mid; destruct p_mid.
  { (* lower half *) now apply IHn. }
  (* upper half *)
  apply IHn. { assumption. }
  replace (low + Z.pos n + 1 + Z.pos n + 1) with (low + Z.pos n~1 + 1) by lia.
  assumption.
}
{ (* 2n *)
  cbn.
  remember (p (low + Z.pos n + 1)) as p_mid; symmetry in Heqp_mid; destruct p_mid.
  { (* lower half *) now apply IHn. }
  (* upper half *)
  apply IHn. { assumption. }
  refine (Mono _ _ _ HighOk).
  lia.
}
(* 1 *)
unfold m. cbn.
remember (p (low + 1)) as p_mid; symmetry in Heqp_mid; now destruct p_mid.
Qed.

Lemma binary_search_rec_change (p q: Z -> bool)
                               (low: Z)
                               (n: positive)
                               (ok: forall x, low < x -> p x = q x):
  binary_search_rec p low n = binary_search_rec q low n.
Proof.
revert low ok. induction n; intros; cbn;
  rewrite ok by lia; repeat rewrite IHn; trivial; intros; apply ok; lia.
Qed.

(** Perform binary search on a monotone boolean function [p]
    which is false on [low] but true on [high].
    Finds a number on which [p] is false but on the next one it's true.
 *)
Definition binary_search (p: Z -> bool)
                         (low high: Z)
: Z
:= match high - low - 1 with
   | Z0 => low
   | Zpos n => binary_search_rec p low n
   | Zneg _ => low (* bad arguments *)
   end.

Lemma binary_search_lower (p: Z -> bool)
                          (low high: Z):
  low <= binary_search p low high.
Proof.
unfold binary_search.
destruct (high - low - 1); try apply Z.le_refl.
apply binary_search_rec_lower.
Qed.

Lemma binary_search_ok (p: Z -> bool)
                       (low high: Z)
                       (Mono: forall x y, x < y -> p x = true -> p y = true)
                       (LowOk: p low = false)
                       (HighOk: p high = true):
  let m := binary_search p low high in
  p m = false /\ p (Z.succ m) = true.
Proof.
unfold binary_search.
remember (high - low - 1) as d. symmetry in Heqd. destruct d as [|n|n].
{ (* 0 *) assert (high = Z.succ low) by lia; now subst high. }
{ (* pos *)
  apply binary_search_rec_ok; try assumption.
  assert (high = low + Z.pos n + 1) by lia.
  now subst high.
}
(* neg *)
(* this case contradicts [Mono] *)
assert (LE: high <= low) by lia.
apply Zle_lt_or_eq in LE.
case LE; clear LE; intro LE.
{ now rewrite (Mono _ _ LE HighOk) in LowOk. }
subst. now rewrite LowOk in HighOk.
Qed.

Lemma binary_search_change (p q: Z -> bool)
                           (low high: Z)
                           (ok: forall x, low < x -> p x = q x):
  binary_search p low high = binary_search q low high.
Proof.
unfold binary_search. destruct (high - low - 1); try easy.
now rewrite (binary_search_rec_change p q) by apply ok.
Qed.

(******************************************************************************
 * Powers and exponents
 ******************************************************************************)

(** Assuming [base > 2], compute the maximum allowed power before an overflow *)
Definition uint256_max_power {C: VyperConfig} (base: Z)
:= binary_search (fun x => 2 ^ 256 <=? Z.pow base x) 0 162.

Lemma uint256_max_power_ok {C: VyperConfig} (base: Z) (BaseOk: 2 < base):
  let p := uint256_max_power base in
  Z.pow base p < 2 ^ 256 /\ 2 ^ 256 <= Z.pow base (Z.succ p).
Proof.
unfold uint256_max_power.
remember (fun x : Z => 2 ^ 256 <=? base ^ x) as f.
assert (F0: f 0 = false) by now subst f.
assert (F162: f 162 = true).
{
  subst f.
  apply Z.leb_le.
  assert (T: 2 ^ 256 <= 3 ^ 162) by now apply Z.leb_le.
  apply (Z.le_trans _ _ _ T).
  apply Z.pow_le_mono_l.
  lia.
}
assert (Mono: forall x y, x < y -> f x = true -> f y = true).
{
  intros. subst f.
  rewrite Z.leb_le in *.
  apply (Z.le_trans (2 ^ 256) (base ^ x) (base ^ y)). { assumption. }
  apply Z.pow_le_mono_r; lia.
}
assert (B := binary_search_ok f 0 162 Mono F0 F162).
subst f. cbn zeta in B.
rewrite Z.leb_gt in B. rewrite Z.leb_le in B.
apply B.
Qed.


(** Unchecked power modulo [2^256]. *)
Definition uint256_pow {C: VyperConfig} (a b: uint256)
: uint256
:= uint256_of_Z (Z_of_uint256 a ^ Z_of_uint256 b).

(** This is checked power with a constant base close to how it's compiled:
    for [base == 0]: [pow == 0]
    for [base == 1]: [pow; 1]
    for [base == 2]: [assert pow < 256; 1 << pow]
    for [base >= 3]: [assert pow <= uint256_max_power base; base ** pow]
 *)
Definition uint256_checked_pow_const_base {C: VyperConfig} (base pow: uint256)
: option uint256
:= let base_Z := Z_of_uint256 base in
   let pow_Z := Z_of_uint256 pow in
   if base_Z =? 0 then Some (if pow_Z =? 0 then one256 else zero256) else
   if base_Z =? 1 then Some one256 else
   if base_Z =? 2
     then if pow_Z <? 256
            then Some (uint256_shl one256 pow)
            else None
     else if pow_Z <=? uint256_max_power base_Z
            then Some (uint256_pow base pow)
            else None.

Lemma uint256_checked_pow_const_base_ok {C: VyperConfig} (base pow: uint256):
  uint256_checked_pow_const_base base pow = interpret_binop Pow base pow.
Proof.
cbn. unfold uint256_checked_pow_const_base. unfold maybe_uint256_of_Z.
rewrite uint256_ok.
remember (Z_of_uint256 base =? 0) as base_0. symmetry in Heqbase_0. destruct base_0.
{ (* 0 ^ pow *)
  rewrite Z.eqb_eq in Heqbase_0.
  rewrite Heqbase_0.
  remember (Z_of_uint256 pow =? 0) as pow_0. symmetry in Heqpow_0. destruct pow_0.
  { (* 0 ^ 0 == 1 *)
    rewrite Z.eqb_eq in Heqpow_0.
    now rewrite Heqpow_0.
  }
  rewrite Z.eqb_neq in Heqpow_0.
  apply Z.pow_0_l' in Heqpow_0. 
  now rewrite Heqpow_0.
}
rewrite Z.eqb_neq in Heqbase_0.
remember (Z_of_uint256 base =? 1) as base_1. symmetry in Heqbase_1. destruct base_1.
{ (* 1 ^ pow *)
  rewrite Z.eqb_eq in Heqbase_1.
  rewrite Heqbase_1.
  rewrite Z.pow_1_l. { easy. }
  apply uint256_range.
}
rewrite Z.eqb_neq in Heqbase_1.
remember (Z_of_uint256 base =? 2) as base_2. symmetry in Heqbase_2. destruct base_2.
{ (* 2 ^ pow *)
  rewrite Z.eqb_eq in Heqbase_2.
  rewrite Heqbase_2.
  unfold uint256_shl.
  replace (Z_of_uint256 one256) with 1 by (unfold one256; now rewrite uint256_ok).
  rewrite Z.shiftl_1_l.
  remember (2 ^ Z_of_uint256 pow mod 2 ^ 256 =? 2 ^ Z_of_uint256 pow) as m. symmetry in Heqm.
  assert (T: 2 ^ 256 <> 0) by discriminate.
  assert (M := Z.mod_small_iff (2 ^ Z_of_uint256 pow) (2 ^ 256) T). clear T.
  assert (R := uint256_range pow).
  assert (NN: ~(2 ^ 256 < 2 ^ Z_of_uint256 pow <= 0)) by lia.
  assert (L: 0 <= 2 ^ Z_of_uint256 pow) by now apply Z.pow_nonneg.
  assert (MM: 2 ^ Z_of_uint256 pow mod 2 ^ 256 = 2 ^ Z_of_uint256 pow 
               <->
              2 ^ Z_of_uint256 pow < 2 ^ 256) by tauto.
  clear M NN.
  assert (Q: 2 ^ Z_of_uint256 pow < 2 ^ 256 <-> Z_of_uint256 pow < 256).
  { symmetry. now apply Z.pow_lt_mono_r_iff. }
  assert (P: 2 ^ Z_of_uint256 pow mod 2 ^ 256 = 2 ^ Z_of_uint256 pow 
              <->
             Z_of_uint256 pow < 256) by tauto.
  clear MM Q.
  remember (Z_of_uint256 pow <? 256) as l. symmetry in Heql.
  destruct l, m; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
                 try rewrite Z.eqb_eq in *; try rewrite Z.eqb_neq in *; trivial.
  { tauto. }
  apply P in Heqm. lia.
}
rewrite Z.eqb_neq in Heqbase_2.
(* base ^ pow, base >= 3 *)
assert (L: 2 < Z_of_uint256 base). { assert (R := uint256_range base). lia. }
assert (M := uint256_max_power_ok _ L).
unfold uint256_pow.
remember (Z_of_uint256 base ^ Z_of_uint256 pow mod 2 ^ 256 
           =?
          Z_of_uint256 base ^ Z_of_uint256 pow) as m.
symmetry in Heqm.
remember (Z_of_uint256 pow <=? uint256_max_power (Z_of_uint256 base)) as l. symmetry in Heql.
enough (H: m = l) by now rewrite H.
destruct l.
{
  rewrite Z.leb_le in Heql.
  subst m.
  rewrite Z.eqb_eq.
  apply Z.mod_small.
  split. { apply Z.pow_nonneg. lia. }
  refine (Z.le_lt_trans _ _ _ _ (proj1 M)).
  apply Z.pow_le_mono_r. { lia. } exact Heql.
}
rewrite Z.leb_gt in Heql.
subst m. rewrite Z.eqb_neq. intro H.
apply Z.mod_small_iff in H. 2:discriminate.
enough (2 ^ 256 <= Z_of_uint256 base ^ Z_of_uint256 pow) by lia.
clear H.
apply (Z.le_trans _ _ _ (proj2 M)).
apply Z.pow_le_mono_r; lia.
Qed.


(** Assuming [pow >= 2], compute the maximum allowed base before an overflow *)
Definition uint256_max_base {C: VyperConfig} (pow: Z)
:= binary_search (fun x => 2 ^ 256 <=? Z.pow x pow) 0 (2 ^ 128).

Lemma uint256_max_base_ok {C: VyperConfig} (pow: Z) (PowOk: 2 <= pow):
  let b := uint256_max_base pow in
  Z.pow b pow < 2 ^ 256 /\ 2 ^ 256 <= Z.pow (Z.succ b) pow.
Proof.
unfold uint256_max_base.
remember (fun x : Z => 2 ^ 256 <=? x ^ pow) as f.
pose (g := fun x => ((0 <=? x) && f x)%bool).
assert (E: binary_search f 0 (2 ^ 128) = binary_search g 0 (2 ^ 128)).
{
  apply binary_search_change.
  intros x L.
  subst f g.
  cbn beta.
  apply Z.lt_le_incl in L.
  apply Z.leb_le in L.
  rewrite L.
  apply Bool.andb_true_l.
}
rewrite E.
assert (Low: g 0 = false).
{
  subst g. subst f.
  replace (0 ^ pow) with 0. 2:{ symmetry. apply Z.pow_0_l. lia. }
  easy.
}
assert (High: g (2 ^ 128) = true).
{
  subst g. subst f.
  apply Z.leb_le.
  replace (2 ^ 256) with ((2 ^ 128) ^ 2) by trivial.
  now apply Z.pow_le_mono_r.
}
assert (Mono: forall x y, x < y -> g x = true -> g y = true).
{
  intros x y XY H. subst g. subst f.
  rewrite Bool.andb_true_iff in *.
  destruct H as (PosX, H).
  split; rewrite Z.leb_le in *; try lia.
  apply (Z.le_trans (2 ^ 256) (x ^ pow) (y ^ pow)). { assumption. }
  apply Z.pow_le_mono_l; lia.
}
assert (B := binary_search_ok g _ _ Mono Low High).
cbn zeta in B. destruct B as (U, V).
rewrite<- E in *.
assert (L := binary_search_lower f 0 (2 ^ 128)).
remember (binary_search f 0 (2 ^ 128)) as x.
subst g. cbn in U. cbn in V.
assert (L': 0 <= Z.succ x) by lia.
rewrite<- Z.leb_le in L.
rewrite<- Z.leb_le in L'.
rewrite L in U. rewrite L' in V.
cbn in U. cbn in V.
subst f.
apply Z.leb_gt in U. apply Z.leb_le in V.
tauto.
Qed.

(** This is checked power with a constant exponent close to how it's compiled:
    for [pow == 0]: [base; 1]
    for [pow == 1]: [base ** 1]
    for [pow >= 2]: [assert base <= uint256_max_base pow; base ** pow

    Note that [base ** 1] cannot be replaced by base because it makes the value canonical.
 *)
Definition uint256_checked_pow_const_exponent {C: VyperConfig} (base pow: uint256)
: option uint256
:= let base_Z := Z_of_uint256 base in
   let pow_Z := Z_of_uint256 pow in
   if pow_Z =? 0 then Some one256 else
   if pow_Z =? 1 then Some (uint256_pow base pow) else
   if base_Z <=? uint256_max_base pow_Z
     then Some (uint256_pow base pow)
     else None.

Lemma uint256_checked_pow_const_exponent_ok {C: VyperConfig} (base pow: uint256):
  uint256_checked_pow_const_exponent base pow = interpret_binop Pow base pow.
Proof.
cbn. unfold uint256_checked_pow_const_exponent. unfold maybe_uint256_of_Z.
rewrite uint256_ok.
remember (Z_of_uint256 pow =? 0) as pow_0. symmetry in Heqpow_0. destruct pow_0.
{ (* base ^ 0 *)
  rewrite Z.eqb_eq in Heqpow_0. rewrite Heqpow_0.
  now rewrite Z.pow_0_r.
}
rewrite Z.eqb_neq in Heqpow_0.
remember (Z_of_uint256 pow =? 1) as pow_1. symmetry in Heqpow_1. destruct pow_1.
{ (* base ^ 1 *)
  unfold uint256_pow.
  rewrite Z.eqb_eq in Heqpow_1. rewrite Heqpow_1.
  rewrite Z.pow_1_r.
  assert (R := Z.mod_small _ _ (uint256_range base)).
  rewrite<- Z.eqb_eq in R.
  now rewrite R.
}
rewrite Z.eqb_neq in Heqpow_1.
assert (L: 2 <= Z_of_uint256 pow) by (assert (R := uint256_range pow); lia).
assert (B := uint256_max_base_ok _ L).
remember (Z_of_uint256 base ^ Z_of_uint256 pow mod 2 ^ 256 
           =?
          Z_of_uint256 base ^ Z_of_uint256 pow) as m.
symmetry in Heqm.
remember (Z_of_uint256 base <=? uint256_max_base (Z_of_uint256 pow)) as l. symmetry in Heql.
enough (H: m = l) by now rewrite H.
assert (R := uint256_range base).
destruct l.
{
  rewrite Z.leb_le in Heql.
  subst m.
  rewrite Z.eqb_eq.
  apply Z.mod_small.
  split. { apply Z.pow_nonneg. tauto. }
  refine (Z.le_lt_trans _ _ _ _ (proj1 B)).
  apply Z.pow_le_mono_l. lia.
}
rewrite Z.leb_gt in Heql.
subst m. rewrite Z.eqb_neq. intro H.
apply Z.mod_small_iff in H. 2:discriminate.
enough (2 ^ 256 <= Z_of_uint256 base ^ Z_of_uint256 pow) by lia.
clear H.
apply (Z.le_trans _ _ _ (proj2 B)).
apply Z.pow_le_mono_l.
split. 2:lia.
enough (0 <= uint256_max_base (Z_of_uint256 pow)) by lia.
unfold uint256_max_base.
apply binary_search_lower.
Qed.

(********************************************************************************************)
(* Here are the rewrites of comparison ops into expressions with lt, eq and iszero: *)

(* There is in fact a GT instruction in the EVM. However we're not using it. *)
Lemma uint256_gt_ok {C: VyperConfig} (a b: uint256):
  uint256_gt a b = uint256_lt b a.
Proof.
unfold uint256_gt.
unfold uint256_lt.
now rewrite Z.gtb_ltb.
Qed.

Lemma uint256_le_ok {C: VyperConfig} (a b: uint256):
  uint256_le a b = uint256_iszero (uint256_lt b a).
Proof.
unfold uint256_le.
unfold uint256_lt.
unfold uint256_iszero.
rewrite Z.leb_antisym.
rewrite Bool.if_negb.
unfold one256. unfold zero256.
destruct (Z_of_uint256 b <? Z_of_uint256 a); now rewrite uint256_ok.
Qed.

Lemma uint256_ge_ok {C: VyperConfig} (a b: uint256):
  uint256_ge a b = uint256_iszero (uint256_lt a b).
Proof.
unfold uint256_ge.
unfold uint256_lt.
unfold uint256_iszero.
rewrite Z.geb_leb.
rewrite Z.leb_antisym.
rewrite Bool.if_negb.
unfold one256. unfold zero256.
destruct (Z_of_uint256 a <? Z_of_uint256 b); now rewrite uint256_ok.
Qed.

Lemma uint256_ne_ok {C: VyperConfig} (a b: uint256):
  uint256_ne a b = uint256_iszero (uint256_eq a b).
Proof.
unfold uint256_ne.
unfold uint256_eq.
unfold uint256_iszero.
unfold one256. unfold zero256.
destruct (Z_of_uint256 a =? Z_of_uint256 b); now rewrite uint256_ok.
Qed.
