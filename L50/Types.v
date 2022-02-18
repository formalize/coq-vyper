From Coq Require Import ZArith Ascii String Eqdep_dec.
From Vyper Require Import Config.

Inductive int_size
:= I8 | I32 | I64 | I128 | I256.

Definition int_size_in_bits (i: int_size): Z
:= match i with
   | I8 => 8
   | I32 => 32
   | I64 => 64
   | I128 => 128
   | I256 => 256
   end.

Definition int_size_in_bytes (i: int_size): Z
:= match i with
   | I8 => 1
   | I32 => 4
   | I64 => 8
   | I128 => 16
   | I256 => 32
   end.

Lemma int_size_ok (i: int_size):
  int_size_in_bits i = (8 * int_size_in_bytes i)%Z.
Proof.
  destruct i; trivial. 
Qed.

Definition string_of_int_size (i: int_size): string
:= match i with
   | I8 => "8"
   | I32 => "32"
   | I64 => "64"
   | I128 => "128"
   | I256 => "256"
   end.

Definition int_size_of_string (s: string): option int_size
:= match s with
   | "8"%string => Some I8
   | "32"%string => Some I32
   | "64"%string => Some I64
   | "128"%string => Some I128
   | "256"%string => Some I256
   | _ => None
   end.

Lemma int_size_of_string_of_int_size (i: int_size):
  int_size_of_string (string_of_int_size i) = Some i.
Proof.
now destruct i.
Qed.

Definition uint_max (i: int_size) := (2 ^ int_size_in_bits i - 1)%Z.
Definition sint_max (i: int_size) := (2 ^ (int_size_in_bits i - 1) - 1)%Z.
Definition sint_min (i: int_size) := (- 2 ^ (int_size_in_bits i - 1))%Z.

Example uint_max_byte: uint_max I8 = 255%Z.    Proof. trivial. Qed.
Example sint_min_byte: sint_min I8 = (-128)%Z. Proof. trivial. Qed.
Example sint_max_byte: sint_max I8 = 127%Z.    Proof. trivial. Qed.

Inductive yul_type
:= BoolType
 | IntType (size: int_size) (signed: bool).

Lemma yul_type_eq_dec (a b: yul_type)
: {a = b} + {a <> b}.
Proof.
repeat decide equality.
Defined.

Definition U8 := IntType I8 false.
Definition S8 := IntType I8 true.
Definition U32 := IntType I32 false.
Definition S32 := IntType I32 true.
Definition U64 := IntType I64 false.
Definition S64 := IntType I64 true.
Definition U128 := IntType I128 false.
Definition S128 := IntType I128 true.
Definition U256 := IntType I256 false.
Definition S256 := IntType I256 true.

Definition uint256_to_Z_as_signed {C: VyperConfig} (n: uint256)
: Z
:= let z := Z_of_uint256 n in
   if Z.testbit z 255%Z
     then z - 2 ^ 256
     else z.

Inductive yul_value {C: VyperConfig} (t: yul_type)
:= NumberValue (value: uint256)
               (ok: match t with
                    | BoolType => false
                    | IntType size true  => let x := uint256_to_Z_as_signed value in
                                            andb (sint_min size <=? x)%Z (x <=? sint_max size)%Z
                    | IntType size false => let x := Z_of_uint256 value in
                                            andb (0 <=? x)%Z (x <=? uint_max size)%Z
                    end = true)
 | BoolValue (b: bool)
             (ok:  match t with
                   | BoolType => true
                   | _ => false
                   end = true).

Definition yul_true  {C: VyperConfig} := BoolValue BoolType true eq_refl.
Definition yul_false {C: VyperConfig} := BoolValue BoolType false eq_refl.

Lemma yul_uint256_helper {C: VyperConfig} (value: uint256):
  ((0 <=? Z_of_uint256 value)%Z && (Z_of_uint256 value <=? uint_max I256)%Z)%bool = true.
Proof.
assert (R := uint256_range value).
apply andb_true_intro. split.
now rewrite Z.leb_le.
unfold uint_max. unfold int_size_in_bits.
rewrite Z.leb_le.
apply Zsucc_le_reg.
replace (Z.succ (2 ^ 256 - 1))%Z with (2 ^ 256)%Z by trivial.
now apply Zlt_le_succ.
Qed.

Definition yul_uint256 {C: VyperConfig} (value: uint256)
: yul_value U256
:= NumberValue U256 value (yul_uint256_helper value).

Definition dynamic_value {C: VyperConfig} := { t: yul_type & yul_value t }.

Definition dynamic_value_of_uint256 {C: VyperConfig} (value: uint256)
:= existT _ U256 (yul_uint256 value).

Definition uint256_of_yul_value {C: VyperConfig} {t: yul_type} (y: yul_value t)
: uint256
:= match y with
   | NumberValue _ value _ => value
   | BoolValue _ true  _ => one256
   | BoolValue _ false _ => zero256
   end.

Local Lemma uint256_to_yul_value_helper_bool {C: VyperConfig} {t: yul_type} (T: t = BoolType):
   match t with
   | BoolType => true
   | IntType _ _ => false
   end = true.
Proof.
now subst.
Qed.

Local Lemma uint256_to_yul_value_helper_sint {C: VyperConfig} {t: yul_type} {u : uint256}
                                             {size: int_size} (T: t = IntType size true)
                                             (E: let x := uint256_to_Z_as_signed u in
                                                  ((sint_min size <=? x)%Z &&
                                                    (x <=? sint_max size)%Z)%bool = true):
   match t with
   | BoolType => false
   | IntType size true =>
       let x := uint256_to_Z_as_signed u in ((sint_min size <=? x)%Z && (x <=? sint_max size)%Z)%bool
   | IntType size false => let x := Z_of_uint256 u in ((0 <=? x)%Z && (x <=? uint_max size)%Z)%bool
   end = true.
Proof.
now subst.
Qed.

Local Lemma uint256_to_yul_value_helper_uint {C: VyperConfig} {t: yul_type} {u : uint256}
                                             {size: int_size} (T: t = IntType size false)
                                             (E: let x := Z_of_uint256 u in
                                                  ((0 <=? x)%Z && (x <=? uint_max size)%Z)%bool = true):
   match t with
   | BoolType => false
   | IntType size true =>
       let x := uint256_to_Z_as_signed u in ((sint_min size <=? x)%Z && (x <=? sint_max size)%Z)%bool
   | IntType size false => let x := Z_of_uint256 u in ((0 <=? x)%Z && (x <=? uint_max size)%Z)%bool
   end = true.
Proof.
now subst.
Qed.

Definition yul_value_of_uint256 {C: VyperConfig} (u: uint256) (t: yul_type)
: option (yul_value t)
:= match t as t' return t = t' -> _ with
   | BoolType => fun T =>
                 match Z_of_uint256 u with
                 | 0%Z => Some (BoolValue t false (uint256_to_yul_value_helper_bool T))
                 | 1%Z => Some (BoolValue t true (uint256_to_yul_value_helper_bool T))
                 | _ => None
                 end
   | IntType size true => fun T =>
                          let x := uint256_to_Z_as_signed u in
                          (if andb (sint_min size <=? x)%Z (x <=? sint_max size)%Z as c
                           return _ = c -> _
                             then fun E => Some (NumberValue t u (uint256_to_yul_value_helper_sint T E))
                             else fun _ => None) eq_refl
   | IntType size false => fun T =>
                           let x := Z_of_uint256 u in
                           (if andb (0 <=? x)%Z (x <=? uint_max size)%Z as c return _ = c -> _
                              then fun E => Some (NumberValue t u (uint256_to_yul_value_helper_uint T E))
                              else fun _ => None) eq_refl
   end eq_refl.

Lemma yul_value_of_uint256_u256 {C: VyperConfig} (u: uint256):
  yul_value_of_uint256 u U256 = Some (yul_uint256 u).
Proof.
simpl.
assert (R := uint256_range u).
unfold uint_max. unfold int_size_in_bits.
assert (T: ((0 <=? Z_of_uint256 u)%Z && (Z_of_uint256 u <=? 2 ^ 256 - 1)%Z)%bool = true).
{
  apply andb_true_intro.
  destruct R as (L, U).
  split. { apply Z.leb_le. exact L. }
  apply Z.leb_le.
  rewrite Z.sub_1_r.
  apply Z.lt_le_pred in U.
  exact U.
}
rewrite Logic2.if_yes with (E := T).
f_equal.
unfold yul_uint256.
f_equal.
apply eq_proofs_unicity. decide equality.
Qed.

Lemma yul_value_of_uint256_of_yul_value {C: VyperConfig} (t: yul_type) (v: yul_value t):
  yul_value_of_uint256 (uint256_of_yul_value v) t = Some v.
Proof.
destruct t; cbn; destruct v; try discriminate.
{
  destruct b; cbn; [unfold one256 | unfold zero256];
     rewrite uint256_ok; cbn; repeat f_equal; apply eq_proofs_unicity;
     decide equality.
}
destruct signed; cbn in *.
{
  (* signed *)
  remember (fun E =>
             Some (NumberValue (IntType size true) value (uint256_to_yul_value_helper_sint eq_refl E)))
    as good_branch.
  enough (Q: forall E, good_branch E = Some (NumberValue (IntType size true) value ok)).
  {
    clear Heqgood_branch.
    revert good_branch Q.
    assert (ok' := ok).
    now rewrite ok'.
  }
  intros.
  subst. repeat f_equal.
  apply eq_proofs_unicity; decide equality.
}
(* unsigned *)
remember (fun E =>
           Some (NumberValue (IntType size false) value (uint256_to_yul_value_helper_uint eq_refl E)))
  as good_branch.
enough (Q: forall E, good_branch E = Some (NumberValue (IntType size false) value ok)).
{
  clear Heqgood_branch.
  revert good_branch Q.
  assert (ok' := ok).
  now rewrite ok'.
}
intros.
subst. repeat f_equal.
apply eq_proofs_unicity; decide equality.
Qed.

Definition uint256_of_dynamic_value {C: VyperConfig} (d: dynamic_value)
: uint256
:= let '(existT _ _ v) := d in
   uint256_of_yul_value v.

Lemma bool_eq_via_uint256 {C: VyperConfig}
                          (a b: bool)
                          (E: (if a then one256 else zero256)
                               =
                              (if b then one256 else zero256)):
  a = b.
Proof.
assert (E': Z_of_uint256 (if a then one256 else zero256) = Z_of_uint256 (if b then one256 else zero256))
  by now rewrite E.
unfold one256 in E'. unfold zero256 in E'.
destruct a, b; repeat rewrite uint256_ok in E'; now try discriminate.
Qed.

Lemma yul_value_eq_via_uint256 {C: VyperConfig}
                               (t: yul_type)
                               (a b: yul_value t)
                               (E: uint256_of_yul_value a = uint256_of_yul_value b):
  a = b.
Proof.
unfold uint256_of_yul_value in E.
destruct a, b, t; try discriminate; [| apply bool_eq_via_uint256 in E ];
  subst; f_equal; apply Eqdep_dec.eq_proofs_unicity; decide equality.
Qed.

Definition string_of_type (t: yul_type)
:= match t with
   | BoolType => "bool"%string
   | IntType size signed => String (if signed then "s"%char else "u"%char) (string_of_int_size size)
   end.

Example string_of_u256: string_of_type U256 = "u256"%string. Proof. trivial. Qed.

Definition type_of_string (s: string)
: option yul_type
:= match s with
   | String "s"%char size =>
        match int_size_of_string size with
        | Some s => Some (IntType s true)
        | None => None
        end
   | String "u"%char size =>
        match int_size_of_string size with
        | Some s => Some (IntType s false)
        | None => None
        end
   | "bool"%string => Some BoolType
   | _ => None
   end.

Lemma type_of_string_of_type (t: yul_type):
  type_of_string (string_of_type t) = Some t.
Proof.
destruct t as [|size]. { trivial. }
now destruct size, signed.
Qed.


Local Lemma int_zero_value_helper {C: VyperConfig} (size: int_size) (signed: bool):
   match IntType size signed with
   | BoolType => false
   | IntType size true =>
       let x := uint256_to_Z_as_signed zero256 in
       ((sint_min size <=? x)%Z && (x <=? sint_max size)%Z)%bool
   | IntType size false =>
       let x := Z_of_uint256 zero256 in ((0 <=? x)%Z && (x <=? uint_max size)%Z)%bool
   end = true.
Proof.
cbn. unfold zero256. unfold uint256_to_Z_as_signed.
rewrite uint256_ok. cbn.
now destruct signed, size.
Qed.

Definition int_zero_value {C: VyperConfig} (size: int_size) (signed: bool)
: yul_value (IntType size signed)
:= NumberValue (IntType size signed) zero256 (int_zero_value_helper size signed).


Definition zero_value {C: VyperConfig} (t: yul_type)
: yul_value t
:= match t with
   | BoolType => yul_false
   | IntType size signed => int_zero_value size signed
   end.

Lemma zero_value_ok {C: VyperConfig} (t: yul_type):
  Z_of_uint256 (uint256_of_yul_value (zero_value t)) = 0%Z.
Proof.
destruct t; cbn; unfold zero256; rewrite uint256_ok; trivial.
Qed.