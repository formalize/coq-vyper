From Coq Require Import Arith ZArith Eqdep_dec String.

From Vyper Require Import Config NaryFun.
From Vyper Require Import L10.Base CheckedArith UInt256.

(** Assert that the given builtin only computes the given pure unary function. *)
Definition BuiltinIsUnop {C: VyperConfig} (f: builtin) (unop: uint256 -> uint256)
:= match projT1 f as arity return _ = arity -> _ with
   | 1 => fun E => forall (w: world_state) (a: uint256),
                     nary_call_1 (projT2 f w) E a = (w, ExprSuccess (unop a))
   | _ => fun _ => False
   end eq_refl.

(** If a builtin is an unop, then its arity is 1. *)
Lemma builtin_is_unop_arity {C: VyperConfig} (f: builtin) (unop: uint256 -> uint256)
                            (Ok: BuiltinIsUnop f unop):
  projT1 f = 1.
Proof.
unfold BuiltinIsUnop in Ok.
remember (fun E : projT1 f = 1 =>
             forall (w : world_state) (a : uint256),
             nary_call_1 (projT2 f w) E a = (w, ExprSuccess (unop a))) as foo.
clear Heqfoo.
destruct (projT1 f) as [|n]; try contradiction.
now destruct n.
Qed.

(** [nary_call] works as it should on builtins approved by BuiltinIsUnop. *)
Lemma builtin_is_unop_call {C: VyperConfig} (f: builtin) (unop: uint256 -> uint256)
                           (Ok: BuiltinIsUnop f unop)
                           (w: world_state)
                           (a: uint256)
                           (ArityOk: projT1 f <= 1):
  nary_call (projT2 f w) (a :: nil) ArityOk = (w, ExprSuccess (unop a), nil).
Proof.
assert (Arity1 := builtin_is_unop_arity f unop Ok).
unfold BuiltinIsUnop in Ok.
remember (fun E : projT1 f = 1 =>
                 forall (w : world_state) (a: uint256),
                 nary_call_1 (projT2 f w) E a = (w, ExprSuccess (unop a))) as Good.
enough (G: Good Arity1).
{
  clear Ok. subst.
  rewrite nary_call_1_ok with (E := Arity1).
  f_equal. apply G.
}
clear HeqGood.
destruct (projT1 f) as [|n]; try contradiction.
destruct n; try contradiction.
assert (R: Arity1 = eq_refl). { apply eq_proofs_unicity. decide equality. }
rewrite R. assumption.
Qed.

Lemma builtin_is_unop_ok {C: VyperConfig} (f: builtin) (unop: uint256 -> uint256)
                         (Ok: BuiltinIsUnop f unop)
                         (w: world_state)
                         (a: uint256)
                         (LengthOk: (projT1 f =? Datatypes.length (a :: nil)) = true):
  call_builtin (a :: nil) LengthOk (projT2 f w) = (w, ExprSuccess (unop a)).
Proof.
unfold call_builtin.
now rewrite (builtin_is_unop_call f unop Ok w a).
Qed.

(** Assert that the given builtin only computes the given pure binary function. *)
Definition BuiltinIsBinop {C: VyperConfig} (f: builtin) (binop: uint256 -> uint256 -> uint256)
:= match projT1 f as arity return _ = arity -> _ with
   | 2 => fun E => forall (w: world_state) (a b: uint256),
                     nary_call_2 (projT2 f w) E a b = (w, ExprSuccess (binop a b))
   | _ => fun _ => False
   end eq_refl.

(** If a builtin is an unop, then its arity is 2. *)
Lemma builtin_is_binop_arity {C: VyperConfig} (f: builtin) (binop: uint256 -> uint256 -> uint256)
                             (Ok: BuiltinIsBinop f binop):
  projT1 f = 2.
Proof.
unfold BuiltinIsBinop in Ok.
remember (fun E : projT1 f = 2 =>
                 forall (w : world_state) (a b : uint256),
                 nary_call_2 (projT2 f w) E a b = (w, ExprSuccess (binop a b))) as foo.
clear Heqfoo.
destruct (projT1 f) as [|n]; try contradiction.
destruct n; try contradiction.
now destruct n.
Qed.

(** [nary_call] works as it should on builtins approved by BuiltinIsBinop. *)
Lemma builtin_is_binop_call {C: VyperConfig} (f: builtin) (binop: uint256 -> uint256 -> uint256)
                            (Ok: BuiltinIsBinop f binop)
                            (w: world_state)
                            (a b: uint256)
                            (ArityOk: projT1 f <= 2):
  nary_call (projT2 f w) (a :: b :: nil) ArityOk = (w, ExprSuccess (binop a b), nil).
Proof.
assert (Arity2 := builtin_is_binop_arity f binop Ok).
unfold BuiltinIsBinop in Ok.
remember (fun E : projT1 f = 2 =>
                 forall (w : world_state) (a b : uint256),
                 nary_call_2 (projT2 f w) E a b = (w, ExprSuccess (binop a b))) as Good.
enough (G: Good Arity2).
{
  clear Ok. subst.
  rewrite nary_call_2_ok with (E := Arity2).
  f_equal. apply G.
}
clear HeqGood.
destruct (projT1 f) as [|n]; try contradiction.
destruct n; try contradiction.
destruct n; try contradiction.
assert (R: Arity2 = eq_refl). { apply eq_proofs_unicity. decide equality. }
rewrite R. assumption.
Qed.

Lemma builtin_is_binop_ok {C: VyperConfig} (f: builtin) (binop: uint256 -> uint256 -> uint256)
                          (Ok: BuiltinIsBinop f binop)
                          (w: world_state)
                          (a b: uint256)
                          (LengthOk: (projT1 f =? List.length (a :: b :: nil)) = true):
  call_builtin (a :: b :: nil) LengthOk (projT2 f w) = (w, ExprSuccess (binop a b)).
Proof.
unfold call_builtin.
now rewrite (builtin_is_binop_call f binop Ok w a).
Qed.

Definition builtin_of_unop {C: VyperConfig} (f: uint256 -> uint256)
: builtin
:= existT _ 1 (fun w =>
                (fun a: uint256 => (w, ExprSuccess (f a))): nary_fun _ 1 _).

Lemma builtin_of_unop_ok {C: VyperConfig} (f: uint256 -> uint256):
  BuiltinIsUnop (builtin_of_unop f) f.
Proof. easy. Qed.

Definition builtin_of_binop {C: VyperConfig} (f: uint256 -> uint256 -> uint256)
: builtin
:= existT _ 2 (fun w =>
                (fun (a b: uint256) => (w, ExprSuccess (f a b))): nary_fun _ 2 _).

Lemma builtin_of_binop_ok {C: VyperConfig} (f: uint256 -> uint256 -> uint256):
  BuiltinIsBinop (builtin_of_binop f) f.
Proof. easy. Qed.


(******************************************)
(* Builtins for uint256 modulo arithmetic *)
(******************************************)

Definition builtin_uint256_add {C: VyperConfig} := builtin_of_binop uint256_add.
Definition builtin_uint256_sub {C: VyperConfig} := builtin_of_binop uint256_sub.
Definition builtin_uint256_mul {C: VyperConfig} := builtin_of_binop uint256_mul.
Definition builtin_uint256_div {C: VyperConfig} := builtin_of_binop uint256_div.
Definition builtin_uint256_mod {C: VyperConfig} := builtin_of_binop uint256_mod.
Definition builtin_uint256_pow {C: VyperConfig} := builtin_of_binop uint256_pow.
Definition builtin_uint256_shl {C: VyperConfig} := builtin_of_binop uint256_shl.
Definition builtin_uint256_shr {C: VyperConfig} := builtin_of_binop uint256_shr.

(*****************)
(* Builtin names *)
(*****************)

Record builtin_names_config := { builtin_name_uint256_add: string
                               ; builtin_name_uint256_sub: string
                               ; builtin_name_uint256_mul: string
                               ; builtin_name_uint256_div: string
                               ; builtin_name_uint256_mod: string
                               ; builtin_name_uint256_pow: string
                               ; builtin_name_uint256_not: string
                               ; builtin_name_uint256_iszero: string
                               ; builtin_name_uint256_and: string
                               ; builtin_name_uint256_or: string
                               ; builtin_name_uint256_xor: string
                               ; builtin_name_uint256_lt: string
                               ; builtin_name_uint256_eq: string
                               ; builtin_name_uint256_shl: string
                               ; builtin_name_uint256_shr: string
                               }.

Definition builtin_names_std
: builtin_names_config
:= {| builtin_name_uint256_add    := "uint256_add"
    ; builtin_name_uint256_sub    := "uint256_sub"
    ; builtin_name_uint256_mul    := "uint256_mul"
    ; builtin_name_uint256_div    := "uint256_div"
    ; builtin_name_uint256_mod    := "uint256_mod"
    ; builtin_name_uint256_pow    := "uint256_exp" (* not pow! *)
    ; builtin_name_uint256_not    := "uint256_not"
    ; builtin_name_uint256_iszero := "uint256_iszero"
    ; builtin_name_uint256_and    := "uint256_and"
    ; builtin_name_uint256_or     := "uint256_or"
    ; builtin_name_uint256_xor    := "uint256_xor"
    ; builtin_name_uint256_lt     := "uint256_lt"
    ; builtin_name_uint256_eq     := "uint256_eq"
    ; builtin_name_uint256_shl    := "uint256_shl"
    ; builtin_name_uint256_shr    := "uint256_shr"
   |}.

Definition BuiltinsSupportUnop {C: VyperConfig}
                               (builtins: string -> option builtin)
                               (name: string)
                               (unop: uint256 -> uint256)
:= match builtins name with
   | Some b => BuiltinIsUnop b unop
   | None => False
   end.

Definition BuiltinsSupportBinop {C: VyperConfig}
                                (builtins: string -> option builtin)
                                (name: string)
                                (binop: uint256 -> uint256 -> uint256)
:= match builtins name with
   | Some b => BuiltinIsBinop b binop
   | None => False
   end.


Definition BuiltinsSupportUInt256 {C: VyperConfig}
                                  (names: builtin_names_config)
                                  (builtins: string -> option builtin)
:= BuiltinsSupportBinop builtins (builtin_name_uint256_add names) uint256_add
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_sub names) uint256_sub
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_mul names) uint256_mul
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_div names) uint256_div
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_mod names) uint256_mod
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_pow names) uint256_pow
/\ BuiltinsSupportUnop  builtins (builtin_name_uint256_not names) uint256_not
/\ BuiltinsSupportUnop  builtins (builtin_name_uint256_iszero names) uint256_iszero
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_and names) uint256_and
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_or  names) uint256_or
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_xor names) uint256_xor
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_lt  names) uint256_lt
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_eq  names) uint256_eq
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_shl names) uint256_shl
/\ BuiltinsSupportBinop builtins (builtin_name_uint256_shr names) uint256_shr.
