From Coq Require Import ZArith.
Require Import Config L10.AST.

(** Bitwise not *)
Definition uint256_not {C: VyperConfig} (a: uint256)
:= uint256_of_Z (Z.lxor (Z.ones 256) (Z_of_uint256 a)).

(** Logical not ("iszero"). *)
Definition uint256_iszero {C: VyperConfig} (a: uint256)
:= if (Z_of_uint256 a =? 0)%Z
     then one256
     else zero256.

Definition interpret_unop {C: VyperConfig} (op: unop) (a: uint256)
: option uint256
:= match op with
   | BitwiseNot => Some (uint256_not a)
   | Neg => maybe_uint256_of_Z (- Z_of_uint256 a) (* This only allows 0. *)
   | LogicalNot => Some (uint256_iszero a)
   end.

(** Bitwise and *)
Definition uint256_and {C: VyperConfig} (a b: uint256)
:= uint256_of_Z (Z.land (Z_of_uint256 a) (Z_of_uint256 b)).

(** Bitwise or *)
Definition uint256_or {C: VyperConfig} (a b: uint256)
:= uint256_of_Z (Z.lor (Z_of_uint256 a) (Z_of_uint256 b)).

(** Bitwise xor *)
Definition uint256_xor {C: VyperConfig} (a b: uint256)
:= uint256_of_Z (Z.lxor (Z_of_uint256 a) (Z_of_uint256 b)).

Definition uint256_lt {C: VyperConfig} (a b: uint256)
:= if (Z_of_uint256 a <?  Z_of_uint256 b)%Z then one256 else zero256.

Definition uint256_eq {C: VyperConfig} (a b: uint256)
:= if (Z_of_uint256 a =?  Z_of_uint256 b)%Z then one256 else zero256.

Definition uint256_gt {C: VyperConfig} (a b: uint256)
:= if (Z_of_uint256 a >?  Z_of_uint256 b)%Z then one256 else zero256.

Definition uint256_le {C: VyperConfig} (a b: uint256)
:= if (Z_of_uint256 a <=?  Z_of_uint256 b)%Z then one256 else zero256.

Definition uint256_ge {C: VyperConfig} (a b: uint256)
:= if (Z_of_uint256 a >=?  Z_of_uint256 b)%Z then one256 else zero256.

Definition uint256_ne {C: VyperConfig} (a b: uint256)
:= if (Z_of_uint256 a =?  Z_of_uint256 b)%Z then zero256 else one256.

Definition interpret_binop {C: VyperConfig} (op: binop) (a b: uint256)
: option uint256
:= match op with
   | Lt => Some (uint256_lt a b)
   | Le => Some (uint256_le a b)
   | Gt => Some (uint256_gt a b)
   | Ge => Some (uint256_ge a b)
   | Eq => Some (uint256_eq a b)
   | Ne => Some (uint256_ne a b)
   | BitwiseOr  => Some (uint256_or a b)
   | BitwiseAnd => Some (uint256_and a b)
   | BitwiseXor => Some (uint256_xor a b)
   (* Nov 2020: changed shifts to checked as x << n is basically arithmetic, namely x * 2**n *)
   | ShiftLeft  => maybe_uint256_of_Z (Z.shiftl (Z_of_uint256 a) (Z_of_uint256 b))
   | ShiftRight => maybe_uint256_of_Z (Z.shiftr (Z_of_uint256 a) (Z_of_uint256 b))
   | Add => maybe_uint256_of_Z (Z_of_uint256 a + Z_of_uint256 b)%Z
   | Sub => maybe_uint256_of_Z (Z_of_uint256 a - Z_of_uint256 b)%Z
   | Mul => maybe_uint256_of_Z (Z_of_uint256 a * Z_of_uint256 b)%Z
   | Quot => let bz := Z_of_uint256 b in
             if (bz =? 0)%Z
               then None
               else maybe_uint256_of_Z (Z_of_uint256 a / bz)%Z
   | Mod => let bz := Z_of_uint256 b in
            if (bz =? 0)%Z
               then None
               else maybe_uint256_of_Z (Z_of_uint256 a mod bz)%Z
   | Pow => maybe_uint256_of_Z (Z.pow (Z_of_uint256 a) (Z_of_uint256 b))%Z
   end.