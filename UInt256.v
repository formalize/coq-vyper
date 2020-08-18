From Coq Require Import ZArith.
Require Import Config UntypedAST.

Definition interpret_unop {C: VyperConfig} (op: unop) (a: uint256)
: option uint256
:= match op with
   | BitwiseNot => Some (uint256_of_Z (Z.lxor (Z.ones 256) (Z_of_uint256 a)))
   | Neg => maybe_uint256_of_Z (- Z_of_uint256 a) (* This only allows 0. *)
   end.

Definition interpret_binop {C: VyperConfig} (op: binop) (a b: uint256)
: option uint256
:= match op with
   | Lt => Some (if (Z_of_uint256 a <?  Z_of_uint256 b)%Z then one256 else zero256)
   | Le => Some (if (Z_of_uint256 a <=? Z_of_uint256 b)%Z then one256 else zero256)
   | Gt => Some (if (Z_of_uint256 a >?  Z_of_uint256 b)%Z then one256 else zero256)
   | Ge => Some (if (Z_of_uint256 a >=? Z_of_uint256 b)%Z then one256 else zero256)
   | Eq => Some (if (Z_of_uint256 a =?  Z_of_uint256 b)%Z then one256 else zero256)
   | Ne => Some (if (Z_of_uint256 a =?  Z_of_uint256 b)%Z then zero256 else one256)
   | BitwiseOr  => Some (uint256_of_Z (Z.lor  (Z_of_uint256 a) (Z_of_uint256 b)))
   | BitwiseAnd => Some (uint256_of_Z (Z.land (Z_of_uint256 a) (Z_of_uint256 b)))
   | BitwiseXor => Some (uint256_of_Z (Z.lxor (Z_of_uint256 a) (Z_of_uint256 b)))
   | ShiftLeft  => Some (uint256_of_Z (Z.shiftl (Z_of_uint256 a) (Z_of_uint256 b)))
   | ShiftRight => Some (uint256_of_Z (Z.shiftr (Z_of_uint256 a) (Z_of_uint256 b)))
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