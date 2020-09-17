From Coq Require Import String ZArith CyclicAxioms ZModulo.
Require FSet Map OpenArray.

Class VyperConfig := {
  string_set: Type;
  string_set_impl: FSet.class String.string_dec string_set;
  string_map: Type -> Type;
  string_map_impl: forall t: Type, Map.class String.string_dec t (string_map t);
  world_state: Type;
  uint256: Type;
  Z_of_uint256: uint256 -> Z;
  uint256_of_Z: Z -> uint256;
  uint256_ok: forall z: Z, Z_of_uint256 (uint256_of_Z z) = (z mod 2^256)%Z;
  uint256_range: forall u: uint256, (0 <= Z_of_uint256 u < 2^256)%Z;
  storage_lookup: world_state -> string -> option uint256;
  storage_insert: world_state -> string -> uint256 -> world_state;
  memory: Type;
  memory_impl: OpenArray.class (uint256_of_Z 0%Z) memory;
}.

Lemma two_to_256_ne_0: (2^256 <> 0)%Z.
Proof.
apply Z.pow_nonzero. { discriminate. }
rewrite<- Z.leb_le. trivial.
Qed.

Lemma two_to_256_pos: (0 < 2^256)%Z.
Proof.
apply Z.pow_pos_nonneg.
{ rewrite<- Z.ltb_lt. trivial. }
rewrite<- Z.leb_le. trivial.
Qed.

Definition sample_config
:= {|
      string_set := FSet.string_avl_set;
      string_set_impl := FSet.string_avl_set_impl;
      string_map := Map.string_avl_map;
      string_map_impl := Map.string_avl_map_impl;
      world_state := Map.string_avl_map Z;
      uint256 := Z;
      Z_of_uint256 u := (u mod 2^256)%Z;
      uint256_of_Z z := (z mod 2^256)%Z;
      uint256_ok z := Z.mod_mod _ _ two_to_256_ne_0;
      uint256_range u := Z.mod_pos_bound _ _ two_to_256_pos;
      storage_lookup := let _ := Map.string_avl_map_impl in Map.lookup;
      storage_insert := let _ := Map.string_avl_map_impl in Map.insert;
      memory := list Z;
      memory_impl := OpenArray.list_inst 0%Z;
   |}.

Definition zero256 {C: VyperConfig} := uint256_of_Z 0%Z.
Definition one256  {C: VyperConfig} := uint256_of_Z 1%Z.

Definition maybe_uint256_of_Z {C: VyperConfig} (z: Z)
:= let u := uint256_of_Z z in
   if (Z_of_uint256 u =? z)%Z
     then Some u
     else None.