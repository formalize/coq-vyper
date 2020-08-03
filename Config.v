From Coq Require Import String ZArith.
Require FSet Map.

Class VyperConfig := {
  string_set: Type;
  string_set_impl: FSet.class String.string_dec string_set;
  string_map: Type -> Type;
  string_map_impl: forall t: Type, Map.class String.string_dec t (string_map t);
  world_state: Type;
  uint256: Type;
  storage_lookup: world_state -> string -> option uint256;
}.

Definition sample_config
:= {|
      string_set := FSet.string_avl_set;
      string_set_impl := FSet.string_avl_set_impl;
      string_map := Map.string_avl_map;
      string_map_impl := Map.string_avl_map_impl;
      world_state := Map.string_avl_map Z;
      uint256 := Z; (* XXX *)
      storage_lookup := let _ := Map.string_avl_map_impl in Map.lookup;
   |}.