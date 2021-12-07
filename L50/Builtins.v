(* Yul's builtins are different from L10-L40 builtins because of the different type system. *)

From Coq Require Import List String Arith.

From Vyper Require Import Config Map NaryFun.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types.

Record yul_builtin {C: VyperConfig} := {
  b_input_types: list yul_type;
  b_output_types: list yul_type;
  b_fun: world_state -> nary_fun uint256 (List.length b_input_types) (world_state * list uint256)
}.

Fixpoint mass_typecheck {C: VyperConfig} (values: list dynamic_value) (types: list yul_type)
: bool
:= match values, types with
   | nil, nil => true
   | (existT _ t _) :: vtail, thead :: ttail =>
      if yul_type_eq_dec t thead
        then mass_typecheck vtail ttail
        else false
   | _, _ => false
   end.

(* mass typecheck fails if the numbers of values and types mismatch *)
Lemma mass_typecheck_length {C: VyperConfig} (values: list dynamic_value) (types: list yul_type)
                            (H: mass_typecheck values types = true):
  List.length values = List.length types.
Proof.
revert types H.
induction values as [|vhead]; intros; cbn in H; destruct types as [|thead]; try discriminate.
{ trivial. }
{ now destruct vhead. }
cbn. f_equal.
apply IHvalues.
destruct vhead as (t, _).
now destruct (yul_type_eq_dec t thead).
Qed.

Fixpoint mass_cast {C: VyperConfig} (values: list uint256) (types: list yul_type)
: string + list dynamic_value
:= match values, types with
   | nil, nil => inr nil
   | vhead :: vtail, thead :: ttail =>
      match yul_value_of_uint256 vhead thead with
      | Some v =>
          match mass_cast vtail ttail with
          | inl err => inl err
          | inr tail => inr (existT _ thead v :: tail)
          end
      | None => inl ("cannot cast to " ++ string_of_type thead)%string
      end
   | _, _ => inl "cannot cast: different number of types"%string
   end.

Local Lemma call_builtin_helper {C: VyperConfig}
                                (b: yul_builtin)
                                (args: list dynamic_value)
                                (E: mass_typecheck args (b_input_types b) = true):
  List.length (b_input_types b) <= List.length (List.map uint256_of_dynamic_value args).
Proof.
rewrite List.map_length.
apply Nat.eq_le_incl.
symmetry.
apply mass_typecheck_length.
assumption.
Qed.

Definition call_builtin {C: VyperConfig} (b: yul_builtin) (world: world_state) (args: list dynamic_value)
: world_state * expr_result (list dynamic_value)
:= (if mass_typecheck args (b_input_types b) as a return _ = a -> _
     then fun E =>
          let args_u256 := List.map uint256_of_dynamic_value args in
          let '((world', outputs_256), _) := nary_call (b_fun b world) args_u256
                                                       (call_builtin_helper b args E)
           in (world', match mass_cast outputs_256 (b_output_types b) with
                       | inl err => expr_error err
                       | inr outputs => ExprSuccess outputs
                       end)
     else fun _ => (world, expr_error "builtin argument type mismatch"%string)) eq_refl.