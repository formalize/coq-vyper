(* Yul's builtins are different from L10-L40 builtins because of the different type system. *)

From Coq Require Import List String Arith.

From Vyper Require Import Config Map NaryFun.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types.

Record yul_builtin {C: VyperConfig} := {
  b_input_types: list yul_type;
  b_output_types: list yul_type;
  b_fun: world_state -> nary_fun uint256 (List.length b_input_types)
                                         (world_state * expr_result (list uint256))
}.

Inductive mass_typecheck_result
:= MassTypecheckOk
 | MassTypecheckWrongType
 | MassTypecheckWrongArity.

Fixpoint mass_typecheck {C: VyperConfig} (values: list dynamic_value) (types: list yul_type)
: mass_typecheck_result
:= match values, types with
   | nil, nil => MassTypecheckOk
   | (existT _ t _) :: vtail, thead :: ttail =>
      if yul_type_eq_dec t thead
        then mass_typecheck vtail ttail
        else MassTypecheckWrongType
   | _, _ => MassTypecheckWrongArity
   end.

Lemma mass_typecheck_ok_rewrite {C: VyperConfig} (values: list dynamic_value) (types: list yul_type)
                                {Result: Type} 
                                (when_ok: mass_typecheck values types = MassTypecheckOk -> Result)
                                (when_wt: mass_typecheck values types = MassTypecheckWrongType -> Result)
                                (when_wa: mass_typecheck values types = MassTypecheckWrongArity -> Result)
                                (Ok: mass_typecheck values types = MassTypecheckOk):
  match mass_typecheck values types as z return _ = z -> Result with
  | MassTypecheckOk => when_ok
  | MassTypecheckWrongType => when_wt
  | MassTypecheckWrongArity => when_wa
  end eq_refl = when_ok Ok.
Proof.
destruct (mass_typecheck values types); try discriminate.
f_equal. apply Eqdep_dec.eq_proofs_unicity. decide equality.
Qed.

(* mass typecheck fails if the numbers of values and types mismatch *)
Lemma mass_typecheck_length {C: VyperConfig} (values: list dynamic_value) (types: list yul_type)
                            (H: mass_typecheck values types = MassTypecheckOk):
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

(** Test if the list only has u256. *)
Definition all_are_u256 (l: list yul_type)
: bool
:= List.forallb (fun x => if yul_type_eq_dec x U256 then true else false) l.

Lemma all_are_u256_head (head: yul_type) (tail: list yul_type)
                        (Ok: all_are_u256 (head :: tail) = true):
  head = U256.
Proof.
unfold all_are_u256 in Ok.
rewrite forallb_forall in Ok.
rewrite<- Forall_forall in Ok.
apply Forall_inv in Ok.
now destruct (yul_type_eq_dec head U256) as [Y|N].
Qed.

Lemma all_are_u256_tail (head: yul_type) (tail: list yul_type)
                        (Ok: all_are_u256 (head :: tail) = true):
  all_are_u256 tail = true.
Proof.
unfold all_are_u256 in *.
rewrite forallb_forall in *.
rewrite<- Forall_forall in *.
apply Forall_inv_tail in Ok.
exact Ok.
Qed.


Lemma mass_typecheck_u256 {C: VyperConfig}
                          (v: list uint256)
                          (types: list yul_type)
                          (Ok: all_are_u256 types = true):
  mass_typecheck
        (List.map (fun x: uint256 => existT _ U256 (yul_uint256 x)) v)
        types
   =
  if List.length v =? List.length types then MassTypecheckOk else MassTypecheckWrongArity.
Proof.
revert types Ok. induction v as [|h]; intros; destruct types as [|htype]; try easy.
assert (OkHead := all_are_u256_head _ _ Ok). subst htype.
cbn. exact (IHv _ (all_are_u256_tail _ _ Ok)).
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
                                (E: mass_typecheck args (b_input_types b) = MassTypecheckOk):
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
:= match mass_typecheck args (b_input_types b) as a return _ = a -> _ with
   | MassTypecheckOk => fun E =>
          let args_u256 := List.map uint256_of_dynamic_value args in
          match nary_call (b_fun b world) args_u256 (call_builtin_helper b args E) with
          | ((world', ExprSuccess outputs_256), _) =>
              (world', match mass_cast outputs_256 (b_output_types b) with
                       | inl err => expr_error err
                       | inr outputs => ExprSuccess outputs
                       end)
          | ((world', ExprAbort ab), _) => (world', ExprAbort ab)
          end
  | MassTypecheckWrongType => fun _ => (world, expr_error "builtin argument type mismatch"%string)
  | MassTypecheckWrongArity => fun _ => (world, expr_error "builtin with wrong arity"%string)
  end eq_refl.
