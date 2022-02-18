From Coq Require Import String Arith ZArith PropExtensionality Lia.

From Vyper Require Import Config Calldag.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require Import AST Descend Callset Descend Expr Stmt Interpret.
From Vyper.L40Metered Require Import Interpret Expr Stmt.

Lemma call_metering_ok
           {C: VyperConfig}
           {bigger_call_depth_bound smaller_call_depth_bound: nat}
           (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
           {max_call_depth: nat}
           (DepthOk: bigger_call_depth_bound <= max_call_depth)
           {cd: calldag}
           (fc: fun_ctx cd bigger_call_depth_bound)
           (builtins: string -> option builtin)
           (world: world_state)
           (arg_values: list uint256):
  let '(world', result) := interpret_call builtins fc world arg_values
   in interpret_call_metered max_call_depth (cd_decls cd) builtins (fun_decl fc)
                             world arg_values
       =
      (world', Some result).
Proof.
revert smaller_call_depth_bound Ebound fc world arg_values max_call_depth DepthOk.
induction bigger_call_depth_bound; intros. { discriminate. }
inversion Ebound. subst. clear Ebound.
unfold interpret_call. fold (@interpret_call C smaller_call_depth_bound cd).
match goal with
|- let '(world', result) :=
     match fun_decl fc as d with
     | FunDecl name arity body => ?X
     end eq_refl
   in _ = _
    =>
   remember (fun name arity body => X) as do_call
end.
enough (Q: forall name arity body E,
           let '(world', result) := do_call name arity body E in
           interpret_call_metered max_call_depth (cd_decls cd) builtins
                                  (FunDecl name arity body) world arg_values
            =
           (world', Some result)).
{
  clear Heqdo_call.
  destruct (fun_decl fc) as (name, arity, body).
  apply Q.
}
intros. subst do_call.
unfold interpret_call_metered.
destruct max_call_depth. { apply Nat.nle_succ_0 in DepthOk. contradiction. }
simpl. (* cbn does something weird *)
fold interpret_call_metered.
remember (Datatypes.length arg_values =? N.to_nat arity) as arity_ok.
destruct arity_ok. 2:reflexivity.
assert (IH: forall (fc': fun_ctx cd smaller_call_depth_bound)
                   (world: world_state)
                   (arg_values: list uint256),
             let
             '(world', result) := interpret_call builtins fc' world arg_values in
              interpret_call_metered max_call_depth (cd_decls cd) builtins (fun_decl fc') world arg_values = (world', Some result)).
{
  intros.
  assert (D := fun_bound_ok fc'). rewrite Nat.ltb_lt in D.
  destruct smaller_call_depth_bound. { apply Nat.nlt_0_r in D. contradiction. }
  apply (IHbigger_call_depth_bound _ eq_refl).
  apply (le_S_n _ _ DepthOk).
}
assert (M := let _ := memory_impl in
             block_metering_ok eq_refl fc
                               (interpret_call builtins)
                               (interpret_call_metered max_call_depth
                                                       (cd_decls cd) builtins)
                               IH builtins world (OpenArray.from_list arg_values) nil
                               body ((Interpret.interpret_call_helper E))).
destruct interpret_block as ((world', loc'), result). rewrite M.
destruct result; try easy.
now destruct a.
Qed.

(* XXX this is a dup from somewhere else *)
Lemma match_some {T R} {x: option T} {y: T} (E: x = Some y)
                 (some_branch: forall z: T, x = Some z -> R)
                 (none_branch: x = None -> R):
  match x as x' return x = x' -> _ with
  | Some z => some_branch z
  | None => none_branch
  end eq_refl
   =
  some_branch y E.
Proof.
destruct x. 2:discriminate.
inversion E. subst. f_equal. apply proof_irrelevance.
Qed.

Lemma match_none {T R} {x: option T} (E: x = None)
                 (some_branch: forall z: T, x = Some z -> R)
                 (none_branch: x = None -> R):
  match x as x' return x = x' -> _ with
  | Some z => some_branch z
  | None => none_branch
  end eq_refl
   =
  none_branch E.
Proof.
destruct x. 1:discriminate.
inversion E. subst. f_equal. apply proof_irrelevance.
Qed.

Fixpoint max_depth_by_names (m: string -> option nat) (l: list string)
{struct l}
: nat
:= match l with
   | nil => 0
   | (h :: t)%list => match m h with
                      | Some n => max n (max_depth_by_names m t)
                      | None   =>        max_depth_by_names m t
                      end
   end.

Definition max_depth_in_calldag {C: VyperConfig}
                                (cd: calldag)
:= let _ := string_map_impl in
   max_depth_by_names (cd_depthmap cd)
                      (List.map fst (Map.items (cd_decls cd))).

Lemma max_depth_in_calldag_ok {C: VyperConfig}
                              {cd: calldag}
                              {name: string}
                              {d: decl}
                              {depth: nat}
                              (Ok: cd_declmap cd name = Some d)
                              (D: cd_depthmap cd name = Some depth):
  depth <= max_depth_in_calldag cd.
Proof.
unfold cd_declmap in Ok.
rewrite Map.items_ok in Ok.
unfold max_depth_in_calldag.
remember (Map.items (cd_decls cd)) as l. clear Heql.
induction l as [|(k,v)]. { easy. }
cbn in *.
destruct string_dec as [E|NE].
{ subst k. rewrite D. lia. }
assert (IH := IHl Ok).
destruct (cd_depthmap cd k); lia.
Qed.

Lemma metering_ok
           {C: VyperConfig}
           {max_call_depth: nat}
           {cd: calldag}
           (DepthOk: max_depth_in_calldag cd < max_call_depth)
           (builtins: string -> option builtin)
           (fun_name: string)
           (world: world_state)
           (args: list uint256):
  let '(world', result) := interpret builtins cd fun_name world args
   in interpret_metered max_call_depth (cd_decls cd) builtins fun_name world args
       =
      (world', Some result).
Proof.
unfold interpret.
unfold interpret_metered.
unfold make_fun_ctx_and_bound.
unfold cd_declmap. unfold Base.map_lookup.
refine (match Map.lookup (cd_decls cd) fun_name as z return _ = z -> _ with
        | Some d => fun E => _
        | None => fun E => _
        end eq_refl).
2:{ rewrite (match_none E). rewrite E. trivial. }
rewrite (match_some E).
refine (match cd_depthmap cd fun_name as z return _ = z -> _ with
        | Some depth => fun D => _
        | None => fun D => _
        end eq_refl).
2:{ exfalso. exact (Calldag.make_fun_ctx_helper E D). }
rewrite (match_some D).
assert (M' := max_depth_in_calldag_ok E D).
assert (M: S depth <= max_call_depth) by lia.
assert (CM := call_metering_ok eq_refl M {|
             fun_name := fun_name;
             fun_depth := depth;
             fun_depth_ok := D;
             fun_decl := d;
             fun_decl_ok := E;
             fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth)
           |} builtins world args).
destruct interpret_call as (world', result).
rewrite E. apply CM.
Qed.
