From Coq Require Import Ascii String List NArith DecimalString DecimalN DecimalPos.

From Vyper Require Import Config.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L10 Require Import Base.

From Vyper.From40To50 Require Import Translate Proto.


Definition starts_with_dollar (s: string)
: bool
:= match s with
   | String "$"%char _ => true
   | _ => false
   end.

Lemma starts_with_dollar_eqb (head: ascii) (tail: string):
  starts_with_dollar (String head tail) = Ascii.eqb head "$"%char.
Proof.
cbn.
destruct head as (b0, b1, b2, b3, b4, b5, b6, b7).
now destruct b0, b1, b2, b3, b4, b5, b6, b7.
Qed.

(** [translate_fun_decls] prefixes everything with '$'. *)
Lemma translated_decls_start_with_dollar {C: VyperConfig}
                                {B: builtin_names_config}
                                {protos: string_map proto}
                                (decls40: string_map L40.AST.decl)
                                (decls50: string_map L50.AST.fun_decl)
                                (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
                                (name: string)
                                (Ok: map_lookup decls50 name <> None):
  starts_with_dollar name = true.
Proof.
unfold translate_fun_decls in DeclsOk.
remember (Map.items decls40) as items40. clear Heqitems40.
revert decls50 DeclsOk Ok.
induction items40 as [|(k,v)]; intros; cbn in DeclsOk.
{
  inversion DeclsOk. subst. unfold map_lookup in Ok.
  now rewrite Map.empty_lookup in Ok.
}
destruct (translate_fun_decl B protos v). { discriminate. }
destruct alist_maybe_map_kv. { discriminate. }
cbn in DeclsOk. inversion DeclsOk. subst. clear DeclsOk.
unfold map_lookup in Ok. rewrite Map.insert_ok in Ok.
remember (string_dec (String "$" k) name) as found.
destruct found. { now subst. }
unfold map_lookup in IHitems40.
now refine (IHitems40 _ _ Ok).
Qed.

(** The same as the previous one but more convenient to use for builtins. *)
Lemma unmangled_names_are_not_translated {C: VyperConfig}
                                         {B: builtin_names_config}
                                         {protos: string_map proto}
                                         (decls40: string_map L40.AST.decl)
                                         (decls50: string_map L50.AST.fun_decl)
                                         (DeclsOk: translate_fun_decls B protos decls40 = inr decls50)
                                         (name: string)
                                         (Ok: starts_with_dollar name = false):
  map_lookup decls50 name = None.
Proof.
remember (map_lookup decls50 name) as d. destruct d; trivial.
assert (NE: map_lookup decls50 name <> None). { rewrite<- Heqd. discriminate. }
rewrite (translated_decls_start_with_dollar decls40 decls50 DeclsOk name NE) in Ok.
discriminate.
Qed.

Lemma mangled_safety_equiv {T} (builtins: string -> option T):
  (forall x, builtins ("$" ++ x)%string = None)
   <->
  (forall x, builtins x <> None -> starts_with_dollar x = false).
Proof.
cbn.
split.
{
  intros H x Ok.
  destruct x as [|head]. { easy. }
  rewrite starts_with_dollar_eqb.
  cbn.
  remember ((head =? "$")%char) as head_is_dollar. destruct head_is_dollar. 2:trivial.
  symmetry in Heqhead_is_dollar. apply Ascii.eqb_eq in Heqhead_is_dollar.
  subst. exfalso. exact (Ok (H x)).
}
intros H x.
assert (Ok := H (String "$"%char x)). clear H.
remember (builtins (String "$" x)) as b. destruct b. 2:trivial.
clear Heqb. cbn in Ok. exfalso. assert (W: Some t <> None) by discriminate.
assert (Ok' := Ok W). discriminate.
Qed.

(***************************************************************************************************)

(* not in standard library? oh well *)
Lemma string_app_l_inj (a b c: string)
                       (E: (a ++ b = a ++ c)%string):
  b = c.
Proof.
induction a as [|h]. { easy. }
cbn in E. inversion E. tauto.
Qed.

(* why is it not in stdlib? *)
Lemma to_uint_nonnil (a: N):
  N.to_uint a <> Decimal.Nil.
Proof.
destruct a as [|p]. { easy. }
cbn. apply Unsigned.to_uint_nonnil.
Qed.

Lemma string_of_N_inj (a b: N)
                      (E: NilZero.string_of_uint (N.to_uint a)
                           =
                          NilZero.string_of_uint (N.to_uint b)):
  a = b.
Proof.
assert (UsuA := NilZero.usu (N.to_uint a) (to_uint_nonnil a)).
assert (UsuB := NilZero.usu (N.to_uint b) (to_uint_nonnil b)).
apply DecimalN.Unsigned.to_uint_inj.
enough (Q: Some (N.to_uint a) = Some (N.to_uint b)) by now inversion Q.
rewrite<- UsuA. rewrite<- UsuB.
now rewrite E.
Qed.

Lemma make_var_name_inj (prefix: string) (a b: N)
                        (E: make_var_name prefix a = make_var_name prefix b):
  a = b.
Proof.
cbn in E. inversion E. apply string_of_N_inj.
apply string_app_l_inj with (a := prefix). assumption.
Qed.

Lemma make_var_name_inj' (prefix: string) (a b: N)
                         (NE: a <> b):
  make_var_name prefix a <> make_var_name prefix b.
Proof.
intro E. apply NE.
exact (make_var_name_inj prefix a b E).
Qed.
