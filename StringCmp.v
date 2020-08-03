Require Import Ascii String Structures.OrderedTypeEx NArith Arith.

Definition ascii_compare (a b : ascii) : comparison :=
  N.compare (N_of_ascii a) (N_of_ascii b).

Lemma ascii_compare_eq (a b : ascii):
  ascii_compare a b = Eq  <->  a = b.
Proof.
unfold ascii_compare.
rewrite N.compare_eq_iff.
split. 2:{ intro. now subst. }
intro H.
rewrite<- (ascii_N_embedding a).
rewrite<- (ascii_N_embedding b).
now rewrite H.
Qed.

Lemma ascii_compare_lt (a b : ascii):
  ascii_compare a b = Lt  <->  nat_of_ascii a < nat_of_ascii b.
Proof.
unfold ascii_compare. unfold nat_of_ascii.
rewrite N2Nat.inj_compare.
rewrite Nat.compare_lt_iff.
reflexivity.
Qed.

Fixpoint string_compare (a b : string) : comparison :=
  match a with
  | EmptyString =>
      match b with
      | EmptyString => Eq
      | _ => Lt
      end
  | String a_head a_tail =>
      match b with
      | EmptyString => Gt
      | String b_head b_tail =>
          match ascii_compare a_head b_head with
          | Lt => Lt
          | Gt => Gt
          | Eq => string_compare a_tail b_tail
          end
      end
  end.

Lemma string_compare_eq (a b : string):
  string_compare a b = Eq  <->  a = b.
Proof.
generalize b. clear b.
induction a; intro b. { induction b; easy. }
cbn.
destruct b. { easy. }
remember (ascii_compare _ _) as cmp. symmetry in Heqcmp.
destruct cmp; split; try discriminate;
  try rewrite ascii_compare_eq in Heqcmp; try subst;
  try rewrite IHa; intro H.
{ now subst. }
{ now inversion H. }
{ inversion H; subst. rewrite<- Heqcmp. now rewrite ascii_compare_eq. }
{ inversion H; subst. rewrite<- Heqcmp. now rewrite ascii_compare_eq. }
Qed.

Lemma ascii_compare_antisym (a b : ascii):
  ascii_compare a b = CompOpp (ascii_compare b a).
Proof.
unfold ascii_compare.
apply N.compare_antisym.
Qed.

Lemma string_compare_antisym (a b : string):
  string_compare a b = CompOpp (string_compare b a).
Proof.
generalize b. clear b.
induction a. { destruct b; easy. }
intro b. destruct b. { easy. }
cbn. rewrite IHa. clear IHa.
remember (ascii_compare _ _) as cmp. symmetry in Heqcmp.
destruct cmp; rewrite ascii_compare_antisym in Heqcmp; destruct ascii_compare; cbn in *; easy.
Qed.

Lemma string_compare_lt (a b : string):
  string_compare a b = Lt  <->  String_as_OT.lt a b.
Proof.
generalize b. clear b.
induction a.
{
  destruct b. { easy. }
  cbn. split; trivial. intro. apply String_as_OT.lts_empty.
}
intro b. cbn. destruct b. { easy. }
remember (ascii_compare _ _) as cmp. symmetry in Heqcmp.
destruct cmp; split; intro H; try discriminate; trivial.
{
  rewrite ascii_compare_eq in Heqcmp. subst.
  apply String_as_OT.lts_tail.
  apply IHa.
  assumption.
}
{
  rewrite ascii_compare_eq in Heqcmp. subst.
  inversion H; subst. { rewrite IHa. assumption. }
  apply Nat.lt_irrefl in H1. contradiction.
}
{
  apply String_as_OT.lts_head.
  rewrite<- ascii_compare_lt.
  assumption.
}
{
  exfalso. inversion H; subst.
  {
     assert(X: ascii_compare a1 a1 = Eq). { apply ascii_compare_eq. trivial. }
     rewrite Heqcmp in X. discriminate.
  }
  rewrite<- ascii_compare_lt in *. rewrite Heqcmp in *. discriminate.
}
Qed.

Module StringLexicalOrder <: UsualOrderedType.
  Definition t := string.

  Definition eq := @eq string.
  Definition lt (a b : t) := string_compare a b = Lt.

  Lemma compare_helper_eq {a b : string} (G: string_compare a b = Eq):
    a = b.
  Proof.
    now apply string_compare_eq.
  Qed.

  Lemma compare_helper_gt {a b : string} (G: string_compare a b = Gt):
    string_compare b a = Lt.
  Proof.
    rewrite string_compare_antisym. rewrite G. trivial.
  Qed.

  Definition compare (a b : string) : OrderedType.Compare lt eq a b :=
    match string_compare a b as z return _ = z -> _ with
    | Lt => fun E => OrderedType.LT E
    | Gt => fun E => OrderedType.GT (compare_helper_gt E)
    | Eq => fun E => OrderedType.EQ (compare_helper_eq E)
    end eq_refl.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Lemma lt_trans (a b c : string) (AB : lt a b) (BC : lt b c):
    lt a c.
  Proof.
    unfold lt in *. rewrite string_compare_lt in *.
    apply (String_as_OT.lt_trans a b c AB BC).
  Qed.

  Lemma lt_not_eq (a b : string) (H : lt a b):
    ~ eq a b.
  Proof.
    unfold lt in *. unfold eq. rewrite<- string_compare_eq.
    rewrite H. discriminate.
  Qed.

  Definition eq_dec := string_dec.
End StringLexicalOrder.