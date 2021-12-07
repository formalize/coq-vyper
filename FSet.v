From Coq Require Import Bool Setoid List NArith ZArith.
From Coq Require ListSet.
From Coq Require Import FSets.FSetAVL FSetFacts.
From Coq Require String HexString.

Require Import ListSet2 StringCmp.

(** A finite set class.
    These axioms require convertibility to lists.
    (see theories/Lists/ListSet.v from a Coq distribution).
    See theories/MSet/MSetInterface.v for a module-based interface.
 *)
Class class {M: Type} (E: forall x y: M, {x = y} + {x <> y}) (S: Type) := {
  (** Convert a set to a list. The order may be arbitrary. *)
  to_list: S -> list M;
  (** A list produced by set_to_list may only include each element once. *)
  to_list_nodup (s: S): NoDup (to_list s);
  (** Build a set from a list. The list may contain duplicates. *)
  from_list: list M -> S;

  (** Membership test. *) 
  has: S -> M -> bool;

  (** [has] may be computed from [to_list]. *) 
  has_to_list (x: M) (s: S):
    has s x = ListSet.set_mem E x (to_list s);

  (** A set obtained from [from_list] has the same members as the list. *)
  has_from_list (x: M) (l: list M):
    has (from_list l) x = ListSet.set_mem E x l;

  (** An empty set. Could work faster than [from_list nil].
      Note that there may be different empty sets even though they are all equivalent.
      In particular, it might happen that that [empty <> from_list nil].
   *)
  empty: S;
  empty_to_list: to_list empty = nil;

  (** A set with a single element. Could work faster than [set_from_list (x :: nil)]. *)
  singleton: M -> S;
  singleton_to_list (x: M): to_list (singleton x) = x :: nil;

  (** The number of elements in a set. Could work faster than [length (set_to_list s)]. *)
  size_nat: S -> nat;
  size_nat_to_list (s: S): size_nat s = length (to_list s); 

  (** A test for empty set. Could work faster than [set_size_nat =? 0]. *)
  is_empty: S -> bool;
  is_empty_to_list (s: S): is_empty s = true <-> to_list s = nil;

  (** The number of elements in a set, the version with N.
      Could work faster than [N_of_nat (set_size_nat _)].
   *)
  size: S -> N;
  size_ok (s: S): size s = N_of_nat (size_nat s);

  (** Add an item to a set. *)
  add: S -> M -> S;
  add_ok (s: S) (x: M) (y: M):
    has (add s x) y = if E x y then true else has s y;

  (** Remove an item from a set. *)
  remove: S -> M -> S;
  remove_ok (s: S) (x: M) (y: M):
    has (remove s x) y = if E x y then false else has s y;

  union: S -> S -> S;
  union_ok (a b: S): 
    forall x: M,
      has (union a b) x
       =
      orb (has a x) (has b x);
  inter: S -> S -> S;
  inter_ok (a b: S): 
    forall x: M,
      has (inter a b) x
       =
      andb (has a x) (has b x);
  diff: S -> S -> S;
  diff_ok (a b: S): 
    forall x: M,
      has (diff a b) x
       =
      andb (has a x) (negb (has b x));

  for_all: S -> (M -> bool) -> bool;
  for_all_ok (s: S) (p: M -> bool):
    for_all s p = true
     <->
    forall x: M,
      has s x = true -> p x = true;

  (** A test for being a subset. *)
  is_subset: S -> S -> bool;
  is_subset_ok (little big: S):
    is_subset little big = true 
     <->
    forall x: M,
      orb (negb (has little x)) (has big x) = true;

  (** A test for set equality.
      Note that two set_eq sets may not be equal in the sense of Coq's equality,
      for example: when lists are used as sets, [0, 1] and [1, 0] are set_eq but not eq.
    *)
  equal: S -> S -> bool;
  equal_ok (a b: S):
    equal a b = true 
     <->
    forall x: M,
      has a x = has b x;
}.

Definition lists_as_sets {M: Type} (E: forall x y: M, {x = y} + {x <> y})
: class E {l: list M | NoDup l}
:= {|
      to_list s := proj1_sig s;
      to_list_nodup s := proj2_sig s;
      from_list (l: list M) := exist _ (nodup E l) (NoDup_nodup E l);
      has s x := nodup_list_in E x s;
      has_to_list x l := eq_refl;
      has_from_list := set_mem_nodup E;
      empty := exist _ nil (NoDup_nil M);
      empty_to_list := eq_refl;
      singleton (x: M) := exist _ (x :: nil) (NoDup_cons x (@in_nil _ x) (NoDup_nil M));
      singleton_to_list (x: M) := eq_refl;
      size_nat s := length (proj1_sig s);
      size_nat_to_list s := eq_refl;
      is_empty s := list_is_empty (proj1_sig s);
      is_empty_to_list s := list_is_empty_ok (proj1_sig s);
      size s := N.of_nat (length (proj1_sig s));
      size_ok s := eq_refl;
      add s x := nodup_list_add E x s;
      add_ok s x := nodup_list_add_ok E x s;
      remove s x := nodup_list_remove E x s;
      remove_ok s x := nodup_list_remove_ok E x s;
      union := nodup_list_union E;
      union_ok := nodup_list_union_ok E;
      inter := nodup_list_inter E;
      inter_ok := nodup_list_inter_ok E;
      diff := nodup_list_diff E;
      diff_ok := nodup_list_diff_ok E;
      for_all := nodup_list_forall;
      for_all_ok := nodup_list_forall_ok E;
      is_subset := nodup_list_subset E;
      is_subset_ok := nodup_list_subset_ok E;
      equal := nodup_list_set_eq E;
      equal_ok := nodup_list_set_eq_ok E;
   |}.

(****************************************************************************************)

(* A set of strings based on FSetAVL. *)

Module StringAVLSet := FSetAVL.Make StringLexicalOrder.
Definition string_avl_set := StringAVLSet.t.

Lemma ina_in {A} (l: list A) (x: A):
  SetoidList.InA eq x l <-> In x l.
Proof.
induction l; split; intro H; inversion H; subst; clear H; cbn; try tauto.
{ now constructor. }
rewrite<- IHl in *.
now apply SetoidList.InA_cons_tl.
Qed.

Lemma nodupa_nodup {A} (l: list A):
  SetoidList.NoDupA eq l <-> NoDup l.
Proof.
induction l; split; intro H; inversion H; subst; clear H; cbn; try tauto; constructor.
{ rewrite<- ina_in. assumption. }
{ tauto. }
{ rewrite ina_in. assumption. }
{ tauto. }
Qed.

Lemma string_avl_set_to_list_nodup (s: string_avl_set):
  NoDup (StringAVLSet.elements s).
Proof.
rewrite<- nodupa_nodup.
apply StringAVLSet.elements_3w.
Qed.

Lemma string_avl_set_in_to_list x l:
  StringAVLSet.mem x l = ListSet.set_mem String.string_dec x (StringAVLSet.elements l).
Proof.
remember (StringAVLSet.mem x l) as m. destruct m; symmetry in Heqm; symmetry.
{
  rewrite set_mem_true. rewrite<- ina_in. 
  apply StringAVLSet.elements_1.
  now apply StringAVLSet.mem_2.
}
rewrite set_mem_false. rewrite<- ina_in. 
intro H. apply StringAVLSet.elements_2 in H.
apply StringAVLSet.mem_1 in H.
rewrite Heqm in H. discriminate.
Qed.

Lemma string_avl_set_in_from_list x l:
  StringAVLSet.mem x
    (fold_right StringAVLSet.add StringAVLSet.empty l) 
   =
  ListSet.set_mem String.string_dec x l.
Proof.
induction l. { trivial. }
remember (ListSet.set_mem _ _ _) as m.
symmetry in Heqm. destruct m.
{
  apply StringAVLSet.mem_2 in IHl.
  apply set_mem_true in Heqm.
  assert (T: ListSet.set_mem String.string_dec x (a :: l) = true).
  {
    rewrite set_mem_true.
    cbn. now right.
  }
  rewrite T. clear T.
  apply StringAVLSet.mem_1.
  cbn.
  now apply StringAVLSet.add_2.
}
rewrite set_mem_false in Heqm.
match goal with
|- ?lhs = ?rhs => remember lhs as p
end.
cbn.
destruct String.string_dec as [EQ|NE].
{ subst. apply StringAVLSet.mem_1. now apply StringAVLSet.add_1. }
assert (F: p = false).
{
  destruct p; trivial.
  symmetry in Heqp.
  apply StringAVLSet.mem_2 in Heqp.
  cbn in Heqp.
  apply StringAVLSet.add_3 in Heqp.
  {
    apply StringAVLSet.mem_1 in Heqp.
    rewrite<- Heqp. rewrite<- IHl. trivial.
  }
  intro H.
  symmetry in H.
  contradiction.
}
rewrite F. symmetry. now apply set_mem_false.
Qed.

Lemma string_avl_set_empty_to_list s:
  StringAVLSet.is_empty s = true <-> StringAVLSet.elements s = nil.
Proof.
split; intro H.
{
  apply StringAVLSet.is_empty_2 in H.
  unfold StringAVLSet.Empty in H.
  remember (StringAVLSet.elements s) as e.
  destruct e as [| h ]. { trivial. }
  assert (Q: StringAVLSet.In h s).
  {
    apply StringAVLSet.elements_2.
    rewrite ina_in.
    rewrite<- Heqe.
    now constructor.
  }
  exfalso. exact (H h Q).
}
apply StringAVLSet.is_empty_1.
unfold StringAVLSet.Empty.
intros x J. apply StringAVLSet.elements_1 in J. rewrite ina_in in J.
rewrite H in J. cbn in J. exact J.
Qed.

Lemma string_avl_set_add_ok x s y:
  StringAVLSet.mem y (StringAVLSet.add x s)
   =
  if String.string_dec x y then true else StringAVLSet.mem y s.
Proof.
destruct (String.string_dec x y) as [EQ|NE].
{
  apply StringAVLSet.mem_1.
  apply StringAVLSet.add_1.
  assumption.
}
remember (StringAVLSet.mem y s) as y_in.
symmetry in Heqy_in.
destruct y_in.
{
  apply StringAVLSet.mem_2 in Heqy_in.
  apply StringAVLSet.mem_1.
  apply StringAVLSet.add_2.
  assumption.
}
remember (StringAVLSet.mem y (StringAVLSet.add x s)) as f.
symmetry in Heqf. destruct f; trivial.
apply StringAVLSet.mem_2 in Heqf.
assert (J := StringAVLSet.add_3 NE Heqf).
apply StringAVLSet.mem_1 in J.
rewrite<- Heqy_in. rewrite<- J.
trivial.
Qed.

Lemma string_avl_set_remove_ok x s y:
  StringAVLSet.mem y (StringAVLSet.remove x s) 
   =
  if String.string_dec x y then false else StringAVLSet.mem y s.
Proof.
destruct (String.string_dec x y) as [EQ|NE].
{
  remember (StringAVLSet.mem y _) as f. symmetry in Heqf. destruct f; trivial.
  apply StringAVLSet.mem_2 in Heqf.
  apply (StringAVLSet.remove_1 EQ) in Heqf.
  contradiction.
}
remember (StringAVLSet.mem y s) as y_in.
symmetry in Heqy_in.
destruct y_in.
{
  apply StringAVLSet.mem_2 in Heqy_in.
  apply StringAVLSet.mem_1.
  exact (StringAVLSet.remove_2 NE Heqy_in).
}
remember (StringAVLSet.mem y (StringAVLSet.remove x s)) as f.
symmetry in Heqf. destruct f; trivial.
apply StringAVLSet.mem_2 in Heqf.
assert (J := StringAVLSet.remove_3 Heqf).
apply StringAVLSet.mem_1 in J.
rewrite<- Heqy_in. rewrite<- J.
trivial.
Qed.

Lemma string_avl_set_union_ok a b x:
  StringAVLSet.mem x (StringAVLSet.union a b) = StringAVLSet.mem x a || StringAVLSet.mem x b.
Proof.
remember (StringAVLSet.mem x (StringAVLSet.union a b)) as in_ab.
remember (StringAVLSet.mem x a) as in_a.
remember (StringAVLSet.mem x b) as in_b.
symmetry in Heqin_ab. symmetry in Heqin_a. symmetry in Heqin_b.
destruct in_ab; destruct in_a; destruct in_b; cbn; trivial; exfalso;
  try apply StringAVLSet.mem_2 in Heqin_ab;
  try apply StringAVLSet.mem_2 in Heqin_a;
  try apply StringAVLSet.mem_2 in Heqin_b.
{
  apply StringAVLSet.union_1 in Heqin_ab.
  case Heqin_ab; intro H; apply StringAVLSet.mem_1 in H; rewrite H in *; easy.
}
{ now rewrite (StringAVLSet.mem_1 (StringAVLSet.union_2 b Heqin_a)) in Heqin_ab. }
{ now rewrite (StringAVLSet.mem_1 (StringAVLSet.union_2 b Heqin_a)) in Heqin_ab. }
now rewrite (StringAVLSet.mem_1 (StringAVLSet.union_3 a Heqin_b)) in Heqin_ab.
Qed.

Lemma string_avl_set_inter_ok a b x:
  StringAVLSet.mem x (StringAVLSet.inter a b) = StringAVLSet.mem x a && StringAVLSet.mem x b.
Proof.
remember (StringAVLSet.mem x (StringAVLSet.inter a b)) as in_ab.
remember (StringAVLSet.mem x a) as in_a.
remember (StringAVLSet.mem x b) as in_b.
symmetry in Heqin_ab. symmetry in Heqin_a. symmetry in Heqin_b.
destruct in_ab; destruct in_a; destruct in_b; cbn; trivial; exfalso;
  try apply StringAVLSet.mem_2 in Heqin_ab;
  try apply StringAVLSet.mem_2 in Heqin_a;
  try apply StringAVLSet.mem_2 in Heqin_b.
{
  apply StringAVLSet.inter_2 in Heqin_ab.
  apply StringAVLSet.mem_1 in Heqin_ab.
  rewrite Heqin_ab in Heqin_b. discriminate.
}
{
  apply StringAVLSet.inter_1 in Heqin_ab.
  apply StringAVLSet.mem_1 in Heqin_ab.
  rewrite Heqin_ab in Heqin_a. discriminate.
}
{
  apply StringAVLSet.inter_1 in Heqin_ab.
  apply StringAVLSet.mem_1 in Heqin_ab.
  rewrite Heqin_ab in Heqin_a. discriminate.
}
now rewrite (StringAVLSet.mem_1 (StringAVLSet.inter_3 Heqin_a Heqin_b)) in Heqin_ab.
Qed.

Lemma string_avl_set_diff_ok a b x:
  StringAVLSet.mem x (StringAVLSet.diff a b) = StringAVLSet.mem x a && negb (StringAVLSet.mem x b).
Proof.
remember (StringAVLSet.mem x (StringAVLSet.diff a b)) as in_ab.
remember (StringAVLSet.mem x a) as in_a.
remember (StringAVLSet.mem x b) as in_b.
symmetry in Heqin_ab. symmetry in Heqin_a. symmetry in Heqin_b.
destruct in_ab; destruct in_a; destruct in_b; cbn; trivial;
  try apply StringAVLSet.mem_2 in Heqin_ab;
  try apply StringAVLSet.mem_2 in Heqin_a;
  try apply StringAVLSet.mem_2 in Heqin_b.
{ now apply StringAVLSet.diff_2 in Heqin_ab. }
{
  apply StringAVLSet.diff_1 in Heqin_ab.
  apply StringAVLSet.mem_1 in Heqin_ab.
  rewrite Heqin_ab in Heqin_a. discriminate.
}
{
  apply StringAVLSet.diff_1 in Heqin_ab.
  apply StringAVLSet.mem_1 in Heqin_ab.
  rewrite Heqin_ab in Heqin_a. discriminate.
}
apply StringAVLSet.diff_3 with (s' := b) in Heqin_a.
{
  apply StringAVLSet.mem_1 in Heqin_a.
  rewrite Heqin_ab in Heqin_a. discriminate.
}
intro H. apply StringAVLSet.mem_1 in H.
rewrite H in Heqin_b. discriminate.
Qed.

Lemma string_avl_set_forall_ok s (p: String.string -> bool):
  StringAVLSet.for_all p s = true 
   <->
  forall x,
    StringAVLSet.mem x s = true -> p x = true.
Proof.
split; intro H.
{
  apply StringAVLSet.for_all_2 in H.
  {
    intros x XIn.
    unfold StringAVLSet.For_all in H.
    apply StringAVLSet.mem_2 in XIn.
    exact (H x XIn).
  }
  intros x y E. now subst.
}
apply StringAVLSet.for_all_1.
{ intros x y E. now subst. }
intros x XIn.
apply H.
now apply StringAVLSet.mem_1.
Qed.

Lemma string_avl_set_subset_ok a b:
 StringAVLSet.subset a b = true 
  <->
 forall x,
   negb (StringAVLSet.mem x a) || StringAVLSet.mem x b = true.
Proof.
split; intro H.
{
  apply StringAVLSet.subset_2 in H.
  unfold StringAVLSet.Subset in H.
  intro x.
  remember (StringAVLSet.mem x a) as in_a.
  remember (StringAVLSet.mem x b) as in_b.
  symmetry in Heqin_a. symmetry in Heqin_b.
  destruct in_a; destruct in_b; cbn; trivial;
    try apply StringAVLSet.mem_2 in Heqin_a;
    try apply StringAVLSet.mem_2 in Heqin_b.
  now rewrite (StringAVLSet.mem_1 (H _ Heqin_a)) in Heqin_b.
}
apply StringAVLSet.subset_1.
intros x InA.
apply StringAVLSet.mem_1 in InA.
apply StringAVLSet.mem_2.
assert (Q := H x).
rewrite InA in Q.
remember (StringAVLSet.mem x b) as in_b.
symmetry in Heqin_b. destruct in_b; trivial.
Qed.

Lemma string_avl_set_eq_ok a b:
  StringAVLSet.equal a b = true 
   <->
  forall x,
    StringAVLSet.mem x a = StringAVLSet.mem x b.
Proof.
split; intro H.
{
  intro x.
  apply StringAVLSet.equal_2 in H.
  unfold StringAVLSet.Equal in H.
  remember (StringAVLSet.mem x a) as in_a.
  remember (StringAVLSet.mem x b) as in_b.
  symmetry. symmetry in Heqin_a. symmetry in Heqin_b.
  destruct in_a; destruct in_b; cbn; trivial;
    try apply StringAVLSet.mem_2 in Heqin_a;
    try apply StringAVLSet.mem_2 in Heqin_b;
    try discriminate.
  { 
    rewrite (H x) in Heqin_a;
    rewrite (StringAVLSet.mem_1 Heqin_a) in Heqin_b.
    discriminate.
  }
  rewrite<- (H x) in Heqin_b.
  rewrite (StringAVLSet.mem_1 Heqin_b) in Heqin_a.
  discriminate.
}
apply StringAVLSet.equal_1.
unfold StringAVLSet.Equal.
intro x.
remember (StringAVLSet.mem x a) as in_a.
remember (StringAVLSet.mem x b) as in_b.
symmetry. symmetry in Heqin_a. symmetry in Heqin_b.
destruct in_a; destruct in_b; cbn; trivial;
  try (rewrite (H x) in Heqin_a; rewrite Heqin_a in Heqin_b; discriminate);
  try apply StringAVLSet.mem_2 in Heqin_a;
  try apply StringAVLSet.mem_2 in Heqin_b;
  try tauto.
split; intro Z; apply StringAVLSet.mem_1 in Z; rewrite Z in *; discriminate.
Qed.

(* 8.14: #[export] *)
Instance string_avl_set_impl: class String.string_dec string_avl_set
:= {|
      to_list := StringAVLSet.elements;
      to_list_nodup := string_avl_set_to_list_nodup;
      from_list l := fold_right StringAVLSet.add StringAVLSet.empty l;
      has s x := StringAVLSet.mem x s;
      has_to_list := string_avl_set_in_to_list;
      has_from_list := string_avl_set_in_from_list;
      empty := StringAVLSet.empty;
      empty_to_list := eq_refl;
      singleton := StringAVLSet.singleton;
      singleton_to_list s := eq_refl;
      size_nat := StringAVLSet.cardinal;
      size_nat_to_list := StringAVLSet.cardinal_1;
      is_empty := StringAVLSet.is_empty;
      is_empty_to_list := string_avl_set_empty_to_list;
      size s := N.of_nat (StringAVLSet.cardinal s);
      size_ok s := eq_refl;
      add s x := StringAVLSet.add x s;
      add_ok s x := string_avl_set_add_ok x s;
      remove s x := StringAVLSet.remove x s;
      remove_ok s x := string_avl_set_remove_ok x s;
      union := StringAVLSet.union;
      union_ok := string_avl_set_union_ok;
      inter := StringAVLSet.inter;
      inter_ok := string_avl_set_inter_ok;
      diff := StringAVLSet.diff;
      diff_ok := string_avl_set_diff_ok;
      for_all s p := StringAVLSet.for_all p s;
      for_all_ok := string_avl_set_forall_ok;
      is_subset := StringAVLSet.subset;
      is_subset_ok := string_avl_set_subset_ok;
      equal := StringAVLSet.equal;
      equal_ok := string_avl_set_eq_ok;
   |}.

(****************************************************************************************)


Section SetFacts.

Context {M: Type} {E: forall x y: M, {x = y} + {x <> y}} {S: Type} {C: class E S}.

Lemma empty_ok (x: M):
  has empty x = false.
Proof.
rewrite has_to_list.
rewrite empty_to_list; auto.
Qed.

Lemma singleton_ok (x y: M):
  has (singleton x) y = true <-> x = y.
Proof.
rewrite has_to_list.
rewrite singleton_to_list.
cbn.
destruct E as [EQ|NE]. { symmetry in EQ. tauto. }
split; intro H. { congruence. }
symmetry in H. contradiction.
Qed.

Lemma singleton_iff (x y: M):
  has (singleton x) y = if E x y then true else false.
Proof.
  destruct E. { rewrite singleton_ok. exact e. }
  remember (has _ _) as h. symmetry in Heqh. destruct h.
  { now rewrite singleton_ok in Heqh. }
  trivial.
Qed.

Lemma is_empty_true (a: S) (H: is_empty a = true) (x: M):
  has a x = false.
Proof.
rewrite has_to_list. rewrite is_empty_to_list in H. 
rewrite H. trivial.
Qed.

Lemma is_empty_true_iff (a: S):
  is_empty a = true  <->  forall x, has a x = false.
Proof.
split. { apply is_empty_true. }
intro H.
rewrite is_empty_to_list.
remember (to_list a) as l.
destruct l as [|h]. { trivial. }
assert (Hh := H h).
rewrite has_to_list in Hh.
rewrite<- Heql in Hh.
cbn in Hh.
now destruct (E h h).
Qed.

Lemma is_empty_false (a: S) (H: is_empty a = false):
  exists x: M,
    has a x = true.
Proof.
remember (to_list a) as l.
destruct l.
{
  symmetry in Heql. rewrite<- is_empty_to_list in Heql. 
  rewrite Heql in H. congruence.
}
exists m.
rewrite has_to_list.
rewrite<- Heql.
cbn. now destruct E.
Qed.

Lemma add_has (x: M) (s: S):
  has (add s x) x = true.
Proof.
rewrite add_ok. now destruct E.
Qed.

Lemma is_subset_refl (a: S):
  is_subset a a = true.
Proof.
rewrite is_subset_ok. intro x.
bool. destruct has; tauto.
Qed.

Lemma is_subset_equal (a b: S) (Eq: equal a b = true):
  is_subset a b = true.
Proof.
rewrite is_subset_ok. rewrite equal_ok in Eq. intro x.
rewrite (Eq x).
destruct has; tauto.
Qed.

Lemma is_subset_trans {a b c: S}
                      (AB: is_subset a b = true)
                      (BC: is_subset b c = true):
  is_subset a c = true.
Proof.
rewrite is_subset_ok in *. intro x.
assert (ABx := AB x).
assert (BCx := BC x).
bool.
destruct has; destruct has; destruct has; tauto.
Qed.

Lemma is_subset_antisym {a b: S}
                        (AB: is_subset a b = true)
                        (BC: is_subset b a = true):
  equal a b = true.
Proof. 
rewrite is_subset_ok in AB.
rewrite is_subset_ok in BC.
rewrite equal_ok. intro x.
assert (ABx := AB x).
assert (BCx := BC x).
bool.
destruct has; destruct has; trivial; case ABx; case BCx; try tauto; 
  intros; try tauto; symmetry; tauto.
Qed.

Lemma is_subset_if {a b: S}
                   (AB: is_subset a b = true)
                   (x: M)
                   (H: has a x = true):
  has b x = true.
Proof.
assert (Ok := proj1 (is_subset_ok a b) AB x).
rewrite H in Ok. apply Ok.
Qed.

Lemma empty_subset {a: S}:
  is_subset empty a = true.
Proof.
rewrite is_subset_ok.
intro x.
now rewrite empty_ok.
Qed.

Lemma add_subset (x: M) (s: S):
  is_subset s (add s x) = true.
Proof.
rewrite is_subset_ok. intro y.
rewrite add_ok. bool. destruct (E x y); try tauto.
destruct has; tauto.
Qed.

Lemma union_subset_l (a b: S):
  is_subset a (union a b) = true.
Proof.
rewrite is_subset_ok. intro x.
rewrite union_ok.
destruct has; now destruct has.
Qed.

Lemma union_subset_r (a b: S):
  is_subset b (union a b) = true.
Proof.
rewrite is_subset_ok. intro x.
rewrite union_ok.
destruct has; now destruct has.
Qed.

Lemma union_subset_and (a b c: S):
  is_subset (union a b) c = is_subset a c && is_subset b c.
Proof.
remember (is_subset a c) as ac. symmetry in Heqac.
remember (is_subset b c) as bc. symmetry in Heqbc.
destruct ac.
{ (* ac = true *)
  rewrite is_subset_ok in Heqac.
  rewrite andb_true_l.
  destruct bc.
  { (* bc = true *)
    rewrite is_subset_ok in Heqbc.
    rewrite is_subset_ok.
    intro x. assert (ACx := Heqac x). assert (BCx := Heqbc x).
    rewrite union_ok.
    destruct has; now destruct has.
  }
  (* bc = false *)
  remember (is_subset (union a b) c) as f. symmetry in Heqf.
  destruct f. 2:trivial.
  rewrite is_subset_ok in Heqf.
  enough (is_subset b c = true). { rewrite Heqbc in *. symmetry. assumption. }
  rewrite is_subset_ok.
  intro x. assert (ACx := Heqac x). assert (Fx := Heqf x).
  rewrite union_ok in Fx.
  destruct has; destruct has; 
    try rewrite orb_true_r in *; 
    try rewrite orb_false_r in *; trivial.
  discriminate.
}
(* ac = false *)
rewrite andb_false_l.
remember (is_subset (union a b) c) as f. symmetry in Heqf.
destruct f. 2:trivial.
rewrite is_subset_ok in Heqf.
enough (is_subset a c = true). { rewrite Heqac in *. symmetry. assumption. }
rewrite is_subset_ok.
intro x. assert (Fx := Heqf x).
rewrite union_ok in Fx.
destruct has; destruct has;
  try rewrite orb_true_r in *;
  try repeat rewrite orb_false_r in *; trivial.
Qed.

Lemma add_subset_and (a b: S) (x: M):
  is_subset (add a x) b = is_subset a b && has b x.
Proof.
remember (is_subset a b) as ab. symmetry in Heqab.
remember (has b x) as bx. symmetry in Heqbx.
destruct ab.
{
  rewrite is_subset_ok in Heqab.
  rewrite andb_true_l.
  destruct bx.
  { (* bx = true *)
    rewrite is_subset_ok.
    intro y. assert (ABy := Heqab y).
    rewrite add_ok.
    destruct E; now subst.
  }
  remember (is_subset (add a x) b) as f. symmetry in Heqf.
  destruct f. 2:trivial.
  rewrite is_subset_ok in Heqf.
  assert (ABx := Heqab x). assert (Fx := Heqf x).
  destruct has; destruct has; 
    try rewrite orb_true_r in *; 
    try rewrite orb_false_r in *; trivial.
  { cbn in ABx. discriminate. }
  rewrite add_has in Fx. cbn in Fx. discriminate.
}
remember (is_subset (add a x) b) as f. symmetry in Heqf.
destruct f. 2:trivial.
enough (AB: is_subset a b = true) by (rewrite Heqab in AB; discriminate).
clear Heqab.
rewrite is_subset_ok in Heqf. rewrite is_subset_ok.
intro y. assert (Fy := Heqf y). clear Heqf.
rewrite add_ok in Fy.
clear bx Heqbx.
destruct E.
{ cbn in Fy. rewrite Fy. apply orb_true_r. }
exact Fy.
Qed.

Lemma inter_subset_l (a b: S):
  is_subset (inter a b) a = true.
Proof.
rewrite is_subset_ok. intro x.
rewrite inter_ok.
destruct has; now destruct has.
Qed.

Lemma inter_subset_r (a b: S):
  is_subset (inter a b) b = true.
Proof.
rewrite is_subset_ok. intro x.
rewrite inter_ok.
destruct has; now destruct has.
Qed.

Lemma union_monotonic_l (a b c: S)
                        (H: is_subset a b = true):
  is_subset (union a c) (union b c) = true.
Proof.
rewrite is_subset_ok in *. intro x.
repeat rewrite union_ok.
assert (Hx := H x). clear H.
destruct (has a x); destruct (has b x); destruct (has c x); tauto.
Qed.

Lemma union_monotonic_r (a b c: S)
                        (H: is_subset b c = true):
  is_subset (union a b) (union a c) = true.
Proof.
rewrite is_subset_ok in *. intro x.
repeat rewrite union_ok.
assert (Hx := H x). clear H.
destruct (has a x); destruct (has b x); destruct (has c x); tauto.
Qed.

Lemma union_monotonic (a b c d: S)
                      (AB: is_subset a b = true)
                      (CD: is_subset c d = true):
  is_subset (union a c) (union b d) = true.
Proof.
assert (Q: is_subset (union a c) (union a d) = true) by now apply union_monotonic_r.
apply (is_subset_trans Q).
now apply union_monotonic_l.
Qed.

Lemma inter_monotonic_l (a b c: S)
                        (H: is_subset a b = true):
  is_subset (inter a c) (inter b c) = true.
Proof.
rewrite is_subset_ok in *. intro x.
repeat rewrite inter_ok.
assert (Hx := H x). clear H.
destruct (has a x); destruct (has b x); destruct (has c x); tauto.
Qed.

Lemma inter_monotonic_r (a b c: S)
                        (H: is_subset b c = true):
  is_subset (inter a b) (inter a c) = true.
Proof.
rewrite is_subset_ok in *. intro x.
repeat rewrite inter_ok.
assert (Hx := H x). clear H.
destruct (has a x); destruct (has b x); destruct (has c x); tauto.
Qed.

Lemma inter_monotonic (a b c d: S)
                      (AB: is_subset a b = true)
                      (CD: is_subset c d = true):
  is_subset (inter a c) (inter b d) = true.
Proof.
assert (Q: is_subset (inter a c) (inter a d) = true) by now apply inter_monotonic_r.
apply (is_subset_trans Q).
now apply inter_monotonic_l.
Qed.

End SetFacts.



Section SetUtils.

Context {M: Type} {E: forall x y: M, {x = y} + {x <> y}} {S: Type} {C: class E S}.

Definition filter (s: S) (f: M -> bool) := from_list (List.filter f (to_list s)).

Lemma filter_ok (s: S) (f: M -> bool) (x: M):
  has (filter s f) x = has s x && f x.
Proof.
unfold filter.
rewrite has_from_list.
rewrite has_to_list.
induction to_list. { easy. }
cbn. remember (f a) as fa. destruct fa.
{
  cbn. destruct (E x a). 2:assumption.
  subst. now rewrite<- Heqfa.
}
rewrite IHl. destruct (E x a). 2: trivial.
subst. rewrite<- Heqfa. repeat rewrite Bool.andb_false_r. trivial.
Qed.

End SetUtils.

Section SetInject.

Context {A B: Type}
        (EA: forall x y: A, {x = y} + {x <> y})
        (EB: forall x y: B, {x = y} + {x <> y}) (SB: Type) (CB: class EB SB)
        (inj: A -> B) (uninj: B -> A) (UninjInj: forall x: A, uninj (inj x) = x).

Definition inj_t := { s: SB | forall x, has s x = true -> inj (uninj x) = x }.
Definition SA := inj_t.

Lemma inj_to_list_nodup (s: SA):
  NoDup (map uninj (to_list (proj1_sig s))).
Proof.
assert (P := proj2_sig s). cbn in P.
assert (W: map inj (map uninj (to_list (proj1_sig s))) = to_list (proj1_sig s)).
{
  rewrite map_map.
  assert (Q: forall x : B, ListSet.set_mem EB x (to_list (proj1_sig s)) = true -> inj (uninj x) = x).
  { intros. apply P. now rewrite has_to_list. }
  remember (to_list (proj1_sig s)) as l. clear Heql P.
  induction l. { easy. }
  cbn. cbn in Q. assert (Qa := Q a). destruct (EB a a). 2:{ contradiction. }
  rewrite (Qa eq_refl). f_equal. apply IHl.
  intro b. assert (Qb := Q b). destruct (EB b a).
  { intro. apply (Qb eq_refl). }
  exact Qb.
}
assert (D := to_list_nodup (proj1_sig s)).
rewrite<- W in D.
apply NoDup_map_inv in D. exact D.
Qed.

Lemma inj_from_list_helper (l: list A) (x: B):
  has (from_list (map inj l)) x = true -> inj (uninj x) = x.
Proof.
rewrite has_from_list.
induction l. { easy. }
cbn.
destruct (EB x (inj a)). { subst x. now rewrite UninjInj. }
apply IHl.
Qed.

Lemma inj_has_to_list (x: A) (s: SA):
  has (proj1_sig s) (inj x) = ListSet.set_mem EA x (map uninj (to_list (proj1_sig s))).
Proof.
assert (P := proj2_sig s). cbn in P.
rewrite (has_to_list (inj x) (proj1_sig s)).
assert (Q: forall x : B, ListSet.set_mem EB x (to_list (proj1_sig s)) = true -> inj (uninj x) = x).
{ intros. apply P. now rewrite has_to_list. }
remember (to_list (proj1_sig s)) as l. clear Heql P.
induction l. { easy. }
cbn. destruct (EB (inj x) a).
{ subst a. rewrite UninjInj. now destruct (EA x x). }
destruct (EA x (uninj a)).
{ subst x. assert (Qa := Q a). cbn in Qa. destruct (EB a a); tauto. }
apply IHl. intro b.
assert (Qb := Q b). cbn in Qb. destruct (EB b a); subst; tauto.
Qed.

Lemma inj_has_from_list (x: A) (l: list A):
  has (from_list (map inj l)) (inj x) = ListSet.set_mem EA x l.
Proof.
rewrite has_from_list.
induction l. { easy. }
cbn.
destruct (EA x a) as [EQA|NEA]. { subst x. now destruct EB. }
destruct EB as [EQB|NEB]. 2:apply IHl.
rewrite<- (UninjInj x) in NEA.
rewrite<- (UninjInj a) in NEA.
rewrite EQB in NEA.
contradiction.
Qed.

Lemma inj_empty_helper (x: B):
  has empty x = true -> inj (uninj x) = x.
Proof.
intro H.
rewrite empty_ok in H.
discriminate.
Qed.

Lemma inj_empty_to_list:
  map uninj (to_list empty) = nil.
Proof.
now rewrite empty_to_list.
Qed.

Lemma inj_singleton_helper (x: A) (y: B):
  has (singleton (inj x)) y = true -> inj (uninj y) = y.
Proof.
rewrite singleton_ok. intro. subst y. now rewrite UninjInj.
Qed.

Lemma inj_singleton_to_list (x: A):
  map uninj (to_list (singleton (inj x))) = x :: nil.
cbn.
rewrite singleton_to_list. cbn. now rewrite UninjInj.
Qed.

Lemma inj_size_nat_to_list (s: SA):
  size_nat (proj1_sig s) = length (map uninj (to_list (proj1_sig s))).
Proof.
rewrite size_nat_to_list.
now rewrite map_length.
Qed.

Lemma inj_is_empty_to_list (s: SA):
  is_empty (proj1_sig s) = true <-> map uninj (to_list (proj1_sig s)) = nil.
Proof.
rewrite is_empty_to_list.
now destruct to_list.
Qed.

Lemma inj_size_ok (s: SA):
  size (proj1_sig s) = N.of_nat (size_nat (proj1_sig s)).
Proof.
apply size_ok.
Qed.

Lemma inj_add_helper (s: SA) (x: A) (y: B):
  has (add (proj1_sig s) (inj x)) y = true -> inj (uninj y) = y.
Proof.
assert (P := proj2_sig s). cbn in P.
rewrite add_ok. destruct EB.
{ subst y. now rewrite UninjInj. }
apply P.
Qed.

Lemma inj_add_ok (s: SA) (x y : A):
  has (add (proj1_sig s) (inj x)) (inj y) = (if EA x y then true else has (proj1_sig s) (inj y)).
Proof.
rewrite add_ok.
destruct EA as [EQA|NEA], EB as [EQB|NEB]; subst; try easy.
(* NEA, EQB *)
rewrite<- (UninjInj x) in NEA.
rewrite<- (UninjInj y) in NEA.
rewrite EQB in NEA.
contradiction.
Qed.

Lemma inj_remove_helper (s: SA) (x: A) (y: B):
  has (remove (proj1_sig s) (inj x)) y = true -> inj (uninj y) = y.
Proof.
assert (P := proj2_sig s). cbn in P.
rewrite remove_ok. destruct EB. { easy. }
apply P.
Qed.

Lemma inj_remove_ok (s: SA) (x y : A):
  has (remove (proj1_sig s) (inj x)) (inj y) = (if EA x y then false else has (proj1_sig s) (inj y)).
Proof.
rewrite remove_ok.
destruct EA as [EQA|NEA], EB as [EQB|NEB]; subst; try easy.
(* NEA, EQB *)
rewrite<- (UninjInj x) in NEA.
rewrite<- (UninjInj y) in NEA.
rewrite EQB in NEA.
contradiction.
Qed.

Lemma inj_union_helper (s1 s2: SA) (x: B):
  has (union (proj1_sig s1) (proj1_sig s2)) x = true -> inj (uninj x) = x.
Proof.
assert (P := proj2_sig s1). cbn in P.
assert (Q := proj2_sig s2). cbn in Q.
rewrite union_ok. intro H. apply Bool.orb_prop in H.
case H; clear H; intro H; [apply P | apply Q]; exact H.
Qed.

Lemma inj_union_ok (a b: SA) (x: A):
  has (union (proj1_sig a) (proj1_sig b)) (inj x) = has (proj1_sig a) (inj x) || has (proj1_sig b) (inj x).
Proof.
now rewrite union_ok.
Qed.

Lemma inj_inter_helper (s1 s2: SA) (x: B):
  has (inter (proj1_sig s1) (proj1_sig s2)) x = true -> inj (uninj x) = x.
Proof.
assert (P := proj2_sig s1). cbn in P.
rewrite inter_ok. intro H. apply andb_prop in H.
exact (P x (proj1 H)).
Qed.

Lemma inj_inter_ok (a b: SA) (x: A):
  has (inter (proj1_sig a) (proj1_sig b)) (inj x) = has (proj1_sig a) (inj x) && has (proj1_sig b) (inj x).
Proof.
now rewrite inter_ok.
Qed.

Lemma inj_diff_helper (s1 s2: SA) (x: B):
  has (diff (proj1_sig s1) (proj1_sig s2)) x = true -> inj (uninj x) = x.
Proof.
assert (P := proj2_sig s1). cbn in P.
rewrite diff_ok. intro H. apply andb_prop in H.
exact (P x (proj1 H)).
Qed.

Lemma inj_diff_ok (a b: SA) (x: A):
  has (diff (proj1_sig a) (proj1_sig b)) (inj x) = has (proj1_sig a) (inj x) && negb (has (proj1_sig b) (inj x)).
Proof.
now rewrite diff_ok.
Qed.

Lemma inj_for_all_ok (s : SA) (p : A -> bool):
  for_all (proj1_sig s) (fun x : B => p (uninj x)) = true 
   <->
  (forall x : A, has (proj1_sig s) (inj x) = true -> p x = true).
Proof.
rewrite for_all_ok.
split.
{
  intros H x T.
  rewrite<- (UninjInj x).
  apply (H (inj x) T).
}
intros H x T.
apply (H (uninj x)).
rewrite (proj2_sig s x T). exact T.
Qed.

Lemma inj_subset_ok (little big: SA):
  is_subset (proj1_sig little) (proj1_sig big) = true
   <->
  (forall x : A, negb (has (proj1_sig little) (inj x)) || has (proj1_sig big) (inj x) = true).
Proof.
rewrite is_subset_ok.
split.
{ intros H x. apply (H (inj x)). }
intros H x.
assert (P := proj2_sig little x).
assert (W := H (uninj x)).
match goal with
|- ?l = ?r => remember l as lhs; destruct lhs; trivial
end.
symmetry in Heqlhs. apply orb_false_elim in Heqlhs.
destruct Heqlhs as (InLittle, NotInBig).
apply negb_false_iff in InLittle.
rewrite (P InLittle) in W.
rewrite InLittle in W. rewrite NotInBig in W. apply W.
Qed.

Lemma inj_equal_ok (a b: SA):
  equal (proj1_sig a) (proj1_sig b) = true 
   <->
  (forall x : A, has (proj1_sig a) (inj x) = has (proj1_sig b) (inj x)).
Proof.
rewrite equal_ok.
split.
{ intros H x. apply (H (inj x)). }
intros H x.
assert (P := proj2_sig a x).
assert (Q := proj2_sig b x).
assert (W := H (uninj x)).
match goal with
|- ?l = ?r => remember l as lhs; remember r as rhs;
              symmetry in Heqlhs; symmetry in Heqrhs;
              destruct lhs, rhs
end; try easy;
  try rewrite (P eq_refl) in W;
  try rewrite (Q eq_refl) in W;
  rewrite Heqlhs in W;
  rewrite Heqrhs in W;
  apply W.
Qed.


Definition inj_impl: class EA SA
:= {| to_list s := map uninj (to_list (proj1_sig s))
    ; to_list_nodup := inj_to_list_nodup
    ; from_list l := exist _ (from_list (map inj l)) (inj_from_list_helper l)
    ; has s x := has (proj1_sig s) (inj x)
    ; has_to_list := inj_has_to_list
    ; has_from_list := inj_has_from_list
    ; empty := exist _ empty inj_empty_helper
    ; empty_to_list := inj_empty_to_list
    ; singleton x := exist _ (singleton (inj x)) (inj_singleton_helper x)
    ; singleton_to_list := inj_singleton_to_list
    ; size_nat s := size_nat (proj1_sig s)
    ; size_nat_to_list := inj_size_nat_to_list
    ; is_empty s := is_empty (proj1_sig s)
    ; is_empty_to_list := inj_is_empty_to_list
    ; size s := size (proj1_sig s)
    ; size_ok := inj_size_ok
    ; add s x := exist _ (add (proj1_sig s) (inj x)) (inj_add_helper s x)
    ; add_ok := inj_add_ok
    ; remove s x := exist _ (remove (proj1_sig s) (inj x)) (inj_remove_helper s x)
    ; remove_ok := inj_remove_ok
    ; union s1 s2 := exist _ (union (proj1_sig s1) (proj1_sig s2)) (inj_union_helper s1 s2)
    ; union_ok := inj_union_ok
    ; inter s1 s2 := exist _ (inter (proj1_sig s1) (proj1_sig s2)) (inj_inter_helper s1 s2)
    ; inter_ok := inj_inter_ok
    ; diff s1 s2 := exist _ (diff (proj1_sig s1) (proj1_sig s2)) (inj_diff_helper s1 s2)
    ; diff_ok := inj_diff_ok
    ; for_all s p := for_all (proj1_sig s) (fun x => p (uninj x))
    ; for_all_ok := inj_for_all_ok
    ; is_subset s1 s2 := is_subset (proj1_sig s1) (proj1_sig s2)
    ; is_subset_ok := inj_subset_ok
    ; equal s1 s2 := equal (proj1_sig s1) (proj1_sig s2)
    ; equal_ok := inj_equal_ok
   |}.

End SetInject.

(* This is a crude but convenient way to get N and Z sets
   through storing the numbers as strings.
 *)
Definition N_set
:= (SA String.string_dec string_avl_set string_avl_set_impl HexString.of_N HexString.to_N).
Definition N_set_impl
: class N.eq_dec N_set
:= inj_impl N.eq_dec String.string_dec
            string_avl_set string_avl_set_impl
            HexString.of_N HexString.to_N HexString.to_N_of_N.

Definition Z_set
:= (SA String.string_dec string_avl_set string_avl_set_impl HexString.of_Z HexString.to_Z).
Definition Z_set_impl
: class Z.eq_dec Z_set
:= inj_impl Z.eq_dec String.string_dec
            string_avl_set string_avl_set_impl
            HexString.of_Z HexString.to_Z HexString.to_Z_of_Z.