From Coq Require Import NArith List.
From Coq Require Import Lia.

Require Path.
Require Map.

Section LongestPath.

Context {V: Type} (R: V -> V -> Prop).

(** A pathmap associates with every vertex a path starting at that vertex.
    It also caches the path's length.
    The Max requirement says that the path should
    either have the maximal possible length or be long enough as defined by [bound].
 *)
Record pathmap {bound: nat} := {
  (** This typing is a bit weird but if it's typed straightforwardly ([pm_lookup x: Path.t R x])
      then typing the Map becomes a problem.
      The best solution would be to have a dependent Map. Why don't we have it already?
   *)
  pm_lookup (x: V): { start: V & Path.t R start} * N;
  pm_Start  (x: V): projT1 (fst (pm_lookup x)) = x;
  pm_Len    (x: V): snd (pm_lookup x) = N.of_nat (Path.length (projT2 (fst (pm_lookup x))));
  pm_Max    (x: V): let (p, n) := pm_lookup x in
                    n = N.of_nat bound
                     \/
                    (n < N.of_nat bound)%N
                     /\
                    forall q: Path.t R x, Path.length q <= Path.length (projT2 p)
}.
Arguments pathmap (bound): clear implicits.

(** The zero pathmap associates an empty path to every vertex. *)
Definition zero_pathmap
: pathmap 0
:= {| pm_lookup x := (existT _ x (Path.Nil x), 0%N)
    ; pm_Start  x := eq_refl
    ; pm_Len    x := eq_refl
    ; pm_Max    x := or_introl (eq_refl: 0%N = N.of_nat 0)
   |}.

Local Lemma collect_helper_head {h t}
                                {children: list V}
                                {bound: nat}
                                {pm: pathmap bound}
                                (E: children = h :: t)
                                (H: projT1 (fst (pm_lookup pm h)) = h):
  In (projT1 (fst (pm_lookup pm h))) children.
Proof.
subst. rewrite H. apply in_eq.
Qed.

Local Lemma collect_helper_tail {x h t}
                                {children: list V}
                                (E: children = h :: t)
                                (ChildrenOk: forall y, In y children -> R x y):
  forall y, In y t -> R x y.
Proof.
subst. intros y H. apply ChildrenOk. apply in_cons. exact H.
Qed.

(** Find the maximal length path starting at [x] and continuing
    with one of the vertices in the [children] list.
    The result is bound by [S bound].

    Here's approximately how it works:
      - query pm to get the longest path starting at every child
      - select the longest among those
      - attach x to the start of the path
 *)
Fixpoint collect {bound: nat} {boundN: N}
                 (pm: pathmap bound)
                 (BoundOk: boundN = N.of_nat bound)
                 (x: V)
                 (children: list V)
                 (ChildrenOk: forall y, In y children -> R x y)
{struct children}
: Path.t R x * N
:= match children as children' return _ = children' -> _ with
   | nil => fun _ => (Path.Nil x, 0%N)
   | cons h t => fun E =>
      let r := pm_lookup pm h in
      let nh_plus_1 := N.succ (snd r) in
      if (snd r =? boundN)%N
        then (Path.Cons (projT1 (fst r)) 
                        (ChildrenOk (projT1 (fst r)) (collect_helper_head E (pm_Start pm h)))
                        (projT2 (fst r)),
              nh_plus_1)
        else let (pt, nt) := collect pm BoundOk x t (collect_helper_tail E ChildrenOk) in
             if (snd r <? nt)%N
               then (pt, nt)
               else (Path.Cons (projT1 (fst r)) 
                        (ChildrenOk (projT1 (fst r)) (collect_helper_head E (pm_Start pm h)))
                        (projT2 (fst r)),
                     nh_plus_1)
   end eq_refl.

Lemma collect_length {bound: nat} {boundN: N}
                     (pm: pathmap bound)
                     (BoundOk: boundN = N.of_nat bound)
                     (x: V)
                     (children: list V)
                     (ChildrenOk: forall y, In y children -> R x y):
  let (p, n) := collect pm BoundOk x children ChildrenOk in
  n = N.of_nat (Path.length p).
Proof.
induction children. { easy. }
assert (L := pm_Len pm a). assert (St := pm_Start pm a).
cbn.
remember (collect_helper_head eq_refl (pm_Start pm a)) as helper_head.
clear Heqhelper_head. revert helper_head.
destruct (pm_lookup pm a) as (ph, nh). cbn.
remember (nh =? boundN)%N as early_stop.
destruct early_stop.
{ cbn in *. subst. now rewrite<- Nat2N.inj_succ. }
assert (T := IHchildren (collect_helper_tail eq_refl ChildrenOk)).
destruct (collect pm BoundOk x children (collect_helper_tail eq_refl ChildrenOk)) as (pt, nt).
destruct (nh <? nt)%N; subst. { trivial. }
cbn in *. subst. now rewrite<- Nat2N.inj_succ.
Qed.

Lemma collect_bound {bound: nat} {boundN: N}
                    (pm: pathmap bound)
                    (BoundOk: boundN = N.of_nat bound)
                    (x: V)
                    (children: list V)
                    (ChildrenOk: forall y, In y children -> R x y):
  Path.length (fst (collect pm BoundOk x children ChildrenOk)) <= S bound.
Proof.
induction children. { apply PeanoNat.Nat.le_0_l. }
assert (L := pm_Len pm a). assert (M := pm_Max pm a).
cbn.
remember (collect_helper_head eq_refl (pm_Start pm a)) as helper_head.
clear Heqhelper_head. revert helper_head.
destruct (pm_lookup pm a) as (ph, nh). cbn in *. intro helper_head.
remember (nh =? boundN)%N as early_stop.
destruct early_stop.
{
  cbn. rewrite<- PeanoNat.Nat.succ_le_mono.
  case M; clear M; intro M.
  {
    apply PeanoNat.Nat.eq_le_incl.
    subst.
    apply Nat2N.inj. exact M.
  }
  destruct M as (M, _). subst. lia.
}
assert (T := IHchildren (collect_helper_tail eq_refl ChildrenOk)).
destruct (collect pm BoundOk x children (collect_helper_tail eq_refl ChildrenOk)) as (pt, nt).
remember (nh <? nt)%N as f. destruct f; subst. { trivial. }
cbn in *. symmetry in Heqf. rewrite N.ltb_ge in Heqf.
rewrite<- PeanoNat.Nat.succ_le_mono. (* XXX dup from above *)
case M; intro H.
{
  apply PeanoNat.Nat.eq_le_incl.
  subst.
  apply Nat2N.inj. exact H.
}
destruct H as (H, _).
subst. lia.
Qed.

(** Assert that the second vertex of the path is in the list.
    Special case: an empty path satisfies this predicate.
 *)
Definition SecondIn {x: V} (p: Path.t R x) (l: list V)
: Prop
:= (if Path.is_empty p as empty return _ = empty -> _
       then fun T => True
       else fun F => In (Path.second p F) l)
     eq_refl.

(** [collect] finds the maximal length path among those
    whose second vertex is among the given list of children.
 *)
Lemma collect_max_partial {bound: nat} {boundN: N}
                          (pm: pathmap bound)
                          (BoundOk: boundN = N.of_nat bound)
                          (x: V)
                          (children: list V)
                          (ChildrenOk: forall y, In y children -> R x y):
    let (p, n) := collect pm BoundOk x children ChildrenOk in
      n = N.succ boundN
       \/
      (n < N.succ boundN)%N
       /\
      forall q: Path.t R x,
        SecondIn q children -> Path.length q <= Path.length p.
Proof.
induction children.
{
  cbn. right. split. { apply N.lt_0_succ. } intros q H.
  destruct q. 2:easy.
  apply PeanoNat.Nat.le_refl.
}
remember (collect pm BoundOk x (a :: children) ChildrenOk) as c.
assert (L := collect_length pm BoundOk x (a :: children) ChildrenOk). rewrite<- Heqc in L.
assert (B := collect_bound  pm BoundOk x (a :: children) ChildrenOk). rewrite<- Heqc in B.
destruct c as (p, n). cbn in B. apply Lt.le_lt_or_eq in B.
case B; clear B; intro B. 2:{ left. subst. rewrite B. apply Nat2N.inj_succ. }
right. split. { subst. lia. }
intros q H.
(* goal: Path.length q <= Path.length p *)
destruct q. { apply PeanoNat.Nat.le_0_l. }
cbn in *.
cbn in *. case H; clear H; intro H.
{ (* q goes through the first child *)
  subst.
  assert (L := pm_Len pm v).
  assert (M := pm_Max pm v).
  remember (collect_helper_head eq_refl (pm_Start pm v)) as helper_head.
  clear Heqhelper_head.
  destruct (pm_lookup pm v) as (ph, nh).
  cbn in *.
  remember (nh =? N.of_nat bound)%N as e. symmetry in Heqe. destruct e.
  {
    rewrite N.eqb_eq in Heqe.
    inversion Heqc. subst p. cbn in *. lia.
  }
  apply N.eqb_neq in Heqe.
  case M; clear M; intro M. { contradiction. }
  destruct M as (K, M). assert (Q := M q).
  destruct (collect pm eq_refl x children (collect_helper_tail eq_refl ChildrenOk)) as (pt, nt).
  remember (nh <? nt)%N as f. symmetry in Heqf. destruct f.
  {
    rewrite N.ltb_lt in Heqf.
    inversion Heqc. lia.
  }
  rewrite N.ltb_ge in Heqf.
  inversion Heqc. lia.
}
(* q goes through the tail *)
assert (IH := IHchildren (collect_helper_tail eq_refl ChildrenOk)).
(* XXX lots of dup *)
subst.
assert (L := pm_Len pm a).
assert (M := pm_Max pm a).
remember (collect_helper_head eq_refl (pm_Start pm a)) as helper_head.
clear Heqhelper_head.
destruct (pm_lookup pm a) as (ph, nh).
cbn in *.
remember (nh =? N.of_nat bound)%N as e. symmetry in Heqe. destruct e.
{
  rewrite N.eqb_eq in Heqe.
  inversion Heqc. subst p. cbn in *. lia.
}
apply N.eqb_neq in Heqe.
case M; clear M; intro M. { contradiction. }
destruct M as (K, M).
assert (L' := collect_length pm eq_refl x children (collect_helper_tail eq_refl ChildrenOk)).
assert (B' := collect_bound  pm eq_refl x children (collect_helper_tail eq_refl ChildrenOk)).
destruct (collect pm eq_refl x children (collect_helper_tail eq_refl ChildrenOk)) as (pt, nt).
remember (nh <? nt)%N as f. symmetry in Heqf. destruct f.
{
  rewrite N.ltb_lt in Heqf.
  inversion Heqc. cbn in B'.
  case IH; clear IH; intro IH.
  { subst. lia. }
  destruct IH as (_, IH).
  assert (IHq := IH (Path.Cons v Ok q) H).
  apply IHq.
}
rewrite N.ltb_ge in Heqf.
inversion Heqc. subst p. cbn.
rewrite<- PeanoNat.Nat.succ_le_mono.
case IH; clear IH; intro IH. { subst. lia. }
destruct IH as (_, IH).
assert (IHq := IH (Path.Cons v Ok q) H).
cbn in IHq. lia.
Qed.

(** [collect] finds the longest path given list of all children. *)
Lemma collect_max {bound: nat} {boundN: N}
                  (pm: pathmap bound)
                  (BoundOk: boundN = N.of_nat bound)
                  (x: V)
                  (children: list V)
                  (ChildrenOk: forall y, In y children <-> R x y):
    let (p, n) := collect pm BoundOk x children (fun y => proj1 (ChildrenOk y)) in
      n = N.succ boundN
       \/
      (n < N.succ boundN)%N
       /\
      forall q: Path.t R x,
        Path.length q <= Path.length p.
Proof.
assert (M := collect_max_partial pm BoundOk x children (fun y => proj1 (ChildrenOk y))).
destruct collect.
case M; clear M; intro M. { left. exact M. }
right. split. { tauto. }
destruct M as (B, M).
intro q.
apply (M q).
(* goal: SecondIn q children *)
destruct q. { easy. }
cbn. rewrite ChildrenOk. exact Ok.
Qed.

(*******************************************************************************************)

Context {EqDec: forall x y: V, {x = y} + {x <> y}}
        {M: Type}
        (MImpl: Map.class EqDec ({ start: V & Path.t R start} * N) M)
        (all: list V)
        (fanout: forall v, list V)
        (fanout_ok: forall (u v: V), In v (fanout u) <-> R u v).

(** Do [collect] on every vertex. *)
Definition collect_alist {bound: nat} {boundN: N}
                         (pm: pathmap bound)
                         (BoundOk: boundN = N.of_nat bound)
:= List.map (fun x =>
               let (p, n) := collect pm BoundOk x (fanout x) (fun y => proj1 (fanout_ok x y)) in
               (x, (existT _ x p, n)))
            all.

Lemma collect_alist_total {bound: nat} {boundN: N}
                          (pm: pathmap bound)
                          (BoundOk: boundN = N.of_nat bound)
                          (all_ok: forall v: V, In v all)
                          (x: V):
  match Map.alist_lookup EqDec (collect_alist pm BoundOk) x with
  | Some _ => True
  | None => False
  end.
Proof.
unfold collect_alist.
assert (A := all_ok x). clear all_ok.
induction all. { now apply List.in_nil in A. }
inversion A.
{
  subst. cbn. destruct collect as (p, n).
  now destruct EqDec.
}
cbn. destruct collect as (p, n).
destruct EqDec. { trivial. }
apply (IHl H).
Qed.

Lemma collect_alist_start {bound: nat} {boundN: N}
                          (pm: pathmap bound)
                          (BoundOk: boundN = N.of_nat bound)
                          (x: V):
  match Map.alist_lookup EqDec (collect_alist pm BoundOk) x with
  | Some p => projT1 (fst p) = x
  | None => True
  end.
Proof.
unfold collect_alist.
induction all. { easy. }
cbn. destruct collect. destruct EqDec. { easy. }
apply IHl.
Qed.

Lemma collect_alist_len {bound: nat} {boundN: N}
                        (pm: pathmap bound)
                        (BoundOk: boundN = N.of_nat bound)
                        (x: V):
  match Map.alist_lookup EqDec (collect_alist pm BoundOk) x with
  | Some p => snd p = N.of_nat (Path.length (projT2 (fst p)))
  | None => True
  end.
Proof.
unfold collect_alist.
induction all. { easy. }
cbn. remember (collect pm BoundOk a (fanout a) (fun y : V => proj1 (fanout_ok a y))) as c.
destruct c. destruct EqDec. 2:apply IHl.
cbn.
assert (L := collect_length pm BoundOk a (fanout a) (fun y : V => proj1 (fanout_ok a y))).
rewrite<- Heqc in L. exact L.
Qed.

Lemma collect_alist_max {bound: nat} {boundN: N}
                        (pm: pathmap bound)
                        (BoundOk: boundN = N.of_nat bound)
                        (x: V):
  match Map.alist_lookup EqDec (collect_alist pm BoundOk) x with
  | Some pn => let (p, n) := pn in
                    n = N.of_nat (S bound)
                     \/
                    (n < N.of_nat (S bound))%N
                     /\
                    forall q: Path.t R x, Path.length q <= Path.length (projT2 p)
  | None => True
  end.
Proof.
unfold collect_alist.
induction all. { easy. }
cbn. remember (collect pm BoundOk a (fanout a) (fun y : V => proj1 (fanout_ok a y))) as c.
destruct c. destruct EqDec. 2:apply IHl.
cbn.
assert (Max := collect_max pm BoundOk a (fanout a) (fanout_ok a)).
rewrite<- Heqc in Max. subst.
case Max; clear Max; intro Max. { left. lia. }
right. split. lia. tauto.
Qed.

(** Do [collect] on every vertex and build a Map out of it. *)
Definition collect_map {bound: nat} {boundN: N}
                       (pm: pathmap bound)
                       (BoundOk: boundN = N.of_nat bound)
:= Map.of_alist (collect_alist pm BoundOk).

Lemma collect_map_total {bound: nat} {boundN: N}
                        (pm: pathmap bound)
                        (BoundOk: boundN = N.of_nat bound)
                        (all_ok: forall v: V, In v all)
                        (x: V):
  match Map.lookup (collect_map pm BoundOk) x with
  | Some _ => True
  | None => False
  end.
Proof.
unfold collect_map. rewrite Map.of_alist_ok.
apply collect_alist_total. assumption.
Qed.

Local Lemma collect_map_lookup_helper {bound: nat} {boundN: N}
                                      (pm: pathmap bound)
                                      (BoundOk: boundN = N.of_nat bound)
                                      (all_ok: forall v: V, In v all)
                                      (x: V)
                                      (E: Map.lookup (collect_map pm BoundOk) x = None):
  False.
Proof.
assert (T := collect_map_total pm BoundOk all_ok x).
rewrite E in T. exact T.
Qed.

Definition collect_map_lookup {bound: nat} {boundN: N}
                              (pm: pathmap bound)
                              (BoundOk: boundN = N.of_nat bound)
                              (all_ok: forall v: V, In v all)
                              (x: V)
:= match Map.lookup (collect_map pm BoundOk) x as r return _ = r -> _ with
   | Some x => fun _ => x
   | None => fun E => False_rect _ (collect_map_lookup_helper pm BoundOk all_ok x E)
   end eq_refl.

Lemma collect_map_start {bound: nat} {boundN: N}
                        (pm: pathmap bound)
                        (BoundOk: boundN = N.of_nat bound)
                        (all_ok: forall v: V, In v all)
                        (x: V):
  projT1 (fst (collect_map_lookup pm BoundOk all_ok x)) = x.
Proof.
unfold collect_map_lookup.
assert (T := collect_map_total pm BoundOk all_ok x).
assert (A := collect_alist_start pm BoundOk x).
unfold collect_map in *. rewrite Map.of_alist_ok in T.
remember (collect_map_lookup_helper pm BoundOk all_ok x) as foo. clear Heqfoo.
revert foo. unfold collect_map. rewrite Map.of_alist_ok. intro foo.
now destruct (Map.alist_lookup EqDec (collect_alist pm BoundOk)).
Qed.

Lemma collect_map_len {bound: nat} {boundN: N}
                      (pm: pathmap bound)
                      (BoundOk: boundN = N.of_nat bound)
                      (all_ok: forall v: V, In v all)
                      (x: V):
  let p := (collect_map_lookup pm BoundOk all_ok x) in
  snd p = N.of_nat (Path.length (projT2 (fst p))).
Proof.
unfold collect_map_lookup.
assert (T := collect_map_total pm BoundOk all_ok x).
assert (A := collect_alist_len pm BoundOk x).
unfold collect_map in *. rewrite Map.of_alist_ok in T.
remember (collect_map_lookup_helper pm BoundOk all_ok x) as foo. clear Heqfoo.
revert foo. unfold collect_map. rewrite Map.of_alist_ok. intro foo.
now destruct (Map.alist_lookup EqDec (collect_alist pm BoundOk)).
Qed.

Lemma collect_map_max {bound: nat} {boundN: N}
                      (pm: pathmap bound)
                      (BoundOk: boundN = N.of_nat bound)
                      (all_ok: forall v: V, In v all)
                      (x: V):
  let (p, n) := (collect_map_lookup pm BoundOk all_ok x) in
    n = N.of_nat (S bound)
     \/
    (n < N.of_nat (S bound))%N
     /\
    forall q: Path.t R x, Path.length q <= Path.length (projT2 p).
Proof.
unfold collect_map_lookup.
assert (T := collect_map_total pm BoundOk all_ok x).
assert (A := collect_alist_max pm BoundOk x).
unfold collect_map in *. rewrite Map.of_alist_ok in T.
remember (collect_map_lookup_helper pm BoundOk all_ok x) as foo. clear Heqfoo.
revert foo. unfold collect_map. rewrite Map.of_alist_ok. intro foo.
now destruct (Map.alist_lookup EqDec (collect_alist pm BoundOk)).
Qed.

Definition pathmap_advance {bound: nat} {boundN: N}
                           (pm: pathmap bound)
                           (BoundOk: boundN = N.of_nat bound)
                           (all_ok: forall v: V, In v all)
: pathmap (S bound)
:= let m := collect_map pm BoundOk in
   {|
      pm_lookup x :=
         match Map.lookup m x as r return _ = r -> _ with
         | Some x => fun _ => x
         | None => fun E => False_rect _ (collect_map_lookup_helper pm BoundOk all_ok x E)
         end eq_refl;
      pm_Start := collect_map_start pm BoundOk all_ok;
      pm_Len := collect_map_len pm BoundOk all_ok;
      pm_Max := collect_map_max pm BoundOk all_ok;
   |}.

Local Lemma compute_pathmap_rec_helper {bound boundN new_bound}
                                       (BoundOk : boundN = N.of_nat bound)
                                       (E : bound = S new_bound):
  N.pred boundN = N.of_nat new_bound.
Proof.
lia.
Qed.

Local Fixpoint compute_pathmap_rec (bound: nat) (boundN: N)
                                   (BoundOk: boundN = N.of_nat bound)
                                   (all_ok: forall v: V, In v all)
: pathmap bound
:= match bound as bound' return bound = bound' -> _ with
   | O => fun _ => zero_pathmap
   | S new_bound => fun E =>
        let new_boundN := N.pred boundN in
        let ok := compute_pathmap_rec_helper BoundOk E in
        pathmap_advance (compute_pathmap_rec new_bound new_boundN ok all_ok) ok all_ok
   end eq_refl.

Definition compute_pathmap (all_ok: forall v: V, In v all) (bound: nat)
: pathmap bound
:= compute_pathmap_rec bound (N.of_nat bound) eq_refl all_ok.

End LongestPath.