From Coq Require Import NArith List.

Require Path Cycle.
Require Import Dirichlet LongestPath.

Section Depthmap.

Context {V: Type}
        (R: V -> V -> Prop)
        {EqDec: forall x y: V, {x = y} + {x <> y}}
        (all: list V)
        (all_ok: forall v: V, In v all).

Local Lemma cycle_from_long_path_helper {start: V}
                                        {p: Path.t R start}
                                        (Long: length all <= Path.length p):
  length all < length (Path.vertices_with_start p).
Proof.
rewrite Path.vertices_with_start_length.
apply Lt.le_lt_n_Sm. exact Long.
Qed.

(** Extract a cycle from a path of at least [length all] arcs. *)
Definition cycle_from_long_path {start: V}
                                {p: Path.t R start}
                                (Long: length all <= Path.length p)
: Cycle.t R
:= let v := Path.vertices_with_start p in
   let d := dirichlet EqDec (fun x _ => all_ok x) (cycle_from_long_path_helper Long) in
   Cycle.from_dup (dup_ok d).

(**************************************************************************************)

Context {M: Type}
        (MImpl: Map.class EqDec ({ start: V & Path.t R start} * N) M)
        (fanout: forall v, list V)
        (fanout_ok: forall (u v: V), In v (fanout u) <-> R u v).

Definition long_enough_pathmap
: pathmap R (length all)
:= compute_pathmap R MImpl all fanout fanout_ok all_ok (length all).

Local Lemma look_for_cycle_rec_helper_nil (l: list V)
                                          (E: l = nil)
                                          (A: V -> Prop):
  Forall A l.
Proof.
subst. apply Forall_nil.
Qed.


Local Lemma look_for_cycle_rec_helper_cons 
      {pm: pathmap R (length all)}
      {n: N}
      {l: list V}
      {h: V}
      {t: list V}
      (E: l = h :: t)
      (L: (snd (pm_lookup R (length all) pm h) <? n)%N = true):
  Cycle.t R + Forall (fun a => (snd (pm_lookup R (length all) pm a) < n)%N) t ->
  Cycle.t R + Forall (fun a => (snd (pm_lookup R (length all) pm a) < n)%N) l.
Proof.
rewrite N.ltb_lt in L.
intro H. destruct H as [Cycle|Tail]. { exact (inl Cycle). }
right. subst l. apply Forall_cons; assumption.
Qed.

Local Lemma look_for_cycle_rec_helper_cycle
      {pm: pathmap R (length all)}
      {n: N}
      (NOk: n = N.of_nat (length all))
      {l: list V}
      {h: V}
      {t: list V}
      (E: l = h :: t)
      (L: (snd (pm_lookup R (length all) pm h) <? n)%N = false):
  length all <= Path.length (projT2 (fst (pm_lookup R (length all) pm h))).
Proof.
rewrite N.ltb_ge in L. subst.
assert (Len := pm_Len _ _ pm h).
rewrite Len in L.
rewrite<- N.compare_le_iff in L.
rewrite N2Nat.inj_compare in L.
repeat rewrite Nat2N.id in L.
rewrite PeanoNat.Nat.compare_le_iff in L.
exact L.
Qed.

Fixpoint look_for_cycle_rec (pm: pathmap R (length all))
                            (n: N)
                            (NOk: n = N.of_nat (length all))
                            (l: list V)
: Cycle.t R + Forall (fun a => (snd (pm_lookup _ _ pm a) < n)%N) l
:= match l as l' return l = l' -> _ with
   | nil => fun E => inr (look_for_cycle_rec_helper_nil l E _)
   | cons h t => fun E => 
         (if (snd (pm_lookup _ _ pm h) <? n)%N as lt return _ = lt -> _
             then fun L => look_for_cycle_rec_helper_cons E L
                             (look_for_cycle_rec pm n NOk t)
             else fun L => inl (cycle_from_long_path 
                                 (look_for_cycle_rec_helper_cycle NOk E L)))
           eq_refl
   end eq_refl.

(** Either discover a cycle or confirm that all the paths in [pm] are truly longest. *)
Definition look_for_cycle (pm: pathmap R (length all))
:= look_for_cycle_rec pm (N.of_nat (length all)) eq_refl all.

End Depthmap.