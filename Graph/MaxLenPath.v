From Coq Require Import NArith List.
From Coq Require Import FMapPositive.

Require Path.


(* A path that has maximal length among those starting at the same vertex. *)
Record max_len_path {V: Type} (R: V -> V -> Prop)
:= {
    mlp_start: V;
    mlp_path: Path.t R mlp_start;
    mlp_len: N;
    mlp_len_ok: mlp_len = N.of_nat (Path.length mlp_path);
    mlp_ok: forall q: Path.t R mlp_start,
              Path.length q <= Path.length mlp_path
   }.
Arguments mlp_start  {_ _}.
Arguments mlp_path   {_ _}.
Arguments mlp_len    {_ _}.
Arguments mlp_len_ok {_ _}.
Arguments mlp_ok     {_ _}.

(* A maximal length path among those that start with vertices in the specified list. *)
Record max_len_path_nonempty_list {V: Type} (R: V -> V -> Prop)
                                  (vs: list V)
:= {
    mlpn_start: V;
    mlpn_path: Path.t R mlpn_start;
    mlpn_In: In mlpn_start vs;
    mlpn_len: N;
    mlpn_len_ok: mlpn_len = N.of_nat (Path.length mlpn_path);
    mlpn_ok: forall (v: V)
                     (q: Path.t R v),
                In v vs -> Path.length q <= Path.length mlpn_path;
   }.
Arguments mlpn_start  {_ _ _}.
Arguments mlpn_path   {_ _ _}.
Arguments mlpn_In     {_ _ _}.
Arguments mlpn_len    {_ _ _}.
Arguments mlpn_len_ok {_ _ _}.
Arguments mlpn_ok     {_ _ _}.

(* A helper for max_len_path_cons_nonempty. *)
Lemma max_len_path_cons_tail {V: Type} {R: V -> V -> Prop} {vs: list V}
                             (h: max_len_path R)
                             (t: max_len_path_nonempty_list R vs)
                             (E: (mlp_len h <=? mlpn_len t)%N = true)
                             (v: V)
                             (q: Path.t R v)
                             (H: In v (mlp_start h :: vs)):
    Path.length q <= Path.length (mlpn_path t).
Proof.
cbn in H.
destruct H. 2: exact (mlpn_ok t v q H).
subst.
assert (L := mlp_ok h q).
apply N.leb_le in E.
rewrite mlp_len_ok in E. rewrite mlpn_len_ok in E.
rewrite<- N.compare_le_iff in E.
rewrite<- Nat2N.inj_compare in E.
rewrite PeanoNat.Nat.compare_le_iff in E.
exact (PeanoNat.Nat.le_trans _ _ _ L E).
Qed.

(* A helper for max_len_path_cons_nonempty. *)
Lemma max_len_path_cons_head {V: Type} {R: V -> V -> Prop} {vs: list V}
                             (h: max_len_path R)
                             (t: max_len_path_nonempty_list R vs)
                             (E: (mlp_len h <=? mlpn_len t)%N = false)
                             (v: V)
                             (q: Path.t R v)
                             (H: In v (mlp_start h :: vs)):
    Path.length q <= Path.length (mlp_path h).
Proof.
cbn in H.
destruct H. { subst. exact (mlp_ok h q). }
assert(T := mlpn_ok t v q H).
apply N.leb_gt in E.
rewrite mlp_len_ok in E. rewrite mlpn_len_ok in E.
rewrite<- N.compare_lt_iff in E.
rewrite<- Nat2N.inj_compare in E.
rewrite PeanoNat.Nat.compare_lt_iff in E.
apply PeanoNat.Nat.lt_le_incl.
exact (PeanoNat.Nat.le_lt_trans _ _ _ T E).
Qed.

(* This is how to grow the list of max_len_path_nonempty_list. *)
Definition max_len_path_cons_nonempty {V: Type} {R: V -> V -> Prop}
                                      {vs: list V}
                                      (h: max_len_path R)
                                      (t: max_len_path_nonempty_list R vs)
  : max_len_path_nonempty_list R (mlp_start h :: vs)
  := let f := N.leb (mlp_len h) (mlpn_len t) in
     match f as f' return (f = f' -> _) with
     | true => fun E => {|
                           mlpn_start := mlpn_start t;
                           mlpn_path := mlpn_path t;
                           mlpn_In := in_cons _ _ _ (mlpn_In t);
                           mlpn_len := mlpn_len t;
                           mlpn_len_ok := mlpn_len_ok t;
                           mlpn_ok := max_len_path_cons_tail h t E;
                         |}
     | false => fun E => {|
                           mlpn_start := mlp_start h;
                           mlpn_path := mlp_path h;
                           mlpn_In := in_eq _ _;
                           mlpn_len := mlp_len h;
                           mlpn_len_ok := mlp_len_ok h;
                           mlpn_ok := max_len_path_cons_head h t E;
                          |}
     end eq_refl.

(* Since we can't start growing the list of max_len_path_nonempty_list
   from an empty list, we have to start from singletons.
   We can convert max_len_path to max_len_path_nonempty_list of a singleton.
 *)
Program Definition max_len_path_single {V: Type} {R: V -> V -> Prop}
                                       (m: max_len_path R)
: max_len_path_nonempty_list R (mlp_start m :: nil)
:= {|
    mlpn_start := mlp_start m;
    mlpn_path := mlp_path m;
    mlpn_In := in_eq _ _;
    mlpn_len := mlp_len m;
    mlpn_len_ok := mlp_len_ok m;
    mlpn_ok := _;
  |}.
Next Obligation.
destruct H; [|contradiction]. subst.
exact (mlp_ok m q).
Qed.

(* A wrapper for max_len_path_nonempty_list that takes the empty list as a special case. *)
Inductive max_len_path_for_list {V: Type} (R: V -> V -> Prop)
                                (vs: list V)
:= MLPL_Empty (Ok: vs = nil)
 | MLPL_Nonempty (m: max_len_path_nonempty_list R vs).
Arguments MLPL_Empty    {_ _ _}.
Arguments MLPL_Nonempty {_ _ _}.

(* Finally a nice-looking cons for max_len_path_for_list. *)
Program Definition max_len_path_cons {V: Type} {R: V -> V -> Prop}
                                     {vs: list V}
                                     (h: max_len_path R)
                                     (t: max_len_path_for_list R vs)
  : max_len_path_for_list R (mlp_start h :: vs)
  := MLPL_Nonempty (match t with
                    | MLPL_Empty is_nil => max_len_path_single h
                    | MLPL_Nonempty m => max_len_path_cons_nonempty h m
                    end).

Program Definition max_len_path_collect_nonempty
                                {V: Type} {R: V -> V -> Prop}
                                {vs: list V}
                                (m: max_len_path_nonempty_list R vs)
                                (u: V)
                                (Ok: forall v, In v vs <-> R u v)
  : max_len_path R
  := {|
      mlp_start := u;
      mlp_path := Path.Cons _ (proj1 (Ok _) (mlpn_In m)) (mlpn_path m);
      mlp_len := N.succ (mlpn_len m);
      mlp_len_ok := _;
      mlp_ok := _;
    |}.
Next Obligation.
  rewrite (mlpn_len_ok m).
  now rewrite<- Nat2N.inj_succ.
Qed.
Next Obligation.
  destruct q; cbn. { auto with arith. }
  apply le_n_S.
  apply (mlpn_ok m v q).
  now rewrite Ok.
Qed.

Program Definition max_len_path_collect_empty {V: Type} {R: V -> V -> Prop}
                                              {vs: list V}
                                              (E: vs = nil)
                                              (u: V)
                                              (Ok: forall v, In v vs <-> R u v)
: max_len_path R
:= {|
    mlp_start := u;
    mlp_path := Path.Nil u;
    mlp_len := N0;
    mlp_len_ok := eq_refl;
    mlp_ok := _;
  |}.
Next Obligation.
destruct q. { auto. }
exfalso.
now rewrite<- Ok in *.
Qed.

(* collect builds a max_len_path for a vertex from max_len_path_for_list for the fanout set. *)
Definition max_len_path_collect {V: Type} {R: V -> V -> Prop}
                                {vs: list V}
                                (m: max_len_path_for_list R vs)
                                (u: V)
                                (Ok: forall v, In v vs <-> R u v)
  : max_len_path R
  := match m with
     | MLPL_Empty is_nil => max_len_path_collect_empty is_nil u Ok
     | MLPL_Nonempty m => max_len_path_collect_nonempty m u Ok
     end.

Lemma max_len_path_collect_start {V: Type} {R: V -> V -> Prop}
                                 {vs: list V}
                                 (m: max_len_path_for_list R vs)
                                 (u: V)
                                 (Ok: forall v, In v vs <-> R u v):
  mlp_start (max_len_path_collect m u Ok) = u.
Proof.
  now destruct m.
Qed.
