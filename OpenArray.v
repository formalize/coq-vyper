From Coq Require Import Arith NArith Lia.

Local Open Scope list_scope.

(** An OpenArray is an infinite array in which only finite amount of items are nonzero. *)
Class class {Value: Type} (Zero: Value) (A: Type) := {
  get: A -> N -> Value;
  empty: A;

  empty_ok: forall n: N,
              get empty n = Zero;

  put: A -> N -> Value -> A;

  put_ok: forall (a: A) (n k: N) (v: Value),
            get (put a n v) k 
             =
            if (n =? k)%N
              then v
              else get a k;

  to_list: A -> list Value;

  to_list_ok: forall (a: A) (n: N),
                get a n = List.nth (N.to_nat n) (to_list a) Zero;

  (** Given an offset and a count, convert the corresponding subarray to a list. *)
  view: A -> N -> N -> list Value;
  view_len: forall (a: A) (offset count: N),
              List.length (view a offset count) = N.to_nat count;
  view_ok: forall (a: A) (offset count: N) (n: N) (ok: (n < count)%N),
                  List.nth_error (view a offset count) (N.to_nat n) = Some (get a (offset + n)%N);

  from_list: list Value -> A;
  from_list_ok: forall (l: list Value) (n: N),
                  get (from_list l) n = List.nth (N.to_nat n) l Zero;
}.

Lemma put_same {Value: Type} {Zero: Value} {A: Type} (C: class Zero A)
               (a: A) (n: N) (v: Value):
  get (put a n v) n = v.
Proof.
rewrite put_ok.
enough (H: (n =? n)%N = true) by now rewrite H.
now apply N.eqb_eq.
Qed.

Fixpoint firstn_or_pad {A} (l: list A) (n: nat) (pad: A)
: list A
:= match n, l with
   | 0, _ => nil
   | S n', nil => List.repeat pad n
   | S n', h :: t => h :: firstn_or_pad t n' pad
   end.

Lemma firstn_or_pad_length {A} (l: list A) (n: nat) (pad: A):
  List.length (firstn_or_pad l n pad) = n.
Proof.
revert l. induction n; intro l.
{ now induction l. }
destruct l. { cbn. f_equal. apply List.repeat_length. }
cbn. f_equal. apply IHn.
Qed.

Lemma nth_skipn {A} (a: list A) (m n: nat) (default: A):
  List.nth (m + n) a default = List.nth n (List.skipn m a) default.
Proof.
revert n a. induction m; intros; cbn. { trivial. }
destruct a as [|h]. { now destruct n. }
cbn. apply IHm.
Qed.

Lemma view0 {Value: Type} {Zero: Value} {A: Type} (C: class Zero A)
            (a: A) (n: N):
  view a n 0 = nil.
Proof.
assert (LenOk := view_len a n 0).
remember (view _ _ _) as v.
destruct v. 2:discriminate.
trivial.
Qed.

Lemma view1 {Value: Type} {Zero: Value} {A: Type} (C: class Zero A)
            (a: A) (n: N):
  view a n 1 = get a n :: nil.
Proof.
assert (LenOk := view_len a n 1).
remember (view _ _ _) as v.
destruct v as [|x]. { discriminate. }
destruct v. 2:discriminate.
assert (OkX := view_ok a n 1 0 N.lt_0_1).
rewrite<- Heqv in OkX.
cbn in OkX.
rewrite N.add_0_r in OkX.
inversion OkX. now subst x.
Qed.

Lemma view2 {Value: Type} {Zero: Value} {A: Type} (C: class Zero A)
            (a: A) (n: N):
  view a n 2 = get a n :: get a (N.succ n) :: nil.
Proof.
assert (LenOk := view_len a n 2).
remember (view _ _ _) as v.
destruct v as [|x]. { discriminate. }
destruct v as [|y]. { discriminate. }
destruct v. 2:discriminate.
assert (OkX := view_ok a n 2 0 N.lt_0_2).
assert (OkY := view_ok a n 2 1 N.lt_1_2).
rewrite<- Heqv in OkX.
rewrite<- Heqv in OkY.
rewrite N.add_0_r in OkX.
rewrite N.add_1_r in OkY.
cbn in OkX.
replace (N.to_nat 1) with 1 in OkY by trivial.
cbn in OkY.
inversion OkX. subst x.
inversion OkY. now subst y.
Qed.

Section ListInst.
  Context {Value: Type} (Zero: Value).

  Lemma list_empty_ok (n: N):
    List.nth (N.to_nat n) nil Zero = Zero.
  Proof.
  cbn. now destruct N.to_nat.
  Qed.

  Lemma list_put_single (n k: nat) (v: Value):
    List.nth k (List.repeat Zero n ++ v :: nil) Zero
     =
    if n =? k then v else Zero.
  Proof.
  remember (n =? k) as e. symmetry in Heqe. destruct e.
  {
    rewrite Nat.eqb_eq in Heqe. subst k.
    induction n; easy.
  }
  apply Nat.eqb_neq in Heqe.
  revert k Heqe. induction n; intros.
  {
    induction k. { easy. }
    now destruct k.
  }
  induction k. { easy. }
  cbn. apply IHn.
  intro H. now subst.
  Qed.

  Lemma list_put_ok (a: list Value) (n k: N) (v: Value):
    List.nth (N.to_nat k)
      (if N.to_nat n <? length a
        then List.firstn (N.to_nat n) a ++ v :: List.skipn (S (N.to_nat n)) a
        else a ++ List.repeat Zero (N.to_nat n - length a) ++ v :: nil) Zero =
    (if (n =? k)%N then v else List.nth (N.to_nat k) a Zero).
  Proof.
  remember (N.to_nat n) as n'. remember (N.to_nat k) as k'.
  replace (n =? k)%N with (n' =? k').
  2:{
    subst. remember (n =? k)%N as eq_N. symmetry in Heqeq_N.
    destruct eq_N.
    { rewrite N.eqb_eq in Heqeq_N. subst. now rewrite Nat.eqb_eq. }
    remember (N.to_nat n =? N.to_nat k) as eq_nat. symmetry in Heqeq_nat.
    destruct eq_nat. 2:trivial.
    rewrite Nat.eqb_eq in Heqeq_nat. apply N2Nat.inj in Heqeq_nat. subst.
    apply N.eqb_neq in Heqeq_N. tauto.
  }
  clear Heqn' Heqk' n k.
  remember (n' <? length a) as n_lt_len. symmetry in Heqn_lt_len.
  revert k' a Heqn_lt_len. induction n'; intros.
  {
    destruct k', a; cbn in Heqn_lt_len; subst; cbn; trivial.
    now destruct k'.
  }
  destruct a as [ | h].
  {
    cbn.
    destruct n_lt_len. { easy. }
    destruct k'. { easy. }
    cbn. apply list_put_single.
  }
  replace (S n' <? length (h :: a)) with (n' <? length a) in Heqn_lt_len by easy.
  replace (List.firstn (S n') (h :: a)) with (h :: List.firstn n' a) by easy.
  repeat rewrite<- List.app_comm_cons.
  match goal with
  |- context G [ if ?cond then (h :: ?x) else (h :: ?y) ] =>
        replace (if cond then (h :: x) else (h :: y)) with (h :: if n_lt_len then x else y)
          by now destruct cond
  end.
  destruct k'. { easy. }
  cbn. now apply IHn'.
  Qed.

  Lemma list_view_ok (a: list Value) (offset count n: N) (Ok: (n < count)%N):
    List.nth_error
      (firstn_or_pad (List.skipn (N.to_nat offset) a) (N.to_nat count) Zero)
      (N.to_nat n) 
     =
    Some (List.nth (N.to_nat (offset + n)) a Zero).
  Proof.
  rewrite N2Nat.inj_add. rewrite nth_skipn.
  remember (List.skipn (N.to_nat offset) a) as l. clear a Heql offset.
  remember (N.to_nat n) as k.
  remember (N.to_nat count) as c.
  assert (L: k < c) by lia.
  clear n count Heqk Heqc Ok.
  revert k c L. induction l; intros.
  {
    cbn. replace (match k with 0 | _ => Zero end) with Zero by now destruct k.
    replace (match c with
             | 0 => nil
             | S _ => List.repeat Zero c
             end)
      with (List.repeat Zero c)
      by now destruct c.
    rewrite List.nth_error_nth' with (d := Zero) by (rewrite List.repeat_length; lia).
    f_equal.
   
    revert k L. induction c; intros. { now destruct k. }
    destruct k. { easy. }
    cbn. apply IHc.
    lia.
  }
  cbn. destruct k, c; try easy.
  cbn. apply IHl. lia.
  Qed.

  Definition list_inst
  : class Zero (list Value)
  := {| get a n := List.nth (N.to_nat n) a Zero
      ; empty := nil
      ; empty_ok := list_empty_ok
      ; put a n v := let i := N.to_nat n in
                     let len := List.length a in
                     if i <? len
                       then List.firstn i a ++ v :: List.skipn (S i) a
                       else a ++ List.repeat Zero (i - len) ++ v :: nil
      ; put_ok := list_put_ok
      ; to_list a := a
      ; to_list_ok a n := eq_refl
      ; from_list a := a
      ; from_list_ok a n := eq_refl
      ; view a offset count := firstn_or_pad (List.skipn (N.to_nat offset) a) (N.to_nat count) Zero
      ; view_len a offset count := firstn_or_pad_length _ _ _
      ; view_ok := list_view_ok
     |}.

End ListInst.