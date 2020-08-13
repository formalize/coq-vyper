Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Record dup {A} (l: list A) := {
  dup_x: A;
  dup_a: list A;
  dup_b: list A;
  dup_c: list A;
  dup_ok: l = dup_a ++ dup_x :: dup_b ++ dup_x :: dup_c
}.
Arguments dup_x {_ _}.
Arguments dup_a {_ _}.
Arguments dup_b {_ _}.
Arguments dup_c {_ _}.
Arguments dup_ok {_ _}.

Lemma dup_to_no_nodup {A} {l: list A} (d: dup l):
  ~ NoDup l.
Proof.
unfold not. intros.
assert(Ok := dup_ok d).
rewrite Ok in H.
apply NoDup_remove_2 in H.
apply H. clear H Ok.
rewrite app_assoc.
apply in_or_app.
right.
auto with *.
Qed.

Program Definition dup_cons {A} {l: list A} (x: A) (d: dup l)
: dup (x :: l)
:= {| dup_a := x :: dup_a d
    ; dup_b := dup_b d
    ; dup_c := dup_c d
    ; dup_x := dup_x d
    ; dup_ok := _
    |}.
Next Obligation.
f_equal. apply (dup_ok d).
Qed.

Lemma remove_preserves_in {A}
    (eq_dec : forall x y: A, {x = y}+{x <> y})
    (x y: A) (l: list A):
  In x (remove eq_dec y l) <-> x <> y /\ In x l.
Proof.
induction l. { simpl. tauto. }
simpl. destruct eq_dec as [y_eq_a | y_ne_a].
{
  rewrite IHl.
  rewrite y_eq_a.
  split. { tauto. }
  intros (x_ne_a, H).
  split. { assumption. }
  destruct H. { symmetry in H. contradiction. }
  assumption.
}
simpl. rewrite IHl. split. 
{
  intro H.
  destruct H.
  {
    rewrite H.
    split.
    {
      rewrite H in y_ne_a.
      intro F. symmetry in F. contradiction.
    }
    left. trivial.
  }
  destruct H as (x_ne_y, In_x_l).
  split. { assumption. }
  right. assumption.
}
intros (x_ne_y, H).
destruct H as [a_eq_x | In_x_l].
{
  left. assumption.
}
right. split. assumption. assumption.
Qed.

Lemma remove_length_le {A}
    (eq_dec : forall x y: A, {x = y}+{x <> y})
    (x: A) (l: list A):
  length (remove eq_dec x l) <= length l.
Proof.
induction l.
{
  simpl. trivial.
}
simpl. destruct eq_dec. auto with arith.
simpl. auto with arith.
Qed.

Lemma remove_length_lt {A}
    (eq_dec : forall x y: A, {x = y}+{x <> y})
    (x: A) (l: list A):
  In x l -> length (remove eq_dec x l) < length l.
Proof.
induction l.
{
  simpl. tauto.
}
simpl.
intro H.
destruct H.
{
  rewrite H. destruct eq_dec.
  {
    assert(LE := remove_length_le eq_dec x l).
    auto with arith.
  }
  simpl.
  exfalso.
  apply n. trivial.
}
apply IHl in H.
destruct eq_dec.
auto with arith.
simpl. auto with arith.
Qed.

Lemma dirichlet_nil {A} 
    (a b: list A)
    (Bound : length b < length a)
    (E : a = nil):
  False.
Proof.
subst. cbn in Bound.
apply Nat.nlt_0_r in Bound.
assumption.
Qed.

Record list_cursor {A} (l: list A) := {
  lc_left: list A;
  lc_current: A;
  lc_right: list A;
  lc_ok: l = rev lc_left ++ lc_current :: lc_right
}.
Arguments lc_left {_ _}.
Arguments lc_current {_ _}.
Arguments lc_right {_ _}.
Arguments lc_ok {_ _}.

Inductive list_find_result {A} (good: A -> bool) (l: list A)
:= LFR_Success (cursor: list_cursor l) (ok: good (lc_current cursor) = true)
 | LFR_Failure (Oops: Forall (fun x => good x = false) l).

Lemma rec_cons_app {A} (x: A) (a b: list A):
  rev (x :: a) ++ b = rev a ++ x :: b.
Proof.
cbn. now rewrite<- app_assoc.
Qed.

Local Lemma list_find_rec_helper {A} (good: A -> bool) (left: list A) (l: list A)
                                 (LeftOk: Forall (fun x => good x = false) left):
  Forall (fun x : A => good x = false) (rev left ++ nil).
Proof.
rewrite app_nil_r. rewrite Forall_forall in *.
intro x. rewrite<- in_rev. apply LeftOk.
Qed.

Local Fixpoint list_find_rec {A} (good: A -> bool) (left: list A) (l: list A)
                             (LeftOk: Forall (fun x => good x = false) left)
: list_find_result good (rev left ++ l)
:= match l with
   | nil => LFR_Failure _ _ (list_find_rec_helper good left l LeftOk)
   | h :: t => let g := good h in
               (if g as g' return g = g' -> list_find_result good (rev left ++ h :: t)
                 then fun T => 
                    LFR_Success _ _ 
                                {| lc_left := left
                                 ; lc_current := h
                                 ; lc_right := t
                                 ; lc_ok := eq_refl
                                 |}
                                T
                 else fun F =>
                   let tresult := list_find_rec good (h :: left) t (Forall_cons _ F LeftOk) in
                   match tresult as tresult'
                     return tresult = tresult' -> list_find_result good (rev left ++ h :: t)
                   with
                   | LFR_Success _ _ c ok => fun Y => 
                        match rec_cons_app h left t in _ = z return list_find_result good z with
                        | eq_refl => LFR_Success _ _ c ok
                        end
                   | LFR_Failure _ _ Oops => fun N => LFR_Failure _ _ 
                        match rec_cons_app h left t in _ = z 
                            return Forall (fun x => good x = false) z with
                        | eq_refl => Oops
                        end
                   end eq_refl
                 ) eq_refl
   end.

Definition list_find {A} (good: A -> bool) (l: list A)
: list_find_result good l
:= list_find_rec good nil l (Forall_nil _).

Lemma dirichlet_rec_success {A} 
    (prefix a b: list A)
    (eq_dec : forall x y: A, {x = y}+{x <> y})
    (h : A)
    (t : list A)
    (E : a = h :: t)
    (c : list_cursor t)
    (ok : (if eq_dec (lc_current c) h then true else false) = true)
    (Found : list_find (fun x : A => if eq_dec x h then true else false) t
              =
             LFR_Success (fun x : A => if eq_dec x h then true else false) t c ok):
  prefix ++ a = prefix ++ h :: rev (lc_left c) ++ h :: lc_right c.
Proof.
assert(H: h = lc_current c).
{
  clear Found.
  remember (eq_dec (lc_current c) h) as e.
  destruct e. { symmetry. assumption. } discriminate.
}
subst. repeat f_equal.
exact (lc_ok c).
Qed.

Lemma dirichlet_rec_fail_In
    {A : Type}
    {a b : list A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (Sub : forall x : A, In x a -> In x b)
    (h : A)
    (t : list A)
    (E : a = h :: t)
    (Oops : Forall (fun x : A => (if eq_dec x h then true else false) = false) t):
  forall x : A, In x t -> In x (remove eq_dec h b).
Proof.
intros.
rewrite remove_preserves_in.
split.
{
  (* x <> h *)
  intro. subst. rewrite Forall_forall in Oops.
  assert(Q := Oops h H).
  destruct eq_dec; easy.
}
apply Sub. subst. cbn. tauto.
Qed.

Lemma dirichlet_rec_fail_length
    {A : Type}
    {a b : list A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (Sub : forall x : A, In x a -> In x b)
    (Bound: length b < length a)
    (h : A)
    (t : list A)
    (E : a = h :: t)
    (Oops : Forall (fun x : A => (if eq_dec x h then true else false) = false) t):
  length (remove eq_dec h b) < length t.
Proof.
assert(B: In h b).
{
  apply Sub.
  subst. cbn. left. trivial.
}
assert(L := remove_length_lt eq_dec h b B). (* length (remove eq_dec h b) < length b *)
assert(M: length b <= length t).
{
  subst. cbn in Bound.
  auto with arith.
}
apply (lt_le_trans _ _ _ L M).
Qed.

Fixpoint dirichlet_rec {A} 
    (prefix a b: list A)
    (eq_dec : forall x y: A, {x = y}+{x <> y})
    (Sub: forall x, In x a -> In x b)
    (Bound: length b < length a)
: dup (rev prefix ++ a)
:= match a as a' return a = a' -> dup (rev prefix ++ a) with
   | nil => fun E => False_rect _ (dirichlet_nil a b Bound E)
   | h :: t => fun E =>
        let e := list_find (fun x => if (eq_dec x h) then true else false) t in
        match e as e' return e = e' -> dup (rev prefix ++ a) with
        | LFR_Success _ _ c ok => fun Found => 
             {| dup_a := rev prefix
              ; dup_b := rev (lc_left c)
              ; dup_c := lc_right c
              ; dup_x := h
              ; dup_ok := dirichlet_rec_success (rev prefix) a b eq_dec h t E c ok Found
              |}
        | LFR_Failure _ _ Oops => fun NotFound =>
              match (eq_sym E) in _ = z return dup (rev prefix ++ z) with
              | eq_refl =>
                match rec_cons_app h prefix t in _ = z return dup z with
                | eq_refl =>
                    dirichlet_rec (h :: prefix) t
                      (remove eq_dec h b) 
                      eq_dec
                      (dirichlet_rec_fail_In     eq_dec Sub       h t E Oops)
                      (dirichlet_rec_fail_length eq_dec Sub Bound h t E Oops)
                end
              end
        end eq_refl
   end eq_refl.

Definition dirichlet {A}
    {a b: list A}
    (eq_dec : forall x y: A, {x = y}+{x <> y})
    (Sub: forall x, In x a -> In x b)
    (Bound: length b < length a)
: dup a
:= dirichlet_rec nil a b eq_dec Sub Bound.