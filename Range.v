From Coq Require Import NArith Arith Lia List.

Local Open Scope list_scope.

Definition range (offset count: N)
: list N
:= let fix range' (countdown: nat)
   := match countdown with
      | O => nil
      | S k => cons (offset + count - 1 - N.of_nat k)%N
                    (range' k)
      end
   in range' (N.to_nat count).

Local Example range_example:
  range 5 3 = (5 :: 6 :: 7 :: nil)%N.
Proof.
trivial.
Qed.

Definition range_nat (offset count: nat)
: list N
:= let fix range' (countdown: nat)
   := match countdown with
      | O => nil
      | S k => cons (N.of_nat (offset + count - 1 - k))
                    (range' k)
      end
   in range' count.

Lemma range_nat_ok (offset count: nat):
  range_nat offset count = range (N.of_nat offset) (N.of_nat count).
Proof.
unfold range, range_nat.
rewrite Nat2N.id.
revert offset. induction count. { trivial. }
intro offset. cbn.
assert (IH := IHcount (S offset)). clear IHcount.
f_equal. { f_equal. lia. }
assert (EqLHS:
          forall t,
            (fix range' (countdown : nat) : list N :=
             match countdown with
             | 0 => nil
             | S k => (N.of_nat (offset + S count - 1 - k)) :: range' k
             end) t
              =
            (fix range' (countdown : nat) : list N :=
             match countdown with
             | 0 => nil
             | S k => (N.of_nat (S offset + count - 1 - k)) :: range' k
             end) t).
{
  clear IH. intro t.
  revert offset. induction t. { easy. }
  intro offset.
  f_equal. 2:apply IHt.
  f_equal. f_equal. lia.
}
rewrite EqLHS. clear EqLHS.
assert (EqRHS:
          forall t,
            (fix range' (countdown : nat) : list N :=
             match countdown with
             | 0 => nil
             | S k =>
                 (N.of_nat offset + N.pos (Pos.of_succ_nat count) - 1 - N.of_nat k)%N :: range' k
             end) t
              =
            (fix range' (countdown : nat) : list N :=
             match countdown with
             | 0 => nil
             | S k => (N.of_nat (S offset) + N.of_nat count - 1 - N.of_nat k)%N :: range' k
             end) t).
{
  clear IH. intro t.
  revert offset. induction t. { easy. }
  intro offset.
  f_equal. 2:apply IHt.
  f_equal. f_equal. lia.
}
rewrite EqRHS. clear EqRHS.
apply IH.
Qed.

Lemma range_via_nat (offset count: N):
  range offset count = range_nat (N.to_nat offset) (N.to_nat count).
Proof.
rewrite range_nat_ok.
now repeat rewrite N2Nat.id.
Qed.

Lemma range_cons (offset count: N):
  range offset (N.succ count) = offset :: range (N.succ offset) count.
Proof.
rewrite range_via_nat.
unfold range_nat.
revert offset. induction count; intros.
{
  cbn. replace (Pos.to_nat 1) with 1 by easy.
  f_equal. lia.
}
cbn. rewrite Pnat.Pos2Nat.inj_succ.
f_equal. { lia. }
match goal with
|- ?l _ = ?r _ =>
        enough (forall x, l x = r x) by easy
end.
intro x. induction x. { trivial. }
f_equal. { lia. }
apply IHx.
Qed.
