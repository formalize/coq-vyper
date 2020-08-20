From Coq Require Import Arith.

Fixpoint nary_fun (T: Type) (n: nat) (R: Type)
: Type
:= match n with
   | O => R
   | S k => T -> (nary_fun T k R)
   end.

Fixpoint nary_call {T n R} (f: nary_fun T n R) (l: list T) (ok: n <= length l)
: R * list T
:= match n as n' return nary_fun T n' R  ->  n' <= length l  ->  R * list T with
   | 0 => fun f' ok' => (f', l)
   | S k => fun f' => match l as l' return S k <= length l'  ->  R * list T with
                      | nil => fun ok' => False_rect _ (Nat.nle_succ_0 _ ok')
                      | (h :: t)%list => fun ok' => nary_call (f' h) t (le_S_n _ _ ok')
                      end
   end f ok.

Definition nary_call' {T n R} (f: nary_fun T n R) (l: list T) (ok: n <=? length l = true)
:= nary_call f l (proj1 (Nat.leb_le _ _) ok).

Local Example nary_call_example_pow:
  nary_call' (Nat.pow: nary_fun nat 2 nat) (2 :: 3 :: 5 :: nil)%list eq_refl = (8, 5 :: nil)%list.
Proof. trivial. Qed.