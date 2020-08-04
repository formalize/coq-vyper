From Coq Require List.
Local Open Scope list_scope.

(* A path has its start (but not its end) in its type. *)
Inductive path {V: Type} (R: V -> V -> Prop) (start: V)
  := Nil
   | Cons (v: V)  (* it's perfectly fine if v = start *)
          (Ok: R start v)
          (next: path R v).
Arguments Nil {_ _} (_).
Arguments Cons {_ _ _}.
Definition t {V: Type} := @path V.

Fixpoint endpoint {V: Type} {R: V -> V -> Prop} {start: V}
                  (p: path R start)
  : V
  := match p with
     | Nil _ => start
     | Cons _ _ next => endpoint next
     end.

Definition is_empty {V: Type} {R: V -> V -> Prop} {start: V}
                    (p: path R start)
: bool
:= match p with
     | Nil _      => true
     | Cons _ _ _ => false
     end.

Fixpoint length {V: Type} {R: V -> V -> Prop} {start: V}
                (p: path R start)
: nat
:= match p with
   | Nil _ => O
   | Cons _ _ next => S (length next)
   end.

Definition flip {A B C: Type} (f: A -> B -> C) (b: B) (a: A): C := f a b.

Fixpoint glue {V: Type} {R: V -> V -> Prop} {mid: V}
              (to_start: path (flip R) mid)
              (to_end: path R mid)
: path R (endpoint to_start)
:= match to_start with
   | Nil _ => to_end
   | Cons v Ok v_to_start =>    (* start <- ... <- v <- mid -> ... -> end *)
        glue v_to_start (Cons mid Ok to_end)
   end.

(* Doesn't include start. *)
Fixpoint vertices {V: Type} {R: V -> V -> Prop} {start: V} (p: path R start)
: list V
:= match p with
   | Nil _ => nil
   | Cons v _ next => cons v (vertices next)
   end.

Definition vertices_with_start {V: Type} {R: V -> V -> Prop} {start: V} (p: path R start)
:= (start :: vertices p)%list.

(** Truncate the path to the given maximum number of vertices (not including the start). *)
Fixpoint firstn {V: Type}
                {R: V -> V -> Prop}
                {start: V}
                (n: nat)
                (p: path R start)
: path R start
:= match n with
   | 0 => Nil start
   | S k => match p with
            | Nil _ => Nil start
            | Cons v ok next => Cons v ok (firstn k next)
            end
   end.

Lemma firstn_vertices {V: Type}
                      {R: V -> V -> Prop}
                      {start: V}
                      (p: path R start)
                      (n: nat):
  vertices (firstn n p) = List.firstn n (vertices p).
Proof.
generalize start p. clear start p.
induction n; cbn in *. trivial.
induction p; cbn in *. trivial.
f_equal.
apply IHn.
Qed.

Lemma firstn_endpoint {V: Type}
                      {R: V -> V -> Prop}
                      {start: V}
                      {a b: list V}
                      {v: V}
                      (p: path R start)
                      (H: vertices p = a ++ v :: b):
  endpoint (firstn (S (List.length a)) p) = v.
Proof.
generalize a H. clear H a.
induction p; intros; cbn in *.
{
  symmetry in H.
  apply List.app_eq_nil in H.
  destruct H.
  discriminate.
}
induction a; intros; cbn in *; inversion H; subst.
{ now induction p. }
now apply IHp.
Qed.

Lemma is_empty_true {V: Type}
                    {R: V -> V -> Prop}
                    {start: V}
                    (p: path R start):
  is_empty p = true <-> vertices p = nil.
Proof.
induction p; easy.
Qed.

Lemma is_empty_false {V: Type}
                     {R: V -> V -> Prop}
                     {start: V}
                     (p: path R start):
  is_empty p = false <-> vertices p <> nil.
Proof.
induction p; easy.
Qed.

Lemma nonempty_if_has_two_vertices
    {V: Type}
    {R: V -> V -> Prop}
    {start: V}
    {p: path R start}
    {x y: V}
    {a b c: list V}
    (H: vertices_with_start p = a ++ x :: b ++ y :: c):
  is_empty p = false.
Proof.
unfold vertices_with_start in H.
destruct p. 2: { easy. }
cbn in *.
destruct a.
{
  rewrite List.app_nil_l in H.
  inversion H. subst.
  symmetry in H2. 
  apply List.app_eq_nil in H2.
  destruct H2.
  discriminate.
}
cbn in *.
inversion H. subst.
symmetry in H2.
apply List.app_eq_nil in H2.
destruct H2.
discriminate.
Qed.

(** Get the second vertex in a non-empty path. *)
Program Definition second
    {V: Type}
    {R: V -> V -> Prop}
    {start: V}
    (p: path R start)
    (Nonempty: is_empty p = false)
: V
:= match p as p' return p = p' -> V with
   | Nil _ => fun E => False_rect _ _
   | Cons v _ _ => fun _ => v
   end eq_refl.

(** Remove the first arc from a non-empty path. *)
Program Definition rest
    {V: Type}
    {R: V -> V -> Prop}
    {start: V}
    (p: path R start)
    (Nonempty: is_empty p = false)
: path R (second p Nonempty)
:= match p as p' return p = p' -> path R (second p Nonempty) with
   | Nil _ => fun E => False_rect _ _
   | Cons v _ next => fun _ => next
   end eq_refl.
