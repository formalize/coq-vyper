From Coq Require Import List.

Require Path.

Record cycle {V: Type} (R: V -> V -> Prop)
:= { vertex: V;
     path: Path.t R vertex;
     Closed: Path.endpoint path = vertex;
     Nonempty: Path.is_empty path = false;
   }.
Arguments vertex   {_ _}.
Arguments path     {_ _}.
Arguments Closed   {_ _}.
Arguments Nonempty {_ _}.
Definition t {V: Type} := @cycle V.

Local Lemma from_return_helper {V: Type}
                               {R: V -> V -> Prop}
                               {start: V}
                               {p: Path.t R start}
                               {a b: list V}
                               (Return: Path.vertices p = a ++ start :: b):
  Path.is_empty (Path.firstn (S (length a)) p) = false.
Proof.
rewrite Path.is_empty_false.
rewrite Path.firstn_vertices.
destruct Path.vertices. 2:{ easy. }
symmetry in Return.
apply app_eq_nil in Return.
now destruct Return.
Qed.

Local Definition from_return {V: Type}
                             {R: V -> V -> Prop}
                             {start: V}
                             {p: Path.t R start}
                             {a b: list V}
                             (Return: Path.vertices p = a ++ start :: b)
: cycle R
:= {| vertex := start
    ; path := Path.firstn (S (length a)) p
    ; Closed := Path.firstn_endpoint p Return
    ; Nonempty := from_return_helper Return
    |}.


Local Lemma from_dup_nil {V: Type}
                         {R: V -> V -> Prop}
                         {start: V}
                         {p: Path.t R start}
                         {v: V}
                         {a b c: list V}
                         (Dup: Path.vertices_with_start p = a ++ v :: b ++ v :: c)
                         (E : a = nil):
  Path.vertices p = b ++ start :: c.
Proof.
subst. unfold Path.vertices_with_start in Dup.
rewrite app_nil_l in Dup.
inversion Dup. subst start.
assumption.
Qed.

Local Lemma from_dup_cons {V: Type}
                          {R: V -> V -> Prop}
                          {start: V}
                          {p: Path.t R start}
                          {v h: V}
                          {a b c t: list V}
                          (Dup: Path.vertices_with_start p = a ++ v :: b ++ v :: c)
                          (E : a = h :: t):
  Path.vertices_with_start (Path.rest p (Path.nonempty_if_has_two_vertices Dup)) 
   =
  t ++ v :: b ++ v :: c.
Proof.
unfold Path.vertices_with_start in *.
subst a.
destruct p; cbn in *.
{
  exfalso. inversion Dup. subst. symmetry in H1.
  apply app_eq_nil in H1. destruct H1. discriminate.
}
inversion Dup. easy.
Qed.

(* Extract a cycle from a duplication in Path.vertices_with_start. *)
Fixpoint from_dup {V: Type}
                  {R: V -> V -> Prop}
                  {start: V}
                  {p: Path.t R start}
                  {v: V}
                  {a b c: list V}
                  (Dup: Path.vertices_with_start p = a ++ v :: b ++ v :: c)
: cycle R
:= match a as a' return a = a' -> cycle R with
   | nil => fun E => from_return (from_dup_nil Dup E)
   | h :: t => fun E => from_dup (from_dup_cons Dup E)
   end eq_refl.