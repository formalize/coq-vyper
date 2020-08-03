From Coq Require Import String.
From Coq Require Import FSets.FMapAVL FSets.FMapFacts.

Require Import StringCmp.

Fixpoint alist_lookup {Key Value: Type} (KeyEqDec: forall x y: Key, {x = y} + {x <> y})
                       (a: list (Key * Value)) (query: Key)
: option Value
:= match a with
   | nil => None
   | (key, value) :: tail => 
       if KeyEqDec query key
         then Some value
         else alist_lookup KeyEqDec tail query
   end.

Class class {Key: Type} (KeyEqDec: forall x y: Key, {x = y} + {x <> y})
             (Value: Type)
             (M: Type)
:= {
  lookup: M -> Key -> option Value;

  is_empty: M -> bool;
  is_empty_ok (m: M):
    is_empty m = true 
     <->
    forall key: Key,
      lookup m key = None;

  empty: M;
  empty_ok: is_empty empty = true;
  
  insert: M -> Key -> Value -> M;
  insert_ok (m: M) (key: Key) (value: Value) (x: Key):
    lookup (insert m key value) x
     = 
    if KeyEqDec key x
      then Some value
      else lookup m x;

  remove: M -> Key -> M;
  remove_ok (m: M) (key: Key) (x: Key):
    lookup (remove m key) x
     = 
    if KeyEqDec key x
      then None
      else lookup m x;

  items: M -> list (Key * Value);
  items_ok (m: M) (key: Key):
    lookup m key = alist_lookup KeyEqDec (items m) key;
  items_nodup (m: M):
    NoDup (List.map fst (items m));

  (* XXX this is not needed *)
  merge (newer older: M): M;
  merge_ok (newer older: M) (key: Key):
    lookup (merge newer older) key
     =
    match lookup newer key with
    | Some value => Some value
    | None => lookup older key
    end;
}.

Module StringAVLMap := FMapAVL.Make StringLexicalOrder.
Definition string_avl_map := StringAVLMap.t.

Lemma string_avl_map_is_empty_ok {Value: Type} (map: StringAVLMap.t Value):
  StringAVLMap.is_empty map = true
   <->
  forall key,
    StringAVLMap.find key map = None.
Proof.
split; intro H.
{
  intro key.
  apply StringAVLMap.is_empty_2 in H.
  remember (StringAVLMap.find key map) as f.
  symmetry in Heqf. destruct f; trivial.
  apply StringAVLMap.find_2 in Heqf.
  assert (Z := H key v Heqf).
  contradiction.
}
apply StringAVLMap.is_empty_1.
intros k v Maps.
apply StringAVLMap.find_1 in Maps.
rewrite (H k) in Maps.
discriminate.
Qed.

Lemma string_avl_map_empty_ok (Value: Type):
  StringAVLMap.is_empty (StringAVLMap.empty Value) = true.
Proof.
apply StringAVLMap.is_empty_1.
apply StringAVLMap.empty_1.
Qed.

Lemma string_avl_map_find_none {Value: Type} 
                               (m: StringAVLMap.t Value)
                               (k: String.string):
  StringAVLMap.find k m = None
   <->
  forall v: Value,
    ~ StringAVLMap.MapsTo k v m.
Proof.
split; intro H.
{
  intros v J.
  apply StringAVLMap.find_1 in J.
  rewrite H in J.
  discriminate.
}
remember (StringAVLMap.find k m) as f; destruct f; trivial.
symmetry in Heqf.
apply StringAVLMap.find_2 in Heqf.
exfalso. exact (H v Heqf).
Qed.

Lemma string_avl_map_insert_ok {Value: Type} 
                               (m: StringAVLMap.t Value)
                               (key: String.string)
                               (value: Value)
                               (x: String.string):
    StringAVLMap.find x (StringAVLMap.add key value m)
     = 
    if String.string_dec key x
      then Some value
      else StringAVLMap.find x m.
Proof.
destruct (string_dec key x) as [EQ|NE].
{
  apply StringAVLMap.find_1.
  now apply StringAVLMap.add_1.
}
remember (StringAVLMap.find x m) as f. symmetry in Heqf. destruct f.
{
  apply StringAVLMap.find_2 in Heqf.
  apply StringAVLMap.find_1.
  now apply StringAVLMap.add_2.
}
rewrite string_avl_map_find_none in *.
intros v H.
apply StringAVLMap.add_3 in H; try assumption.
exact (Heqf v H).
Qed.

Lemma string_avl_map_remove_ok {Value: Type} 
                               (m: StringAVLMap.t Value)
                               (key: String.string)
                               (x: String.string):
    StringAVLMap.find x (StringAVLMap.remove key m)
     = 
    if String.string_dec key x
      then None
      else StringAVLMap.find x m.
Proof.
destruct (string_dec key x) as [EQ|NE].
{
  apply string_avl_map_find_none.
  intros v H.
  assert(J: StringAVLMap.In x (StringAVLMap.remove key m)).
  { exists v. apply H. }
  exact (StringAVLMap.remove_1 EQ J).
}
remember (StringAVLMap.find x m) as f. symmetry in Heqf. destruct f.
{
  apply StringAVLMap.find_2 in Heqf.
  apply StringAVLMap.find_1.
  now apply StringAVLMap.remove_2.
}
rewrite string_avl_map_find_none in *.
intros v H.
apply StringAVLMap.remove_3 in H; try assumption.
exact (Heqf v H).
Qed.

Lemma string_avl_map_items_ok {Value: Type} 
                               (m: StringAVLMap.t Value)
                               (key: String.string):
   StringAVLMap.find key m = alist_lookup string_dec (StringAVLMap.elements m) key.
Proof.
remember (StringAVLMap.find (elt:=Value) key m) as f. symmetry in Heqf.
destruct f.
{
  (* the key is there *)
  apply StringAVLMap.find_2 in Heqf.
  apply StringAVLMap.elements_1 in Heqf.
  assert (N := StringAVLMap.elements_3w m).
  remember (StringAVLMap.elements m) as a. clear Heqa.
  induction a; cbn in *. { easy. }
  destruct a as (head, tail).
  destruct string_dec.
  {
    f_equal.
    inversion N. inversion Heqf; subst.
    destruct H4. (* this gets ugly starting from here *)
    cbn in *. assumption.
    clear H2 IHa N Heqf. exfalso.
    generalize tail H1. clear tail H1.
    induction a0. { easy. }
    destruct a. inversion H4; subst.
    {
      destruct H0. cbn in *. subst.
      intros.
      apply H1. now constructor.
    }
    intros.
    apply (IHa0 H0 tail).
    intro Z.
    apply H1.
    apply InA_cons_tl.
    assumption.
  }
  inversion N; inversion Heqf; subst.
  { destruct H4. cbn in *. contradiction. }
  apply IHa in H4; assumption.
}
(* the key is not there *)
assert (L := @StringAVLMap.elements_2 _ m).
remember (StringAVLMap.elements m) as a. clear Heqa.
induction a. { easy. }
destruct a as (head, tail).
cbn.
destruct string_dec.
{
  subst.
  assert (Q: InA (StringAVLMap.eq_key_elt (elt:=Value)) (head, tail) ((head, tail) :: a0)).
  { now constructor. }
  rewrite (StringAVLMap.find_1 (L head tail Q)) in Heqf.
  symmetry. assumption.
}
apply IHa.
intros.
apply L.
apply InA_cons_tl.
assumption.
Qed.

Lemma string_avl_map_items_nodup {Value: Type} 
                                  (m: StringAVLMap.t Value):
  NoDup (List.map fst (StringAVLMap.elements m)).
Proof.
assert (L := @StringAVLMap.elements_3w _ m).
remember (StringAVLMap.elements (elt:=Value) m) as a. clear Heqa.
induction a. { constructor. }
destruct a as (head, tail). cbn.
inversion L; subst.
constructor.
{
  intro H. apply H1.
  clear H1 H2 L IHa.
  induction a0. { easy. }
  inversion H; subst.
  { now apply InA_cons_hd. }
  apply InA_cons_tl.
  tauto.
}
apply IHa.
assumption.
Qed.

Definition string_avl_map_merge {Value: Type} (newer older: StringAVLMap.t Value)
:= fold_right
     (fun (p: string * Value) m =>
        match p with
        | (k, v) => StringAVLMap.add k v m
        end)
     older
     (StringAVLMap.elements newer).

Lemma string_avl_map_merge_ok {Value: Type} (newer m: StringAVLMap.t Value) (key: string):
  StringAVLMap.find key (string_avl_map_merge newer m)
   =
  match StringAVLMap.find key newer with
  | Some value => Some value
  | None => StringAVLMap.find key m
  end.
Proof.
unfold string_avl_map_merge. 
rewrite (string_avl_map_items_ok newer key).
remember (StringAVLMap.elements (elt:=Value) newer) as a.
clear Heqa.
induction a. { trivial. }
cbn in *.
destruct a as (k, v).
rewrite string_avl_map_insert_ok.
destruct (string_dec key k).
{
  subst.
  now destruct (string_dec k k).
}
destruct (string_dec k key). { subst. contradiction. }
apply IHa.
Qed.

Definition string_avl_map_impl (Value: Type): class string_dec Value (string_avl_map Value)
:= {|
     lookup map key := StringAVLMap.find key map;
     is_empty map := StringAVLMap.is_empty map;
     is_empty_ok := string_avl_map_is_empty_ok;
     empty := StringAVLMap.empty Value;
     empty_ok := string_avl_map_empty_ok Value;
     insert map key value := StringAVLMap.add key value map;
     insert_ok := string_avl_map_insert_ok;
     remove map key := StringAVLMap.remove key map;
     remove_ok := string_avl_map_remove_ok;
     items map := StringAVLMap.elements map;
     items_ok := string_avl_map_items_ok;
     items_nodup := string_avl_map_items_nodup;
     merge := string_avl_map_merge;
     merge_ok := string_avl_map_merge_ok;
   |}.

Section MapFacts.

Context {Key: Type} {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
         {Value: Type}
         {M: Type}
         {MapImpl: class KeyEqDec Value M}.

Lemma empty_lookup (query: Key):
  lookup empty query = None.
Proof.
apply is_empty_ok.
apply empty_ok.
Qed.

Definition of_alist (l: list (Key * Value))
: M
:= fold_right (fun (p: Key * Value) m => let (k, v) := p in insert m k v) empty l.

Lemma of_alist_ok (l: list (Key * Value)) (query: Key):
  lookup (of_alist l) query = alist_lookup KeyEqDec l query.
Proof.
induction l. { cbn. now apply empty_lookup. }
cbn. destruct a as (k, v). rewrite insert_ok.
destruct (KeyEqDec k query); destruct (KeyEqDec query k); try contradiction; subst; easy.
Qed.

End MapFacts.