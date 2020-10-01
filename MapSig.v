From Coq Require Import Eqdep_dec List.
Require Map.

(** MapSig implements a Map interface for [sig] types (that is, dependent pairs [{x: A| P x}]). *)

Section MapSig.

Context {Key: Type}
        {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
        {KeyIsGood: Key -> bool}
        {Value: Type}
        {M: Type}
        (MInst: Map.class KeyEqDec Value M).

Definition t := { m: M | forall key: Key, match Map.lookup m key with
                                          | Some _ => KeyIsGood key = true
                                          | None => True
                                          end }.

Definition key_sig := { key: Key | KeyIsGood key = true }.

Lemma key_sig_eq {a b: key_sig}
                 (H: proj1_sig a = proj1_sig b):
  a = b.
Proof.
destruct a as (x, p).
destruct b as (y, q).
cbn in H. subst y.
f_equal.
apply eq_proofs_unicity.
decide equality.
Qed.

Lemma key_sig_eq_dec_helper {a b: key_sig} (NE: proj1_sig a <> proj1_sig b):
  a <> b.
Proof.
intro H. subst b. contradiction.
Qed.

Definition key_sig_eq_dec (a b: key_sig)
: {a = b} + {a <> b}
:= match KeyEqDec (proj1_sig a) (proj1_sig b) as k return _ = k -> _ with
   | left e =>fun E => left (key_sig_eq e)
   | right n => fun E => right (key_sig_eq_dec_helper n)
   end eq_refl.

Definition lookup (m: t) (k: key_sig)
: option Value
:= Map.lookup (proj1_sig m) (proj1_sig k).

Definition is_empty (m: t)
: bool
:= Map.is_empty (proj1_sig m).

Lemma is_empty_ok (m: t):
    is_empty m = true 
     <->
    forall key: key_sig,
      lookup m key = None.
Proof.
unfold is_empty. unfold lookup.
rewrite Map.is_empty_ok.
assert (MOk := proj2_sig m). cbn in MOk.
split. { intros H key. apply H. }
intros H key.
assert (MOkKey := MOk key).
remember (Map.lookup (proj1_sig m) key) as v.
destruct v. 2:trivial.
assert (A := (H (exist _ key MOkKey))). cbn in A.
rewrite Heqv. rewrite A. trivial.
Qed.

Local Lemma empty_spec (key: Key):
   match Map.lookup Map.empty key with
   | Some _ => KeyIsGood key = true
   | None => True
   end.
Proof.
now rewrite Map.empty_lookup.
Qed.

Definition empty
: t
:= exist _ Map.empty empty_spec.

Lemma empty_ok: is_empty empty = true.
Proof.
unfold is_empty. cbn. now rewrite Map.empty_ok.
Qed.

Local Lemma insert_spec (m: t) (key: key_sig) (value: Value) (query: Key):
    match Map.lookup (Map.insert (proj1_sig m) (proj1_sig key) value) query with
    | Some _ => KeyIsGood query = true
    | None => True
    end.
Proof.
rewrite Map.insert_ok.
destruct (KeyEqDec (proj1_sig key) query).
{ subst query. apply (proj2_sig key). }
exact (proj2_sig m query).
Qed.

Definition insert (m: t) (key: key_sig) (value: Value)
: t
:= exist _ (Map.insert (proj1_sig m) (proj1_sig key) value) (insert_spec m key value).

Lemma insert_ok (m: t) (key: key_sig) (value: Value) (x: key_sig):
  lookup (insert m key value) x
   = 
  if key_sig_eq_dec key x
    then Some value
    else lookup m x.
Proof.
unfold lookup. unfold insert. cbn. rewrite Map.insert_ok.
unfold key_sig_eq_dec.
remember (KeyEqDec (proj1_sig key) (proj1_sig x)) as e.
now destruct e.
Qed.

Local Lemma remove_spec (m: t) (key: key_sig) (query: Key):
    match Map.lookup (Map.remove (proj1_sig m) (proj1_sig key)) query with
    | Some _ => KeyIsGood query = true
    | None => True
    end.
Proof.
rewrite Map.remove_ok.
destruct (KeyEqDec (proj1_sig key) query). { trivial. }
exact (proj2_sig m query).
Qed.

Definition remove (m: t) (key: key_sig)
: t
:= exist _ (Map.remove (proj1_sig m) (proj1_sig key)) (remove_spec m key).

Lemma remove_ok (m: t) (key: key_sig) (x: key_sig):
  lookup (remove m key) x
   = 
  if key_sig_eq_dec key x
    then None
    else lookup m x.
Proof.
unfold lookup. unfold remove. cbn. rewrite Map.remove_ok.
unfold key_sig_eq_dec.
remember (KeyEqDec (proj1_sig key) (proj1_sig x)) as e.
now destruct e.
Qed.

Local Lemma mark_helper_head {l : list (Key * Value)}
                             {h: Key * Value}
                             {t: list (Key * Value)}
                             (Ok : Forall (fun kv : Key * Value => KeyIsGood (fst kv) = true) l)
                             (E: l = h :: t):
  KeyIsGood (fst h) = true.
Proof.
subst l. inversion Ok. assumption.
Qed.

Local Lemma mark_helper_tail {l : list (Key * Value)}
                             {h: Key * Value}
                             {t: list (Key * Value)}
                             (Ok : Forall (fun kv : Key * Value => KeyIsGood (fst kv) = true) l)
                             (E: l = h :: t):
  Forall (fun kv : Key * Value => KeyIsGood (fst kv) = true) t.
Proof.
subst l. inversion Ok. assumption.
Qed.

Fixpoint mark (l: list (Key * Value))
              (Ok: Forall (fun kv: Key * Value => KeyIsGood (fst kv) = true) l)
: list (key_sig * Value)
:= match l as l' return l = l' -> _ with
   | nil => fun _ => nil
   | cons h t => fun E => cons (exist _ (fst h) (mark_helper_head Ok E), snd h) 
                               (mark t (mark_helper_tail Ok E))
   end eq_refl.

Lemma mark_map_proj1_sig (l: list (Key * Value))
                         (Ok: Forall (fun kv: Key * Value => KeyIsGood (fst kv) = true) l):
  map (@proj1_sig _ _) (map fst (mark l Ok)) = map fst l.
Proof.
induction l. { easy. }
cbn. f_equal. apply IHl.
Qed.

Local Lemma items_helper (m: t):
  Forall (fun kv : Key * Value => KeyIsGood (fst kv) = true)
         (Map.items (proj1_sig m)).
Proof.
assert (MOk := proj2_sig m).
assert (Ok: forall key: Key,
              match Map.alist_lookup KeyEqDec (Map.items (proj1_sig m)) key with
              | Some value => Map.lookup (proj1_sig m) key = Some value
              | None => True
              end).
{
  intro key.
  rewrite<- Map.items_ok.
  now destruct Map.lookup.
}
assert (ND := Map.items_nodup (proj1_sig m)).
induction (Map.items (proj1_sig m)); constructor.
{ (* goal: KeyIsGood (fst a) = true *)
  assert (MOkA := MOk (fst a)).
  assert (OkA := Ok (fst a)).
  destruct a as (key, value). cbn in *.
  destruct (KeyEqDec key key). 2:contradiction.
  now destruct (Map.lookup (proj1_sig m) key).
}
apply IHl. 2:{ now inversion ND. }
intro query. cbn in Ok.
assert (Q := Ok query).
destruct a as (key, value).
destruct (KeyEqDec query key). 2:{ exact Q. }
subst query.
cbn in ND.
inversion ND.
rewrite (Map.alist_lookup_not_in KeyEqDec l key) by assumption.
trivial.
Qed.

Definition items (m: t) := mark (Map.items (proj1_sig m)) (items_helper m).

Lemma items_ok (m: t) (key: key_sig):
  lookup m key = Map.alist_lookup key_sig_eq_dec (items m) key.
Proof.
unfold lookup. rewrite Map.items_ok. unfold items.
remember (items_helper m) as F. clear HeqF. revert F.
induction (Map.items (proj1_sig m)); intro F. { easy. }
cbn. destruct a as (k, v). destruct key as (query, QueryIsGood).
unfold key_sig_eq_dec. cbn in *.
remember (KeyEqDec query k) as e. destruct e. { trivial. }
apply IHl.
Qed.

Lemma key_sig_list_not_in {l: list key_sig} {key: key_sig}
                          (H: ~ In (proj1_sig key) (map (@proj1_sig _ _) l)):
  ~ In key l.
Proof.
induction l. { easy. }
intro I. inversion I; subst; cbn in *; tauto.
Qed.

Lemma key_sig_list_nodup {l: list key_sig}
                         (H: NoDup (map (@proj1_sig _ _) l)):
  NoDup l.
Proof.
induction l. { constructor. }
constructor.
{ 
  inversion H. subst.
  induction l. { easy. }
  apply key_sig_list_not_in.
  assumption.
}
apply IHl. now inversion H.
Qed.

Lemma items_nodup (m: t):
  NoDup (map fst (items m)).
Proof.
apply key_sig_list_nodup.
unfold items.
rewrite mark_map_proj1_sig.
apply Map.items_nodup.
Qed.

Local Lemma merge_spec (newer older: t) (key: Key):
  match Map.lookup (Map.merge (proj1_sig newer) (proj1_sig older)) key with
  | Some _ => KeyIsGood key = true
  | None => True
  end.
Proof.
rewrite Map.merge_ok.
assert (OkN := proj2_sig newer key).
assert (OkO := proj2_sig older key).
now destruct (Map.lookup (proj1_sig newer) key).
Qed.

Definition merge (newer older: t)
: t
:= exist _ (Map.merge (proj1_sig newer) (proj1_sig older)) (merge_spec newer older).

Lemma merge_ok (newer older: t) (key: key_sig):
    lookup (merge newer older) key
     =
    match lookup newer key with
    | Some value => Some value
    | None => lookup older key
    end.
Proof.
unfold lookup. cbn.
rewrite Map.merge_ok.
trivial.
Qed.


Local Lemma map_endo_spec (m: t) (f: Value -> Value) (key: Key):
  match Map.lookup (Map.map_endo (proj1_sig m) f) key with
  | Some _ => KeyIsGood key = true
  | None => True
  end.
Proof.
rewrite Map.map_endo_ok.
assert (C := proj2_sig m key).
now destruct Map.lookup.
Qed.

Definition map_endo (m: t) (f: Value -> Value)
: t
:= exist _ (Map.map_endo (proj1_sig m) f) (map_endo_spec m f).

Lemma map_endo_ok (m: t) (f: Value -> Value) (key: key_sig):
   lookup (map_endo m f) key = match lookup m key with
                               | Some value => Some (f value)
                               | None => None
                               end.
Proof.
unfold map_endo. unfold lookup. cbn.
apply Map.map_endo_ok.
Qed.

Instance instance: Map.class key_sig_eq_dec Value t
:= {| Map.lookup      := lookup
    ; Map.is_empty    := is_empty
    ; Map.is_empty_ok := is_empty_ok
    ; Map.empty       := empty
    ; Map.empty_ok    := empty_ok
    ; Map.insert      := insert
    ; Map.insert_ok   := insert_ok
    ; Map.remove      := remove
    ; Map.remove_ok   := remove_ok
    ; Map.items       := items
    ; Map.items_ok    := items_ok
    ; Map.items_nodup := items_nodup
    ; Map.merge       := merge
    ; Map.merge_ok    := merge_ok
    ; Map.map_endo    := map_endo
    ; Map.map_endo_ok := map_endo_ok
   |}.

End MapSig.