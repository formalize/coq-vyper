From Coq Require Import String List ListSet Arith NArith.
From Coq Require PropExtensionality.
From Vyper Require Map FSet MapSig.
From Vyper Require Import Config Graph.Depthmap.

Record generic_calldag {C: VyperConfig} 
                       {Decl: Type}
                       (callset: Decl -> string_set)
                       (may_call_undeclared: bool)
:= {
  cd_decls: string_map Decl;
  cd_depthmap: string -> option nat;
  cd_depthmap_ok:
    let _ := string_map_impl in
    forall name: string,
      match Map.lookup cd_decls name with
      | None => True
      | Some decl =>
          match cd_depthmap name with
          | None => False
          | Some x =>
              let _ := string_set_impl in
              FSet.for_all (callset decl)
                           (fun callee => match cd_depthmap callee with
                                          | None => may_call_undeclared
                                          | Some y => y <? x
                                          end)
               = true
            end
      end;
}.
Arguments cd_decls       {C Decl callset may_call_undeclared}.
Arguments cd_depthmap    {C Decl callset may_call_undeclared}.
Arguments cd_depthmap_ok {C Decl callset may_call_undeclared}.

(* This is for compatibility with an older definition via cd_declmap. *)
Definition cd_declmap {C: VyperConfig}
                      {Decl: Type}
                      {callset: Decl -> string_set}
                      {may_call_undeclared: bool}
                      (d: generic_calldag callset may_call_undeclared)
:= let _ := string_map_impl in
   Map.lookup (cd_decls d).

(**
  A functional context is the result of looking up a function by name in a calldag.
 *)
Record fun_ctx {C: VyperConfig}
               {Decl: Type}
               {decl_callset: Decl -> string_set}
               {may_call_undeclared: bool}
               (cd: generic_calldag decl_callset may_call_undeclared)
               (bound: nat) := {
  fun_name: string;
  fun_depth: nat;
  fun_depth_ok: cd_depthmap cd fun_name = Some fun_depth;
  fun_decl: Decl;
  fun_decl_ok: cd_declmap cd fun_name = Some fun_decl;
  fun_bound_ok: fun_depth <? bound = true;
}.
Arguments fun_name     {C _ _ _ _ _}.
Arguments fun_depth    {C _ _ _ _ _}.
Arguments fun_depth_ok {C _ _ _ _ _}.
Arguments fun_decl     {C _ _ _ _ _}.
Arguments fun_decl_ok  {C _ _ _ _ _}.
Arguments fun_bound_ok {C _ _ _ _ _}.

Local Lemma make_fun_ctx_helper {C: VyperConfig}
                                {Decl: Type}
                                {decl_callset: Decl -> string_set}
                                {may_call_undeclared: bool}
                                {cd: generic_calldag decl_callset may_call_undeclared}
                                {name: string}
                                {d: Decl}
                                (Ed: cd_declmap cd name = Some d)
                                (Edepth: cd_depthmap cd name = None):
  False.
Proof.
assert (W := cd_depthmap_ok cd name).
unfold cd_declmap in Ed.
rewrite Ed in W. rewrite Edepth in W. exact W.
Qed.

(** Create a function context from scratch (meaning that there's no pre-existing bound). *)
Definition make_fun_ctx_and_bound {C: VyperConfig}
                                  {Decl: Type}
                                  {decl_callset: Decl -> string_set}
                                  {may_call_undeclared: bool}
                                  (cd: generic_calldag decl_callset may_call_undeclared)
                                  (name: string)
: option { bound: nat & fun_ctx cd bound }
:= match cd_declmap cd name as maybe_d return _ = maybe_d -> _ with
   | None => fun _ => None
   | Some d => fun Ed =>
      match cd_depthmap cd name as depth' return _ = depth' -> _ with
      | None => fun Edepth => False_rect _ (make_fun_ctx_helper Ed Edepth)
      | Some depth => fun Edepth => Some (existT _
                                                 (S depth)
                                                 {| fun_name := name
                                                  ; fun_decl := d
                                                  ; fun_decl_ok := Ed
                                                  ; fun_depth := depth
                                                  ; fun_depth_ok := Edepth
                                                  ; fun_bound_ok := proj2 (Nat.ltb_lt _ _)
                                                                          (Nat.lt_succ_diag_r _)
                                                 |})
      end eq_refl
   end eq_refl.

(*************************************************************************************************)
(* Here's some stuff to facilitate calldag translations: *)

(* This might be easier with monads. *)
Fixpoint alist_maybe_map {Key Value Value' Err: Type}
                         (KeyEqDec: forall x y: Key, {x = y} + {x <> y})
                         (a: list (Key * Value)) (f: Value -> Err + Value')
{struct a}
: Err + list (Key * Value')
:= match a with
   | nil => inr nil
   | cons (k, v) t =>
      match f v with
      | inl err => inl err
      | inr fv =>
          match alist_maybe_map KeyEqDec t f with
          | inl err => inl err
          | inr mt => inr (cons (k, fv) mt)
          end
      end
   end.

Lemma alist_maybe_map_ok {Key Value Value' Err: Type}
                         {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
                         {a: list (Key * Value)}
                         {a': list (Key * Value')}
                         {f: Value -> Err + Value'}
                         (E: alist_maybe_map KeyEqDec a f = inr a')
                         (key: Key):
  match Map.alist_lookup KeyEqDec a key with
  | Some v =>
      match f v with
      | inl _ => False
      | inr fv => Map.alist_lookup KeyEqDec a' key = Some fv
      end
  | None => Map.alist_lookup KeyEqDec a' key =None
  end.
Proof.
revert a' E.
induction a as [|(k, v)]; intros. { cbn in *. inversion E. now subst. }
cbn in *.
remember (KeyEqDec key k) as key_k.
destruct key_k.
{
  destruct (f v). { discriminate. }
  subst.
  destruct (alist_maybe_map KeyEqDec a f). { discriminate. }
  inversion E. subst. cbn.
  now destruct (KeyEqDec k k).
}
destruct (f v). { discriminate. }
subst.
destruct (alist_maybe_map KeyEqDec a f). { discriminate. }
inversion E. subst. cbn.
rewrite<- Heqkey_k.
now apply IHa.
Qed.

Definition map_maybe_map {Key Err: Type} {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
                         {Value: Type}
                         {M: Type}
                         {MapImpl: Map.class KeyEqDec Value M}
                         {Value': Type} {M': Type} {MapImpl': Map.class KeyEqDec Value' M'}
                         (m: M)  (f: Value -> Err + Value')
: Err + M'
:= match alist_maybe_map KeyEqDec (Map.items m) f with
   | inl err => inl err
   | inr m' => inr (Map.of_alist m')
   end.

Lemma map_maybe_map_ok {Key Err: Type} {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
                       {Value: Type}
                       {M: Type}
                       {MapImpl: Map.class KeyEqDec Value M}
                       {Value': Type} {M': Type} {MapImpl': Map.class KeyEqDec Value' M'}
                       {m: M}
                       {f: Value -> Err + Value'}
                       {m': M'}
                       (E: map_maybe_map m f = inr m')
                       (key: Key):
  match Map.lookup m key with
  | Some v =>
      match f v with
      | inl _ => False
      | inr fv => Map.lookup m' key = Some fv
      end
  | None => Map.lookup m' key =None
  end.
Proof.
unfold map_maybe_map in E.
remember (alist_maybe_map KeyEqDec (Map.items m) f) as a'.
destruct a'. { discriminate. }
assert (L := alist_maybe_map_ok (eq_sym Heqa') key).
rewrite Map.items_ok.
destruct (Map.alist_lookup KeyEqDec (Map.items m) key); inversion E; subst.
{
  destruct (f v). { easy. }
  now rewrite Map.of_alist_ok.
}
now rewrite Map.of_alist_ok.
Qed.

(**************************************************************************************************)

(** Convert a list of declarations into a dictionary.
    A duplicate declaraton name will result in an error.
 *)
Fixpoint make_declmap {C: VyperConfig} {Decl: Type} (get_decl_name: Decl -> string) (decls: list Decl)
: string + string_map Decl
:= let _ := string_map_impl in
   match decls with
   | nil => inr Map.empty
   | (h :: t)%list =>
       match make_declmap get_decl_name t with
       | inl err => inl err
       | inr m => let name := get_decl_name h in
                  match Map.lookup m name with
                  | Some _ => inl ("duplicate name: " ++ name)%string
                  | None => inr (Map.insert m name h)
                  end
       end
   end.

(** Same as [make_declmap] but doesn't check for duplicates. *)
Fixpoint make_declmap_unchecked {C: VyperConfig} {Decl: Type}
                                (get_decl_name: Decl -> string)
                                (decls: list Decl)
: string_map Decl
:= let _ := string_map_impl in
   match decls with
   | nil => Map.empty
   | (h :: t)%list => Map.insert (make_declmap_unchecked get_decl_name t) (get_decl_name h) h
   end.

(** An alternative implementation of [make_declmap_unchecked]. *)
Lemma make_declmap_unchecked_alt {C: VyperConfig} {Decl: Type}
                                 (get_decl_name: Decl -> string)
                                 (decls: list Decl):
  make_declmap_unchecked get_decl_name decls
   =
  let _ := string_map_impl in
  Map.of_alist (map (fun d => (get_decl_name d, d)) decls).
Proof.
induction decls. { easy. }
cbn in *. now rewrite IHdecls.
Qed.

Lemma make_declmap_nodup {C: VyperConfig} {Decl: Type}
                         (get_decl_name: Decl -> string)
                         (decls: list Decl)
                         (Ok: NoDup (List.map get_decl_name decls)):
  make_declmap get_decl_name decls = inr (make_declmap_unchecked get_decl_name decls).
Proof.
induction decls. { easy. }
cbn in Ok. rewrite NoDup_cons_iff in Ok. destruct Ok as (NotIn, NoDupTail).
cbn. rewrite (IHdecls NoDupTail).
rewrite make_declmap_unchecked_alt. cbn.
rewrite Map.of_alist_ok.
rewrite Map.alist_lookup_not_in. { trivial. }
now rewrite map_map.
Qed.

(***************************************************************************)

Definition has {C: VyperConfig} {Value: Type}
               (m: string_map Value)
               (key: string)
: bool
:= let _ := string_map_impl in
   match Map.lookup m key with
   | Some _ => true
   | None => false
   end.

Definition declared_name {C: VyperConfig} {Decl: Type} (declmap: string_map Decl)
: Type
:= {name: string | has declmap name = true}.

Lemma declared_name_irrel {C: VyperConfig} {Decl: Type} (declmap: string_map Decl)
                          (a b: declared_name declmap)
                          (E: proj1_sig a = proj1_sig b):
  a = b.
Proof.
destruct a as (a_name, a_ok).
destruct b as (b_name, b_ok).
cbn in E. subst.
enough (a_ok = b_ok) by now subst.
apply Eqdep_dec.eq_proofs_unicity.
decide equality.
Qed.

Local Lemma decl_of_declared_name_helper {C: VyperConfig} {Decl: Type} {declmap: string_map Decl}
                                         (query: declared_name declmap)
                                         (E: let _ := string_map_impl in
                                             Map.lookup declmap (proj1_sig query) = None)
                                         (ok: has declmap (proj1_sig query) = true):
  False.
Proof.
unfold has in ok. cbn in E.
now destruct Map.lookup.
Qed.

Definition decl_of_declared_name {C: VyperConfig} {Decl: Type} {declmap: string_map Decl}
                                 (query: declared_name declmap)
: Decl
:= let _ := string_map_impl in
   match Map.lookup declmap (proj1_sig query) as result return _ = result -> _ with
   | Some x => fun _ => x
   | None => fun E => False_rect _ (decl_of_declared_name_helper query E (proj2_sig query))
   end eq_refl.

Definition Calls {C: VyperConfig} {Decl: Type} {declmap: string_map Decl}
                 (callset: Decl -> string_set)
                 (caller callee: declared_name declmap)
: Prop
:= let _ := string_set_impl in
   FSet.has (callset (decl_of_declared_name caller)) (proj1_sig callee) = true.

(** Build a list of dependent pairs from a list and a Forall condition. *)
Fixpoint list_exist {T: Type} {P: T -> Prop} {l: list T} (F: Forall P l)
: list {x: T | P x}
:= match l as l' return l = l' -> _ with
   | nil => fun _ => nil
   | h :: t => fun E => let F': Forall P (h :: t) := eq_ind l (Forall P) F (h :: t) E in
                        exist _ h (Forall_inv F') :: list_exist (Forall_inv_tail F')
   end eq_refl.

Lemma list_exist_in {T: Type} {P: T -> Prop} {l: list T} (F: Forall P l)
                    (Irrel: forall (a b: {x: T | P x}),
                              proj1_sig a = proj1_sig b -> a = b)
                    (x: T) (Px: P x):
  In x l <-> In (exist _ x Px) (list_exist F).
Proof.
induction l as [|h]. { easy. }
cbn. split; intro H; case H; clear H; intro H.
{ left. subst. now apply Irrel. }
{ right. now apply IHl. }
{ left. now inversion H. }
right. now apply IHl in H.
Qed.

Definition all_names {C: VyperConfig} {Decl: Type} (declmap: string_map Decl)
:= let _ := string_map_impl in
   map fst (Map.items declmap).

Lemma all_names_ok {C: VyperConfig} {Decl: Type} (declmap: string_map Decl) (name: string):
  In name (all_names declmap)  <->  has declmap name = true.
Proof.
unfold has. unfold all_names.
assert (ItemsOk := let _ := string_map_impl in Map.items_ok declmap name).
rewrite ItemsOk. clear ItemsOk.
remember (Map.items declmap) as l. clear Heql. induction l as [|head]. { easy. }
destruct head as (key, value). cbn.
destruct (string_dec name key) as [E|NE]. { symmetry in E. tauto. }
assert (NE': key <> name). { intro H. symmetry in H. contradiction. }
tauto.
Qed.

Lemma all_declared_names_helper {C: VyperConfig} {Decl: Type} (declmap: string_map Decl):
  let _ := string_map_impl in
  Forall (fun name => has declmap name = true) (all_names declmap).
Proof.
rewrite Forall_forall. intros name. apply all_names_ok.
Qed.

Definition all_declared_names {C: VyperConfig} {Decl: Type} (declmap: string_map Decl)
: list (declared_name declmap)
:= list_exist (all_declared_names_helper declmap).

Lemma all_declared_names_ok {C: VyperConfig} {Decl: Type} (declmap: string_map Decl)
                            (d: declared_name declmap):
  In d (all_declared_names declmap).
Proof.
destruct d as (name, is_declared).
apply (list_exist_in (all_declared_names_helper declmap)
                     (declared_name_irrel declmap)).
unfold all_names.
unfold has in is_declared.
assert (ItemsOk := let _ := string_map_impl in Map.items_ok declmap name).
destruct (Map.lookup declmap name). 2:{ discriminate. }
remember (Map.items declmap) as l. clear Heql. induction l as [|head]. { easy. }
destruct head as (head_name, head_decl).
cbn in *.
destruct string_dec. { left. now symmetry. }
right. exact (IHl ItemsOk).
Qed.

Definition declset {C: VyperConfig} {Decl: Type} (declmap: string_map Decl)
: string_set
:= let _ := string_set_impl in
   let _ := string_map_impl in
   FSet.from_list (map fst (Map.items declmap)).

(** The list of called functions but restricted to the actually declared symbols
    (not actually declared functions because with parameterized [Decl]
    we have no way to distinguish function declarations from other declarations)
 *)
Definition restricted_call_list {C: VyperConfig} {Decl: Type}
                                {declmap: string_map Decl}
                                (callset: Decl -> string_set)
                                (d: declared_name declmap)
: list string
:= let _ := string_set_impl in
   set_inter string_dec (FSet.to_list (callset (decl_of_declared_name d))) (all_names declmap).

Lemma restricted_call_list_nodup {C: VyperConfig} {Decl: Type}
                                 (declmap: string_map Decl)
                                 (callset: Decl -> string_set)
                                 (d: declared_name declmap):
  NoDup (restricted_call_list callset d).
Proof.
apply set_inter_nodup.
{ apply FSet.to_list_nodup. }
apply Map.items_nodup.
Qed.

Lemma restricted_call_list_all_declared {C: VyperConfig} {Decl: Type}
                                        {declmap: string_map Decl}
                                        (callset: Decl -> string_set)
                                        (d: declared_name declmap):
  Forall (fun name => has declmap name = true)
         (restricted_call_list callset d).
Proof.
rewrite Forall_forall. intros name H.
unfold restricted_call_list in H.
apply set_inter_elim2 in H.
revert name H. rewrite<- Forall_forall.
apply all_declared_names_helper.
Qed.

Definition declared_call_list {C: VyperConfig} {Decl: Type}
                              {declmap: string_map Decl}
                              (callset: Decl -> string_set)
                              (d: declared_name declmap)
: list (declared_name declmap)
:= list_exist (restricted_call_list_all_declared callset d).


Lemma declared_call_list_ok {C: VyperConfig} {Decl: Type}
                            {declmap: string_map Decl}
                            (callset: Decl -> string_set)
                            (a b: declared_name declmap):
  In b (declared_call_list callset a)  <->  Calls callset a b.
Proof.
unfold Calls. unfold declared_call_list.
destruct b as (b_name, b_ok).
rewrite<- (list_exist_in (restricted_call_list_all_declared callset a)
            (declared_name_irrel declmap)).
unfold restricted_call_list. cbn.
rewrite FSet.has_to_list.
remember (FSet.to_list (callset (decl_of_declared_name a))) as l. destruct Heql.
rewrite ListSet2.set_mem_true.
rewrite set_inter_iff.
enough (In b_name (all_names declmap)) by tauto.
now apply all_names_ok.
Qed.

Definition make_depthmap {C: VyperConfig} {Decl: Type}
                         (declmap: string_map Decl)
                         (callset: Decl -> string_set)
: Cycle.t (Calls callset) +
  { f: declared_name declmap -> N |
      forall a b : declared_name declmap,
        Calls callset a b -> (f b < f a)%N }
:= cycle_or_depthmap (Calls callset) (all_declared_names declmap) (all_declared_names_ok declmap)
     (MapSig.instance
       (string_map_impl ({start : declared_name declmap & Path.t (Calls callset) start} * N)))
     (declared_call_list callset)
     (declared_call_list_ok callset).

Definition cycle_error_message {C: VyperConfig} {Decl: Type}
                               (declmap: string_map Decl)
                               {callset: Decl -> string_set}
                               (cycle: Cycle.t (@Calls C Decl declmap callset))
: string
:= let fix path_to_string {v: declared_name declmap} (p: Path.t (Calls callset) v)
       := match p with
          | Path.Nil _ => proj1_sig v
          | Path.Cons _ _ rest => (proj1_sig v ++ " -> " ++ path_to_string rest)%string
          end
   in ("recursion is not allowed but a call cycle is detected: " ++ path_to_string (Cycle.path cycle)).


(** This is an adapter between [make_depthmap],
    which returns a total function on declared names into N,
    and [generic_calldag], which wants a partial function on all strings. 
 *)
Definition adapt_depthmap {C: VyperConfig} {Decl} (callset: Decl -> string_set) (declmap: string_map Decl)
                          (depthmap: {f: declared_name declmap -> N |
                                       forall a b : declared_name declmap,
                                         Calls callset a b -> (f b < f a)%N})
                          (name: string)
: option nat
:= (if has declmap name as has' return _ = has' -> _
      then fun E => Some (N.to_nat (proj1_sig depthmap (exist _ name E)))
      else fun _ => None) eq_refl.

Lemma adapt_depthmap_ok {C: VyperConfig} {Decl} (callset: Decl -> string_set)
                        (declmap: string_map Decl)
                        (depthmap:
                          {f: declared_name declmap -> N |
                             forall a b: declared_name declmap,
                               Calls callset a b -> (f b < f a)%N})
                        (name: string):
   let _ := string_map_impl in
   match Map.lookup declmap name with
   | Some decl =>
       match adapt_depthmap callset declmap depthmap name with
       | Some x =>
           let _ := string_set_impl in
           FSet.for_all (callset decl)
             (fun callee : string =>
              match adapt_depthmap callset declmap depthmap callee with
              | Some y => y <? x
              | None => true
              end) = true
       | None => False
       end
   | None => True
   end.
Proof.
unfold adapt_depthmap.
remember (Map.lookup declmap name) as d.
destruct d. 2:{ trivial. }
remember (fun x =>
      let _ := @string_set_impl C in
      FSet.for_all (callset d)
      (fun callee : string =>
       match
         (if has declmap callee as has' return (has declmap callee = has' -> option nat)
          then
           fun E : has declmap callee = true =>
           Some
             (N.to_nat
                (proj1_sig depthmap (exist (fun name0 : string => has declmap name0 = true) callee E)))
          else fun _ : has declmap callee = false => None) eq_refl
       with
       | Some y => y <? x
       | None => true
       end) = true) as P.
assert (T: has declmap name = true). { unfold has in *. now rewrite<- Heqd. }
assert (R: forall name' (E': has declmap name' = true),
   (if has declmap name' as has' return (has declmap name' = has' -> option nat)
   then
    fun E : has declmap name' = true =>
    Some
      (N.to_nat (proj1_sig depthmap (exist (fun name0 : string => has declmap name0 = true) name' E)))
   else fun _ : has declmap name' = false => None) eq_refl =
  Some
      (N.to_nat (proj1_sig depthmap (exist (fun name0 : string => has declmap name0 = true) name' E')))).
{
  intros.
  remember (fun E =>
              Some (N.to_nat
                     (proj1_sig depthmap 
                        (exist (fun name0 : string => has declmap name0 = true) name' E)))) as f.
  match goal with
  |- _ = ?rhs => replace rhs with (f E') by now subst
  end.
  clear Heqf.
  destruct (has declmap name'). { f_equal. apply Eqdep_dec.eq_proofs_unicity. decide equality. }
  discriminate.
}
rewrite (R name T). subst P. cbn.
rewrite FSet.for_all_ok.
intros callee CalleeOk.
remember (fun y: nat =>
    match
      N.to_nat (proj1_sig depthmap (exist (fun name0 : string => has declmap name0 = true) name T))
    with
    | 0 => false
    | S m' => y <=? m'
    end) as some_branch.
assert (Ok: forall E: has declmap callee = true,
            some_branch
              (N.to_nat
                (proj1_sig depthmap
                           (exist (fun name0 : string => has declmap name0 = true) callee E))) = true).
{
  intro E. subst.
  assert (K := proj2_sig depthmap (exist (fun name0 : string => has declmap name0 = true) name T)
                         (exist _ callee E)).
  unfold Calls in K.
  assert (D:
     decl_of_declared_name (exist (fun name0 : string => has declmap name0 = true) name T) = d).
  {
    unfold decl_of_declared_name.
    cbn.
    remember (fun E0 : Map.lookup declmap name = None =>
    False_rect Decl
      (Calldag.decl_of_declared_name_helper
         (exist (fun name0 : string => has declmap name0 = true) name T) E0 T)) as bad.
    clear Heqbad.
    destruct (Map.lookup declmap name). { now inversion Heqd. } discriminate.
  }
  rewrite D in K. clear D. cbn in K.
  assert (L := K CalleeOk). clear K.
  unfold Calls in *. (* invisible fix *)
  remember (proj1_sig depthmap (exist (fun name : string => has declmap name = true) name T)) as x.
  remember (proj1_sig depthmap (exist (fun name : string => has declmap name = true) callee E)) as y.
  clear Heqx Heqy.
  apply N.compare_lt_iff in L.
  rewrite N2Nat.inj_compare in L.
  apply nat_compare_lt in L.
  destruct (N.to_nat x). { now apply Nat.nlt_0_r in L. }
  rewrite Nat.leb_le.
  now apply lt_n_Sm_le.
}
clear Heqsome_branch.
(* caveman's destruct *)
assert (X: forall x: bool, x = true \/ x = false). { destruct x; tauto. }
assert (H := X (has declmap callee)). clear X.
case H; clear H; intro H.
{ rewrite (R callee H). apply Ok. }
clear R.
enough (R: (if has declmap callee as has' return (has declmap callee = has' -> option nat)
             then
              fun E : has declmap callee = true =>
              Some
                (N.to_nat (proj1_sig depthmap (exist (fun name0 : string => has declmap name0 = true) callee E)))
             else fun _ : has declmap callee = false => None) eq_refl = None).
{ now rewrite R. }
clear Ok.
remember (fun E =>
            Some (N.to_nat
                   (proj1_sig depthmap 
                      (exist (fun name0 : string => has declmap name0 = true) callee E)))) as f.
clear Heqf.
now destruct (has declmap callee).
Qed.

(** Build a calldag from a list of declarations (the declaration type is polymorphic).
    Two errors are possible: duplicated declaration and a call cycle.
    Calling an undeclared function is allowed since L10 does that to call builtin functions.
 *)
Definition make_calldag {C: VyperConfig} {Decl} 
                        (decl_name: Decl -> string)
                        (callset: Decl -> string_set)
                        (decls: list Decl)
: string + generic_calldag callset true
:= match make_declmap decl_name decls with
   | inl err => inl err
   | inr declmap =>
      match make_depthmap declmap callset with
      | inl cycle => inl (cycle_error_message declmap cycle)
      | inr depthmap =>
          inr {| cd_decls := declmap
               ; cd_depthmap := adapt_depthmap callset declmap depthmap
               ; cd_depthmap_ok := adapt_depthmap_ok callset declmap depthmap
              |}
      end
   end.

(***************************************************************************************************)

Local Lemma calldag_maybe_map_helper {C: VyperConfig}
                          {Decl Decl': Type}
                          {callset: Decl -> string_set}
                          {may_call_undeclared: bool}
                          {callset': Decl' -> string_set}
                          (cd: generic_calldag callset may_call_undeclared)
                          (f: Decl -> string + Decl')
                          (decls': string_map Decl')
                          (NoNewCalls: let _ := string_set_impl in
                                       forall (d: Decl) (d': Decl'),
                                         f d = inr d'
                                          ->
                                         FSet.is_subset (callset' d') (callset d) = true):
     let _ := string_map_impl Decl  in
     let _ := string_map_impl Decl' in
     forall (E: map_maybe_map (cd_decls cd) f = inr decls')
            (name: string),
       match Map.lookup decls' name with
       | Some decl =>
           match cd_depthmap cd name with
           | Some x =>
               let _ := string_set_impl in
               FSet.for_all (callset' decl)
                 (fun callee: string =>
                  match cd_depthmap cd callee with
                  | Some y => y <? x
                  | None => may_call_undeclared
                  end) = true
           | None => False
           end
       | None => True
       end.
Proof.
intros.
remember (Map.lookup _ name) as m.
destruct m. 2:trivial.
assert (D := cd_depthmap_ok cd name).
assert (F := map_maybe_map_ok E name).
destruct (Map.lookup (cd_decls cd) name). 2:{ now rewrite F in Heqm. }
destruct (cd_depthmap cd name). 2:assumption.
rewrite FSet.for_all_ok. rewrite FSet.for_all_ok in D.
intros x H.
remember (f _) as d'.
destruct d'. { contradiction. }
rewrite<- Heqm in F. inversion F; subst.
assert (NNC := NoNewCalls _ _ (eq_sym Heqd')).
rewrite FSet.is_subset_ok in NNC.
assert (NNCx := NNC x). clear NNC.
rewrite H in NNCx.
cbn in NNCx.
apply (D x NNCx).
Qed.

(** Apply a partial function [f] to every declaration in the calldag.
    Returns an error if [f] cannot be applied to at least one declaration.
    If should introduce no new calls, then the depthmap is going to be still valid.
 *)
Definition calldag_maybe_map {C: VyperConfig} {Decl Decl'}
                             {callset: Decl -> string_set}
                             {may_call_undeclared: bool}
                             {callset': Decl' -> string_set}
                             (f: Decl -> string + Decl')
                             (NoNewCalls: let _ := string_set_impl in
                                          forall (d: Decl) (d': Decl'),
                                            f d = inr d'
                                             ->
                                            FSet.is_subset (callset' d') (callset d) = true)
                             (cd: generic_calldag callset may_call_undeclared)
: string + generic_calldag callset' may_call_undeclared
:= let D := @string_map_impl C Decl in
   let D' := @string_map_impl C Decl' in
   match map_maybe_map (cd_decls cd) f as cd' return _ = cd' -> _ with
   | inl err => fun _ => inl err
   | inr decls' => fun E => inr
     {| cd_decls := decls'
      ; cd_depthmap := cd_depthmap cd
      ; cd_depthmap_ok := calldag_maybe_map_helper cd f decls' NoNewCalls E
     |}
   end eq_refl.

(** [calldag_maybe_map] preserves the depthmap.
    This should be trivial since the depthmap is literally unchanged.
    However, this still requires some effort due to dependent types.
 *)
Lemma calldag_maybe_map_depthmap_ok {C: VyperConfig} {Decl Decl'}
                                    {callset: Decl -> string_set}
                                    {may_call_undeclared: bool}
                                    {callset': Decl' -> string_set}
                                    (f: Decl -> string + Decl')
                                    (NoNewCalls: let _ := string_set_impl in
                                                 forall (d: Decl) (d': Decl'),
                                                   f d = inr d'
                                                    ->
                                                   FSet.is_subset (callset' d') (callset d) = true)
                                    {cd:  generic_calldag callset  may_call_undeclared}
                                    {cd': generic_calldag callset' may_call_undeclared}
                                    (Ok: calldag_maybe_map f NoNewCalls cd = inr cd')
                                    (name: string):
  cd_depthmap cd name
   =
  cd_depthmap cd' name.
Proof.
destruct cd as (decls, depthmap, depthmap_ok).
unfold calldag_maybe_map in Ok.
cbn in *.
remember (fun decls' (E : map_maybe_map decls f = inr decls') =>
           inr
             {|
             cd_decls := decls';
             cd_depthmap := depthmap;
             cd_depthmap_ok := calldag_maybe_map_helper
                                 {|
                                   cd_decls := decls;
                                   cd_depthmap := depthmap;
                                   cd_depthmap_ok := depthmap_ok 
                                 |} f decls' NoNewCalls E
             |}) as good_branch.
assert (K: forall (d': string_map Decl')
                  (E: map_maybe_map decls f = inr d'),
             good_branch d' E = inr cd'
              ->
             cd_depthmap cd' name = depthmap name).
{
  intros. subst.
  inversion H. now subst.
}
clear Heqgood_branch.
destruct map_maybe_map as [|d']. { discriminate. }
symmetry.
apply (K d' eq_refl Ok).
Qed.

(** This is how [calldag_maybe_map] works on the declmap. *)
Lemma calldag_maybe_map_declmap {C: VyperConfig} {Decl Decl'}
                                {callset: Decl -> string_set}
                                {may_call_undeclared: bool}
                                {callset': Decl' -> string_set}
                                (f: Decl -> string + Decl')
                                (NoNewCalls: let _ := string_set_impl in
                                             forall (d: Decl) (d': Decl'),
                                               f d = inr d'
                                                ->
                                               FSet.is_subset (callset' d') (callset d) = true)
                                {cd:  generic_calldag callset  may_call_undeclared}
                                {cd': generic_calldag callset' may_call_undeclared}
                                (Ok: calldag_maybe_map f NoNewCalls cd = inr cd')
                                (name: string):
  match cd_declmap cd name with
  | Some d => Some (f d)
  | None => None
  end
   =
  match cd_declmap cd' name with
  | Some d => Some (inr d)
  | None => None
  end.
Proof.
destruct cd as (decls, depthmap, depthmap_ok).
unfold calldag_maybe_map in Ok.
cbn in *.
remember (fun decls' (E : map_maybe_map decls f = inr decls') =>
         inr
           {|
           cd_decls := decls';
           cd_depthmap := depthmap;
           cd_depthmap_ok := calldag_maybe_map_helper
                               {|
                               cd_decls := decls;
                               cd_depthmap := depthmap;
                               cd_depthmap_ok := depthmap_ok |} f decls' NoNewCalls E |})
  as good_branch.
unfold cd_declmap. cbn.
assert (K: forall (d': string_map Decl')
                  (E: map_maybe_map decls f = inr d'),
             good_branch d' E = inr cd'
              ->
             let _ := string_map_impl Decl in
             let _ := string_map_impl Decl' in
             match Map.lookup decls name with
             | Some d => Some (f d)
             | None => None
             end = match Map.lookup (cd_decls cd') name with
                   | Some d => Some (inr d)
                   | None => None
                   end).
{
  intros. subst.
  inversion H. subst.
  cbn.
  clear H Ok.
  assert (M := map_maybe_map_ok E name).
  destruct (Map.lookup decls name). 2:{ now destruct Map.lookup. }
  destruct (f d). { contradiction. }
  (* interestingly, rewrite M doesn't work *)
  destruct Map.lookup. { now inversion M. }
  discriminate.
}
clear Heqgood_branch.
destruct (map_maybe_map decls f) as [|d']. { discriminate. }
apply (K d' eq_refl Ok).
Qed.

Section CalldagMaybeMapFunCtx.
  Context {C: VyperConfig} {Decl Decl'}
          {callset: Decl -> string_set}
          {may_call_undeclared: bool}
          {callset': Decl' -> string_set}
          (f: Decl -> string + Decl')
          (NoNewCalls: let _ := string_set_impl in
                       forall (d: Decl) (d': Decl'),
                         f d = inr d'
                          ->
                         FSet.is_subset (callset' d') (callset d) = true)
          {cd:  generic_calldag callset  may_call_undeclared}
          {cd': generic_calldag callset' may_call_undeclared}
          (Ok: calldag_maybe_map f NoNewCalls cd = inr cd')
          {bound: nat}
          (fc: fun_ctx cd bound).

  Local Lemma calldag_maybe_map_fun_ctx_fun_decl_helper:
    cd_declmap cd' (fun_name fc) <> None.
  Proof.
  intro E.
  assert (F := fun_decl_ok fc).
  assert (M := calldag_maybe_map_declmap f NoNewCalls Ok (fun_name fc)).
  rewrite F in M.
  rewrite E in M.
  discriminate.
  Qed.

  (** This is the [Decl'] to which [f] maps the name of [fc] *)
  Definition cached_mapped_decl
  : Decl'
  := match cd_declmap cd' (fun_name fc)
     as d' return _ = d' -> _
     with
     | Some f => fun _ => f
     | None => fun E =>
          False_rect _ (calldag_maybe_map_fun_ctx_fun_decl_helper E)
     end eq_refl.

  Local Lemma cached_mapped_decl_ok:
    cd_declmap cd' (fun_name fc)
     =
    Some cached_mapped_decl.
  Proof.
  assert (D := fun_decl_ok fc).
  unfold cached_mapped_decl.
  remember calldag_maybe_map_fun_ctx_fun_decl_helper as foo. clear Heqfoo. revert foo.
  destruct (cd_declmap cd' (fun_name fc)). { trivial. }
  intro. contradiction.
  Qed.

  Local Lemma calldag_maybe_map_fun_ctx_depth_ok:
    cd_depthmap cd' (fun_name fc) = Some (fun_depth fc).
  Proof.
  rewrite<- (calldag_maybe_map_depthmap_ok f NoNewCalls Ok).
  apply (fun_depth_ok fc).
  Qed.

  (** Apply [calldag_maybe_map] to a function context.
   *)
  Definition fun_ctx_map
  : fun_ctx cd' bound
  := {| fun_name := fun_name fc
      ; fun_depth := fun_depth fc
      ; fun_depth_ok := calldag_maybe_map_fun_ctx_depth_ok
      ; fun_decl := cached_mapped_decl
      ; fun_decl_ok := cached_mapped_decl_ok
      ; fun_bound_ok := fun_bound_ok fc
     |}.
End CalldagMaybeMapFunCtx.

(** Creating a function context from scratch in a calldag mapped with [calldag_maybe_map]
    is the same as creating it in the original calldag and than mapping it with [fun_ctx_map].
 *)
Lemma make_fun_ctx_and_bound_ok {C: VyperConfig} {Decl Decl'}
                                {callset: Decl -> string_set}
                                {may_call_undeclared: bool}
                                {callset': Decl' -> string_set}
                                (f: Decl -> string + Decl')
                                (NoNewCalls: let _ := string_set_impl in
                                             forall (d: Decl) (d': Decl'),
                                               f d = inr d'
                                                ->
                                               FSet.is_subset (callset' d') (callset d) = true)
                                {cd:  generic_calldag callset  may_call_undeclared}
                                {cd': generic_calldag callset' may_call_undeclared}
                                (Ok: calldag_maybe_map f NoNewCalls cd = inr cd')
                                (fun_name: string):
   make_fun_ctx_and_bound cd' fun_name
    =
   match make_fun_ctx_and_bound cd fun_name with
   | Some (existT _ bound fc) => Some (existT _ bound (fun_ctx_map f NoNewCalls Ok fc))
   | None => None
   end.
Proof.
(* this is surprisingly complicated due to a lot of convoy destructuring *)
unfold make_fun_ctx_and_bound.
remember (fun d (Ed : cd_declmap cd' fun_name = Some d) =>
    match
      cd_depthmap cd' fun_name as depth'
      return (cd_depthmap cd' fun_name = depth' -> option {bound : nat & fun_ctx cd' bound})
    with
    | Some depth =>
        fun Edepth : cd_depthmap cd' fun_name = Some depth =>
        Some
          (existT (fun bound : nat => fun_ctx cd' bound) (S depth)
             {|
             fun_name := fun_name;
             fun_depth := depth;
             fun_depth_ok := Edepth;
             fun_decl := d;
             fun_decl_ok := Ed;
             fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |})
    | None =>
        fun Edepth : cd_depthmap cd' fun_name = None =>
        False_rect (option {bound : nat & fun_ctx cd' bound}) (make_fun_ctx_helper Ed Edepth)
    end eq_refl) as lhs_some_branch.
remember (fun d (Ed : cd_declmap cd fun_name = Some d) =>
      match
        cd_depthmap cd fun_name as depth'
        return (cd_depthmap cd fun_name = depth' -> option {bound : nat & fun_ctx cd bound})
      with
      | Some depth =>
          fun Edepth : cd_depthmap cd fun_name = Some depth =>
          Some
            (existT (fun bound : nat => fun_ctx cd bound) (S depth)
               {|
               fun_name := fun_name;
               fun_depth := depth;
               fun_depth_ok := Edepth;
               fun_decl := d;
               fun_decl_ok := Ed;
               fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth) |})
      | None =>
          fun Edepth : cd_depthmap cd fun_name = None =>
          False_rect (option {bound : nat & fun_ctx cd bound}) (make_fun_ctx_helper Ed Edepth)
      end eq_refl) as rhs_some_branch.
enough (SomeBranchOk: forall d' d Ed' Ed
                             (DeclOk: f d = inr d'),
                        lhs_some_branch d' Ed'
                         =
                        match rhs_some_branch d Ed with
                        | Some (existT _ bound fc) =>
                            Some
                              (existT _ bound
                                 (fun_ctx_map f NoNewCalls Ok fc))
                        | None => None
                        end).
{
  cbn in *.
  remember (fun _: _ = None => None) as lhs_none_branch.
  assert (NoneBranchOk: forall E, lhs_none_branch E = None).
  { subst. trivial. }
  clear Heqlhs_some_branch Heqrhs_some_branch Heqlhs_none_branch.
  assert (T := calldag_maybe_map_declmap f NoNewCalls Ok fun_name).
  destruct (cd_declmap cd fun_name); destruct (cd_declmap cd' fun_name);
    try easy.
  apply SomeBranchOk.
  now inversion T.
}
subst. cbn. intros.

remember (fun depth (Edepth : @cd_depthmap C Decl' callset' may_call_undeclared cd' fun_name = @Some nat depth) =>
    @Some {bound : nat & @fun_ctx C Decl' callset' may_call_undeclared cd' bound}
      (@existT nat (fun bound : nat => @fun_ctx C Decl' callset' may_call_undeclared cd' bound)
         (S depth)
         {|
         fun_name := fun_name;
         fun_depth := depth;
         fun_depth_ok := Edepth;
         fun_decl := d';
         fun_decl_ok := Ed';
         fun_bound_ok := _ |}))
  as depth_lhs_some_branch.
remember (fun depth (Edepth : cd_depthmap cd fun_name = Some depth) =>
      Some
        (existT (fun bound : nat => fun_ctx cd bound) (S depth)
           _))
  as depth_rhs_some_branch.
enough (A: forall depth E' E,
          depth_lhs_some_branch depth E'
           =
          match depth_rhs_some_branch depth E with
          | Some (existT _ bound fc) =>
              Some
                (existT (fun bound' : nat => fun_ctx cd' bound') bound
                   (fun_ctx_map f NoNewCalls Ok fc))
          | None => None
          end).
{
  clear Heqdepth_lhs_some_branch Heqdepth_rhs_some_branch.
  remember (fun Edepth : cd_depthmap cd' fun_name = None =>
      False_rect (option {bound : nat & fun_ctx cd' bound}) (Calldag.make_fun_ctx_helper Ed' Edepth))
    as lhs_none_branch.
  remember (fun Edepth : cd_depthmap cd fun_name = None =>
        False_rect (option {bound : nat & fun_ctx cd bound}) (Calldag.make_fun_ctx_helper Ed Edepth))
    as rhs_none_branch.
  clear Heqlhs_none_branch Heqrhs_none_branch.
  assert (Guard' := make_fun_ctx_helper Ed').
  assert (Guard  := make_fun_ctx_helper Ed).
  assert (T := calldag_maybe_map_depthmap_ok f NoNewCalls Ok fun_name).
  destruct (cd_depthmap cd' fun_name), (cd_depthmap cd fun_name); try easy.
  inversion T. subst.
  apply A.
}
intros. subst.
f_equal. f_equal.
unfold fun_ctx_map. cbn.
assert (FunCtxEq: forall name1 depth depth_ok1 decl1 decl_ok1 bound_ok1
                         name2       depth_ok2 decl2 decl_ok2 bound_ok2
                         (Name: name1 = name2)
                         (Decl: decl1 = decl2),
  ({| fun_name := name1
    ; fun_depth := depth
    ; fun_depth_ok := depth_ok1
    ; fun_decl := decl1
    ; fun_decl_ok := decl_ok1
    ; fun_bound_ok := bound_ok1 |}: fun_ctx cd' (S depth))
   =
  {| fun_name := name2
   ; fun_depth := depth
   ; fun_depth_ok := depth_ok2
   ; fun_decl := decl2
   ; fun_decl_ok := decl_ok2
   ; fun_bound_ok := bound_ok2 |}).
{
  intros. subst.
  assert (depth_ok1 = depth_ok2) by apply PropExtensionality.proof_irrelevance.
  assert (decl_ok1 = decl_ok2) by apply PropExtensionality.proof_irrelevance.
  assert (bound_ok1 = bound_ok2) by apply PropExtensionality.proof_irrelevance.
  subst.
  trivial.
}
apply FunCtxEq. { (* name: *) trivial. }
clear FunCtxEq.
assert (Unsome: forall {T} (x y: T), Some x = Some y -> x = y).
{ intros T x y H. now inversion H. }
apply Unsome.
rewrite<- cached_mapped_decl_ok. cbn. symmetry. exact Ed'.
Qed.
