From Coq Require Import String List ListSet Arith NArith.
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