From Coq Require Import String Arith.
From Vyper Require Import Config.

Record generic_calldag {C: VyperConfig} (decl_type: Type) (callset: decl_type -> string_set) := {
  cd_decls: string_map decl_type;
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
                                          | None => false
                                          | Some y => y <? x
                                          end)
               = true
            end
      end;
}.
Arguments cd_decls {C decl_type callset}.
Arguments cd_depthmap {C decl_type callset}.
Arguments cd_depthmap_ok {C decl_type callset}.

(* This is for compatibility with an older definition via cd_declmap. *)
Definition cd_declmap {C: VyperConfig} {decl_type: Type} {callset: decl_type -> string_set}
                      (d: generic_calldag decl_type callset)
:= let _ := string_map_impl in
   Map.lookup (cd_decls d).

(**
  A functional context is the result of looking up a function by name in a calldag.
 *)
Record fun_ctx {C: VyperConfig}
               {decl_type: Type}
               {decl_callset: decl_type -> string_set}
               (cd: generic_calldag decl_type decl_callset)
               (bound: nat) := {
  fun_name: string;
  fun_depth: nat;
  fun_depth_ok: cd_depthmap cd fun_name = Some fun_depth;
  fun_decl: decl_type;
  fun_decl_ok: cd_declmap cd fun_name = Some fun_decl;
  fun_bound_ok: fun_depth <? bound = true;
}.
Arguments fun_name     {C _ _ _ _}.
Arguments fun_depth    {C _ _ _ _}.
Arguments fun_depth_ok {C _ _ _ _}.
Arguments fun_decl     {C _ _ _ _}.
Arguments fun_decl_ok  {C _ _ _ _}.
Arguments fun_bound_ok {C _ _ _ _}.

Local Lemma make_fun_ctx_helper {C: VyperConfig}
                                {decl_type: Type}
                                {decl_callset: decl_type -> string_set}
                                {cd: generic_calldag decl_type decl_callset}
                                {name: string}
                                {d: decl_type}
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
                                  {decl_type: Type}
                                  {decl_callset: decl_type -> string_set}
                                  (cd: generic_calldag decl_type decl_callset)
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