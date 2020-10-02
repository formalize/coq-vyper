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