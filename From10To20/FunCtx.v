From Coq Require Import String ZArith Eqdep_dec.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L20.AST L10.Interpret L20.Interpret.

From Vyper.From10To20 Require Import Translate Callset.

Local Lemma translate_calldag_helper {C: VyperConfig}
                                     (cd: L10.Descend.calldag):
  let _ := string_map_impl in
  let is_private_call (name: string)
   := match cd_declmap cd name with
      | Some _ => true
      | _ => false
      end
  in forall name: string,
       match
         Map.lookup (Map.map (cd_decls cd) (fun d => translate_decl is_private_call d)) name
       with
       | Some decl =>
           match cd_depthmap cd name with
           | Some x =>
               let _ := string_set_impl in
               FSet.for_all (Callset.decl_callset decl)
                 (fun callee : string =>
                  match cd_depthmap cd callee with
                  | Some y => y <? x
                  | None => false
                  end) = true
           | None => False
           end
       | None => True
       end.
Proof.
intros MapImpl is_private_call name.
assert (D := cd_depthmap_ok cd name).
rewrite Map.map_ok.
cbn.
remember (Map.lookup (cd_decls cd) name) as maybe_f. destruct maybe_f. 2:easy.
destruct (cd_depthmap cd name). 2:{ easy. }
rewrite FSet.for_all_ok in *. intros x H.
rewrite callset_translate_decl in H.
apply Bool.andb_true_iff in H.
assert (Q := D x (proj1 H)). clear D.
destruct (cd_depthmap cd x). 2:easy.
destruct n; rewrite Nat.ltb_lt in Q. { now apply Nat.nlt_0_r in Q. }
rewrite Nat.leb_le.
apply Nat.lt_succ_r. exact Q.
Qed.


Definition translate_calldag {C: VyperConfig} (cd: L10.Descend.calldag)
: L20.Descend.calldag
:= let is_private_call (name: string)
   := match cd_declmap cd name with
      | Some _ => true
      | _ => false
      end
   in {| cd_decls := Map.map (cd_decls cd)
                             (fun d => translate_decl is_private_call d)
       ; cd_depthmap := cd_depthmap cd
       ; cd_depthmap_ok := translate_calldag_helper cd
      |}.

Lemma translate_calldag_ok {C: VyperConfig} (cd: L10.Descend.calldag) (name: string):
  let is_private_call (name: string)
   := match cd_declmap cd name with
      | Some _ => true
      | _ => false
      end
  in cd_declmap (translate_calldag cd) name 
      =
     match cd_declmap cd name with
     | Some f => Some (translate_decl is_private_call f)
     | None => None
     end.
Proof.
unfold cd_declmap. cbn. rewrite Map.map_ok. trivial.
Qed.

(***************************************************************************************************)

Section FunCtx.
  Context {C: VyperConfig}
          {bound: nat}
          {cd: L10.Descend.calldag}
          (fc: fun_ctx cd bound)
          {cd2: L20.Descend.calldag}
          (ok: cd2 = translate_calldag cd).

  Local Lemma translate_fun_ctx_depthmap_helper (name: string):
    cd_depthmap cd2 name
     =
    cd_depthmap cd name.
  Proof.
  subst. trivial.
  Qed.

  Local Lemma translate_fun_ctx_fun_decl_helper:
    cd_declmap cd2 (fun_name fc) <> None.
  Proof.
  intro E.
  assert (Ok := fun_decl_ok fc).
  subst cd2. cbn in E. rewrite translate_calldag_ok in E. rewrite Ok in E. discriminate.
  Qed.

  Definition cached_translated_decl
  := match cd_declmap cd2 (fun_name fc)
     as d' return _ = d' -> _
     with
     | Some f => fun _ => f
     | None => fun E =>
          False_rect _ (translate_fun_ctx_fun_decl_helper E)
     end eq_refl.

  Local Lemma translate_fun_ctx_decl_ok:
    cd_declmap cd2 (fun_name fc) 
     =
    Some cached_translated_decl.
  Proof.
  assert (D := fun_decl_ok fc).
  unfold cached_translated_decl.
  remember translate_fun_ctx_fun_decl_helper as foo. clear Heqfoo. revert foo.
  destruct (cd_declmap cd2 (fun_name fc)). { trivial. }
  intro. contradiction.
  Qed.

  Definition translate_fun_ctx
  : fun_ctx cd2 bound
  := let name := fun_name fc in
     {| fun_name := name
      ; fun_depth := fun_depth fc
      ; fun_depth_ok :=
          eq_trans (translate_fun_ctx_depthmap_helper name)
                   (fun_depth_ok fc)
      ; fun_decl := cached_translated_decl
      ; fun_decl_ok := translate_fun_ctx_decl_ok
      ; fun_bound_ok := fun_bound_ok fc
     |}.

End FunCtx.