From Coq Require Import String ZArith Eqdep_dec.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L20.AST L30.AST L20.Interpret L30.Interpret.

From Vyper.From20To30 Require Import Translate Callset.



Local Lemma translate_calldag_depthmap_ok {C: VyperConfig}
                                          (name: string)
                                          (cd: L20.Descend.calldag)
                                          (d: string_map L30.AST.decl):
   let _ := string_map_impl in
   forall E: map_maybe_map (cd_decls cd) translate_decl = inr d,
     match Map.lookup d name with
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
intros.
remember (Map.lookup d name) as m.
destruct m. 2:trivial.
assert (D := cd_depthmap_ok cd name).
assert (F := map_maybe_map_ok E name).
destruct (Map.lookup (cd_decls cd) name). 2:{ now rewrite F in Heqm. }
destruct (cd_depthmap cd name). 2:assumption.
rewrite FSet.for_all_ok. rewrite FSet.for_all_ok in D.
intros x H.
remember (translate_decl d1) as d30.
destruct d30. { contradiction. }
rewrite<- Heqm in F. inversion F; subst.
rewrite (callset_translate_decl _ _ (eq_sym Heqd30)) in H.
apply (D x H).
Qed.

Definition translate_calldag {C: VyperConfig} (cd: L20.Descend.calldag)
: string + L30.Descend.calldag
:= let _ := string_map_impl in
   match map_maybe_map (cd_decls cd) translate_decl as cd' return _ = cd' -> _ with
   | inl err => fun _ => inl err
   | inr d => fun E => inr
     {| cd_decls := d
      ; cd_depthmap := cd_depthmap cd
      ; cd_depthmap_ok name := translate_calldag_depthmap_ok name cd d E
     |}
   end eq_refl.

(***************************************************************************************************)

Section FunCtx1.
  Context {C: VyperConfig}
          {bound: nat}
          {cd20: L20.Descend.calldag}
          {cd30: L30.Descend.calldag}
          (ok: translate_calldag cd20 = inr cd30).

  Lemma translate_fun_ctx_depthmap (name: string):
    cd_depthmap cd30 name
     =
    cd_depthmap cd20 name.
  Proof.
  destruct cd20.
  unfold translate_calldag in ok.
  cbn in *.
  remember (fun d (E : map_maybe_map cd_decls translate_decl = inr d) =>
         inr
           {|
           cd_decls := d;
           cd_depthmap := cd_depthmap;
           cd_depthmap_ok := fun name : string =>
                             translate_calldag_depthmap_ok name
                               {|
                               cd_decls := cd_decls;
                               cd_depthmap := cd_depthmap;
                               cd_depthmap_ok := cd_depthmap_ok |} d E |}) as good_branch.
  assert (K: forall (d30: string_map L30.AST.decl)
                    (E: map_maybe_map cd_decls translate_decl = inr d30),
               good_branch d30 E = inr cd30 
                ->
               Calldag.cd_depthmap cd30 name = cd_depthmap name).
  {
    intros. subst.
    inversion H. now subst.
  }
  clear Heqgood_branch.
  destruct (map_maybe_map cd_decls translate_decl) as [|d30]. { discriminate. }
  apply (K d30 eq_refl ok).
  Qed.

  Lemma translate_fun_ctx_declmap (name: string):
    match cd_declmap cd20 name with
    | Some d => Some (translate_decl d)
    | None => None
    end
     =
    match cd_declmap cd30 name with
    | Some d => Some (inr d)
    | None => None
    end.
  Proof.
  destruct cd20.
  unfold translate_calldag in ok.
  cbn in *.
  remember (fun d (E : map_maybe_map cd_decls translate_decl = inr d) =>
         inr
           {|
           cd_decls := d;
           cd_depthmap := cd_depthmap;
           cd_depthmap_ok := fun name : string =>
                             translate_calldag_depthmap_ok name
                               {|
                               cd_decls := cd_decls;
                               cd_depthmap := cd_depthmap;
                               cd_depthmap_ok := cd_depthmap_ok |} d E |}) as good_branch.
  unfold cd_declmap. cbn.
  assert (K: forall (d30: string_map L30.AST.decl)
                    (E: map_maybe_map cd_decls translate_decl = inr d30),
               good_branch d30 E = inr cd30 
                ->
               let _ := string_map_impl in
               match Map.lookup cd_decls name with
               | Some d => Some (translate_decl d)
               | None => None
               end = match Map.lookup (Calldag.cd_decls cd30) name with
                     | Some d => Some (inr d)
                     | None => None
                     end).
  {
    intros. subst.
    inversion H. subst.
    cbn.
    clear H ok.
    assert (M := map_maybe_map_ok E name).
    destruct (Map.lookup cd_decls name). 2:{ now destruct Map.lookup. }
    destruct (translate_decl d). { contradiction. }
    (* why rewrite M doesn't work? *)
    destruct Map.lookup. { now inversion M. }
    discriminate.
  }
  clear Heqgood_branch.
  destruct (map_maybe_map cd_decls translate_decl) as [|d30]. { discriminate. }
  apply (K d30 eq_refl ok).
  Qed.
End FunCtx1.

Section FunCtx2.
  Context {C: VyperConfig}
          {bound: nat}
          {cd20: L20.Descend.calldag}
          (fc: fun_ctx cd20 bound)
          {cd30: L30.Descend.calldag}
          (ok: translate_calldag cd20 = inr cd30).

  Local Lemma translate_fun_ctx_fun_decl_helper:
    cd_declmap cd30 (fun_name fc) <> None.
  Proof.
  intro E.
  assert (Ok := fun_decl_ok fc).
  assert (M := translate_fun_ctx_declmap ok (fun_name fc)).
  rewrite Ok in M.
  rewrite E in M.
  discriminate.
  Qed.

  Definition cached_translated_decl
  := match cd_declmap cd30 (fun_name fc)
     as d' return _ = d' -> _
     with
     | Some f => fun _ => f
     | None => fun E =>
          False_rect _ (translate_fun_ctx_fun_decl_helper E)
     end eq_refl.

  Local Lemma translate_fun_ctx_decl_ok:
    cd_declmap cd30 (fun_name fc) 
     =
    Some cached_translated_decl.
  Proof.
  assert (D := fun_decl_ok fc).
  unfold cached_translated_decl.
  remember translate_fun_ctx_fun_decl_helper as foo. clear Heqfoo. revert foo.
  destruct (cd_declmap cd30 (fun_name fc)). { trivial. }
  intro. contradiction.
  Qed.

  Definition translate_fun_ctx
  : fun_ctx cd30 bound
  := let name := fun_name fc in
     {| fun_name := name
      ; fun_depth := fun_depth fc
      ; fun_depth_ok :=
          eq_trans (translate_fun_ctx_depthmap ok name)
                   (fun_depth_ok fc)
      ; fun_decl := cached_translated_decl
      ; fun_decl_ok := translate_fun_ctx_decl_ok
      ; fun_bound_ok := fun_bound_ok fc
     |}.
End FunCtx2.