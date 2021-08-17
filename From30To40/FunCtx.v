From Coq Require Import ZArith NArith String List.

From Vyper Require Import Config NaryFun Calldag.
From Vyper Require Map.
From Vyper.L30 Require AST Descend.
From Vyper.L40 Require AST Descend.
From Vyper.CheckArith Require Import Builtins.

From Vyper.L10 Require Import Base.

From Vyper.From30To40 Require Import Translate Callset.


Local Open Scope list_scope.

Fixpoint translate_decl_alist {C: VyperConfig}
                              (B: builtin_names_config)
                              (declmap: string_map L30.AST.decl)
                              (decls: list (string * L30.AST.decl))
: string + list (string * L40.AST.decl)
:= match decls with
   | nil => inr nil
   | (_, L30.AST.StorageVarDecl _) :: rest => translate_decl_alist B declmap rest
   | (name, L30.AST.FunDecl _ nargs body) :: rest =>
        match translate_stmt B declmap body with
        | inl err => inl err
        | inr body' =>
            match translate_decl_alist B declmap rest with
            | inl err => inl err
            | inr rest' => inr ((name, L40.AST.FunDecl name nargs (L40.AST.Block body')) :: rest')
            end
        end
   end.

Local Lemma translate_decl_alist_no_new_names {C: VyperConfig}
                                              (B: builtin_names_config)
                                              (declmap: string_map L30.AST.decl)
                                              (decls: list (string * L30.AST.decl))
                                              (decls': list (string * L40.AST.decl))
                                              (Ok: translate_decl_alist B declmap decls = inr decls')
                                              (name: string):
  In name (map fst decls') -> In name (map fst decls).
Proof.
revert decls' Ok. induction decls; intros decls' Ok H.
{ cbn in Ok. inversion Ok. now subst. }
destruct a as (n, d). cbn in *.
destruct d.
{ (* storage var *) right. apply (IHdecls _ Ok H). }
destruct (translate_stmt B declmap body) as [err|body']. { discriminate. }
remember (translate_decl_alist B declmap decls) as t_decls.
destruct t_decls as [err | t_decls]. { discriminate. }
inversion Ok. subst. clear Ok.
destruct H. { now left. }
right. now apply (IHdecls _ eq_refl).
Qed.

Lemma translate_decl_alist_ok {C: VyperConfig}
                              (B: builtin_names_config)
                              (declmap: string_map L30.AST.decl)
                              (decls: list (string * L30.AST.decl))
                              (DeclsNoDup: List.NoDup (List.map fst decls))
                              (decls': list (string * L40.AST.decl))
                              (Ok: translate_decl_alist B declmap decls = inr decls')
                              (name: string):
  match Map.alist_lookup string_dec decls name with
  | None | Some (L30.AST.StorageVarDecl _) => Map.alist_lookup string_dec decls' name = None
  | Some (L30.AST.FunDecl _ nargs body) =>
      match translate_stmt B declmap body with
      | inl _ => False
      | inr body' => Map.alist_lookup string_dec decls' name =
                        Some (L40.AST.FunDecl name nargs (L40.AST.Block body'))
      end
  end.
Proof.
revert decls' Ok. induction decls; intros. { cbn in *. now inversion Ok. }
cbn. destruct a as (key, value).
cbn in DeclsNoDup. inversion DeclsNoDup. subst.
assert (IH := IHdecls H2). clear IHdecls.
cbn in Ok.
destruct (string_dec name key) as [E|NE].
{
  destruct value.
  { (* storage var *)
    subst.
    apply Map.alist_lookup_not_in.
    intro Hkey.
    now apply (translate_decl_alist_no_new_names B declmap decls decls') in Hkey.
  }
  destruct (translate_stmt B declmap body) as [err|body']. { discriminate. }
  remember (translate_decl_alist B declmap decls) as t_decls.
  destruct t_decls. { discriminate. }
  inversion Ok. subst. clear Ok.
  cbn. now destruct string_dec.
}
destruct value.
{ (* storage var *) now apply IH. }
destruct (translate_stmt B declmap body). { discriminate. }
remember (translate_decl_alist B declmap decls) as t_decls.
destruct t_decls. { discriminate. }
inversion Ok. subst. clear Ok.
cbn. destruct (string_dec name key). { contradiction. }
apply (IH _ eq_refl).
Qed.

Local Lemma translate_calldag_depthmap_ok {C: VyperConfig}
                                          (B: builtin_names_config)
                                          (declmap: string_map L30.AST.decl)
                                          (name: string)
                                          (cd: L30.Descend.calldag)
                                          (d: list (string * L40.AST.decl)):
   let _ := string_map_impl in
   forall E: translate_decl_alist B declmap (Map.items (cd_decls cd)) = inr d,
   match Map.lookup (Map.of_alist d) name with
   | Some decl =>
       match cd_depthmap cd name with
       | Some x =>
           let H := string_set_impl in
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
intros map_impl E. unfold map_impl in *. clear map_impl.
remember (Map.lookup _ name) as m. symmetry in Heqm.
destruct m as [f|]. 2:{ trivial. }
rewrite Map.of_alist_ok in Heqm.

assert (D := cd_depthmap_ok cd name).
assert (F := translate_decl_alist_ok B declmap
                                     (Map.items (cd_decls cd))
                                     (Map.items_nodup (cd_decls cd))
                                     d E name).
rewrite<- Map.items_ok in F.
destruct (Map.lookup (cd_decls cd) name). 2:{ now rewrite F in Heqm. }
destruct (cd_depthmap cd name). 2:assumption.
rewrite FSet.for_all_ok. rewrite FSet.for_all_ok in D.
intros x H.
destruct d0; rewrite Heqm in F. { discriminate. }
cbn in D.
remember (translate_stmt B declmap body) as body'. destruct body'. { contradiction. }
inversion F. subst. clear F.
cbn in H.
rewrite (callset_translate_stmt B declmap _ _ (eq_sym Heqbody')) in H.
apply (D x H).
Qed.

Definition translate_calldag {C: VyperConfig} (B: builtin_names_config) (cd: L30.Descend.calldag)
: string + L40.Descend.calldag
:= let _ := string_map_impl in
   match translate_decl_alist B (cd_decls cd) (Map.items (cd_decls cd)) as cd' return _ = cd' -> _ with
   | inl err => fun _ => inl err
   | inr d => fun E => inr
     {| cd_decls := Map.of_alist d
      ; cd_depthmap := cd_depthmap cd
      ; cd_depthmap_ok name := translate_calldag_depthmap_ok B (cd_decls cd) name cd d E
     |}
   end eq_refl.


(***************************************************************************************************)

Section FunCtx1.
  Context {C: VyperConfig}
          {bound: nat}
          {cd30: L30.Descend.calldag}
          {cd40: L40.Descend.calldag}
          (B: builtin_names_config)
          (ok: translate_calldag B cd30 = inr cd40).

  Lemma translate_fun_ctx_depthmap (name: string):
    cd_depthmap cd40 name
     =
    cd_depthmap cd30 name.
  Proof.
  destruct cd30.
  unfold translate_calldag in ok.
  cbn in *.
  remember (fun d (E : translate_decl_alist B cd_decls (Map.items cd_decls) = inr d) =>
         inr
           {|
             cd_decls := Map.of_alist d;
             cd_depthmap := cd_depthmap;
             cd_depthmap_ok :=
               fun name : string =>
               translate_calldag_depthmap_ok B cd_decls name
                 {|
                   cd_decls := cd_decls; cd_depthmap := cd_depthmap; cd_depthmap_ok := cd_depthmap_ok
                 |} d E
           |}) as good_branch.
  assert (K: forall (d40: list (string * L40.AST.decl))
                    (E: translate_decl_alist B cd_decls (Map.items cd_decls) = inr d40),
               good_branch d40 E = inr cd40
                ->
               Calldag.cd_depthmap cd40 name = cd_depthmap name).
  {
    intros. subst.
    inversion H. now subst.
  }
  clear Heqgood_branch.
  destruct (translate_decl_alist B cd_decls (Map.items cd_decls)) as [|d40]. { discriminate. }
  apply (K d40 eq_refl ok).
  Qed.

  Lemma translate_fun_ctx_declmap (name: string):
    match cd_declmap cd30 name with
    | Some (L30.AST.FunDecl _ _ body) =>
        Some (translate_stmt B (cd_decls cd30) body)
    | _ => None
    end
     =
    match cd_declmap cd40 name with
    | Some (L40.AST.FunDecl _ _ (L40.AST.Block stmts)) => Some (inr stmts)
    | None => None
    end.
  Proof.
  destruct cd30.
  unfold translate_calldag in ok.
  cbn in *.
  remember (fun d (E: translate_decl_alist B cd_decls (Map.items cd_decls) = inr d) =>
         inr
           {|
             cd_decls := Map.of_alist d;
             cd_depthmap := cd_depthmap;
             cd_depthmap_ok :=
               fun name : string =>
               translate_calldag_depthmap_ok B cd_decls name
                 {|
                   cd_decls := cd_decls; cd_depthmap := cd_depthmap; cd_depthmap_ok := cd_depthmap_ok
                 |} d E
           |}) as good_branch.
  unfold cd_declmap. cbn.
  assert (K: forall (d40: list (string * L40.AST.decl))
                    (E: translate_decl_alist B cd_decls (Map.items cd_decls) = inr d40),
               good_branch d40 E = inr cd40
                ->
               let _ := string_map_impl in
               match Map.lookup cd_decls name with
               | Some (L30.AST.FunDecl _ _ body) => Some (translate_stmt B cd_decls body)
               | _ => None
               end
                =
               match Map.lookup (Calldag.cd_decls cd40) name with
               | Some (AST.FunDecl _ _ (AST.Block stmts)) => Some (inr stmts)
               | None => None
               end).
  {
    intros. subst.
    inversion H. subst.
    cbn.
    clear H ok.
    assert (M := translate_decl_alist_ok B cd_decls (Map.items cd_decls)
                                         (Map.items_nodup _) _ E name).
    rewrite Map.of_alist_ok.
    rewrite<- Map.items_ok in M.
    destruct (Map.lookup cd_decls name). 2:{ now rewrite M. }
    destruct d. { now rewrite M. }
    destruct (translate_stmt B cd_decls body). { contradiction. }
    now rewrite M.
  }
  clear Heqgood_branch.
  destruct (translate_decl_alist B cd_decls (Map.items cd_decls)). { discriminate. }
  apply (K _ eq_refl ok).
  Qed.

  Lemma translate_fun_ctx_declmap_stronger (name: string):
    match cd_declmap cd30 name with
    | Some (L30.AST.FunDecl _ arity body) =>
        Some (name, arity, translate_stmt B (cd_decls cd30) body)
    | _ => None
    end
     =
    match cd_declmap cd40 name with
    | Some (L40.AST.FunDecl name' arity (L40.AST.Block stmts)) =>
        Some (name', arity, inr stmts)
    | None => None
    end.
  Proof.
  destruct cd30.
  unfold translate_calldag in ok.
  cbn in *.
  remember (fun d (E: translate_decl_alist B cd_decls (Map.items cd_decls) = inr d) =>
         inr
           {|
             cd_decls := Map.of_alist d;
             cd_depthmap := cd_depthmap;
             cd_depthmap_ok :=
               fun name : string =>
               translate_calldag_depthmap_ok B cd_decls name
                 {|
                   cd_decls := cd_decls; cd_depthmap := cd_depthmap; cd_depthmap_ok := cd_depthmap_ok
                 |} d E
           |}) as good_branch.
  unfold cd_declmap. cbn.
  assert (K: forall (d40: list (string * L40.AST.decl))
                    (E: translate_decl_alist B cd_decls (Map.items cd_decls) = inr d40),
               good_branch d40 E = inr cd40
                ->
               let _ := string_map_impl in
               match Map.lookup cd_decls name with
               | Some (L30.AST.FunDecl _ arity body) => Some (name, arity, translate_stmt B cd_decls body)
               | _ => None
               end
                =
               match Map.lookup (Calldag.cd_decls cd40) name with
               | Some (AST.FunDecl name' arity (AST.Block stmts)) => Some (name', arity, inr stmts)
               | None => None
               end).
  {
    intros. subst.
    inversion H. subst.
    cbn.
    clear H ok.
    assert (M := translate_decl_alist_ok B cd_decls (Map.items cd_decls)
                                         (Map.items_nodup _) _ E name).
    rewrite Map.of_alist_ok.
    rewrite<- Map.items_ok in M.
    destruct (Map.lookup cd_decls name). 2:{ now rewrite M. }
    destruct d. { now rewrite M. }
    destruct (translate_stmt B cd_decls body). { contradiction. }
    now rewrite M.
  }
  clear Heqgood_branch.
  destruct (translate_decl_alist B cd_decls (Map.items cd_decls)). { discriminate. }
  apply (K _ eq_refl ok).
  Qed.

End FunCtx1.

Section FunCtx2.
  Context {C: VyperConfig}
          {bound: nat}
          {cd30: L30.Descend.calldag}
          (fc: fun_ctx cd30 bound)
          {cd40: L40.Descend.calldag}
          (B: builtin_names_config)
          (ok: translate_calldag B cd30 = inr cd40)
          (NotVar: forall x: string,
                     fun_decl fc <> L30.AST.StorageVarDecl x).

  Local Lemma translate_fun_ctx_fun_decl_helper:
    cd_declmap cd40 (fun_name fc) <> None.
  Proof.
  intro E.
  assert (Ok := fun_decl_ok fc).
  assert (M := translate_fun_ctx_declmap B ok (fun_name fc)).
  rewrite Ok in M.
  rewrite E in M.
  destruct (fun_decl fc). 2:discriminate.
  exact (NotVar name eq_refl).
  Qed.

  Definition cached_translated_decl
  := match cd_declmap cd40 (fun_name fc)
     as d' return _ = d' -> _
     with
     | Some f => fun _ => f
     | None => fun E =>
          False_rect _ (translate_fun_ctx_fun_decl_helper E)
     end eq_refl.

  Local Lemma translate_fun_ctx_decl_ok:
    cd_declmap cd40 (fun_name fc) 
     =
    Some cached_translated_decl.
  Proof.
  assert (D := fun_decl_ok fc).
  unfold cached_translated_decl.
  remember translate_fun_ctx_fun_decl_helper as foo. clear Heqfoo. revert foo.
  destruct (cd_declmap cd40 (fun_name fc)). { trivial. }
  intro. contradiction.
  Qed.

  Definition translate_fun_ctx
  : fun_ctx cd40 bound
  := let name := fun_name fc in
     {| fun_name := name
      ; fun_depth := fun_depth fc
      ; fun_depth_ok :=
          eq_trans (translate_fun_ctx_depthmap B ok name)
                   (fun_depth_ok fc)
      ; fun_decl := cached_translated_decl
      ; fun_decl_ok := translate_fun_ctx_decl_ok
      ; fun_bound_ok := fun_bound_ok fc
     |}.
End FunCtx2.