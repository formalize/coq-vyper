From Coq Require Import String ZArith NArith Lia PropExtensionality.


From Vyper Require Import Config Calldag Logic2.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L10 Require Import Base.
From Vyper.L30 Require AST Callset Interpret.
From Vyper.L40 Require AST Callset Interpret.
From Vyper.From30To40 Require Import FunCtx Translate Stmt.

Lemma interpret_translated_call {C: VyperConfig}
                                (call_depth_bound: nat)
                                (builtins: string -> option L10.Base.builtin)
                                {B: builtin_names_config}
                                (SloadOk: BuiltinsSupportSload B builtins)
                                (SstoreOk: BuiltinsSupportSstore B builtins)
                                (BuiltinsOk: BuiltinsSupportUInt256 B builtins)
                                {cd30: L30.Descend.calldag}
                                {cd40: L40.Descend.calldag}
                                (CalldagOk: translate_calldag B cd30 = inr cd40)
                                (fc30: fun_ctx cd30 call_depth_bound)
                                (FcNotVar: forall x,
                                             fun_decl fc30 <> AST.StorageVarDecl x)
                                (world: world_state)
                                (arg_values: list uint256):
  L40.Interpret.interpret_call builtins (translate_fun_ctx fc30 B CalldagOk FcNotVar) world arg_values
   =
  L30.Interpret.interpret_call builtins fc30 world arg_values.
Proof.
revert world arg_values.
induction call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc30))). }

assert(F: Some (cached_translated_decl fc30 B CalldagOk FcNotVar)
           =
          match fun_decl fc30 with
          | L30.AST.StorageVarDecl name => None
          | L30.AST.FunDecl _ arity body =>
              match translate_stmt B (cd_decls cd30) body with
              | inl _ => None
              | inr x => Some (L40.AST.FunDecl (fun_name fc30) arity (L40.AST.Block x))
              end
          end).
{
  clear IHcall_depth_bound.
  unfold cached_translated_decl in *.
  remember (FunCtx.translate_fun_ctx_fun_decl_helper fc30 B CalldagOk FcNotVar) as foo.
  clear Heqfoo.
  remember (cd_declmap cd40 (fun_name fc30)) as d.
  destruct d. 2:{ contradiction. }
  subst.
  assert (Q := translate_fun_ctx_declmap_stronger B CalldagOk (fun_name fc30)).
  destruct (cd_declmap cd40 (fun_name fc30)) as [d'|]. 2:discriminate.
  inversion Heqd. subst d'. clear Heqd.
  clear foo.
  assert (D := fun_decl_ok fc30).
  rewrite D in Q.
  destruct (fun_decl fc30), d as (d_name, d_arity, d_body), d_body.
  { discriminate. }
  destruct translate_stmt. { discriminate. }
  inversion Q. now subst.
}
intros. cbn.
remember (fun name arity body
              (E: cached_translated_decl fc30 B CalldagOk FcNotVar
                   =
                  AST.FunDecl name arity body) => _)
  as branch_l.
remember (fun name arity body
              (E: fun_decl fc30 = L30.AST.FunDecl name arity body) => _)
  as branch_r.

enough (Ok: forall name arity body_l body_r E_l E_r,
             branch_l (fun_name fc30) arity body_l E_l
              =
             branch_r name arity body_r E_r).
{
  clear Heqbranch_l Heqbranch_r.
  (* destruct might not work, but this will: *)
  refine (match fun_decl fc30 as d' return _ = d' -> _ with
          | L30.AST.StorageVarDecl name => _
          | L30.AST.FunDecl name arity body => _
          end eq_refl).
  {
    intro IsStorageVar.
    apply FcNotVar in IsStorageVar.
    contradiction.
  }
  intro IsFunDecl.
  match goal with
  |- ?l = ?r => replace r with (branch_r name arity body IsFunDecl)
  end.
  2:{
    clear Ok FcNotVar branch_l F.
    destruct (fun_decl fc30). { discriminate. }
    inversion IsFunDecl. subst.
    f_equal.
    apply proof_irrelevance.
  }
  destruct (cached_translated_decl fc30 B CalldagOk FcNotVar).
  rewrite IsFunDecl in F.
  destruct (translate_stmt B (cd_decls cd30) body). { discriminate. }
  inversion F. subst.
  apply Ok.
}
intros. subst.
destruct (Datatypes.length arg_values =? N.to_nat arity). 2:easy.

rewrite E_l in F. rewrite E_r in F.
cbn in F.
remember (translate_stmt B (cd_decls cd30) body_r) as body.
destruct body. { discriminate. }
inversion F. subst body_l. clear F.
rename body_r into body.
now rewrite (let _ := memory_impl in
             interpret_translated_stmt B eq_refl CalldagOk fc30 FcNotVar
                                       IHcall_depth_bound (eq_sym Heqbody)
                                       builtins SloadOk SstoreOk BuiltinsOk
                                       world (OpenArray.from_list arg_values)
                                       (L30.Interpret.interpret_call_helper E_r)
                                       (L40.Interpret.interpret_call_helper E_l)
                                       nil).
Qed.

Lemma match_some {T R} {x: option T} {y: T} (E: x = Some y)
                 (some_branch: forall z: T, x = Some z -> R)
                 (none_branch: x = None -> R):
  match x as x' return x = x' -> _ with
  | Some z => some_branch z
  | None => none_branch
  end eq_refl
   =
  some_branch y E.
Proof.
destruct x. 2:discriminate.
inversion E. subst. f_equal. apply proof_irrelevance.
Qed.

Lemma match_none {T R} {x: option T} (E: x = None)
                 (some_branch: forall z: T, x = Some z -> R)
                 (none_branch: x = None -> R):
  match x as x' return x = x' -> _ with
  | Some z => some_branch z
  | None => none_branch
  end eq_refl
   =
  none_branch E.
Proof.
destruct x. 1:discriminate.
inversion E. subst. f_equal. apply proof_irrelevance.
Qed.


Local Lemma is_fun_to_not_var_decl {C: VyperConfig}
                                   (cd30: L30.Descend.calldag)
                                   (fun_name: string)
                                   (IsFun: match cd_declmap cd30 fun_name with
                                           | Some (L30.AST.FunDecl _ _ _) => True
                                           | _ => False
                                           end)
                                   (b: {bound : nat & fun_ctx cd30 bound})
                                   (FC: make_fun_ctx_and_bound cd30 fun_name = Some b):
  forall x,
    fun_decl (projT2 b) <> AST.StorageVarDecl x.
Proof.
unfold make_fun_ctx_and_bound in FC.
refine (match cd_declmap cd30 fun_name as z return _ = z -> _ with
        | Some (L30.AST.FunDecl name arity body) => fun E => _
        | _ => fun E => _
        end eq_refl); rewrite E in IsFun; try contradiction.
rewrite (match_some E) in FC.
refine (match cd_depthmap cd30 fun_name as z return _ = z -> _ with
        | Some depth => fun Edepth => _
        | _ => fun Edepth => _
        end eq_refl).
2:{ rewrite (match_none Edepth) in FC. exfalso. apply (Calldag.make_fun_ctx_helper E Edepth). }
rewrite (match_some Edepth) in FC.
inversion FC. subst b. clear FC.
cbn.
intros x H. discriminate.
Qed.

Theorem translate_ok {C: VyperConfig}
                     {B: builtin_names_config}
                     (builtins: string -> option builtin)
                     (cd30: L30.Descend.calldag)
                     (cd40: L40.Descend.calldag)
                     (SloadOk: BuiltinsSupportSload B builtins)
                     (SstoreOk: BuiltinsSupportSstore B builtins)
                     (BuiltinsOk: BuiltinsSupportUInt256 B builtins)
                     (Ok: translate_calldag B cd30 = inr cd40)
                     (fun_name: string)
                     (world: world_state)
                     (arg_values: list uint256):
  L40.Interpret.interpret builtins cd40 fun_name world arg_values
   =
  L30.Interpret.interpret builtins cd30 fun_name world arg_values.
Proof.
assert (T := translate_fun_ctx_declmap B Ok fun_name).
unfold L30.Interpret.interpret. unfold L40.Interpret.interpret.
unfold make_fun_ctx_and_bound.
refine (match cd_declmap cd30 fun_name as z return _ = z -> _ with
        | Some (L30.AST.FunDecl name30 arity30 body30) => fun E30 => _
        | _ => fun E30 => _
        end eq_refl); rewrite E30 in T;
  refine (match cd_declmap cd40 fun_name as z return _ = z -> _ with
          | Some (L40.AST.FunDecl name40 arity40 (AST.Block body40)) => fun E40 => _
          | None => fun E40 => _
          end eq_refl); rewrite E40 in T; try discriminate.
{ (* var decl *)
  rewrite (match_some E30). rewrite (match_none E40).
  refine (match cd_depthmap cd30 fun_name as z return _ = z -> _ with
          | Some depth => fun Edepth => _
          | _ => fun Edepth => _
          end eq_refl).
  2:{ exfalso. apply (Calldag.make_fun_ctx_helper E30 Edepth). }
  now rewrite (match_some Edepth).
}
2:{ (* nothing *) rewrite (match_none E30). rewrite (match_none E40). trivial. }
(* function *)
rewrite (match_some E30). rewrite (match_some E40).
refine (match cd_depthmap cd30 fun_name as z return _ = z -> _ with
        | Some depth => fun Edepth => _
        | _ => fun Edepth => _
        end eq_refl).
2:{ exfalso. apply (Calldag.make_fun_ctx_helper E30 Edepth). }
rewrite (match_some Edepth).
assert (D := translate_fun_ctx_depthmap B Ok fun_name).
rewrite Edepth in D.
rewrite (match_some D).
assert (OkBody: translate_stmt B (cd_decls cd30) body30 = inr body40) by now inversion T.
remember ({|
    fun_name := fun_name;
    fun_depth := depth;
    fun_depth_ok := Edepth;
    fun_decl := L30.AST.FunDecl name30 arity30 body30;
    fun_decl_ok := E30;
    fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth)
  |}) as fc30.
remember ({|
    fun_name := fun_name;
    fun_depth := depth;
    fun_depth_ok := D;
    fun_decl := AST.FunDecl name40 arity40 (AST.Block body40);
    fun_decl_ok := E40;
    fun_bound_ok := proj2 (Nat.ltb_lt depth (S depth)) (Nat.lt_succ_diag_r depth)
  |}) as fc40.
assert (FcNotVar: forall x : string, fun_decl fc30 <> AST.StorageVarDecl x).
{ subst. intros x H. cbn in H. discriminate. }
assert (P := FunCtx.translate_fun_ctx_decl_ok fc30 B Ok FcNotVar).
replace (Calldag.fun_name fc30) with fun_name in P by now subst.
assert (F: fc40 = translate_fun_ctx fc30 B Ok FcNotVar).
{
  subst. unfold translate_fun_ctx. cbn.
  rewrite E40 in P.
  remember (AST.FunDecl name40 arity40 (AST.Block body40)) as f. clear Heqf. 
  inversion P; subst f.
  f_equal; apply proof_irrelevance.
}
rewrite F. now apply interpret_translated_call.
Qed.