From Coq Require Import Arith NArith ZArith Lia String.

From Vyper Require Import Logic2.
From Vyper Require Import Config L10.Base Calldag.
From Vyper Require OpenArray.
From Vyper Require Import UInt256.
From Vyper.L30 Require Import AST Stmt Callset VarCap Interpret.
From Vyper.CheckArith Require Import CheckedArith Translate Builtins Stmt.

Lemma translate_call_ok {C: VyperConfig}
                        {bigger_call_depth_bound smaller_call_depth_bound: nat}
                        (Ebound: bigger_call_depth_bound = S smaller_call_depth_bound)
                        (builtins: string -> option L10.Base.builtin)
                        {B: builtin_names_config}
                        (BuiltinsOk: BuiltinsSupportUInt256 B builtins)
                        {cd: L30.Descend.calldag}
                        (fc: fun_ctx cd bigger_call_depth_bound)
                        (world: world_state)
                        (arg_values: list uint256):
  interpret_call builtins (translate_fun_ctx B fc) world arg_values
   =
  interpret_call builtins fc world arg_values.
Proof.
revert world arg_values smaller_call_depth_bound Ebound. induction bigger_call_depth_bound.
{ exfalso. exact (Nat.nlt_0_r _ (proj1 (Nat.ltb_lt _ _) (fun_bound_ok fc))). }
intros. cbn.
assert(F: cached_mapped_decl (translate_decl B) (Translate.translate_calldag_helper B cd) cd fc
           =
          translate_decl B (fun_decl fc)).
{
  clear IHbigger_call_depth_bound.
  unfold cached_mapped_decl.
  remember (Calldag.calldag_map_fun_ctx_fun_decl_helper _ _ cd fc) as foo.
  clear Heqfoo.
  remember (cd_declmap (calldag_map (translate_decl B) (Translate.translate_calldag_helper B cd) cd)
    (fun_name fc)) as d.
  destruct d. 2:{ contradiction. }
  subst.
  assert (Q := calldag_map_declmap (translate_decl B) (Translate.translate_calldag_helper B cd) cd (fun_name fc)).
  destruct (cd_declmap (calldag_map (translate_decl B) (Translate.translate_calldag_helper B cd) cd) (fun_name fc)) as [d'|]. 2:discriminate.
  inversion Heqd. subst d'. clear Heqd.
  remember (cd_declmap cd (fun_name fc)) as x.
  destruct x as [x|]. 2:discriminate.
  inversion Q. f_equal.
  assert (D := fun_decl_ok fc).
  rewrite D in *. inversion Heqx.
  trivial.
}
intros.
cbn.
remember (fun name arity body
              (E: cached_mapped_decl (translate_decl B) (Translate.translate_calldag_helper B cd) cd fc =
                      FunDecl name arity body) =>
      if Datatypes.length arg_values =? N.to_nat arity
          then
           let
           '(world', _, result) :=
            interpret_stmt eq_refl (translate_fun_ctx B fc) (interpret_call builtins) builtins world
              (OpenArray.from_list arg_values) body (Interpret.interpret_call_helper E) in
            (world',
            match result with
            | StmtSuccess => ExprSuccess zero256
            | StmtAbort a => ExprAbort a
            | StmtReturnFromFunction x => ExprSuccess x
            end)
          else
           (world,
           expr_error
             (if match N.to_nat arity with
                 | 0 => false
                 | S m' => Datatypes.length arg_values <=? m'
                 end
              then "function called with too few arguments"%string
              else "function called with too many arguments"%string))
) as branch_l.
remember (fun name arity body
              (E : fun_decl fc = FunDecl name arity body) =>
  if Datatypes.length arg_values =? N.to_nat arity
    then
     let
     '(world', _, result) :=
      interpret_stmt eq_refl fc (interpret_call builtins) builtins world
        (OpenArray.from_list arg_values) body (Interpret.interpret_call_helper E) in
      (world',
      match result with
      | StmtSuccess => ExprSuccess zero256
      | StmtAbort a => ExprAbort a
      | StmtReturnFromFunction x => ExprSuccess x
      end)
    else
     (world,
     expr_error
       (if match N.to_nat arity with
           | 0 => false
           | S m' => Datatypes.length arg_values <=? m'
           end
        then "function called with too few arguments"%string
        else "function called with too many arguments"%string))) as branch_r.
enough (Ok: forall name arity body_l body_r E_l E_r,
             branch_l name arity body_l E_l
              =
             branch_r name arity body_r E_r).
{
  clear Heqbranch_l Heqbranch_r.
  destruct (fun_decl fc); cbn in F; destruct cached_mapped_decl; try easy.
  inversion F; subst.
  apply Ok.
}
intros. subst.
destruct (Datatypes.length arg_values =? N.to_nat arity). 2:easy.

rewrite E_l in F. rewrite E_r in F.
cbn in F. inversion F; subst body_l; clear F.
rename body_r into body.

assert (DoCallOk: forall (fc : fun_ctx cd bigger_call_depth_bound)
                              (world : world_state) (arg_values : list uint256),
                            interpret_call builtins (translate_fun_ctx B fc) world arg_values =
                            interpret_call builtins fc world arg_values).
{
  intros.
  destruct bigger_call_depth_bound as [|n]. { easy. }
  now apply IHbigger_call_depth_bound with (smaller_call_depth_bound := n).
}
assert (T := let _ := memory_impl in
             translate_stmt_ok eq_refl builtins B (var_cap_stmt body) BuiltinsOk
             fc DoCallOk body
             (Interpret.interpret_call_helper E_l)
             (Interpret.interpret_call_helper E_r)
             world
             (OpenArray.from_list arg_values)
             (OpenArray.from_list arg_values)
             (N.le_refl _)
             (fun _ _ => eq_refl)).
cbn in T.
destruct interpret_stmt as ((w', m'), result'); destruct interpret_stmt as ((w, m), result).
destruct T as (Rresult, (Rw, _)). subst. trivial.
Qed.

Theorem translate_ok {C: VyperConfig}
                     (builtins: string -> option L10.Base.builtin)
                     {B: builtin_names_config}
                     (BuiltinsOk: BuiltinsSupportUInt256 B builtins)
                     (cd: L30.Descend.calldag)
                     (fun_name: string)
                     (world: world_state)
                     (arg_values: list uint256):
  interpret builtins (translate_calldag B cd) fun_name world arg_values
   =
  interpret builtins cd fun_name world arg_values.
Proof.
unfold interpret.
unfold translate_calldag.
rewrite (make_fun_ctx_and_bound_map (translate_decl B) _).
destruct (make_fun_ctx_and_bound cd fun_name) as [(bound, fc)|]; cbn. 2:{ trivial. }
destruct bound. { easy. }
apply (translate_call_ok eq_refl builtins BuiltinsOk fc world arg_values).
Qed.