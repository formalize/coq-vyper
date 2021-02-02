From Coq Require Import NArith ZArith Lia String HexString.

From Vyper Require Import Config Calldag.
From Vyper.L30 Require Import AST Callset Descend VarCap.

From Vyper.CheckArith Require Import Builtins CheckedArith.

Definition arithmetic_error
:= Z.of_N
     (List.fold_left (fun x y => N.lor (N.shiftl x 8) y)
       (List.map Ascii.N_of_ascii (list_ascii_of_string "arithmetic error"))
       0%N).

Example hex_arithmetic_error:
  HexString.of_Z arithmetic_error = "0x61726974686d65746963206572726f72"%string.
                                    (*  a r i t h m e t i c   e r r o r *)
Proof. trivial. Qed.

(** AST for [dst = "arithmetic error"; raise dst] *)
Definition ast_raise_arithmetic_error {C: VyperConfig} (dst: N)
: stmt
:= Semicolon (SmallStmt (Const dst (uint256_of_Z arithmetic_error)))
             (SmallStmt (Raise dst)).

(** AST for [scratch[0] = a; scratch[1] = b] *)
Definition ast_pair_to_scratch {C: VyperConfig} (a b: N) (scratch: N)
: stmt
:= Semicolon (SmallStmt (Copy scratch a))
             (SmallStmt (Copy (N.succ scratch) b)).

Definition translate_small_stmt {C: VyperConfig} (B: builtin_names_config)
                                (scratch: N)
                                (ss: small_stmt)
: stmt
:= match ss with
   | UnOp op dst src =>
      match op with
      | L10.AST.BitwiseNot =>
          SmallStmt (BuiltinCall dst (builtin_name_uint256_not B) src 1%N)
      | L10.AST.LogicalNot =>
          SmallStmt (BuiltinCall dst (builtin_name_uint256_iszero B) src 1%N)
      | L10.AST.Neg =>
          (* if src:
               scratch = "arithmetic error"
               raise scratch
             else:
               dst = 0
           *)
          (IfElseStmt src
            (ast_raise_arithmetic_error scratch)
            (SmallStmt (Const dst zero256)))
      end
   | BinOp op dst a b NEpow =>
      match op as op' return op = op' -> _ with
      | L10.AST.BitwiseAnd => fun _ =>
          Semicolon (ast_pair_to_scratch a b scratch)
            (SmallStmt (BuiltinCall dst (builtin_name_uint256_and B) scratch 2%N))
      | L10.AST.BitwiseOr => fun _ =>
          Semicolon (ast_pair_to_scratch a b scratch)
                    (SmallStmt (BuiltinCall dst (builtin_name_uint256_or B) scratch 2%N))
      | L10.AST.BitwiseXor => fun _ =>
          Semicolon (ast_pair_to_scratch a b scratch)
                    (SmallStmt (BuiltinCall dst (builtin_name_uint256_xor B) scratch 2%N))
      | L10.AST.Lt => fun _ =>
          Semicolon (ast_pair_to_scratch a b scratch)
                    (SmallStmt (BuiltinCall dst (builtin_name_uint256_lt B) scratch 2%N))
      | L10.AST.Gt => fun _ =>
          Semicolon (ast_pair_to_scratch b a scratch)
                    (SmallStmt (BuiltinCall dst (builtin_name_uint256_lt B) scratch 2%N))
      | L10.AST.Eq => fun _ =>
          Semicolon (ast_pair_to_scratch a b scratch)
                    (SmallStmt (BuiltinCall dst (builtin_name_uint256_eq B) scratch 2%N))
      | L10.AST.Ne => fun _ =>
          Semicolon 
            (ast_pair_to_scratch a b scratch)
            (Semicolon
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_eq B) scratch 2%N))
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_iszero B) dst 1%N)))
      | L10.AST.Ge => fun _ =>
          Semicolon 
            (ast_pair_to_scratch a b scratch)
            (Semicolon
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_lt B) scratch 2%N))
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_iszero B) dst 1%N)))
      | L10.AST.Le => fun _ =>
          Semicolon 
            (ast_pair_to_scratch b a scratch)
            (Semicolon
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_lt B) scratch 2%N))
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_iszero B) dst 1%N)))
      | L10.AST.Add => fun _ =>
          (*
            scratch[0] = a                                     # a
            scratch[1] = b                                     # a           b
            scratch[1] = builtin("uint256_add", scratch, 2)    # a           a + b
            scratch[2] = a                                     # a           a + b      a
            scratch[0] = builtin("uint256_lt", scratch1, 2)    # a + b < a   a + b      a
            if scratch[0]:
              raise "arithmetic error"
            else:
              dst = scratch[1]
          *)
          Semicolon
            (ast_pair_to_scratch a b scratch)
            (Semicolon
              (SmallStmt (BuiltinCall (N.succ scratch)
                                      (builtin_name_uint256_add B)
                                      scratch 2%N))
              (Semicolon
                (SmallStmt (Copy (scratch + 2)%N a))
                (Semicolon
                  (SmallStmt (BuiltinCall scratch
                                          (builtin_name_uint256_lt B)
                                          (N.succ scratch) 2%N))
                  (IfElseStmt scratch
                    (ast_raise_arithmetic_error scratch)
                    (SmallStmt (Copy dst (N.succ scratch)))))))
      | L10.AST.Sub => fun _ =>
          (*
             scratch0 = a
             scratch1 = b
             scratch2 = builtin("uint256_lt", scratch, 2)
             if scratch2:
               raise "arithmetic error"
             else:
               dst = builtin("uint256_sub", scratch, 2)
          *)
          Semicolon
            (ast_pair_to_scratch a b scratch)
            (Semicolon
              (SmallStmt (BuiltinCall (scratch + 2)%N (builtin_name_uint256_lt B) scratch 2%N))
              (IfElseStmt (scratch + 2)%N
                (ast_raise_arithmetic_error scratch)
                (SmallStmt (BuiltinCall dst (builtin_name_uint256_sub B) scratch 2))))
      | L10.AST.Mul => fun _ =>
          (*
             if a:
               scratch1 = a                                    #       a
               scratch2 = b                                    #       a         b
               scratch0 = builtin("uint256_mul", scratch1, 2)  # a*b   a         b
               scratch1 = builtin("uint256_div", scratch0, 2)  # a*b   a*b/a     b
               scratch1 = builtin("uint256_eq",  scratch1, 2)  # a*b   a*b/a==b  b
               if scratch1:
                 dst = scratch0
               else:
                 raise "arithmetic error"
             else:
               dst = 0
          *)
          IfElseStmt a
            (Semicolon
               (ast_pair_to_scratch a b (N.succ scratch))
               (Semicolon
                 (Semicolon
                   (SmallStmt (BuiltinCall scratch (builtin_name_uint256_mul B)
                                           (N.succ scratch) 2%N))
                   (Semicolon
                     (SmallStmt (BuiltinCall (N.succ scratch) (builtin_name_uint256_div B)
                                             scratch 2%N))
                     (SmallStmt (BuiltinCall (N.succ scratch) (builtin_name_uint256_eq B)
                                             (N.succ scratch) 2%N))))
                 (IfElseStmt (N.succ scratch)
                   (SmallStmt (Copy dst scratch))
                   (ast_raise_arithmetic_error scratch))))
            (SmallStmt (Const dst zero256))
      | L10.AST.Quot => fun _ =>
          (*
             if b:
               scratch[0] = a
               scratch[1] = b
               dst = builtin("uint256_div",  scratch1, 2)
             else
               raise "arithmetic error"
          *)
          IfElseStmt b
            (Semicolon
              (ast_pair_to_scratch a b scratch)
              (SmallStmt (BuiltinCall dst (builtin_name_uint256_div B) scratch 2%N)))
            (ast_raise_arithmetic_error scratch)
      | L10.AST.Mod => fun _ =>
          (*
             if b:
               scratch[0] = a
               scratch[1] = b
               dst = builtin("uint256_mod",  scratch1, 2)
             else
               raise "arithmetic error"
          *)
          IfElseStmt b
                (Semicolon
                  (ast_pair_to_scratch a b scratch)
                  (SmallStmt (BuiltinCall dst (builtin_name_uint256_mod B) scratch 2%N)))
                (ast_raise_arithmetic_error scratch)
      | L10.AST.ShiftRight => fun _ =>
          Semicolon
                (ast_pair_to_scratch a b scratch)
                (SmallStmt (BuiltinCall dst (builtin_name_uint256_shr B) scratch 2%N))
      | L10.AST.ShiftLeft => fun _ =>
          (*
             scratch0 = a                                   #    a
             scratch1 = b                                   #    a            b
             scratch0 = builtin("uint256_shl", scratch, 2)  #    a<<b         b
             scratch1 = builtin("uint256_shr", scratch, 2)  #    a<<b         (a<<b)>>b
             # I had originally written this:
             #   dst = scratch0
             #   scratch0 = a                               #    a            (a<<b)>>b
             # But Coq rejected it because dst may be aliased with a here.
             # Here's the correct code:
             scratch2 = a                                   #    a<<b         (a<<b)>>b    a
             scratch1 = builtin("uint256_eq", scratch1, 2)  #    (a<<b)>>b==a (a<<b)>>b    a
             if scratch1:
               dst = scratch0
             else:
               raise "arithmetic error"
          *)
          Semicolon
             (ast_pair_to_scratch a b scratch)
             (Semicolon
               (SmallStmt (BuiltinCall scratch (builtin_name_uint256_shl B) scratch 2%N))
               (Semicolon
                 (SmallStmt (BuiltinCall (N.succ scratch) (builtin_name_uint256_shr B)
                                         scratch 2%N))
                 (Semicolon
                   (SmallStmt (Copy (scratch + 2)%N a))
                     (Semicolon
                       (SmallStmt (BuiltinCall (N.succ scratch) (builtin_name_uint256_eq B)
                                               (N.succ scratch) 2%N))
                       (IfElseStmt (N.succ scratch)
                         (SmallStmt (Copy dst scratch))
                         (ast_raise_arithmetic_error scratch))))))
      | L10.AST.Pow => fun E => False_rect _ (NEpow E)
      end eq_refl
   | PowConstBase dst base exp =>
       let zbase := Z_of_uint256 base in
       if (zbase =? 0)%Z
         then (* iszero(exp) *)
              SmallStmt (BuiltinCall dst (builtin_name_uint256_iszero B) exp 1%N)
         else
           if (zbase =? 1)%Z
             then SmallStmt (Const dst one256) (* 1 *)
             else
               if (zbase =? 2)%Z
                 then (* scratch1 = exp
                         scratch2 = 256
                         scratch2 = builtin("uint256_lt", scratch1, 2)
                         if scratch2:
                           scratch0 = 1
                           dst = builtin("uint256_shl", scratch0, 2)
                         else:
                           raise "arithmetic error"
                      *)
                      Semicolon
                        (SmallStmt (Copy (N.succ scratch) exp))
                        (Semicolon
                          (SmallStmt (Const (scratch + 2)%N (uint256_of_Z 256%Z)))
                          (Semicolon
                            (SmallStmt (BuiltinCall (scratch + 2)%N
                                                    (builtin_name_uint256_lt B)
                                                    (N.succ scratch) 2%N))
                            (IfElseStmt (scratch + 2)%N
                              (Semicolon
                                (SmallStmt (Const scratch one256))
                                (SmallStmt (BuiltinCall dst
                                                        (builtin_name_uint256_shl B)
                                                        scratch 2%N)))
                              (ast_raise_arithmetic_error scratch))))
                 else (*
                         scratch0 = uint256_max_power base
                         scratch1 = exp
                         scratch2 = builtin("uint256_lt", scratch, 2)
                         if scratch2:
                           raise "arithmetic error"
                         else:
                           scratch0 = base
                           dst = builtin("uint256_pow", scratch, 2)
                      *)
                      Semicolon
                        (SmallStmt (Const scratch
                                     (uint256_of_Z (uint256_max_power zbase))))
                        (Semicolon
                          (SmallStmt (Copy (N.succ scratch) exp))
                          (Semicolon
                            (SmallStmt (BuiltinCall (scratch + 2)%N (builtin_name_uint256_lt B)
                                                    scratch 2))
                            (IfElseStmt (scratch + 2)%N
                              (ast_raise_arithmetic_error scratch)
                              (Semicolon
                                (SmallStmt (Const scratch base))
                                (SmallStmt (BuiltinCall dst (builtin_name_uint256_pow B)
                                                        scratch 2))))))
   | PowConstExp dst base exp =>
      let zexp := Z_of_uint256 exp in
      if (zexp =? 0)%Z
        then SmallStmt (Const dst one256) (* 1 *)
        else
          if (zexp =? 1)%Z
            then (* we do actually have to compute base ** 1 to canonicalize uint256 *)
              Semicolon
                (SmallStmt (Copy scratch base))
                (Semicolon
                  (SmallStmt (Const (N.succ scratch) one256))
                  (SmallStmt (BuiltinCall dst (builtin_name_uint256_pow B)
                                          scratch 2)))
            else (*
                   scratch0 = base
                   scratch1 = uint256_max_base zexp + 1
                   scratch1 = builtin("uint256_lt", scratch, 2)
                   if scratch1:
                     scratch1 = exp
                     dst = builtin("uint256_pow", scratch, 2)
                   else:
                     raise "arithmetic error"
                 *)
             Semicolon
               (SmallStmt (Copy scratch base))
               (Semicolon
                 (SmallStmt (Const (N.succ scratch)
                                   (uint256_of_Z (Z.succ (uint256_max_base zexp)))))
                 (Semicolon
                   (SmallStmt (BuiltinCall (N.succ scratch) (builtin_name_uint256_lt B)
                                           scratch 2))
                   (IfElseStmt (N.succ scratch)
                     (Semicolon
                       (SmallStmt (Const (N.succ scratch) exp))
                       (SmallStmt (BuiltinCall dst (builtin_name_uint256_pow B)
                                               scratch 2)))
                     (ast_raise_arithmetic_error scratch))))
   | _ => SmallStmt ss
   end.

Fixpoint translate_stmt {C: VyperConfig} (B: builtin_names_config)
                        (scratch: N)
                        (s: stmt)
{struct s}
: stmt
:= match s with
   | SmallStmt ss => translate_small_stmt B scratch ss
   | IfElseStmt cond yes no => IfElseStmt cond (translate_stmt B scratch yes)
                                               (translate_stmt B scratch no)
   | Loop var count body => Loop var count (translate_stmt B scratch body)
   | Semicolon a b => Semicolon (translate_stmt B scratch a)
                                (translate_stmt B scratch b)
   end.

Definition translate_decl {C: VyperConfig} (B: builtin_names_config)
                          (d: decl)
: decl
:= match d with
   | StorageVarDecl var => d
   | FunDecl name arity body => FunDecl name arity (translate_stmt B (var_cap_stmt body) body)
   end.

Ltac rr := cbn; trivial;
           repeat rewrite FSet.union_ok;
           repeat rewrite FSet.empty_ok;
           trivial.

Lemma callset_translate_small_stmt {C: VyperConfig}
                                   (B: builtin_names_config)
                                   (scratch: N)
                                   (ss: small_stmt)
                                   (x: string):
  let _ := string_set_impl in
  FSet.has (stmt_callset (translate_small_stmt B scratch ss)) x
   =
  FSet.has (small_stmt_callset ss) x.
Proof.
cbn.
destruct ss; simpl; trivial. (* cbn hangs *)
{ (* UnOp *) destruct op; rr. }
{ (* PowConstBase *)
  destruct Z.eqb. { easy. }
  destruct Z.eqb. { easy. }
  destruct Z.eqb; rr.
}
{ (* PowConstExp *)
  destruct Z.eqb. { easy. }
  destruct Z.eqb; cbn; rr.
}
(* Binop *)
destruct op; simpl; rr.
contradiction.
Qed.

Lemma callset_translate_stmt {C: VyperConfig}
                             (B: builtin_names_config)
                             (scratch: N)
                             (s: stmt)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (stmt_callset (translate_stmt B scratch s)) x
   =
  FSet.has (stmt_callset s) x.
Proof.
cbn.
induction s; cbn; try assumption.
{ (* SmallStmt *) apply callset_translate_small_stmt. }
1-2: repeat rewrite FSet.union_ok;
     rewrite IHs1; rewrite IHs2;
     trivial.
Qed.

Lemma callset_translate_decl {C: VyperConfig}
                             (B: builtin_names_config)
                             (d: decl)
                             (x: string):
  let _ := string_set_impl in
  FSet.has (decl_callset (translate_decl B d)) x
   =
  FSet.has (decl_callset d) x.
Proof.
destruct d; cbn. { easy. }
apply callset_translate_stmt.
Qed.

Local Lemma translate_calldag_helper {C: VyperConfig}
                                     (B: builtin_names_config)
                                     (cd: calldag):
  let H := string_set_impl in
  forall d: decl,
    FSet.is_subset (decl_callset (translate_decl B d)) (decl_callset d) = true.
Proof.
cbn. intro.
apply FSet.is_subset_equal.
apply FSet.equal_ok.
apply callset_translate_decl.
Qed.

Definition translate_calldag {C: VyperConfig}
                             (B: builtin_names_config)
                             (cd: calldag)
:= calldag_map (translate_decl B)
               (translate_calldag_helper B cd)
               cd.

Definition translate_fun_ctx {C: VyperConfig}
                             (B: builtin_names_config)
                             {bound: nat}
                             {cd: calldag}
                             (fc: fun_ctx cd bound)
: fun_ctx (calldag_map (translate_decl B) (translate_calldag_helper B cd) cd) bound
:= fun_ctx_map (translate_decl B) _ cd fc.
