From Coq Require Import ZArith NArith String Lia.

From Vyper Require Import Config NaryFun.
From Vyper Require L30.AST L40.AST.
From Vyper.CheckArith Require Import Builtins.

From Vyper.L10 Require Import Base.

Local Open Scope string_scope.
Local Open Scope list_scope.


Definition BuiltinsSupportSload {C: VyperConfig}
                                (B: builtin_names_config)
                                (builtins: string -> option builtin)
:= match builtins (builtin_name_sload B) with
   | Some (existT _ 1 sload) =>
       forall (w: world_state) (name: string),
         match sload w (string_hash name) with
         | (w', ExprAbort _) => False
         | (w', ExprSuccess val) =>
               w = w'
                /\
               val = match storage_lookup w name with
                     | Some x => x
                     | None => zero256
                     end
         end
   | _ => False
   end.

Definition BuiltinsSupportSstore {C: VyperConfig}
                                 (B: builtin_names_config)
                                 (builtins: string -> option builtin)
:= match builtins (builtin_name_sstore B) with
   | Some (existT _ 2 sstore) =>
       forall (w: world_state) (name: string) (value: uint256),
         match sstore w (string_hash name) value with
         | (w', ExprAbort _) => False
         | (w', ExprSuccess _) =>
               w' = storage_insert w name value
         end
   | _ => False
   end.

Definition BuiltinsSupportStorage {C: VyperConfig}
                                  (B: builtin_names_config)
                                  (builtins: string -> option builtin)
:= BuiltinsSupportSload B builtins /\ BuiltinsSupportSstore B builtins.



Definition var_range {C: VyperConfig} (offset count: N)
: list L40.AST.expr
:= let fix var_range' (countdown: nat)
   := match countdown with
      | O => nil
      | S k => cons (L40.AST.LocalVar (offset + count - 1 - N.of_nat k)%N)
                    (var_range' k)
      end
   in var_range' (N.to_nat count).

Local Example var_range_example {C: VyperConfig}:
  var_range 5 3 = (AST.LocalVar 5 :: AST.LocalVar 6 :: AST.LocalVar 7 :: nil)%list.
Proof.
trivial.
Qed.

Definition var_range_nat {C: VyperConfig} (offset count: nat)
: list L40.AST.expr
:= let fix var_range' (countdown: nat)
   := match countdown with
      | O => nil
      | S k => cons (L40.AST.LocalVar (N.of_nat (offset + count - 1 - k)))
                    (var_range' k)
      end
   in var_range' count.

Lemma var_range_nat_ok {C: VyperConfig} (offset count: nat):
  var_range_nat offset count = var_range (N.of_nat offset) (N.of_nat count).
Proof.
unfold var_range, var_range_nat.
rewrite Nat2N.id.
revert offset. induction count. { trivial. }
intro offset. cbn.
assert (IH := IHcount (S offset)). clear IHcount.
f_equal. { f_equal. lia. }
assert (EqLHS:
          forall t,
            (fix var_range' (countdown : nat) : list AST.expr :=
             match countdown with
             | 0 => nil
             | S k => AST.LocalVar (N.of_nat (offset + S count - 1 - k)) :: var_range' k
             end) t
              =
            (fix var_range' (countdown : nat) : list AST.expr :=
             match countdown with
             | 0 => nil
             | S k => AST.LocalVar (N.of_nat (S offset + count - 1 - k)) :: var_range' k
             end) t).
{
  clear IH. intro t.
  revert offset. induction t. { easy. }
  intro offset.
  f_equal. 2:apply IHt.
  f_equal. f_equal. lia.
}
rewrite EqLHS. clear EqLHS.
assert (EqRHS:
          forall t,
            (fix var_range' (countdown : nat) : list AST.expr :=
             match countdown with
             | 0 => nil
             | S k =>
                 AST.LocalVar (N.of_nat offset + N.pos (Pos.of_succ_nat count) - 1 - N.of_nat k) :: var_range' k
             end) t
              =
            (fix var_range' (countdown : nat) : list AST.expr :=
             match countdown with
             | 0 => nil
             | S k => AST.LocalVar (N.of_nat (S offset) + N.of_nat count - 1 - N.of_nat k) :: var_range' k
             end) t).
{
  clear IH. intro t.
  revert offset. induction t. { easy. }
  intro offset.
  f_equal. 2:apply IHt.
  f_equal. f_equal. lia.
}
rewrite EqRHS. clear EqRHS.
apply IH.
Qed.

Lemma var_range_via_nat {C: VyperConfig} (offset count: N):
  var_range offset count = var_range_nat (N.to_nat offset) (N.to_nat count).
Proof.
rewrite var_range_nat_ok.
now repeat rewrite N2Nat.id.
Qed.


Definition translate_small_stmt {C: VyperConfig}
                                (B: builtin_names_config)
                                (declmap: string_map L30.AST.decl)
                                (ss: L30.AST.small_stmt)
: string + list L40.AST.stmt
:= let op_err := "an operator in L30 can't possibly occur after the CheckArith pass"%string in
   match ss with
   | L30.AST.Pass => inr nil
   | L30.AST.Const dst val =>
      inr ((L40.AST.SmallStmt (L40.AST.Assign dst (L40.AST.Const val))) :: nil)
   | L30.AST.Copy dst src =>
      inr ((L40.AST.SmallStmt (L40.AST.Assign dst (L40.AST.LocalVar src))) :: nil)
   | L30.AST.StorageGet dst name =>
      match map_lookup declmap name with
      | Some (L30.AST.StorageVarDecl _) =>
          inr ((L40.AST.SmallStmt
                  (L40.AST.Assign dst
                    (L40.AST.BuiltinCall
                      (builtin_name_sload B)
                      (L40.AST.Const (string_hash name) :: nil)))) :: nil)
      | _ => inl ("undeclared global variable: " ++ name)%string
      end
   | L30.AST.StoragePut name src =>
      match map_lookup declmap name with
      | Some (L30.AST.StorageVarDecl _) =>
          inr ((L40.AST.SmallStmt
                  (L40.AST.ExprStmt
                    (L40.AST.BuiltinCall
                      (builtin_name_sstore B)
                      (L40.AST.Const (string_hash name) :: L40.AST.LocalVar src :: nil)))) :: nil)
      | _ => inl ("undeclared global variable: " ++ name)%string
      end
   | L30.AST.UnOp _ _ _ => inl op_err
   | L30.AST.PowConstBase _ _ _ => inl op_err
   | L30.AST.PowConstExp _ _ _ => inl op_err
   | L30.AST.BinOp _ _ _ _ _ => inl op_err
   | L30.AST.PrivateCall dst name args_offset args_count =>
        match map_lookup declmap name with
        | Some (L30.AST.FunDecl _ _ _) =>
            inr ((L40.AST.SmallStmt
                   (L40.AST.Assign dst
                     (L40.AST.PrivateCall name (var_range args_offset args_count)))) :: nil)
        | _ => inl ("unable to resolve function: " ++ name)%string
        end
   | L30.AST.BuiltinCall dst name args_offset args_count =>
        inr ((L40.AST.SmallStmt
               (L40.AST.Assign dst
                 (L40.AST.BuiltinCall name (var_range args_offset args_count)))) :: nil)
   | L30.AST.Abort ab =>
        inr ((L40.AST.SmallStmt (L40.AST.Abort ab)) :: nil)
   | L30.AST.Return var =>
        inr ((L40.AST.SmallStmt (L40.AST.Return (L40.AST.LocalVar var))) :: nil)
   | L30.AST.Raise var =>
        inr ((L40.AST.SmallStmt (L40.AST.Raise  (L40.AST.LocalVar var))) :: nil)
   end.

Fixpoint translate_stmt {C: VyperConfig}
                        (B: builtin_names_config)
                        (declmap: string_map L30.AST.decl)
                        (s: L30.AST.stmt)
{struct s}
: string + list L40.AST.stmt
:= match s with
   | L30.AST.SmallStmt ss => translate_small_stmt B declmap ss
   | L30.AST.Semicolon a b =>
      match translate_stmt B declmap a with
      | inl err => inl err
      | inr aa => match translate_stmt B declmap b with
                  | inl err => inl err
                  | inr bb => inr (aa ++ bb)
                  end
      end
   | L30.AST.IfElseStmt condvar yes no =>
      match translate_stmt B declmap yes with
      | inl err => inl err
      | inr yes' =>
          match translate_stmt B declmap no with 
          | inl err => inl err
          | inr no' =>
              inr (L40.AST.Switch (L40.AST.LocalVar condvar)
                                  (L40.AST.Case zero256 (L40.AST.Block no') :: nil)
                                  (Some (L40.AST.Block yes')) :: nil)
          end
      end
   | L30.AST.Loop loopvar count body =>
      let count_z := Z_of_uint256 count in
      if (count_z =? 0)%Z
        then inl "zero-count loops are not allowed"
        else match translate_stmt B declmap body with
             | inl err => inl err
             | inr body' =>
                  inr
                    (* start_z + count_z - 1 < 2^256
                        <->
                       start_z <= 2^256 - count_z *)
                    (L40.AST.Switch
                      (L40.AST.BuiltinCall
                        (builtin_name_uint256_lt B)
                          (L40.AST.Const (uint256_of_Z (2 ^ 256 - count_z)%Z)
                             :: L40.AST.LocalVar loopvar
                             :: nil))
                      ((L40.AST.Case zero256
                        (L40.AST.Block
                          ((L40.AST.Loop loopvar count
                            (L40.AST.Block
                              ((L40.AST.SmallStmt
                                (L40.AST.Assign loopvar
                                  (L40.AST.BuiltinCall (builtin_name_uint256_add B)
                                    (L40.AST.LoopOffset :: L40.AST.LoopCursor :: nil))))
                                :: body')))
                            :: nil)))
                        :: nil)
                      (Some
                        (L40.AST.Block
                          ((L40.AST.SmallStmt
                            (L40.AST.Abort
                              (AbortException (uint256_of_Z (Z_of_string "loop range overflows")))))
                            :: nil)))
                        :: nil)
             end
   end.
