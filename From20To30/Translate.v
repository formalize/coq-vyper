From Coq Require Import NArith String.

From Vyper Require Import Config.
From Vyper Require Import L10.Base.
From Vyper Require L20.AST L30.AST.

Local Open Scope string_scope.

Fixpoint translate_expr {C: VyperConfig} (varmap: string_map N)
                        (dst: N)
                        (offset: N)
                        (e: L20.AST.expr)
{struct e}
: string + L30.AST.stmt
:= let fix translate_expr_list (varmap: string_map N)
                               (offset: N)
                               (exprs: list L20.AST.expr)
       {struct exprs}
       : string + L30.AST.stmt
       := match exprs with
          | nil => inr (L30.AST.SmallStmt L30.AST.Pass)
          | cons h t =>
             match translate_expr varmap offset (N.succ offset) h,
                   translate_expr_list varmap (N.succ offset) t
             with
             | inl err, _ | _, inl err => inl err
             | inr h', inr t' =>
                  inr (L30.AST.Semicolon h' t')
             end
          end
   in match e with
   | L20.AST.Const val => inr (L30.AST.SmallStmt (L30.AST.Const dst val))
   | L20.AST.LocalVar name =>
      match map_lookup varmap name with
      | Some src => inr (L30.AST.SmallStmt (L30.AST.Copy dst src))
      | None => inl "undefined local variable"
      end
   | L20.AST.StorageVar name => inr (L30.AST.SmallStmt (L30.AST.StorageGet dst name))
   | L20.AST.UnOp op a =>
       (* dst = a; dst = op tmp *)
       match translate_expr varmap dst offset a with
       | inl err => inl err
       | inr a' =>
           inr (L30.AST.Semicolon
                 a'
                 (L30.AST.SmallStmt (L30.AST.UnOp op dst dst)))
       end
   | L20.AST.BinOp op a b =>
       (* dst = a; tmp = b; dst = tmp1 op tmp2 *)
       match translate_expr varmap dst offset a,
             translate_expr varmap offset (N.succ offset)%N b
       with
       | inl err, _ | _, inl err => inl err
       | inr a', inr b' =>
           inr (L30.AST.Semicolon
                 (L30.AST.Semicolon a' b')
                 (L30.AST.SmallStmt (L30.AST.BinOp op dst dst offset)))
       end
   | L20.AST.PrivateCall name args =>
       match translate_expr_list varmap offset args with
       | inl err => inl err
       | inr args' =>
         inr (L30.AST.Semicolon
               args'
               (L30.AST.SmallStmt (L30.AST.PrivateCall dst name offset
                                                       (N.of_nat (List.length args)))))
       end
   | L20.AST.BuiltinCall name args =>
       match translate_expr_list varmap offset args with
       | inl err => inl err
       | inr args' =>
         inr (L30.AST.Semicolon
               args'
               (L30.AST.SmallStmt (L30.AST.BuiltinCall dst name offset
                                                       (N.of_nat (List.length args)))))
       end
   | L20.AST.IfThenElse cond yes no =>
       (* dst = cond; if dst { yes } else { no } *)
       match translate_expr varmap dst offset cond,
             translate_expr varmap dst offset yes,
             translate_expr varmap dst offset no
       with
       | inl err, _, _ | _, inl err, _ | _, _, inl err => inl err
       | inr cond', inr yes', inr no' =>
         inr (L30.AST.Semicolon cond'
               (L30.AST.IfElseStmt dst yes' no'))
       end
   | L20.AST.LogicalAnd a b =>
      (* dst = a; if dst { dst = b } else { } *)
       match translate_expr varmap dst offset a,
             translate_expr varmap dst offset b
       with
       | inl err, _ | _, inl err => inl err
       | inr a', inr b' =>
           inr (L30.AST.Semicolon
                 a'
                 (L30.AST.IfElseStmt dst b' (L30.AST.SmallStmt L30.AST.Pass)))
       end
   | L20.AST.LogicalOr a b =>
      (* dst = a; if dst { } else { dst = b } *)
       match translate_expr varmap dst offset a,
             translate_expr varmap dst offset b
       with
       | inl err, _ | _, inl err => inl err
       | inr a', inr b' =>
           inr (L30.AST.Semicolon
                 a'
                 (L30.AST.IfElseStmt dst (L30.AST.SmallStmt L30.AST.Pass) b'))
       end
   end.

Definition translate_small_stmt {C: VyperConfig}
                                (varmap: string_map N)
                                (offset: N)
                                (ss: L20.AST.small_stmt)
: string + L30.AST.stmt
:= match ss with
   | L20.AST.Pass => inr (L30.AST.SmallStmt L30.AST.Pass)
   | L20.AST.Abort ab => inr (L30.AST.SmallStmt (L30.AST.Abort ab))
   | L20.AST.Return result =>
      match translate_expr varmap offset (N.succ offset) result with
      | inl err => inl err
      | inr result' =>
          inr
            (L30.AST.Semicolon
              result'
              (L30.AST.SmallStmt (L30.AST.Return offset)))
      end
   | L20.AST.Raise error =>
      match translate_expr varmap offset (N.succ offset) error with
      | inl err => inl err
      | inr result' =>
          inr (L30.AST.Semicolon result' (L30.AST.SmallStmt (L30.AST.Raise offset)))
      end
   | L20.AST.Assign (L10.AST.AssignableLocalVar name) rhs =>
      match map_lookup varmap name with
      | None => inl "undefined local variable"
      | Some n => translate_expr varmap n offset rhs
      end
   | L20.AST.Assign (L10.AST.AssignableStorageVar name) rhs =>
      match translate_expr varmap offset (N.succ offset) rhs with
      | inl err => inl err
      | inr rhs' =>
          inr (L30.AST.Semicolon rhs' (L30.AST.SmallStmt (L30.AST.StoragePut name offset)))
      end
   | L20.AST.ExprStmt e => translate_expr varmap offset (N.succ offset) e
   end.

Fixpoint translate_stmt {C: VyperConfig}
                        (varmap: string_map N)
                        (offset: N)
                        (s: L20.AST.stmt)
: string + L30.AST.stmt
:= match s with
   | L20.AST.SmallStmt s => translate_small_stmt varmap offset s
   | L20.AST.LocalVarDecl name init body =>
      match map_lookup varmap name with
      | Some _ => inl "local variable already exists"
      | None =>
          match translate_expr varmap offset (N.succ offset) init,
                translate_stmt (map_insert varmap name offset) offset body
          with
          | inl err, _ | _, inl err => inl err
          | inr init', inr body' =>
              inr (L30.AST.Semicolon init' body')
          end
      end
   | L20.AST.IfElseStmt cond yes no =>
       match translate_expr varmap offset (N.succ offset) cond,
             translate_stmt varmap offset yes,
             translate_stmt varmap offset no
       with
       | inl err, _, _ | _, inl err, _ | _, _, inl err => inl err
       | inr cond', inr yes', inr no' =>
         inr (L30.AST.Semicolon cond'
               (L30.AST.IfElseStmt offset yes' no'))
       end
   | L20.AST.Loop var start count body =>
       match map_lookup varmap var with
       | Some _ => inl "local variable already exists"
       | None =>
           match translate_expr varmap offset (N.succ offset) start,
                 translate_stmt (map_insert varmap var offset) (N.succ offset) body
           with
           | inl err, _ | _, inl err => inl err
           | inr start', inr body' =>
             inr (L30.AST.Semicolon start' (L30.AST.Loop offset count body'))
           end
       end
   | L20.AST.Semicolon a b =>
      match translate_stmt varmap offset a,
            translate_stmt varmap offset b
      with
      | inl err, _ | _, inl err => inl err
      | inr a', inr b' => inr (L30.AST.Semicolon a' b')
      end
   end.