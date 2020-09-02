From Coq Require Import String ZArith Eqdep_dec.

From Vyper Require Import Config Calldag L10.Base.
From Vyper Require L10.AST L20.AST L10.Interpret L20.Interpret.

Section Translate.

Context {C: VyperConfig}
        (is_private_call: string -> bool).

(* The only difference in L10 and L20 expressions are the calls. *)
Fixpoint translate_expr (e: L10.AST.expr)
: L20.AST.expr
:= match e with
   | L10.AST.Const val => L20.AST.Const val
   | L10.AST.LocalVar name => L20.AST.LocalVar name
   | L10.AST.StorageVar name => L20.AST.StorageVar name
   | L10.AST.UnOp op a => L20.AST.UnOp op (translate_expr a)
   | L10.AST.BinOp op a b => L20.AST.BinOp op (translate_expr a)
                                              (translate_expr b)
   | L10.AST.IfThenElse cond yes no => L20.AST.IfThenElse (translate_expr cond)
                                                          (translate_expr yes)
                                                          (translate_expr no)
   | L10.AST.LogicalAnd a b => L20.AST.LogicalAnd (translate_expr a)
                                                  (translate_expr b)
   | L10.AST.LogicalOr a b => L20.AST.LogicalOr (translate_expr a)
                                                (translate_expr b)
   | L10.AST.PrivateOrBuiltinCall name args =>
      (if is_private_call name then L20.AST.PrivateCall else L20.AST.BuiltinCall)
        name
        ((fix translate_expr_list (l: list L10.AST.expr)
          := match l with
             | nil => nil
             | cons h t => cons (translate_expr h) (translate_expr_list t)
             end) args)
  end.

(* break, continue and revert are joined together into abort
   assert is translated to if
   augmented assignments are translated to usual ones
 *)
Fixpoint translate_small_stmt (ss: L10.AST.small_stmt)
: L20.AST.stmt
:= match ss with
   | L10.AST.Pass => L20.AST.SmallStmt L20.AST.Pass
   | L10.AST.Break    => L20.AST.SmallStmt (L20.AST.Abort (AbortBreak))
   | L10.AST.Continue => L20.AST.SmallStmt (L20.AST.Abort (AbortContinue))
   | L10.AST.Revert   => L20.AST.SmallStmt (L20.AST.Abort (AbortRevert))
   | L10.AST.Return (Some result) => L20.AST.SmallStmt (L20.AST.Return (translate_expr result))
   | L10.AST.Return None => L20.AST.SmallStmt (L20.AST.Return (L20.AST.Const zero256))
   | L10.AST.Raise error => L20.AST.SmallStmt (L20.AST.Raise (translate_expr error))
   | L10.AST.Assert cond error =>
        L20.AST.IfElseStmt (translate_expr cond)
                           (L20.AST.SmallStmt L20.AST.Pass)
                           (L20.AST.SmallStmt
                             (L20.AST.Raise
                               match error with
                               | Some e => translate_expr e
                               | None => L20.AST.Const zero256
                               end))
   | L10.AST.Assign lhs rhs =>
        L20.AST.SmallStmt (L20.AST.Assign lhs (translate_expr rhs ))
   | L10.AST.BinOpAssign lhs op rhs =>
        L20.AST.SmallStmt
          (L20.AST.Assign lhs 
                          (L20.AST.BinOp op
                                         match lhs with
                                         | L10.AST.AssignableLocalVar name => L20.AST.LocalVar name
                                         | L10.AST.AssignableStorageVar name => L20.AST.StorageVar name
                                         end
                                         (translate_expr rhs)))
   | L10.AST.ExprStmt e => 
        L20.AST.SmallStmt (L20.AST.ExprStmt (translate_expr e))
   end.

(* list of statements are now joined with a 'semicolon' statement
   var declarations are now keeping their scope (let _ = _ in _)
   else branch is obligatory
   there's now only one kind of loop
 *)
Fixpoint translate_stmt (s: L10.AST.stmt)
: L20.AST.stmt
:= let translate_stmt_list
   := fix translate_stmt_list (l: list L10.AST.stmt)
      := match l with
         | nil => L20.AST.SmallStmt L20.AST.Pass
         (* | (h :: nil)%list => translate_stmt h      <- this case makes stuff too complicated *)
         | (L10.AST.LocalVarDecl name maybe_init :: t)%list =>
             L20.AST.LocalVarDecl name
                                  match maybe_init with
                                  | Some init => translate_expr init
                                  | None => L20.AST.Const zero256
                                  end
                                  (translate_stmt_list t)
         | (h :: t)%list => L20.AST.Semicolon (translate_stmt h)
                                              (translate_stmt_list t)
         end
   in match s with
   | L10.AST.LocalVarDecl name maybe_init =>
        L20.AST.LocalVarDecl name
                             match maybe_init with
                             | Some init => translate_expr init
                             | None => L20.AST.Const zero256
                             end
                             (L20.AST.SmallStmt L20.AST.Pass)
   | L10.AST.SmallStmt ss => translate_small_stmt ss
   | L10.AST.IfElseStmt cond yes no =>
        L20.AST.IfElseStmt (translate_expr cond)
                           (translate_stmt_list yes)
                           match no with
                           | Some n => translate_stmt_list n
                           | None => L20.AST.SmallStmt L20.AST.Pass
                           end
   | L10.AST.FixedRangeLoop var maybe_start stop body =>
        let start := match maybe_start with
                           | Some x => x
                           | None => zero256
                           end
         in L20.AST.Loop var
                          (L20.AST.Const start)
                          (uint256_of_Z (Z_of_uint256 stop - Z_of_uint256 start)%Z)
                          (translate_stmt_list body)
   | L10.AST.FixedCountLoop var start count body =>
        L20.AST.Loop var (translate_expr start) count (translate_stmt_list body)
   end.

(* XXX this is a dup from translate_stmt *)
Fixpoint translate_stmt_list (l: list L10.AST.stmt)
: L20.AST.stmt
:= match l with
   | nil => L20.AST.SmallStmt L20.AST.Pass
   | (L10.AST.LocalVarDecl name maybe_init :: t)%list =>
       L20.AST.LocalVarDecl name
                            match maybe_init with
                            | Some init => translate_expr init
                            | None => L20.AST.Const zero256
                            end
                            (translate_stmt_list t)
   | (h :: t)%list => L20.AST.Semicolon (translate_stmt h)
                                        (translate_stmt_list t)
   end.

Definition translate_decl (d: L10.AST.decl)
: L20.AST.decl
:= match d with
   | L10.AST.StorageVarDecl name => L20.AST.StorageVarDecl name
   | L10.AST.FunDecl name arg_names body =>
       L20.AST.FunDecl name arg_names (translate_stmt_list body)
   end.

End Translate.

Fixpoint decl_names {C: VyperConfig} (decls: list L10.AST.decl)
:= List.map L10.AST.decl_name decls.

Definition decl_set {C: VyperConfig} (decls: list L10.AST.decl)
: string_set
:= let _ := string_set_impl in FSet.from_list (decl_names decls).

(* superceded by translate_calldag *)
Definition translate_decl_list {C: VyperConfig} (d: list L10.AST.decl)
: list L20.AST.decl
:= let f := decl_set d in
   let is_private_call (name: string) := let _ := string_set_impl in FSet.has f name in
   List.map (translate_decl is_private_call) d.