From Coq Require Import String List.

Require Import Config FSet.

Inductive unop
:= BitwiseNot
 | Neg.

Inductive binop
:= LogicalOr
 | LogicalAnd
 | Lt
 | Le
 | Gt
 | Ge
 | Eq
 | Ne
 | In
 | NotIn
 | Is
 | IsNot
 | BitwiseOr
 | BitwiseAnd
 | BitwiseXor
 | ShiftLeft
 | ShiftRight
 | Add
 | Sub
 | Mul
 | Div
 | Quot
 | Mod
 | Pow.

Inductive assignable
:= AssignableLocalVar (name: string)
 | AssignableStorageVar (name: string).

Section AST.

Context {C: VyperConfig}.

Inductive expr
:= Const (val: uint256)
 | LocalVar (name: string) (* x *)
 | StorageVar (name: string) (* self.x *)
 | UnOp (op: unop) (a: expr)
 | BinOp (op: binop) (a b: expr)
(* | IfThenElse (cond yes no: expr) *)
 | PrivateOrBuiltinCall (name: string) (args: list expr).

(** Get the set of functions called by an expression. *)
Fixpoint expr_callset (e: expr)
: string_set
:= let _ := string_set_impl in
   match e with
   | Const _ | LocalVar _ | StorageVar _ => empty
   | UnOp _ a => expr_callset a
   | BinOp _ a b => union (expr_callset a) (expr_callset b)
(*   | IfThenElse a b c => union (expr_callset a) (union (expr_callset b) (expr_callset c)) *)
   | PrivateOrBuiltinCall name args =>
      let expr_list_callset := fix expr_list_callset (exprs: list expr) :=
         match exprs with
         | nil => empty
         | (h :: t)%list => union (expr_callset h) (expr_list_callset t)
         end
      in add (expr_list_callset args) name
   end.
Fixpoint expr_list_callset (exprs: list expr)
: string_set
:= let _ := string_set_impl in
   match exprs with
   | nil => empty
   | (h :: t)%list => union (expr_callset h) (expr_list_callset t)
   end.

Inductive small_stmt
:= Pass
 | Break
 | Continue
 | Return (result: option expr)
 | Revert
 | Raise (error: expr)
 | Assert (cond: expr) (error: option expr)
(* | Log *)
 | LocalVarDecl (name: string) (init: option expr)
 | Assign (lhs: assignable) (rhs: expr)
 | BinOpAssign (lhs: assignable) (op: binop) (rhs: expr)
 | ExprStmt (e: expr).

Definition small_stmt_callset (s: small_stmt)
:= let _ := string_set_impl in
   match s with
   | Pass | Break | Continue | Return None | Revert | LocalVarDecl _ None => empty
   | Return (Some e) | LocalVarDecl _ (Some e) | Raise e | Assert e None | ExprStmt e =>
       expr_callset e
   | Assign lhs rhs | BinOpAssign lhs _ rhs => expr_callset rhs
   | Assert cond (Some error) => union (expr_callset cond) (expr_callset error)
   end.

Inductive stmt
:= SmallStmt (s: small_stmt)
 | IfElseStmt (cond: expr) (yes: list stmt) (no: option (list stmt))
 | FixedRangeLoop (var: string) (start: option uint256) (stop: uint256) (body: list stmt)
 | FixedCountLoop (var: string) (start: string) (count: uint256) (body: list stmt).

Fixpoint stmt_callset (s: stmt)
:= let _ := string_set_impl in
   let stmt_list_callset := fix stmt_list_callset (stmts: list stmt) :=
         match stmts with
         | nil => empty
         | (h :: t)%list => union (stmt_callset h) (stmt_list_callset t)
         end
   in match s with
   | SmallStmt a => small_stmt_callset a
   | IfElseStmt cond yes None => union (expr_callset cond) (stmt_list_callset yes)
   | IfElseStmt cond yes (Some no) => union (expr_callset cond)
                                            (union (stmt_list_callset yes) (stmt_list_callset no))
   | FixedRangeLoop var start _ body | FixedCountLoop var start _ body =>
       stmt_list_callset body
   end.

Fixpoint stmt_list_callset (stmts: list stmt)
:= let _ := string_set_impl in
   match stmts with
   | nil => empty
   | (h :: t)%list => union (stmt_callset h) (stmt_list_callset t)
   end.

Definition stmt_list_callset' (stmts: list stmt)
:= let _ := string_set_impl in fold_right union empty (map stmt_callset stmts).

Lemma stmt_list_callset_alt (s: list stmt):
  stmt_list_callset s = stmt_list_callset' s.
Proof.
induction s. { easy. }
cbn. f_equal. apply IHs.
Qed.

Inductive decl
:= (* ImportDecl
      EventDecl
      InterfaceDecl
      StructDecl *)
  StorageVarDecl (name: string)
| FunDecl (name: string) (args: list string) (body: list stmt).

Definition decl_name (d: decl)
: string
:= match d with
   | StorageVarDecl name | FunDecl name _ _ => name
   end.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in match d with
   | StorageVarDecl _ => empty
   | FunDecl name args body => stmt_list_callset body
   end.

End AST.