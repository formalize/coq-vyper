From Coq Require Import String NArith.

From Vyper Require Import Config FSet.

From Vyper.L30 Require Import AST.


Section Callset.

Context {C: VyperConfig}.

(** Get the set of functions called by an expression. *)
Definition small_stmt_callset (ss: small_stmt)
: string_set
:= let _ := string_set_impl in 
   match ss with
   | PrivateCall _ name _ _ => singleton name
   | _ => empty
   end.

Fixpoint stmt_callset (s: stmt)
:= let _ := string_set_impl in
   match s with
   | SmallStmt a => small_stmt_callset a
   | IfElseStmt cond yes no => (union (stmt_callset yes) (stmt_callset no))
   | Loop _ _ body => stmt_callset body
   | Semicolon a b => union (stmt_callset a) (stmt_callset b)
   end.

Definition decl_callset (d: decl)
:= let _ := string_set_impl in match d with
   | StorageVarDecl _ => empty
   | FunDecl name args body => stmt_callset body
   end.



End Callset.