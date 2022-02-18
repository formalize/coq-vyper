From Vyper Require Import Config.
From Vyper.L30 Require Import AST.

Definition small_stmt_is_op_free {C: VyperConfig}
                                 (ss: small_stmt)
: bool
:= match ss with
   | UnOp _ _ _
   | BinOp _ _ _ _ _
   | PowConstBase _ _ _
   | PowConstExp _ _ _ => false
   | _ => true
   end.

Fixpoint stmt_is_op_free {C: VyperConfig}
                         (s: stmt)
: bool
:= match s with
   | SmallStmt ss => small_stmt_is_op_free ss
   | IfElseStmt _ yes no => (stmt_is_op_free yes && stmt_is_op_free no)%bool
   | Loop _ _ body => stmt_is_op_free body
   | Semicolon a b => (stmt_is_op_free a && stmt_is_op_free b)%bool
   end.