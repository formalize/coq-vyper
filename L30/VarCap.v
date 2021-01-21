From Coq Require Import NArith.

From Vyper Require Import Config.
From Vyper.L30 Require Import AST.

Definition var_cap_small_stmt {C: VyperConfig} (ss: small_stmt)
: N
:= match ss with
   | Pass => 0
   | Const dst _ => N.succ dst
   | Copy dst src => N.succ (N.max dst src)
   | StorageGet dst _ => N.succ dst
   | StoragePut _ src => N.succ src
   | UnOp _ dst src => N.succ (N.max dst src)
   | PowConstBase dst base exp => N.succ (N.max dst exp)
   | PowConstExp  dst base exp => N.succ (N.max dst base)
   | BinOp _ dst src1 src2 _ => N.succ (N.max dst (N.max src1 src2))
   | PrivateCall dst _ offset count | BuiltinCall dst _ offset count =>
      match count with
      | 0%N => N.succ dst
      | _ => N.max (N.succ dst) (offset + count)%N
      end
   | Abort _ => 0
   | Return src => N.succ src
   | Raise src => N.succ src
   end.

Fixpoint var_cap_stmt {C: VyperConfig} (s: stmt)
:= match s with
   | SmallStmt ss => var_cap_small_stmt ss
   | IfElseStmt cond_src yes no =>
        N.max (N.succ cond_src) (N.max (var_cap_stmt yes) (var_cap_stmt no))
   | Loop var _ body => N.max (N.succ var) (var_cap_stmt body)
   | Semicolon a b => N.max (var_cap_stmt a) (var_cap_stmt b)
   end.

Fixpoint var_cap_decl {C: VyperConfig} (d: decl)
:= match d with
   | StorageVarDecl _ => 0%N
   | FunDecl _ args_count body => N.max args_count (var_cap_stmt body)
   end.