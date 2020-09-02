From Coq Require Import String List.

From Vyper Require Import Config FSet.
From Vyper.L10 Require AST Base.

Section AST.

Context {C: VyperConfig}.

Inductive expr
:= Const (val: uint256)
 | LocalVar (name: string) (* x *)
 | StorageVar (name: string) (* self.x *)
 | UnOp (op: L10.AST.unop) (a: expr)
 | BinOp (op: L10.AST.binop) (a b: expr)
 | IfThenElse (cond yes no: expr)
 | LogicalAnd (a b: expr)
 | LogicalOr (a b: expr)
 | PrivateCall (name: string) (args: list expr)
 | BuiltinCall (name: string) (args: list expr).

Fixpoint expr_ind' (P: expr -> Prop)
                   (HConst: forall val, P (Const val))
                   (HLocalVar: forall name, P (LocalVar name))
                   (HStorageVar: forall name, P (StorageVar name))
                   (HUnOp: forall op a, P a -> P (UnOp op a))
                   (HBinOp: forall op a b, P a -> P b -> P (BinOp op a b))
                   (HIf: forall cond yes no: expr,
                           P cond -> P yes -> P no -> P (IfThenElse cond yes no))
                   (HAnd: forall a b, P a -> P b -> P (LogicalAnd a b))
                   (HOr:  forall a b, P a -> P b -> P (LogicalOr  a b))
                   (HPrivateCall: forall name args,
                        Forall P args -> P (PrivateCall name args))
                   (HBuiltinCall: forall name args,
                        Forall P args -> P (BuiltinCall name args))
                   (e: expr)
{struct e}
: P e
:= let ind := expr_ind' P HConst HLocalVar HStorageVar 
                        HUnOp HBinOp HIf HAnd HOr 
                        HPrivateCall HBuiltinCall
    in let fix expr_list_ind (l: list expr)
       : Forall P l
       := match l with
          | nil => Forall_nil P
          | cons h t => Forall_cons h (ind h) (expr_list_ind t)
          end
    in match e with
     | Const val => HConst val
     | LocalVar name => HLocalVar name
     | StorageVar name => HStorageVar name
     | UnOp op a => HUnOp op a (ind a)
     | BinOp op a b => HBinOp op a b (ind a) (ind b)
     | IfThenElse cond yes no => HIf cond yes no (ind cond) (ind yes) (ind no)
     | LogicalAnd a b => HAnd a b (ind a) (ind b)
     | LogicalOr a b => HOr a b (ind a) (ind b)
     | PrivateCall name args => HPrivateCall name args (expr_list_ind args)
     | BuiltinCall name args => HBuiltinCall name args (expr_list_ind args)
     end.

(** "Small statement" is a term used in Python grammar, also in rust-vyper grammar.
    Here we don't count local variable declarations as small statements.
 *)
Inductive small_stmt
:= Pass
 | Abort (ab: L10.Base.abort)
 | Return (result: expr)
 | Raise (error: expr)
 | Assign (lhs: L10.AST.assignable) (rhs: expr)
 | ExprStmt (e: expr).

(** Lists of statements are obsolete as they make recursion too tricky.
    Now the statements can be chained together by [Semicolon];
    also [LocalVarDecl] has an explicit scope.
 *)
Inductive stmt
:= SmallStmt (s: small_stmt)
 | LocalVarDecl (name: string) (init: expr) (scope: stmt)
 | IfElseStmt (cond: expr) (yes: stmt) (no: stmt)
 | Loop (var: string) (start: expr) (count: uint256) (body: stmt)
 | Semicolon (a b: stmt).

Inductive decl
:= (* ImportDecl
      EventDecl
      InterfaceDecl
      StructDecl *)
  StorageVarDecl (name: string)
| FunDecl (name: string) (args: list string) (body: stmt).

Definition decl_name (d: decl)
: string
:= match d with
   | StorageVarDecl name | FunDecl name _ _ => name
   end.

End AST.