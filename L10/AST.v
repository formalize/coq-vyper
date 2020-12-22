Require Import Config FSet.
From Coq Require Import String List.

Inductive unop
:= BitwiseNot
 | LogicalNot
 | Neg.

Inductive binop
:= (* LogicalOr
 | LogicalAnd *)
 | Lt
 | Le
 | Gt
 | Ge
 | Eq
 | Ne
(* | In
 | NotIn
 | Is
 | IsNot *)
 | BitwiseOr
 | BitwiseAnd
 | BitwiseXor
 | ShiftLeft
 | ShiftRight
 | Add
 | Sub
 | Mul
(* | Div *)
 | Quot
 | Mod
 | Pow.

(** I cannot make the extractor reliably prioritize [binop] over [comparison],
    resulting in ugly names like [Lt0] for my binops. Here's a workaround that
    is still ugly but not as much as [Lt0].
 *)
Definition BinopLt := Lt.
Definition BinopGt := Gt.
Definition BinopEq := Eq.
Definition BinopLe := Le.
Definition BinopGe := Le.
Definition BinopNe := Ne.

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
 | IfThenElse (cond yes no: expr)
 | LogicalAnd (a b: expr)
 | LogicalOr (a b: expr)
 | PrivateOrBuiltinCall (name: string) (args: list expr).

(* Coq derives wrong induction principle because lists are present. Here's the correct one. *)
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
                   (HCall: forall name args,
                        Forall P args -> P (PrivateOrBuiltinCall name args))
                   (e: expr)
{struct e}
: P e
:= let ind := expr_ind' P HConst HLocalVar HStorageVar HUnOp HBinOp HIf HAnd HOr HCall in
   match e with
   | Const val => HConst val
   | LocalVar name => HLocalVar name
   | StorageVar name => HStorageVar name
   | UnOp op a => HUnOp op a (ind a)
   | BinOp op a b => HBinOp op a b (ind a) (ind b)
   | IfThenElse cond yes no => HIf cond yes no (ind cond) (ind yes) (ind no)
   | LogicalAnd a b => HAnd a b (ind a) (ind b)
   | LogicalOr a b => HOr a b (ind a) (ind b)
   | PrivateOrBuiltinCall name args =>
      HCall name args
        ((fix expr_list_ind (l: list expr)
          : Forall P l
          := match l with
             | nil => Forall_nil P
             | cons h t => Forall_cons h (ind h) (expr_list_ind t)
             end)
          args)
   end.



(** "Small statement" is a term used in Python grammar, also in rust-vyper grammar.
    Here we don't count local variable declarations as small statements.
 *)
Inductive small_stmt
:= Pass
 | Break
 | Continue
 | Return (result: option expr)
 | Revert
 | Raise (error: expr)
 | Assert (cond: expr) (error: option expr)
 | Assign (lhs: assignable) (rhs: expr)
 | BinOpAssign (lhs: assignable) (op: binop) (rhs: expr)
 | ExprStmt (e: expr).


Inductive stmt
:= SmallStmt (ss: small_stmt)
 | LocalVarDecl (name: string) (init: option expr)
 | IfElseStmt (cond: expr) (yes: list stmt) (no: option (list stmt))
 | FixedRangeLoop (var: string) (start: option uint256) (stop: uint256) (body: list stmt)
 | FixedCountLoop (var: string) (start: expr) (count: uint256) (body: list stmt).

Fixpoint stmt_ind' (P: stmt -> Prop)
                   (HSmall: forall ss, P (SmallStmt ss))
                   (HLocalVar: forall name init, P (LocalVarDecl name init))
                   (HIf: forall cond yes no,
                           Forall P yes 
                            ->
                           match no with
                           | Some else_branch => Forall P else_branch
                           | None => True
                           end 
                            ->
                           P (IfElseStmt cond yes no))
                   (HRangeLoop: forall var start stop body,
                                  Forall P body 
                                   ->
                                  P (FixedRangeLoop var start stop body))
                   (HCountLoop: forall var start count body,
                                  Forall P body 
                                   ->
                                  P (FixedCountLoop var start count body))
                   (s: stmt)
: P s
:= let ind := stmt_ind' P HSmall HLocalVar HIf HRangeLoop HCountLoop in
   let fix stmt_list_ind (l: list stmt)
       : Forall P l
       := match l with
          | nil => Forall_nil P
          | cons h t => Forall_cons h (ind h) (stmt_list_ind t)
          end
   in match s with
      | SmallStmt ss => HSmall ss
      | LocalVarDecl name init => HLocalVar name init
      | IfElseStmt cond yes (Some no) => HIf cond yes (Some no) (stmt_list_ind yes) (stmt_list_ind no)
      | IfElseStmt cond yes None => HIf cond yes None (stmt_list_ind yes) I
      | FixedRangeLoop var start stop body => HRangeLoop var start stop body (stmt_list_ind body)
      | FixedCountLoop var start stop body => HCountLoop var start stop body (stmt_list_ind body)
      end.

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

Definition is_local_var_decl {C: VyperConfig} (s: stmt)
:= match s with
   | LocalVarDecl _ _ => true
   | _ => false
   end.

Program Definition var_decl_unpack {C: VyperConfig} (s: stmt) (IsVarDecl: is_local_var_decl s = true)
: string * option expr
:= match s with
   | LocalVarDecl name init => (name, init)
   | _ => False_rect _ _
   end.
Next Obligation.
destruct s; cbn in IsVarDecl; try discriminate.
assert (Bad := H name init). tauto.
Qed.

End AST.