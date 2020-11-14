From Coq Require Import String List HexString.

Require Import Config FSet.

Local Open Scope string_scope.

Inductive unop
:= BitwiseNot
 | LogicalNot
 | Neg.

Definition string_of_unop (op: unop)
:= match op with
   | LogicalNot => "not"
   | BitwiseNot => "~"
   | Neg => "-"
   end.

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


Definition string_of_binop (op: binop)
:= match op with
   | Lt => "<"
   | Le => "<="
   | Gt => ">"
   | Ge => ">="
   | Eq => "=="
   | Ne => "!="
   | BitwiseOr  => "|"
   | BitwiseAnd => "&"
   | BitwiseXor => "^"
   | ShiftLeft  => "<<"
   | ShiftRight => ">>"
   | Add => "+"
   | Sub => "-"
   | Mul => "*"
   | Quot => "//"
   | Mod => "%"
   | Pow => "**"
   end.



Inductive assignable
:= AssignableLocalVar (name: string)
 | AssignableStorageVar (name: string).

Definition string_of_assignable (a: assignable)
:= match a with
   | AssignableLocalVar name => name
   | AssignableStorageVar name => "self." ++ name
   end.

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

(****************************   format   ******************************)

Fixpoint string_of_expr (e: expr)
:= match e with
   | Const u => HexString.of_Z (Z_of_uint256 u)
   | LocalVar name => name
   | StorageVar name => "self." ++ name
   | UnOp op a => "(" ++ string_of_unop op ++ string_of_expr a ++ ")"
   | BinOp op a b => "(" ++ string_of_expr a ++ " " ++ string_of_binop op
                         ++ " " ++ string_of_expr b ++ ")"
   | IfThenElse cond yes no => "(" ++ string_of_expr yes ++ " if "
                                   ++ string_of_expr cond ++ " else "
                                   ++ string_of_expr no ++ ")"
   | LogicalAnd a b => "(" ++ string_of_expr a ++ " and " ++ string_of_expr b ++ ")"
   | LogicalOr  a b => "(" ++ string_of_expr a ++ " or "  ++ string_of_expr b ++ ")"
   | PrivateOrBuiltinCall name args => name ++ "(" ++
       (let fix string_of_expr_list_with_preceding_commas {C: VyperConfig} (a: list expr)
            := fold_right (fun e tail => ", " ++ string_of_expr e ++ tail) "" a
        in match args with
           | nil => ""
           | h :: t => string_of_expr h ++
                         string_of_expr_list_with_preceding_commas t
           end) ++ ")"
   end.


Fixpoint string_of_small_stmt {C: VyperConfig} (ss: small_stmt)
:= match ss with
   | Pass => "pass"
   | Break => "break"
   | Continue => "continue"
   | Return None => "return"
   | Return (Some e) => "return " ++ string_of_expr e
   | Revert => "revert"
   | Raise err => "raise " ++ string_of_expr err
   | Assert cond None => "assert " ++ string_of_expr cond
   | Assert cond (Some err) => "assert " ++ string_of_expr cond ++ ", " ++ string_of_expr err
   | Assign lhs rhs => string_of_assignable lhs ++ " = " ++ string_of_expr rhs
   | BinOpAssign lhs op rhs => string_of_assignable lhs ++ " "
                            ++ string_of_binop op ++ "= " ++ string_of_expr rhs
   | ExprStmt e => string_of_expr e
   end.

Definition add_indent (lines: list string)
:= map (fun s => "    " ++ s) lines.

Definition newline := "
".

Fixpoint lines_of_stmt (s: stmt)
: list string
:= let fix lines_of_stmt_list (l: list stmt)
       := match l with
          | nil => nil
          | h :: t => (lines_of_stmt h ++ lines_of_stmt_list t)%list
          end
   in match s with
      | SmallStmt ss => string_of_small_stmt ss :: nil
      | LocalVarDecl name None => ("var " ++ name) :: nil
      | LocalVarDecl name (Some init) => ("var " ++ name ++ " = " ++ string_of_expr init) :: nil
      | IfElseStmt cond yes None => ("if " ++ string_of_expr cond ++ ":") 
                                    :: add_indent (lines_of_stmt_list yes)
      | IfElseStmt cond yes (Some no) => ("if " ++ string_of_expr cond ++ ":")
                                          :: add_indent (lines_of_stmt_list yes)
                                          ++ "else:" :: add_indent (lines_of_stmt_list no)
      | FixedRangeLoop name None stop body => ("for " ++ name ++ " in range("
                                               ++ HexString.of_Z (Z_of_uint256 stop) ++ "):")
                                               :: add_indent (lines_of_stmt_list body)
      | FixedRangeLoop name (Some start) stop body => ("for " ++ name ++ " in range("
                                                     ++ HexString.of_Z (Z_of_uint256 start) ++ ", "
                                                     ++ HexString.of_Z (Z_of_uint256 stop) ++ "):")
                                                     :: add_indent (lines_of_stmt_list body)
      | FixedCountLoop name start count body =>  ("for " ++ name ++ " in count("
                                                     ++ string_of_expr start ++ ", "
                                                     ++ HexString.of_Z (Z_of_uint256 count) ++ "):")
                                                     :: add_indent (lines_of_stmt_list body)
      end.

Fixpoint lines_of_stmt_list (l: list stmt)
:= match l with
   | nil => nil
   | h :: t => (lines_of_stmt h ++ lines_of_stmt_list t)%list
   end.

Definition lines_of_decl (d: decl)
:= match d with
   | StorageVarDecl name => ("var " ++ name) :: nil
   | FunDecl name args body =>
       ("def " ++ name ++ "(" ++
         match args with
         | nil => ""
         | h :: t => h ++ fold_right (fun x tail => ", " ++ x ++ tail) "" t
         end ++ "):")
       :: add_indent (lines_of_stmt_list body)
   end.

Definition string_of_decl {C: VyperConfig} (d: decl)
:= newline ++ fold_right (fun x tail => x ++ newline ++ tail) "" (lines_of_decl d).

End AST.