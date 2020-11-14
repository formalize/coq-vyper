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

(****************************   format   ******************************)

Local Open Scope string_scope.

Fixpoint string_of_expr (e: expr)
:= match e with
   | Const u => HexString.of_Z (Z_of_uint256 u)
   | LocalVar name => name
   | StorageVar name => "self." ++ name
   | UnOp op a => "(" ++ L10.AST.string_of_unop op ++ string_of_expr a ++ ")"
   | BinOp op a b => "(" ++ string_of_expr a ++ " " ++ L10.AST.string_of_binop op
                         ++ " " ++ string_of_expr b ++ ")"
   | IfThenElse cond yes no => "(" ++ string_of_expr yes ++ " if "
                                   ++ string_of_expr cond ++ " else "
                                   ++ string_of_expr no ++ ")"
   | LogicalAnd a b => "(" ++ string_of_expr a ++ " and " ++ string_of_expr b ++ ")"
   | LogicalOr  a b => "(" ++ string_of_expr a ++ " or "  ++ string_of_expr b ++ ")"
   | PrivateCall name args => name ++ "(" ++
       (let fix string_of_expr_list_with_preceding_commas {C: VyperConfig} (a: list expr)
            := fold_right (fun e tail => ", " ++ string_of_expr e ++ tail) "" a
        in match args with
           | nil => ""
           | h :: t => string_of_expr h ++
                         string_of_expr_list_with_preceding_commas t
           end) ++ ")"
   | BuiltinCall name args => "builtin[" ++ name ++ "](" ++
       (let fix string_of_expr_list_with_preceding_commas {C: VyperConfig} (a: list expr)
            := fold_right (fun e tail => ", " ++ string_of_expr e ++ tail) "" a
        in match args with
           | nil => ""
           | h :: t => string_of_expr h ++
                         string_of_expr_list_with_preceding_commas t
           end) ++ ")"
   end.

Definition string_of_small_stmt (ss: small_stmt)
:= match ss with
   | Pass => "pass"
   | Abort a => "abort " ++ L10.Base.string_of_abort a
   | Return e => "return " ++ string_of_expr e
   | Raise e => "raise " ++ string_of_expr e
   | Assign lhs rhs => L10.AST.string_of_assignable lhs ++ " = " ++ string_of_expr rhs
   | ExprStmt e => string_of_expr e
   end.

Fixpoint lines_of_stmt (s: stmt)
: list string
:=  match s with
    | SmallStmt ss => string_of_small_stmt ss :: nil
    | LocalVarDecl name init scope => ("with " ++ name ++ " = " ++ string_of_expr init ++ ":")
                                    :: L10.AST.add_indent (lines_of_stmt scope)
    | IfElseStmt cond yes no => ("if " ++ string_of_expr cond ++ ":")
                                :: L10.AST.add_indent (lines_of_stmt yes)
                                ++ "else:" :: L10.AST.add_indent (lines_of_stmt no)
    | Loop name start count body =>  ("for " ++ name ++ " in count("
                                       ++ string_of_expr start ++ ", "
                                       ++ HexString.of_Z (Z_of_uint256 count) ++ "):")
                                       :: L10.AST.add_indent (lines_of_stmt body)
    | Semicolon a b => lines_of_stmt a ++ lines_of_stmt b
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
       :: L10.AST.add_indent (lines_of_stmt body)
   end.

Definition string_of_decl (d: decl)
:= L10.AST.newline ++ fold_right (fun x tail => x ++ L10.AST.newline ++ tail) "" (lines_of_decl d).

End AST.