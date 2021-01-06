From Coq Require Import String List HexString.

Require Import Config FSet.

From Vyper Require Import L10.AST.

Local Open Scope string_scope.

Definition string_of_unop (op: unop)
:= match op with
   | LogicalNot => "not"
   | BitwiseNot => "~"
   | Neg => "-"
   end.

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


Definition string_of_assignable (a: assignable)
:= match a with
   | AssignableLocalVar name => name
   | AssignableStorageVar name => "self." ++ name
   end.


(****************************   format   ******************************)

Fixpoint string_of_expr {C: VyperConfig} (e: expr)
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

Definition add_indent {C: VyperConfig} (lines: list string)
:= map (fun s => "    " ++ s) lines.

Definition newline := "
".

Fixpoint lines_of_stmt {C: VyperConfig} (s: stmt)
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

Fixpoint lines_of_stmt_list {C: VyperConfig} (l: list stmt)
:= match l with
   | nil => nil
   | h :: t => (lines_of_stmt h ++ lines_of_stmt_list t)%list
   end.

Definition lines_of_decl {C: VyperConfig} (d: decl)
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

Definition string_of_decls {C: VyperConfig} (l: list decl)
:= fold_right append "" (map string_of_decl l).