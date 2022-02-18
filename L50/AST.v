From Coq Require Import String HexString ZArith.
From Vyper Require Import Config.
From Vyper.L50 Require Import Types.

Inductive expr {C: VyperConfig}
:= FunCall (name: string) (args: list expr) 
 | LocVar (name: string)
 | Const (t: yul_type) (val: yul_value t).

Definition typename: Type := yul_type * string.

Inductive stmt {C: VyperConfig}
:= BlockStmt (s: block)
 | VarDecl (vars: list typename) (init: option expr)
 | Assign (lhs: list string) (rhs: expr)
 | If (cond: expr) (body: block)
 | Expr (e: expr)
 | Switch (e: expr) (cases: list case) (default: option block)
 | For (init: block) (cond: expr) (after body: block)
 | Break
 | Continue
 | Leave
with case  {C: VyperConfig} := Case (t: yul_type) (val: yul_value t) (body: block)
with block {C: VyperConfig} := Block (body: list stmt).

Record fun_decl {C: VyperConfig} := {
  fd_name: string;
  fd_inputs: list typename;
  fd_outputs: list typename;
  fd_body: block;
}.

Definition program {C: VyperConfig}: Type := string_map fun_decl * block.


Definition is_var_decl {C: VyperConfig} (s: stmt)
:= match s with
   | VarDecl _ _ => true
   | _ => false
   end.

Program Definition var_decl_unpack {C: VyperConfig} (s: stmt) (IsVarDecl: is_var_decl s = true)
: list typename * option expr
:= match s with
   | VarDecl vars init => (vars, init)
   | _ => False_rect _ _
   end.
Next Obligation.
destruct s; cbn in IsVarDecl; try discriminate.
exact (H vars init eq_refl).
Qed.

(****************************   print   ******************************)

Local Open Scope list_scope.
Local Open Scope string_scope.

Fixpoint to_comma_list {A} (s: A -> string) (l: list A)
: string
:= match l with
   | nil => ""
   | x :: nil => s x
   | h :: t => s h ++ ", " ++ to_comma_list s t
   end.

Definition string_of_typename (tn: typename)
:= let '(t, n) := tn in
   n ++ ":" ++ string_of_type t.

Definition string_of_yul_value {C: VyperConfig} {t: yul_type} (v: yul_value t)
:= match v with
   | NumberValue _ value _ => HexString.of_Z (Z_of_uint256 value)
   | BoolValue _ true _ => "true"
   | BoolValue _ false _ => "false"
   end.

Fixpoint string_of_expr {C: VyperConfig} (e: expr)
:= match e with
   | FunCall name args => (name ++ "(" ++
                          (* Coq won't allow to_comma_list here *)
                          (fix string_of_exprs (l: list expr) :=
                             match l with
                             | nil => ""
                             | x :: nil => string_of_expr x
                             | h :: t => string_of_expr h ++ ", " ++ string_of_exprs t
                             end) args
                            ++ ")")%string
   | LocVar name => name
   | Const t v => string_of_yul_value v ++ ":" ++ string_of_type t
   end.

Definition attach (a b: list string)
: list string
:= match b with
   | nil => a
   | hb :: tb =>
     let a' := List.rev a in
       match a' with
       | nil => b
       | ha :: ta => List.rev ta ++ (ha ++ " " ++ hb) :: tb
       end
   end.

Fixpoint lines_of_stmt {C: VyperConfig} (s: stmt)
: list string
:= match s with
   | BlockStmt b => lines_of_block b
   | VarDecl vars init => ("let " ++ to_comma_list string_of_typename vars
                             ++ match init with
                                | Some e => " := " ++ string_of_expr e
                                | None => ""
                                end) :: nil
   | Assign lhs rhs => (to_comma_list id lhs ++ " := " ++ string_of_expr rhs) :: nil
   | If cond body => ("if " ++ string_of_expr cond) :: lines_of_block body
   | Expr e => string_of_expr e :: nil
   | Switch e cases default =>
      ("switch " ++ string_of_expr e) ::
      (fix lines_of_cases (l: list case): list string :=
        match l with
        | nil => nil
        | h :: t => (lines_of_case h ++ lines_of_cases t)%list
        end) cases ++
       match default with
       | None => nil
       | Some def => "default" :: lines_of_block def
       end
   | For init cond inc body => attach ("for" :: nil)
                                      (attach (lines_of_block init)
                                              (attach (string_of_expr cond :: nil)
                                                      (lines_of_block inc)))
                                ++ lines_of_block body
   | Break => "break" :: nil
   | Continue => "continue" :: nil
   | Leave => "leave" :: nil
   end
with lines_of_case {C: VyperConfig} (c: case)
: list string
:= let '(Case t v body) := c in
   ("case " ++ string_of_yul_value v ++ ":" ++ string_of_type t) :: lines_of_block body
with lines_of_block {C: VyperConfig} (b: block)
: list string
:= let fix lines_of_stmts (l: list stmt) :=
          match l with
          | nil => nil
          | h :: t => (lines_of_stmt h ++ lines_of_stmts t)%list
          end in
   let '(Block stmts) := b in
   let lines := lines_of_stmts stmts in
   match lines with
   | nil => "{}" :: nil
   | line :: nil => ("{ " ++ line ++ " }") :: nil
   | _ => "{" :: List.map (fun x => "    " ++ x) lines ++ "}" :: nil
   end.

(** Name override is needed because fd_name not properly mangled.
    (Actually fun_decl has no reason to store its name at all.)
 *)
Definition lines_of_fun_decl {C: VyperConfig} (fd: fun_decl) (override_name: string)
:= ("function " ++ override_name ++ 
      "(" ++ to_comma_list string_of_typename (fd_inputs fd) ++ ")" ++
      match fd_outputs fd with
      | nil => ""
      | _ => " -> " ++ to_comma_list string_of_typename (fd_outputs fd)
      end)
   :: lines_of_block (fd_body fd).

Definition lines_of_fun_decls {C: VyperConfig} (decls: string_map fun_decl)
:= let _ := string_map_impl in
   (fix lines_of_alist (l: list (string * fun_decl))
    := match l with
       | nil => nil
       | h :: t => let '(k, v) := h in (lines_of_fun_decl v k ++ lines_of_alist t)%list
       end) (Map.items decls).
