From Coq Require Import String NArith DecimalString HexString.

From Vyper Require Import Config FSet.
From Vyper.L10 Require AST Base ToString.

Section AST.

Context {C: VyperConfig}.

Inductive small_stmt
:= Pass
 | Const (dst: N) (val: uint256)
 | Copy (dst src: N)
 | StorageGet (dst: N) (name: string)
 | StoragePut (name: string) (src: N)
 | UnOp (op: L10.AST.unop) (dst src: N)
 | BinOp (op: L10.AST.binop) (dst src1 src2: N)
 | PrivateCall (dst: N) (name: string) (args_offset args_count: N)
 | BuiltinCall (dst: N) (name: string) (args_offset args_count: N)
 | Abort (ab: L10.Base.abort)
 | Return (src: N)
 | Raise (src: N).

Inductive stmt
:= SmallStmt (s: small_stmt)
 | IfElseStmt (cond_src: N) (yes: stmt) (no: stmt)
 | Loop (var: N) (count: uint256) (body: stmt)
 | Semicolon (a b: stmt).

Inductive decl
:= StorageVarDecl (name: string)
 | FunDecl (name: string) (args_count: N) (body: stmt).

(****************************   format   ******************************)

Local Open Scope string_scope.

Definition string_of_small_stmt (ss: small_stmt)
:= match ss with
   | Pass => "pass"
   | Const dst val => "[" ++ NilZero.string_of_uint (N.to_uint dst) ++ "]"
                      ++ " <- "
                      ++ HexString.of_Z (Z_of_uint256 val)
   | Copy dst src => "[" ++ NilZero.string_of_uint (N.to_uint dst) ++ "]"
                     ++ " <- ["
                     ++ NilZero.string_of_uint (N.to_uint src)
                     ++ "]"
   | StorageGet dst name => "[" ++ NilZero.string_of_uint (N.to_uint dst)
                            ++ "] <- storage_get " ++ name
   | StoragePut name src => "storage_put " ++ name
                            ++ " [" ++ NilZero.string_of_uint (N.to_uint src) ++ "]"
   | UnOp op dst src => "[" ++ NilZero.string_of_uint (N.to_uint dst)
                        ++ "] <- "
                        ++ L10.ToString.string_of_unop op
                        ++ "[" ++ NilZero.string_of_uint (N.to_uint src) ++ "]"
   | BinOp op dst src1 src2 => "[" ++ NilZero.string_of_uint (N.to_uint dst)
                               ++ "] <- [" ++ NilZero.string_of_uint (N.to_uint src1) ++ "]"
                               ++ L10.ToString.string_of_binop op
                               ++ "[" ++ NilZero.string_of_uint (N.to_uint src2) ++ "]"
   | PrivateCall dst name args_offset args_count =>
       "[" ++ NilZero.string_of_uint (N.to_uint dst)
        ++ "] <- " ++ name ++ "/"
        ++ NilZero.string_of_uint (N.to_uint args_count)
        ++ "[" ++ NilZero.string_of_uint (N.to_uint args_offset) ++ "...]"
   | BuiltinCall dst name args_offset args_count =>
       "[" ++ NilZero.string_of_uint (N.to_uint dst)
        ++ "] <- builtin " ++ name ++ "/"
        ++ NilZero.string_of_uint (N.to_uint args_count)
        ++ "[" ++ NilZero.string_of_uint (N.to_uint args_offset) ++ "...]"
   | Abort a => "abort " ++ L10.Base.string_of_abort a
   | Return n => "return [" ++ NilZero.string_of_uint (N.to_uint n) ++ "]"
   | Raise n => "raise [" ++ NilZero.string_of_uint (N.to_uint n) ++ "]"
   end.


Fixpoint lines_of_stmt (s: stmt)
: list string
:=  match s with
    | SmallStmt ss => string_of_small_stmt ss :: nil
    | IfElseStmt cond yes no => ("if [" ++ NilZero.string_of_uint (N.to_uint cond) ++ "]:")
                                :: L10.ToString.add_indent (lines_of_stmt yes)
                                ++ "else:" :: L10.ToString.add_indent (lines_of_stmt no)
    | Loop var count body =>  ("for [" ++ NilZero.string_of_uint (N.to_uint var) ++ "] in count("
                                       ++ HexString.of_Z (Z_of_uint256 count) ++ "):")
                                       :: L10.ToString.add_indent (lines_of_stmt body)
    | Semicolon a b => lines_of_stmt a ++ lines_of_stmt b
    end.

Definition lines_of_decl (d: decl)
: list string
:= (match d with
    | StorageVarDecl name => ("var " ++ name)%string :: nil
    | FunDecl name args body =>
        ("def " ++ name ++ "/" ++ NilZero.string_of_uint (N.to_uint args) ++ ":")%string
        :: L10.ToString.add_indent (lines_of_stmt body)
    end)%list.

Definition string_of_decl (d: decl)
:= let newline := "
" in newline ++ List.fold_right (fun x tail => x ++ newline ++ tail) "" (lines_of_decl d).

Definition string_of_decls {C: VyperConfig} (l: list decl)
:= List.fold_right append "" (List.map string_of_decl l).

End AST.