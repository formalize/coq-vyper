From Coq Require Import String NArith.

From Vyper Require Import Config FSet.
From Vyper.L10 Require AST Base.

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

End AST.