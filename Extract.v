From Coq Require Import ExtrHaskellBasic ExtrHaskellString ZArith.
From Vyper Require Import L10.AST Config Compile.
From Vyper Require L10.ToString L30.AST.
From Vyper.CheckArith Require Import Builtins.
From Vyper Require Import ProtoAST.
From Vyper.Hash Require Import UInt64 ExtrHaskellUInt64.

Definition z_eqb := Z.eqb.
Definition l10_neg := L10.AST.Neg.
Definition l10_decls_to_string {C: VyperConfig} := L10.ToString.string_of_decls.
Definition l30_decls_to_string {C: VyperConfig} := L30.AST.string_of_decls.


Extraction Language Haskell.

Extract Constant Int63.int => "()". (* we never use it anymore but Coq can't figure that out *)

Extraction "haskell/Extracted.hs"
  hex_of_Z
  L10.AST.BinopLt
  L10.AST.BinopGt
  L10.AST.BinopEq
  L10.AST.BinopLe
  L10.AST.BinopGe
  L10.AST.BinopNe
  z_eqb
  compile
  uint256_of_Z
  sample_config
  l10_neg
  l10_decls_to_string
  l30_decls_to_string
  builtin_names_std
  proto_ast.
