From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrHaskellBasic ExtrHaskellString.
From Vyper Require Import L10.AST Config Compile.

Extraction Language Haskell.

Extraction "haskell/Extracted.hs"
  L10.AST.BinopLt
  L10.AST.BinopGt
  L10.AST.BinopEq
  L10.AST.BinopLe
  L10.AST.BinopGe
  L10.AST.BinopNe
  compile
  uint256_of_Z
  sample_config.
