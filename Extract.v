From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrHaskellBasic ExtrHaskellString.
From Vyper Require Import Config L10.AST From20To30.Translate.

Extraction Language Haskell.

Extraction "haskell/Extracted.hs"
  L10.AST.unop
  L10.AST.binop (* this is to prevent [comparison] from taking [Lt], [Gt] and [Eq] *)
  L10.AST.decl
  translate_decl
  uint256_of_Z
  sample_config.
