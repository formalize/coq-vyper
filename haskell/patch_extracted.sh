#! /bin/sh

# This exists because Coq's ExtrHaskellString.v says:
#
# (**
#  * At the moment, Coq's extraction has no way to add extra import
#  * statements to the extracted Haskell code.  You will have to
#  * manually add:
#  *
#  *   import qualified Data.Bits
#  *   import qualified Data.Char
#  *)
#
# You got to be kidding me...

cd $(dirname "$0")
sed 's/^module Extracted where/module PatchedExtracted where\n\nimport qualified Data.Bits\nimport qualified Data.Char/' Extracted.hs >PatchedExtracted.hs
