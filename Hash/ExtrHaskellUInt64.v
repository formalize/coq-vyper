From Coq Require Import Extraction HexString.

From Vyper.Hash Require Import UInt64.

Definition hex_of_Z := HexString.of_Z.

Extract Inlined Constant uint64 => "Data.Word.Word64".
Extract Inlined Constant t      => "Data.Word.Word64".
Extract Constant uint64_of_Z     => "\ x -> (Prelude.read (hex_of_Z x) :: Data.Word.Word64)".
Extract Constant uint64_of_Z_mod => "\ x -> (Prelude.read (hex_of_Z x) :: Data.Word.Word64)".
Extract Inlined Constant bitwise_xor => "Data.Bits.xor".
Extract Inlined Constant bitwise_and => "(Data.Bits..&.)".
Extract Inlined Constant bitwise_or => "(Data.Bits..|.)".
Extract Inlined Constant bitwise_not => "Data.Bits.complement".
Extract Inlined Constant add => "(Prelude.+)".
Extract Inlined Constant UInt64.eqb => "(Prelude.==)".
Extract Inlined Constant is_nonzero => "(Prelude./= 0)".

(* The problem with simply calling shiftL/shiftR is that if sh is too large,
   it would go negative upon conversion to Int, and then the shift will happen in the opposite direction.
 *)
Extract Constant shl => "\ a sh -> if (Prelude.>) sh 64 then 0 else Data.Bits.shiftL a (Prelude.fromIntegral sh)".
Extract Constant shr => "\ a sh -> if (Prelude.>) sh 64 then 0 else Data.Bits.shiftR a (Prelude.fromIntegral sh)".

Extract Inlined Constant uint64_0   => "(0 :: Data.Word.Word64)".
Extract Inlined Constant uint64_1   => "(1 :: Data.Word.Word64)".
Extract Inlined Constant uint64_2   => "(2 :: Data.Word.Word64)".
Extract Inlined Constant uint64_4   => "(4 :: Data.Word.Word64)".
Extract Inlined Constant uint64_8   => "(8 :: Data.Word.Word64)".
Extract Inlined Constant uint64_16  => "(16 :: Data.Word.Word64)".
Extract Inlined Constant uint64_32  => "(32 :: Data.Word.Word64)".
Extract Inlined Constant uint64_64  => "(64 :: Data.Word.Word64)".
Extract Inlined Constant uint64_128 => "(128 :: Data.Word.Word64)".

Extract Inlined Constant uint64_24 => "(24 :: Data.Word.Word64)".
Extract Inlined Constant uint64_40 => "(40 :: Data.Word.Word64)".
Extract Inlined Constant uint64_48 => "(48 :: Data.Word.Word64)".
Extract Inlined Constant uint64_56 => "(56 :: Data.Word.Word64)".