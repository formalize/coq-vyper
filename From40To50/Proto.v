From Coq Require Import String.

From Vyper.L50 Require Import Types.
From Vyper Require Import Config ProtoAST.

Local Open Scope list_scope.
Local Open Scope string_scope.

Record proto := {
  p_name: string;
  p_inputs: list yul_type;
  p_outputs: list yul_type;
}.

(* We take "address" to mean u256 because Yul has no address type. *)
Definition read_type (s: string)
: option yul_type
:= if string_dec s "address"
     then Some U256
     else type_of_string s.

Fixpoint read_types (src: list string)
: string + list yul_type
:= match src with
   | nil => inr nil
   | h :: t => match read_type h with
               | None => inl ("unrecognized type: " ++ h)
               | Some h' => match read_types t with
                            | inl err => inl err
                            | inr t' => inr (h' :: t')
                            end
               end
   end.

Definition make_proto (ast: proto_ast)
: string + proto
:= match read_types (proto_inputs ast) with
   | inl err => inl err
   | inr inputs => 
      match read_types (proto_outputs ast) with
      | inl err => inl err
      | inr outputs => inr {| p_name := proto_name ast
                            ; p_inputs := inputs
                            ; p_outputs := outputs
                           |}
      end
   end.

(** The parameter of type [list proto_ast] should be either embedded into the compiler
    (see builtins.list, haskell/GenerateBuiltinsTable.hs) or should be provided as an
    external file and parsed via haskell/BuiltinsParser.y).
 *)
Definition make_proto_table {C: VyperConfig} (asts: list proto_ast) 
: string + string_map proto
:= let _ := string_map_impl in
   let fix add_protos (l: list proto_ast) (table: string_map proto)
       : string + string_map proto
       := match l with
          | nil => inr table
          | h :: t => match make_proto h with
                      | inl err => inl err
                      | inr p => match Map.lookup table (p_name p) with
                                 | None => add_protos t (Map.insert table (p_name p) p)
                                 | _ => inl ("a prototype with that name already exists: " ++ p_name p)
                                 end
                      end
          end
   in add_protos asts Map.empty.