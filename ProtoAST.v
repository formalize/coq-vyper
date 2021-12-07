From Coq Require Import String.

(** A prototype of a builtin function.
  This is just an AST: types are just strings.
 *)
Record proto_ast := {
  proto_name: string;
  proto_inputs: list string;
  proto_outputs: list string;
}.