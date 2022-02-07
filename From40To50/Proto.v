From Coq Require Import String.

From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types Builtins.
From Vyper Require Import Config ProtoAST NaryFun.

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

(** Test if the only input and output type is u256 (or address, as we don't distinguish it from u256). *)
Definition proto_is_u256_only (p: proto)
: bool
:= all_are_u256 (p_inputs p) && all_are_u256 (p_outputs p).

(** Compile-time builtin function prototypes correspond with what the L50 interpreter got at runtime. *)
Definition ProtosAgree {C: VyperConfig}
                       (protos: string -> option proto)
                       (builtins: string -> option L50.Builtins.yul_builtin)
:= forall name,
     match protos name, builtins name with
     | None, None => True
     | Some p, Some b => p_inputs p = L50.Builtins.b_input_types b 
                          /\
                         p_outputs p = L50.Builtins.b_output_types b
     | _, _ => False
     end.

Definition call_builtin_u256 {C: VyperConfig}
                             (b: yul_builtin)
                             (world: world_state)
                             (args: list uint256)
                             (LenOk: List.length (b_input_types b) = List.length args)
: world_state * expr_result (list uint256)
:= fst (nary_call (b_fun b world) args (PeanoNat.Nat.eq_le_incl _ _ LenOk)).


(*
Definition call_builtin_on_u256_inputs {C: VyperConfig}
                                       (b: yul_builtin)
                                       (world: world_state)
                                       (args: list uint256)
                                       (LenOk: List.length (b_input_types b) = List.length args)
: world_state * expr_result (list dynamic_value)
:= match nary_call (b_fun b world) args (PeanoNat.Nat.eq_le_incl _ _ LenOk) with
   | ((world', ExprSuccess outputs_256), _) =>
       (world', match mass_cast outputs_256 (b_output_types b) with
                | inl err => expr_error err
                | inr outputs => ExprSuccess outputs
                end)
   | ((world', ExprAbort ab), _) => (world', ExprAbort ab)
   end.

Lemma call_builtin_on_u256_inputs_ok {C: VyperConfig}
                                     (b: yul_builtin)
                                     (world: world_state)
                                     (args: list uint256)
                                     (LenOk: List.length (b_input_types b) = List.length args)
                                     (ArgTypesOk: all_are_u256 (b_input_types b) = true):
  call_builtin_on_u256_inputs b world args ArgTypesOk LenOk
   =
  call_builtin b world (List.map (fun x => existT _ U256 (yul_uint256 x)) args).
Proof.
*)