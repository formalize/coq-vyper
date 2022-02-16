From Coq Require Import String NArith ZArith DecimalString List Lia.

From Vyper Require Import Config NaryFun.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require AST.
From Vyper.L50 Require AST.
From Vyper.L50 Require Import Types Expr.

From Vyper.L40Metered Require Import Interpret.

From Vyper.From40To50 Require Import Translate Proto.

(* We need to wrap L50 builtins into L40 versions
   that perform the same typechecks that the L50 interpreter does.

   This is not really necessary with the default list of builtins which is all u256-typed
   (address is not a Yul type and is not typechecked).
 *)

(**
  Typecheck each argument of a [nary_fun].
  Equivalent to running [L50.Builtins.mass_typecheck] before calling
  except no length check on input_types is performed.
 *)
Fixpoint embed_typechecks {C: VyperConfig}
                          {arity: nat}
                          {ReturnType: Type}
                          (f: NaryFun.nary_fun uint256 arity (world_state * expr_result ReturnType))
                          (input_types: list yul_type)
                          (world: world_state)
: NaryFun.nary_fun uint256 arity (world_state * expr_result ReturnType)
:= match arity, f with
   | 0, result  => result
   | S arity', g =>
      match input_types with
      | nil => g
      | (head_type :: tail_types)%list =>
          fun arg =>
            embed_typechecks 
      end
   end.

(*
L10.Base.builtin
L50.Builtins.yul_builtin
L10.Base.call_builtin
L50.Builtins.call_builtin
*)