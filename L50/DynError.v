From Coq Require Import String.

From Vyper Require Import Config Map.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types.

Local Open Scope string_scope.

(**
  An error that can occur during dynamic evaluation.
  This only includes errors that become impossible with static typing.
 *)
Inductive dynamic_error
:= DE_CannotResolveLocalVariable (name: string)
 | DE_TypeMismatch (expected actual: yul_type)

   (** A function is called with extra arguments
    or a variable declaration with an initializer has too few variables. *)
 | DE_TooManyValues

   (** A function is called with not enough arguments
    or an variable declaration with an initializer has too many variables. *)
 | DE_TooFewValues
 | DE_LocalNameShadowing (name: string)
 | DE_LeaveWithoutFunction
 | DE_LeftoverValuesInExpression
 | DE_SingleBooleanExpected
 | DE_SingleValueExpected
 | DE_BreakContinueDisallowed.

Definition string_of_dynamic_error (d: dynamic_error)
:= match d with
   | DE_CannotResolveLocalVariable name => "cannot resolve local variable: " ++ name
   | DE_TypeMismatch expected actual => "type mismatch, expected: " ++ string_of_type expected ++
                                        ", got: " ++ string_of_type actual
   | DE_TooManyValues => "too many values"
   | DE_TooFewValues => "too few values"
   | DE_LocalNameShadowing name => "local name shadowed: " ++ name
   | DE_LeaveWithoutFunction => "leave without function"
   | DE_LeftoverValuesInExpression => "leftover values in expression (use drop())"
   | DE_SingleBooleanExpected => "single boolean expected"
   | DE_SingleValueExpected => "single value expected"
   | DE_BreakContinueDisallowed => "break and continue not allowed"
   end.



(*

:= 

(** A function is called with an argument of a unexpected type
    or an initializer of a variable returns a value of a wrong type. *)
 | DE_VarTypeMismatch
(** There are two local variables (that includes inputs or outputs) with the same name. *)
 | DE_LocalNameShadowing
(** An expression has returned multiple values in the context in which only one was expected. *)
 | DE_ExactlyOneValueExpected
(** A function is declared with the same name as one of the built-in functions. *)
 | DE_BuiltinFunctionShadowing
(** A function is declared with the same name as a function visible from its location. *)
 | DE_LocalFunctionShadowing
 | DE_CannotResolveFunction
 | DE_CannotResolveVariable
 | DE_InternalErrorOutputNotFound
 | DE_UnexpectedBreak
 | DE_UnexpectedContinue. *)