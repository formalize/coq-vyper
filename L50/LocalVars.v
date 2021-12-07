From Coq Require Import String Arith.

From Vyper Require Import Config Map.
From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types AST Builtins DynError.

Local Open Scope list_scope.

(** Lookup all the names in the variable map and check types. 
    The names need not be distinct.
 *)
Fixpoint get_vars_by_typenames {C: VyperConfig}
                               (typenames: list typename)
                               (vars: string_map dynamic_value)
: dynamic_error + list dynamic_value
:= match typenames with
   | nil => inr nil
   | (type, name) :: rest =>
       match map_lookup vars name as z return (_ = z -> _) with
       | None => fun _ => inl (DE_CannotResolveLocalVariable name)
       | Some value => fun found =>
           let t := projT1 value in 
           if yul_type_eq_dec type t
             then match get_vars_by_typenames rest vars with
                  | inl err => inl err
                  | inr rest_results => inr (value :: rest_results)
                  end
             else inl (DE_TypeMismatch type t)
       end eq_refl
   end.

(** Bind several variables. This happens to the function arguments right after a call
    and also in a variable declaration with initializer.
    The names must be distinct because shadowing is not allowed.
 *)
Fixpoint bind_vars_to_values {C: VyperConfig}
                             (vars: list typename)
                             (init: list dynamic_value)
                             (loc: string_map dynamic_value)
: dynamic_error + string_map dynamic_value
:= match vars with
   | nil =>
      match init with
      | nil => inr loc
      | _ => inl DE_TooManyValues
      end
   | (vtype, vname) :: vtail =>
      match init with
      | nil => inl DE_TooFewValues
      | (existT _ itype ivalue as ihead) :: itail =>
          if yul_type_eq_dec vtype itype then
            match map_lookup loc vname with
            | Some _ => inl (DE_LocalNameShadowing vname)
            | None => bind_vars_to_values vtail itail (map_insert loc vname ihead)
            end
          else inl (DE_TypeMismatch vtype itype)
      end
   end.

(** Bind several variables to zeros. 
    This happens to the function outputs right after a call
    and also in a variable declaration without initializer.
    The names must be distinct because shadowing is not allowed.
*)
Fixpoint bind_vars_to_zeros {C: VyperConfig}
                            (vars: list typename)
                            (loc: string_map dynamic_value)
: dynamic_error + string_map dynamic_value
:= match vars with
   | nil => inr loc
   | (vtype, vname) :: vtail =>
        match map_lookup loc vname with
        | Some _ => inl (DE_LocalNameShadowing vname)
        | None => bind_vars_to_zeros vtail (map_insert loc vname (existT _ vtype (zero_value vtype)))
        end
   end.

(** Rebind several variables. This happens in assignments. *)
Fixpoint rebind_vars_to_values {C: VyperConfig}
                               (vars: list string)
                               (rhs: list dynamic_value)
                               (loc: string_map dynamic_value)
: dynamic_error + string_map dynamic_value
:= match vars with
   | nil =>
      match rhs with
      | nil => inr loc
      | _ => inl DE_TooManyValues
      end
   | vname :: vtail =>
      match rhs with
      | nil => inl DE_TooFewValues
      | (existT _ rtype rvalue as rhead) :: rtail =>
            match map_lookup loc vname with
            | Some (existT _ vtype _) =>
                if yul_type_eq_dec vtype rtype
                  then rebind_vars_to_values vtail rtail (map_insert loc vname rhead)
                  else inl (DE_TypeMismatch rtype vtype)
            | None => inl (DE_CannotResolveLocalVariable vname)
            end
      end
   end.

Fixpoint unbind_vars {C: VyperConfig}
                     (vars: list typename)
                     (loc: string_map dynamic_value)
: string_map dynamic_value
:= match vars with
   | nil => loc
   | h :: t => unbind_vars t (map_remove loc (snd h))
   end.