(** This is the top level driver for the compiler. *)

From Coq Require Import String List ListSet Arith NArith.
From Vyper Require Import Config Calldag.
From Vyper.L10 Require AST Callset Descend Interpret.
From Vyper.From10To20 Require FunCtx Call.
From Vyper.From20To30 Require FunCtx Call.
From Vyper Require Import ConstFold L10.Base.

(** This is the verified part of the compiler.
    This function translates a L10 calldag into a L30 calldag (or an error).
 *)
Definition translate_10_to_30 {C: VyperConfig} (calldag10: L10.Descend.calldag)
: string + L30.Descend.calldag
:= let calldag20 := From10To20.FunCtx.translate_calldag calldag10 (* no errors possible *) in
   match const_fold_calldag calldag20 with
   | inl err => inl err
   | inr calldag20' => From20To30.FunCtx.translate_calldag calldag20'
   end.

(** This is the theorem verifying that the compiler works as intended.
 *)
Theorem translate_10_to_30_ok {C: VyperConfig}
                              (calldag10: L10.Descend.calldag)
                              (calldag30: L30.Descend.calldag)
                              (ok: translate_10_to_30 calldag10 = inr calldag30)
                              (builtins: string -> option builtin)
                              (fun_name: string)
                              (world: world_state)
                              (arg_values: list uint256):
  L30.Interpret.interpret builtins calldag30 fun_name world arg_values
   =
  L10.Interpret.interpret builtins calldag10 fun_name world arg_values.
Proof.
(* 10 -> 20 *)
rewrite<- From10To20.Call.translate_ok.
unfold translate_10_to_30 in ok.
remember (From10To20.FunCtx.translate_calldag calldag10) as calldag20.
clear Heqcalldag20.

(* const fold *)
remember (const_fold_calldag calldag20) as calldag20'. symmetry in Heqcalldag20'.
destruct calldag20' as [|calldag20']. { discriminate. }
rewrite<- (const_fold_ok _ Heqcalldag20').
clear Heqcalldag20'.

(* 20 -> 30 *)
apply From20To30.Call.translate_ok. exact ok.
Qed.

(** This function takes the parser output, which is a list of L10 declarations,
    and compiles it into a L30 calldag.

    Here [make_calldag] converts the output of the parser to the input to the verified compiler.
 *)
Definition compile_to_L30 {C: VyperConfig} (parsed_src: list L10.AST.decl)
: string + L30.Descend.calldag
:= match make_calldag L10.AST.decl_name L10.Callset.decl_callset parsed_src with
   | inl err => inl err
   | inr cd => translate_10_to_30 cd
   end.

Definition calldag_to_string {C: VyperConfig} (cd: L30.Descend.calldag)
:= let _ := string_map_impl in
   (List.fold_right (fun x tail => x ++ L10.ToString.newline ++ tail) ""
                    (List.map (fun kv => (L30.AST.string_of_decl (snd kv))) 
                              (Map.items (cd_decls cd))))%string.

(** This is the compiler without parser. *)
Definition compile {C: VyperConfig} (parsed_src: list L10.AST.decl)
: string + string
:= match compile_to_L30 parsed_src with
   | inl err => inl err
   | inr cd => inr (calldag_to_string cd)
   end.