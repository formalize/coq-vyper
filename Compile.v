(** This is the top level driver for the compiler. *)

From Coq Require Import String List ListSet Arith NArith.
From Vyper Require Import Config Calldag ProtoAST.
From Vyper.L10 Require AST Callset Descend Interpret.
From Vyper.From10To20 Require FunCtx Call.
From Vyper.From20To30 Require FunCtx Call.
From Vyper.From30To40 Require Translate FunCtx Call.
From Vyper.From40To50 Require Translate Call.
From Vyper.From40To50 Require Import Proto.
From Vyper.L40Metered Require Call.
From Vyper.CheckArith Require Builtins Translate Call.
From Vyper Require Import ConstFold L10.Base.
From Vyper.L50 Require Import Types.

(** This is the part of the compiler that uses calldags,
      which are declaration maps annotated with maximum possible call depth.
    It starts with L10 (a subset of Fe/Vyper) and reaches L40 (a precursor to Yul).
    This part is defined separately here because the theorem verifying it (the next one)
    looks nice and clean compared to what happens at the final step from L40 to L50.
 *)
Definition translate_10_to_40 {C: VyperConfig}
                              (B: CheckArith.Builtins.builtin_names_config)
                              (calldag10: L10.Descend.calldag)
: string + L40.Descend.calldag
:= match const_fold_calldag                                                     (* 2nd pass *)
           (From10To20.FunCtx.translate_calldag calldag10)                      (* 1st pass *)
   with
   | inl err => inl err
   | inr calldag20' =>
      match From20To30.FunCtx.translate_calldag calldag20' with                 (* 3rd pass *)
      | inl err => inl err
      | inr calldag30 =>
             From30To40.FunCtx.translate_calldag B                              (* 5th pass *)
               (CheckArith.Translate.translate_calldag B calldag30)             (* 4th pass *)
      end
   end.

(**
  This theorem verifies the compiler up to L40.
  The storage is not modeled so [SloadOk] and [SstoreOk] just assert that using storage variables
  just happens to be the same thing as calling [sload()] and [sstore()].
 *)
Theorem translate_10_to_40_ok {C: VyperConfig}
                              (B: CheckArith.Builtins.builtin_names_config)
                              (calldag10: L10.Descend.calldag)
                              (calldag40: L40.Descend.calldag)
                              (Ok: translate_10_to_40 B calldag10 = inr calldag40)
                              (builtins: string -> option builtin)
                              (SloadOk: From30To40.Translate.BuiltinsSupportSload B builtins)
                              (SstoreOk: From30To40.Translate.BuiltinsSupportSstore B builtins)
                              (BuiltinsOk: Builtins.BuiltinsSupportUInt256 B builtins)
                              (fun_name: string)
                              (world: world_state)
                              (arg_values: list uint256):
  L40.Interpret.interpret builtins calldag40 fun_name world arg_values
   =
  L10.Interpret.interpret builtins calldag10 fun_name world arg_values.
Proof.
unfold translate_10_to_40 in Ok.
(* 10 -> 20 *)
rewrite<- From10To20.Call.translate_ok.
remember (From10To20.FunCtx.translate_calldag calldag10) as calldag20.
clear Heqcalldag20.

(* const fold *)
remember (const_fold_calldag calldag20) as calldag20'.
symmetry in Heqcalldag20'.
destruct calldag20' as [|calldag20']. { discriminate. }
rewrite<- (const_fold_ok _ Heqcalldag20').
clear Heqcalldag20'.

(* 20 -> 30 *)
remember (From20To30.FunCtx.translate_calldag calldag20') as calldag30_pre_arith.
symmetry in Heqcalldag30_pre_arith.
destruct calldag30_pre_arith as [|calldag30_pre_arith]. { discriminate. }
rewrite<- (From20To30.Call.translate_ok builtins _ _ Heqcalldag30_pre_arith).
clear Heqcalldag30_pre_arith.

(* check arith *)
rewrite<- (CheckArith.Call.translate_ok builtins BuiltinsOk).
remember (CheckArith.Translate.translate_calldag B calldag30_pre_arith) as calldag30.
clear Heqcalldag30.

(* 30 -> 40 *)
apply (From30To40.Call.translate_ok builtins _ _ SloadOk SstoreOk BuiltinsOk Ok).
Qed.


(** This is the verified part of the compiler.
    It translates a L10 (Fe subset) calldag to L50 (Yul subset).
    The whole compiler consists of parsing, building a calldag,
    translating (that's this part) and printing.
    Since Fe as defined here only has any meaning after the calldag has been built,
    the verified part must start with the calldag. 
 *)
Definition translate {C: VyperConfig}
                     (B: CheckArith.Builtins.builtin_names_config)
                     (protos: string_map proto)
                     (calldag10: L10.Descend.calldag)
: string + string_map L50.AST.fun_decl
:= match translate_10_to_40 B calldag10 with
   | inl err => inl err
   | inr calldag40 =>
        From40To50.Translate.translate_fun_decls B protos (cd_decls calldag40)  (* 6th pass *)
   end.


(** The Yul interpreter needs a maximum call depth,
    which if exceeded will result in a runtime exception.
    This function finds a necessary lower bound for this parameter
    such that this exception can never occur.
    In principle this value could be extracted from the L10 calldag
    and proven to not change throughout translate_10_to_40.
    But this is too complicated and we only care that such a value exists.
    Therefore, this function simply translates till L40 and gets the value from there.
 *)
Definition max_call_depth_lower_bound {C: VyperConfig}
                                      (B: CheckArith.Builtins.builtin_names_config)
                                      (calldag10: L10.Descend.calldag)
: nat
:= match translate_10_to_40 B calldag10 with
   | inl err => 0
   | inr calldag40 => L40Metered.Call.max_depth_in_calldag calldag40
   end.

(** The Yul interpreter needs a maximum loop iteration count,
    which if exceeded will result in a runtime exception.
    Everything in the comment above for [max_call_depth_lower_bound] applies here as well.
 *)
Definition max_loop_iters_lower_bound {C: VyperConfig}
                                      (B: CheckArith.Builtins.builtin_names_config)
                                      (calldag10: L10.Descend.calldag)
: N
:= match translate_10_to_40 B calldag10 with
   | inl err => 0
   | inr calldag40 => L40.AST.max_loop_count_decl_map (cd_decls calldag40)
   end.

(** This is it. This is the proof that the whole thing works.
    There are a lot of new things happening here compared to [translate_10_to_40_ok] above.
    There are two sets of builtins now - since Fe and Yul are typed differently - and they must agree.
    And the compiler needs to know the builtin prototypes so those must agree as well.
    And the compiler expects some builtins to be there and those expectations must be satisfied too.

    The Yul interpreter needs limits on call depth and loop iterations to be a total function.
    Those need to be big enough.

    Memory contents might not agree because the Fe interpreter can return results and throw exceptions
    without modifying memory while the Yul interpreter has to resort to [mstore()] for that.
    But everything else as provided by the [get_world_except_memory] projection will agree.
 *)
Theorem translate_ok {C: VyperConfig}
                     (B: CheckArith.Builtins.builtin_names_config)
                     (builtins10: string -> option L10.Base.builtin)
                     (builtins50: string -> option L50.Builtins.yul_builtin)
                     (BuiltinsAgree: AllBuiltinsAgreeIfU256 builtins10 builtins50)
                     (BuiltinsBasics: From40To50.Stmt.BuiltinsSupportBasics builtins50)
                     (SloadOk: From30To40.Translate.BuiltinsSupportSload B builtins10)
                     (SstoreOk: From30To40.Translate.BuiltinsSupportSstore B builtins10)
                     (BuiltinsSafe: forall x,     (* no builtin name may start with '$' *)
                                      builtins50 ("$" ++ x)%string = None)
                     (BuiltinsHaveArith: Builtins.BuiltinsSupportUInt256 B builtins10)
                     {protos: string_map proto}
                     (KnownProtosOk: check_known_protos B (map_lookup protos) = true)
                     (ProtosOk: ProtosAgree (map_lookup protos) builtins50)

                     (calldag10: L10.Descend.calldag)
                     {decls50: string_map L50.AST.fun_decl}
                     (Ok: translate B protos calldag10 = inr decls50)

                     (max_call_depth: nat)
                     (max_loop_iters: nat)
                     (DepthOk:  max_call_depth_lower_bound B calldag10 < max_call_depth)
                     (ItersOk: (max_loop_iters_lower_bound B calldag10 < N.of_nat max_loop_iters)%N)

                     (fun_name: string)
                     (world: world_state)
                     (args: list uint256):
   let '(world10, result10) := L10.Interpret.interpret builtins10 calldag10 fun_name world args in
   let '(world50, result50) :=
      (L50.Call.interpret
         max_call_depth max_loop_iters
         builtins50 (map_lookup decls50)
         ("$" ++ fun_name) world     (* functions are prefixed with '$' to avoid clashes with builtins *)
         (List.map dynamic_value_of_uint256 args))       (* args are converted into Yul dynamic values *)
   in
     get_world_except_memory world10 = get_world_except_memory world50
      /\
     match result10 with (* Yul returns a list of dynamic values so just result10 = result50 won't do *)
     | ExprAbort a    =>  result50 = Some (ExprAbort a)  (* 'Some' means that we're not out of limits *)
     | ExprSuccess v  =>  result50 = Some (ExprSuccess (dynamic_value_of_uint256 v :: nil))
     end.
Proof.
unfold translate in Ok.
remember (translate_10_to_40 B calldag10) as calldag40. symmetry in Heqcalldag40.
destruct calldag40 as [|calldag40]. { discriminate. }
rewrite<- (translate_10_to_40_ok B calldag10 calldag40 Heqcalldag40 builtins10
           SloadOk SstoreOk BuiltinsHaveArith fun_name world args).
unfold max_call_depth_lower_bound in DepthOk. rewrite Heqcalldag40 in DepthOk.
unfold max_loop_iters_lower_bound in ItersOk. rewrite Heqcalldag40 in ItersOk.
assert (M := L40Metered.Call.metering_ok DepthOk builtins10 fun_name world args).
destruct (Interpret.interpret builtins10 calldag40 fun_name world args) as (world10, result10).
assert (T := From40To50.Call.translate_ok max_call_depth max_loop_iters builtins10 builtins50
                                          BuiltinsAgree BuiltinsBasics BuiltinsSafe BuiltinsHaveArith
                                          KnownProtosOk ProtosOk Ok ItersOk
                                          fun_name world args).
rewrite M in T. clear M.
unfold dynamic_value_of_uint256.
destruct L50.Call.interpret as (world50, result50).
unfold From40To50.Expr.ResultsAgree in T.
destruct result50 as [result50|]. 2:easy.
destruct T as (T, E).
unfold ExprResultsAgree in E.
destruct result10 as [v10|a10], result50 as [v50|a50]; try easy.
2:{ (* double abort *) subst a50. destruct a10; now subst. }
(* double success *)
destruct v50. 1:easy.
destruct v50. 2:easy.
destruct E as (E, _).
now subst.
Qed.

(** This function takes the parser output, which is a list of L10 declarations, and compiles it to L50.

    Here [make_calldag] converts the output of the parser to the input to the verified compiler,
    checking for duplicated names and call cycles.
 *)
Definition compile_to_L50 {C: VyperConfig}
                          (B: CheckArith.Builtins.builtin_names_config)
                          (protos: string_map proto)
                          (parsed_src: list L10.AST.decl)
: string + string_map L50.AST.fun_decl
:= match make_calldag L10.AST.decl_name L10.Callset.decl_callset parsed_src with
   | inl err => inl err
   | inr cd => translate B protos cd
   end.

Definition string_of_fun_decls {C: VyperConfig} (d: string_map L50.AST.fun_decl)
:= (let newline := "
" in List.fold_right (fun x tail => x ++ newline ++ tail) "" (L50.AST.lines_of_fun_decls d))%string.

(** This is the compiler without parsers (for the prototypes and for Fe).
    Both parsers are implemented with the usual Haskell tools, alex and happy.
 *)
Definition compile {C: VyperConfig}
                   (B: CheckArith.Builtins.builtin_names_config)
                   (parsed_proto: list proto_ast)
                   (parsed_src: list L10.AST.decl)
: string + string
:= match make_proto_table parsed_proto with
   | inl err => inl err
   | inr protos => match compile_to_L50 B protos parsed_src with
                   | inl err => inl err
                   | inr d => inr (string_of_fun_decls d)
                   end
   end.
