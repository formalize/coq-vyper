From Coq Require Import Arith NArith String ProofIrrelevance.

From Vyper.L10 Require Import Base.
From Vyper.L50 Require Import Types Builtins.
From Vyper.CheckArith Require Import Builtins.
From Vyper Require Import Config ProtoAST NaryFun Logic2.

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

Definition check_proto (mb_p: option proto) (n_ins n_outs: nat)
:= match mb_p with
   | None => false
   | Some p => (   proto_is_u256_only p
                && (List.length (p_inputs p)  =? n_ins)
                && (List.length (p_outputs p) =? n_outs))%bool%nat
   end.

Definition check_known_protos {C: VyperConfig}
                              (B: builtin_names_config)
                              (protos: string -> option proto)
: bool
:= check_proto (protos (builtin_name_uint256_add B)) 2 1
&& check_proto (protos (builtin_name_uint256_sub B)) 2 1
&& check_proto (protos (builtin_name_uint256_mul B)) 2 1
&& check_proto (protos (builtin_name_uint256_div B)) 2 1
&& check_proto (protos (builtin_name_uint256_mod B)) 2 1
&& check_proto (protos (builtin_name_uint256_pow B)) 2 1
&& check_proto (protos (builtin_name_uint256_not B)) 1 1
&& check_proto (protos (builtin_name_uint256_iszero B)) 1 1
&& check_proto (protos (builtin_name_uint256_and B)) 2 1
&& check_proto (protos (builtin_name_uint256_or B))  2 1
&& check_proto (protos (builtin_name_uint256_xor B)) 2 1
&& check_proto (protos (builtin_name_uint256_lt B))  2 1
&& check_proto (protos (builtin_name_uint256_eq B))  2 1
&& check_proto (protos (builtin_name_uint256_shl B)) 2 1
&& check_proto (protos (builtin_name_uint256_shr B)) 2 1
&& check_proto (protos "mstore") 2 0
&& check_proto (protos "revert") 2 0
&& check_proto (protos "stop") 0 0
&& check_proto (protos "pop") 1 0
&& check_proto (protos "sload") 1 1
&& check_proto (protos "sstore") 2 0.


(** Value agreement between L40 and L50.
    [n]: expected length of [e50]
    The tricky part here is that L50 might have no value where L40 sees zero. 
 *)
Definition ExprResultsAgree {C: VyperConfig}
                            (e40: expr_result uint256)
                            (e50: expr_result (list dynamic_value))
                            (n: N)
:= match e40, e50 with
   | ExprAbort a40, ExprAbort a50               =>  a40 = a50
   | ExprSuccess v40, ExprSuccess nil           =>  v40 = zero256 %Z /\ n = 0%N
   | ExprSuccess v40, ExprSuccess (v50 :: nil)  =>  (* v40 = uint256_of_dynamic_value v50 *)
                                                    v50 = (existT _ U256 (yul_uint256 v40)) /\ n = 1%N
   | _, _ => False
   end.


(** Value agreement between L40 and L50, a variant with u256 list on the L50 side.
    [n]: expected length of [e50]
    The tricky part here is that L50 might have no value where L40 sees zero.
 *)
Definition ExprResultsAgree256 {C: VyperConfig}
                               (e40: expr_result uint256)
                               (e50: expr_result (list uint256))
                               (n: N)
:= match e40, e50 with
   | ExprAbort a40, ExprAbort a50               =>  a40 = a50
   | ExprSuccess v40, ExprSuccess nil           =>  v40 = zero256%Z /\ n = 0%N
   | ExprSuccess v40, ExprSuccess (v50 :: nil)  =>  v40 = v50 /\ n = 1%N
   | _, _ => False
   end.


Definition BuiltinsAgree {C: VyperConfig}
                         (b40: builtin)
                         (b50: L50.Builtins.yul_builtin)
                         (B50InputsU256:   L50.Builtins.all_are_u256 (L50.Builtins.b_input_types  b50) = true)
                         (B50OutputssU256: L50.Builtins.all_are_u256 (L50.Builtins.b_output_types b50) = true)
:= let '(existT _ arity f40) := b40 in
       arity = List.length (L50.Builtins.b_input_types b50)
        /\
       forall (world: world_state) (args: list uint256)
              (LenOk40: (arity =? List.length args = true)%nat)
              (LenOk50: List.length (Builtins.b_input_types b50) = List.length args),
         let (w40, e40) := (L10.Base.call_builtin args LenOk40 (f40 world)) in
         let (w50, e50) := (call_builtin_u256 b50 world args LenOk50) in
         w40 = w50  /\  ExprResultsAgree256 e40 e50 
                                            (N.of_nat (List.length (L50.Builtins.b_output_types b50))).

Definition AllBuiltinsAgreeIfU256 {C: VyperConfig}
                                  (builtins40: string -> option builtin)
                                  (builtins50: string -> option L50.Builtins.yul_builtin)
:= forall name: string,
     match builtins50 name with
     | None => True
     | Some b50 =>
        (if L50.Builtins.all_are_u256 (L50.Builtins.b_input_types b50) as z return _ = z -> _
         then 
           fun i256 =>
            (if L50.Builtins.all_are_u256 (L50.Builtins.b_output_types b50) as z return _ = z -> _
              then fun o256 =>
                   match builtins40 name with
                   | None => False
                   | Some b40 => BuiltinsAgree b40 b50 i256 o256
                   end
              else fun _ => True) eq_refl
         else fun _ => True) eq_refl
     end.

Lemma binop_to_yul {C: VyperConfig}
                   {builtins40: string -> option L10.Base.builtin}
                   {builtins50: string -> option L50.Builtins.yul_builtin}
                   (BuiltinsOk: AllBuiltinsAgreeIfU256 builtins40 builtins50)
                   {protos: string -> option proto}
                   (ProtosOk: ProtosAgree protos builtins50)
                   {name: string}
                   (ProtoOk: check_proto (protos name) 2 1 = true)
                   {binop: uint256 -> uint256 -> uint256}
                   (Support40: BuiltinsSupportBinop builtins40 name binop):
  match builtins50 name with
  | Some b => forall w x y,
                L50.Builtins.call_builtin b w 
                     (existT _ U256 (yul_uint256 x) :: existT _ U256 (yul_uint256 y) :: nil)
                 =
                (w, ExprSuccess (existT _ U256 (yul_uint256 (binop x y)) :: nil))
  | None => False
  end.
Proof.
assert (P := ProtosOk name).
unfold check_proto in ProtoOk.
destruct (protos name) as [p|]. 2:discriminate.
assert (A := BuiltinsOk name).
destruct (builtins50 name) as [b|]. 2:contradiction.
destruct P as (InputsAgree, OutputsAgree).
(* we have:
  InputsAgree : p_inputs p = b_input_types b
  OutputsAgree : p_outputs p = b_output_types b
*)
unfold proto_is_u256_only in ProtoOk.
apply andb_prop in ProtoOk. destruct ProtoOk as (ProtoOk, OutputLenIs1).
apply andb_prop in ProtoOk. destruct ProtoOk as (ProtoOk, InputLenIs2).
apply andb_prop in ProtoOk. destruct ProtoOk as (InputsAreU256, OutputsAreU256).
rewrite InputsAgree in InputsAreU256. rewrite OutputsAgree in OutputsAreU256.
rewrite InputsAgree in InputLenIs2. rewrite OutputsAgree in OutputLenIs1.
apply Nat.eqb_eq in InputLenIs2. apply Nat.eqb_eq in OutputLenIs1.
rewrite if_yes with (E := InputsAreU256) in A.
rewrite if_yes with (E := OutputsAreU256) in A.
unfold BuiltinsSupportBinop in Support40.
destruct (builtins40 name) as [(arity40, f40)|]. 2:contradiction.
unfold BuiltinsAgree in A.
unfold BuiltinIsBinop in Support40. cbn in Support40.
destruct arity40. { destruct A as (A, _). now rewrite InputLenIs2 in A. }
destruct arity40. { destruct A as (A, _). now rewrite InputLenIs2 in A. }
destruct arity40. 2:{ destruct A as (A, _). now rewrite InputLenIs2 in A. }
destruct A as (_, A).
unfold L10.Base.call_builtin in A.
intros w x y.
assert (LenOk50: Datatypes.length (b_input_types b) = Datatypes.length (x :: y :: nil))
  by apply InputLenIs2.
assert (V := A w (x :: y :: nil) eq_refl LenOk50).
cbn in V. clear A.
cbn in Support40. rewrite Support40 in V.
rewrite OutputLenIs1 in V. cbn in V.
assert (BI: b_input_types b = U256 :: U256 :: nil).
{
  clear V.
  remember (b_input_types b) as z.
  destruct z as [|u]. { easy. }
  destruct z as [|v]. { easy. }
  destruct z. 2:easy.
  cbn in InputsAreU256.
  destruct (yul_type_eq_dec u U256) as [Eu|NE]. 2:easy.
  destruct (yul_type_eq_dec v U256) as [Ev|NE]. 2:easy.
  now subst u v.
}
unfold call_builtin.
assert (TypecheckOk: mass_typecheck
                      (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x)
                       :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 y) :: nil) 
                      (b_input_types b) = MassTypecheckOk)
  by now rewrite BI.
rewrite mass_typecheck_ok_rewrite with (Ok := TypecheckOk).
unfold call_builtin_u256 in V.
cbn.
remember ((Nat.eq_le_incl (Datatypes.length (b_input_types b)) (Datatypes.length (x :: y :: nil))
              LenOk50)) as foo.
remember ((Builtins.call_builtin_helper b
        (existT (fun t : yul_type => yul_value t) U256 (yul_uint256 x)
         :: existT (fun t : yul_type => yul_value t) U256 (yul_uint256 y) :: nil) TypecheckOk))
  as bar.
clear Heqfoo. clear Heqbar.
assert (foo = bar) by apply proof_irrelevance. subst bar.
destruct (nary_call (b_fun b w) (x :: y :: nil) foo) as ((w50, r50), trash).
cbn in V. destruct V as (W, V). subst w50.
destruct r50 as [result|]. 2:easy.
assert (BO: b_output_types b = U256 :: nil).
{
  clear V.
  remember (b_output_types b) as z.
  destruct z as [|u]. { easy. }
  destruct z. 2:easy.
  cbn in OutputsAreU256.
  destruct (yul_type_eq_dec u U256) as [Eu|NE]. 2:easy.
  now subst u.
}
rewrite BO.
destruct result. 1:easy.
destruct result. 2:easy.
destruct V as (V, _).
subst u.
unfold mass_cast.
now rewrite yul_value_of_uint256_u256.
Qed.



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