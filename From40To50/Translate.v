From Coq Require Import String NArith DecimalString List.

From Vyper Require Import Config Range.
From Vyper.CheckArith Require Import Builtins.
From Vyper.L10 Require Import Base.
From Vyper.L40 Require AST.
From Vyper.L50 Require AST.
From Vyper.L50 Require Import Types.
From Vyper.From40To50 Require Import Proto.

Local Open Scope list_scope.
Local Open Scope string_scope.

Definition make_var_name (id: string) (index: N)
:= ("$$" ++ id ++ NilZero.string_of_uint (N.to_uint index))%string.


(** Returns the resulting expression and the number of expected values. *)
Fixpoint translate_expr {C: VyperConfig} (protos: string_map proto)
                        (e: L40.AST.expr) (loop_depth: N)
: string + L50.AST.expr * N
:= let _ := string_map_impl in
   let fix translate_expr_list {C: VyperConfig} (l: list L40.AST.expr) (loop_depth: N)
       : string + list L50.AST.expr
       := match l with
          | nil => inr nil
          | cons h t => match translate_expr protos h loop_depth with
                        | inl err => inl err
                        | inr (h', n) =>
                            if (n =? 1)%N
                              then match translate_expr_list t loop_depth with
                                   | inl err => inl err
                                   | inr t' => inr (cons h' t')
                                   end
                              else inl "an expression with exactly one value expected in an expr list"
                        end
          end
   in match e with
      | L40.AST.Const value => inr (L50.AST.Const U256 (yul_uint256 value), 1%N)
      | L40.AST.LocalVar index => inr (L50.AST.LocVar (make_var_name "var" index), 1%N)
      | L40.AST.LoopOffset => if (loop_depth =? 0)%N
                                then inl "LoopOffset outside of a loop"
                                else inr (L50.AST.LocVar (make_var_name "offset" (N.pred loop_depth)), 1%N)
      | L40.AST.LoopCursor => if (loop_depth =? 0)%N
                                then inl "LoopCursor outside of a loop"
                                else  inr (L50.AST.LocVar (make_var_name "cursor" (N.pred loop_depth)), 1%N)
      | L40.AST.PrivateCall name args => 
          match translate_expr_list args loop_depth with
          | inl err => inl err
          | inr args' => inr (L50.AST.FunCall ("$" ++ name) args', 1%N)
          end
      | L40.AST.BuiltinCall name args =>
          match translate_expr_list args loop_depth with
          | inl err => inl err
          | inr args' =>
              match Map.lookup protos name with
              | None => inl ("Unable to find a prototype for a builtin call: " ++ name)
              | Some p =>
                  if proto_is_u256_only p
                    then inr (L50.AST.FunCall name args', N.of_nat (length (p_outputs p)))
                    else inl ("A builtin call is not u256-only: " ++ name)
              end
          end
      end.

Definition translate_small_stmt {C: VyperConfig}
                                (is_in_function: bool)
                                (protos: string_map proto)
                                (ss: L40.AST.small_stmt)
                                (loop_depth: N)
: string + list L50.AST.stmt
:= match ss with
   | L40.AST.Abort AbortBreak    => inr (L50.AST.Break :: nil)
   | L40.AST.Abort AbortContinue => inr (L50.AST.Continue :: nil)
   | L40.AST.Abort (AbortException code) =>
        inr
        (L50.AST.Expr (L50.AST.FunCall "mstore"
                             (* addr: *)    (L50.AST.Const U256 (yul_uint256 zero256)
                             (* value: *) :: L50.AST.Const U256 (yul_uint256 code)
                                          :: nil))
         :: L50.AST.Expr (L50.AST.FunCall "revert"
                            (* addr: *)     (L50.AST.Const U256 (yul_uint256 zero256)
                            (* len:  *)   :: L50.AST.Const U256 (yul_uint256 one256)
                                          :: nil))
         :: nil)
  | L40.AST.Abort AbortReturnFromContract =>
        inr (L50.AST.Expr (L50.AST.FunCall "stop" nil) :: nil)
  | L40.AST.Abort AbortRevert =>
        inr (L50.AST.Expr (L50.AST.FunCall "revert"
                                (* addr: *)     (L50.AST.Const U256 (yul_uint256 zero256)
                                (* len:  *)   :: L50.AST.Const U256 (yul_uint256 zero256)
                                              :: nil))
            :: nil)
  | L40.AST.Return e =>
        if is_in_function
          then match translate_expr protos e loop_depth with
               | inl err => inl err
               | inr (e', 0%N) =>
                       inr (L50.AST.Expr e'
                          :: L50.AST.Assign ("$$result" :: nil) (L50.AST.Const U256 (yul_uint256 zero256))
                          :: L50.AST.Leave
                          :: nil)
               | inr (e', 1%N) =>
                       inr (L50.AST.Assign ("$$result" :: nil) e'
                          :: L50.AST.Leave
                          :: nil)
               | _ => inl "too many values"
               end
          else inl "cannot return from outside any function"
  | L40.AST.Raise e =>
        match translate_expr protos e loop_depth with
        | inl err => inl err
        | inr (e', 0%N) =>
            inr (L50.AST.Expr e'
              :: L50.AST.Expr (L50.AST.FunCall "mstore"
                                 (* addr: *)     (L50.AST.Const U256 (yul_uint256 zero256)
                                 (* value: *) :: (L50.AST.Const U256 (yul_uint256 zero256))
                                              :: nil))
            :: L50.AST.Expr (L50.AST.FunCall "revert"
                                (* addr: *)     (L50.AST.Const U256 (yul_uint256 zero256)
                                (* len:  *)   :: L50.AST.Const U256 (yul_uint256 one256)
                                              :: nil))
            :: nil)
        | inr (e', 1%N) =>
            inr (L50.AST.Expr (L50.AST.FunCall "mstore"
                                 (* addr: *)    (L50.AST.Const U256 (yul_uint256 zero256)
                                 (* value: *) :: e'
                                              :: nil))
              :: L50.AST.Expr (L50.AST.FunCall "revert"
                                  (* addr: *)     (L50.AST.Const U256 (yul_uint256 zero256)
                                  (* len:  *)   :: L50.AST.Const U256 (yul_uint256 one256)
                                                :: nil))
              :: nil)
        | _ => inl "too many values"
        end
  | L40.AST.Assign index e =>
        match translate_expr protos e loop_depth with
        | inl err => inl err
        | inr (e', 0%N) =>
           inr (L50.AST.Expr e'
             :: L50.AST.Assign (make_var_name "var" index :: nil) 
                               (L50.AST.Const U256 (yul_uint256 zero256))
             :: nil)
        | inr (e', 1%N) =>
            inr (L50.AST.Assign (make_var_name "var" index :: nil) e'
              :: nil)
        | _ => inl "too many values"
        end
  | L40.AST.ExprStmt e =>
        match translate_expr protos e loop_depth with
        | inl err => inl err
        | inr (e', 0%N) => inr (L50.AST.Expr e' :: nil)
        | inr (e', 1%N) =>
            inr (L50.AST.Expr (L50.AST.FunCall "pop" (e' :: nil)) :: nil)
        | _ => inl "too many values"
        end
  end.

Fixpoint translate_stmt {C: VyperConfig}
                        (is_in_function: bool)
                        (B: builtin_names_config)
                        (protos: string_map proto)
                        (s: L40.AST.stmt)
                        (loop_depth: N)
{struct s}
: string + list L50.AST.stmt
:= match s with
   | L40.AST.SmallStmt ss => translate_small_stmt is_in_function protos ss loop_depth
   | L40.AST.Switch e cases maybe_default =>
      let fix translate_cases (l: list L40.AST.case)
          := match l with
             | nil => inr nil
             | (L40.AST.Case guard body) :: t =>
                  match translate_block is_in_function B protos body loop_depth with
                  | inl err => inl err
                  | inr body' =>
                      match translate_cases t with
                      | inl err => inl err
                      | inr t' => inr (L50.AST.Case U256 (yul_uint256 guard) body' :: t')
                      end
                  end
             end
      in let translate_default (d: option L40.AST.block)
             := match d with
                | None => inr None
                | Some b => match translate_block is_in_function B protos b loop_depth with
                            | inl err => inl err
                            | inr b' => inr (Some b')
                            end
                end
      in match translate_cases cases with
         | inl err => inl err
         | inr cases' =>
             match translate_default maybe_default with
             | inl err => inl err
             | inr default' =>
                match translate_expr protos e loop_depth with
                | inl err => inl err
                | inr (e', 0%N) => inr (L50.AST.Expr e' 
                                     :: L50.AST.Switch (L50.AST.Const U256 (yul_uint256 zero256))
                                                       cases' default'
                                     :: nil)
                | inr (e', 1%N) => inr (L50.AST.Switch e' cases' default'
                                     :: nil)
                | _ => inl "too many values"
                end
             end
         end
   | L40.AST.Loop index count body =>
      match translate_block is_in_function B protos body (N.succ loop_depth) with
      | inl err => inl err
      | inr body' =>
          let offset_var := make_var_name "offset" loop_depth in
          let cursor_var := make_var_name "cursor" loop_depth in
          inr (L50.AST.For
                (L50.AST.Block
                   (L50.AST.VarDecl ((U256, offset_var) :: nil)
                                    (Some (L50.AST.LocVar (make_var_name "var" index)))
                    :: L50.AST.VarDecl ((U256, cursor_var) :: nil) None
                    :: nil))
                (L50.AST.FunCall (builtin_name_uint256_lt B)
                   (L50.AST.LocVar cursor_var 
                    :: L50.AST.Const U256 (yul_uint256 count)
                    :: nil))
                (L50.AST.Block
                   (L50.AST.Assign (cursor_var :: nil)
                      (L50.AST.FunCall (builtin_name_uint256_add B)
                         (L50.AST.LocVar cursor_var 
                          :: L50.AST.Const U256 (yul_uint256 one256)
                          :: nil))
                   :: nil))
                body'
              :: nil)
      end
   end
with translate_block {C: VyperConfig}
                     (is_in_function: bool)
                     (B: builtin_names_config)
                     (protos: string_map proto)
                     (b: L40.AST.block)
                     (loop_depth: N)
: string + L50.AST.block
:= let '(L40.AST.Block body) := b in
   let fix translate_stmt_list (l: list L40.AST.stmt)
       := match l with
          | nil => inr nil
          | h :: t => match translate_stmt is_in_function B protos h loop_depth with
                      | inl err => inl err
                      | inr h' => match translate_stmt_list t with
                                  | inl err => inl err
                                  | inr t' => inr (h' ++ t')%list
                                  end
                      end
          end
   in match translate_stmt_list body with
      | inl err => inl err
      | inr body' => inr (L50.AST.Block body')
      end.

Definition make_input_typenames (count: N)
:= List.map (fun n => (U256, make_var_name "var" n)) (range 0 count).

Definition make_var_declarations {C: VyperConfig} (start finish: N)
:= map (fun n => L50.AST.VarDecl ((U256, make_var_name "var" n) :: nil) None)
       (range start (finish - start)%N).

Definition translate_fun_decl {C: VyperConfig}
                              (B: builtin_names_config)
                              (protos: string_map proto)
                              (d: L40.AST.decl)
: string + L50.AST.fun_decl
:= let '(L40.AST.FunDecl name args_count body) := d in
   match translate_block true B protos body 0%N with
   | inl err => inl err
   | inr (L50.AST.Block body') =>
      inr {| L50.AST.fd_name := name
           ; L50.AST.fd_inputs := make_input_typenames args_count
           ; L50.AST.fd_outputs := (U256, "$$result") :: nil
           ; L50.AST.fd_body :=
                L50.AST.Block (make_var_declarations args_count (L40.AST.var_cap_block body) ++ body')
          |}
   end.

(* This is a version of alist_maybe_map but we want to map keys too. *)
Fixpoint alist_maybe_map_kv {Key Value Value' Err: Type}
                            (KeyEqDec: forall x y: Key, {x = y} + {x <> y})
                            (a: list (Key * Value))
                            (fkey: Key -> Key)
                            (fval: Value -> Err + Value')
{struct a}
: Err + list (Key * Value')
:= match a with
   | nil => inr nil
   | cons (k, v) t =>
      match fval v with
      | inl err => inl err
      | inr fv =>
          match alist_maybe_map_kv KeyEqDec t fkey fval with
          | inl err => inl err
          | inr mt => inr (cons (fkey k, fv) mt)
          end
      end
   end.

Lemma alist_maybe_map_kv_ok {Key Value Value' Err: Type}
                            {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
                            {a: list (Key * Value)}
                            {a': list (Key * Value')}
                            (fkey: Key -> Key)
                            {fval: Value -> Err + Value'}
                            (E: alist_maybe_map_kv KeyEqDec a fkey fval = inr a')
                            (Inj: forall a b, fkey a = fkey b -> a = b)
                            (key: Key):
  match Map.alist_lookup KeyEqDec a key with
  | Some v =>
      match fval v with
      | inl _ => False
      | inr fv => Map.alist_lookup KeyEqDec a' (fkey key) = Some fv
      end
  | None => Map.alist_lookup KeyEqDec a' (fkey key) =None
  end.
Proof.
revert a' E.
induction a as [|(k, v)]; intros. { cbn in *. inversion E. now subst. }
cbn in *.
remember (KeyEqDec key k) as key_k.
destruct key_k.
{
  destruct (fval v). { discriminate. }
  subst.
  destruct alist_maybe_map_kv. { discriminate. }
  inversion E. subst. cbn.
  now destruct (KeyEqDec (fkey k) (fkey k)).
}
destruct (fval v). { discriminate. }
subst.
destruct alist_maybe_map_kv. { discriminate. }
inversion E. subst. cbn.
destruct (KeyEqDec (fkey key) (fkey k)) as [Ekey|Nkey].
{ apply Inj in Ekey. contradiction. }
now apply IHa.
Qed.

Lemma dollar_inj (a b: string)
                 (H: ("$" ++ a)%string = ("$" ++ b)%string):
  a = b.
Proof.
now inversion H.
Qed.

Definition translate_fun_decls {C: VyperConfig}
                               (B: builtin_names_config)
                               (protos: string_map proto)
                               (decls: string_map L40.AST.decl)
: string + string_map L50.AST.fun_decl
:= let _ := string_map_impl in 
   match alist_maybe_map_kv string_dec (Map.items decls)
                            (fun x => "$" ++ x)%string
                            (translate_fun_decl B protos)
   with
   | inl err => inl err
   | inr a => inr (Map.of_alist a)
   end.

Lemma translate_fun_decls_ok {C: VyperConfig}
                             {B: builtin_names_config}
                             {protos: string_map proto}
                             {decls40: string_map L40.AST.decl}
                             {decls50: string_map L50.AST.fun_decl}
                             (Ok: translate_fun_decls B protos decls40 = inr decls50)
                             (name: string):
  match map_lookup decls40 name, map_lookup decls50 ("$" ++ name)%string with
  | Some d40, Some d50 => translate_fun_decl B protos d40 = inr d50
  | None, None => True
  | _, _ => False
  end.
Proof.
unfold translate_fun_decls in Ok.
unfold map_lookup in *.
rewrite Map.items_ok.
remember (alist_maybe_map_kv _ _ _ _) as a.
destruct a. { discriminate. }
inversion Ok. subst decls50. clear Ok.
symmetry in Heqa. assert (A := alist_maybe_map_kv_ok _ Heqa dollar_inj name).
destruct (Map.alist_lookup string_dec (Map.items decls40) name); rewrite Map.of_alist_ok.
{
  remember (Map.alist_lookup string_dec l name) as x.
  remember (translate_fun_decl B protos d) as d'.
  destruct d'. { contradiction. }
  subst. rewrite A. trivial.
}
now rewrite A.
Qed.
