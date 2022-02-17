From Coq Require Import List String NArith ZArith DecimalString HexString.

From Vyper Require Import Config FSet.
From Vyper Require L10.Base.

(** The exprs are back!
  Note that L40 (like Yul) evaluates arguments right-to-left.
 *)
Inductive expr {C: VyperConfig}
:= Const (val: uint256)
 | LocalVar (index: N)
 | LoopOffset (* always innermost *)
 | LoopCursor (* always innermost *)
 | PrivateCall (name: string) (args: list expr)
 | BuiltinCall (name: string) (args: list expr).

Fixpoint expr_ind' {C: VyperConfig}
                   (P: expr -> Prop)
                   (HConst: forall val, P (Const val))
                   (HLocalVar: forall name, P (LocalVar name))
                   (HLoopStart: P LoopOffset)
                   (HLoopCursor: P LoopCursor)
                   (HPrivateCall: forall name args,
                        Forall P args -> P (PrivateCall name args))
                   (HBuiltinCall: forall name args,
                        Forall P args -> P (BuiltinCall name args))
                   (e: expr)
{struct e}
: P e
:= let ind := expr_ind' P HConst HLocalVar HLoopStart HLoopCursor HPrivateCall HBuiltinCall in
   let fix expr_list_ind (l: list expr)
       : Forall P l
       := match l with
          | nil => Forall_nil P
          | cons h t => Forall_cons h (ind h) (expr_list_ind t)
          end
   in match e with
      | Const val => HConst val
      | LocalVar name => HLocalVar name
      | LoopOffset => HLoopStart
      | LoopCursor => HLoopCursor
      | PrivateCall name args => HPrivateCall name args (expr_list_ind args)
      | BuiltinCall name args => HBuiltinCall name args (expr_list_ind args)
      end.

Inductive small_stmt {C: VyperConfig}
:= Abort (ab: L10.Base.abort)
 | Return (e: expr) (* In Yul this is called "leave" *)
 | Raise (e: expr)
 | Assign (lhs: N) (rhs: expr)
 | ExprStmt (e: expr).

Inductive stmt {C: VyperConfig}
:= SmallStmt (ss: small_stmt)
 | Switch (e: expr) (cases: list case) (default: option block)
 | Loop (var: N) (count: uint256) (body: block) (** starts from 0 *)
with case  {C: VyperConfig} := Case (val: uint256) (body: block)
with block {C: VyperConfig} := Block (body: list stmt).

Fixpoint stmt_ind' {C: VyperConfig}
                   (P: stmt -> Prop)
                   (HSmallStmt: forall ss, P (SmallStmt ss))
                   (HSwitchWithoutDefault:
                      forall e cases,
                        Forall (fun case => match case with
                                            | Case _ (Block body) => Forall P body
                                            end) cases 
                         ->
                        P (Switch e cases None))
                   (HSwitchWithDefault:
                      forall e cases default,
                        Forall (fun case => match case with
                                            | Case _ (Block body) => Forall P body
                                            end) cases
                         ->
                        Forall P default
                         ->
                        P (Switch e cases (Some (Block default))))
                   (HLoop: forall var count body,
                             Forall P body -> P (Loop var count (Block body)))
                   (s: stmt)
{struct s}
: P s
:= let ind := stmt_ind' P HSmallStmt HSwitchWithoutDefault HSwitchWithDefault HLoop in
   let fix stmt_list_ind (l: list stmt)
   : Forall P l
   := match l with
      | nil => Forall_nil P
      | cons h t => Forall_cons h (ind h) (stmt_list_ind t)
      end
   in let case_ind (value: uint256) (body: list stmt)
      : (fun case => match case with
                     | Case _ (Block body) => Forall P body
                     end) (Case value (Block body))
      := stmt_list_ind body
   in let fix case_list_ind (l: list case)
      : Forall (fun case => match case with
                            | Case _ (Block body) => Forall P body
                            end) l
      := match l with
         | nil => Forall_nil (fun case => match case with
                                          | Case _ (Block body) => Forall P body
                                          end)
         | cons (Case val (Block body)) t => Forall_cons _ (case_ind val body) (case_list_ind t)
         end
   in match s with
      | SmallStmt ss => HSmallStmt ss
      | Switch e cases None => HSwitchWithoutDefault e cases (case_list_ind cases)
      | Switch e cases (Some (Block default)) => HSwitchWithDefault e cases default 
                                                                    (case_list_ind cases)
                                                                    (stmt_list_ind default)
      | Loop var count (Block body) => HLoop var count body (stmt_list_ind body)
      end.

Inductive decl {C: VyperConfig}
:= FunDecl (name: string) (args_count: N) (body: block).

Fixpoint var_cap_expr {C: VyperConfig} (e: expr)
: N
:= let fix var_cap_expr_list {C: VyperConfig} (l: list expr) :=
             match l with
             | nil => 0%N
             | h :: t => N.max (var_cap_expr h) (var_cap_expr_list t)
             end
   in match e with
      | Const _ => 0%N
      | LocalVar index => N.succ index
      | LoopOffset => 0%N
      | LoopCursor => 0%N
      | PrivateCall _ args => var_cap_expr_list args
      | BuiltinCall _ args => var_cap_expr_list args
      end.

Definition var_cap_small_stmt {C: VyperConfig} (ss: small_stmt)
:= match ss with
   | Abort _ => 0%N
   | Return e | Raise e | ExprStmt e => var_cap_expr e
   | Assign lhs rhs => N.max (N.succ lhs) (var_cap_expr rhs)
   end.

Fixpoint var_cap_stmt {C: VyperConfig} (s: stmt)
:= match s with
   | SmallStmt ss => var_cap_small_stmt ss
   | Switch e cases default =>
        let fix var_cap_cases (l: list case) :=
                  match l with
                  | nil => 0%N
                  | (Case _ body) :: t => N.max (var_cap_block body) (var_cap_cases t)
                  end
        in let d := match default with
                    | Some b => var_cap_block b
                    | None => 0%N
                    end
        in N.max (var_cap_expr e) (N.max (var_cap_cases cases) d)
  | Loop var _ body => N.max (N.succ var) (var_cap_block body)
  end
with var_cap_block  {C: VyperConfig} (b: block)
:= let '(Block body) := b in
   let fix var_cap_stmt_list (l: list stmt) :=
            match l with
            | nil => 0%N
            | h :: t => N.max (var_cap_stmt h) (var_cap_stmt_list t)
            end
   in var_cap_stmt_list body.

Fixpoint max_loop_count_stmt {C: VyperConfig} (s: stmt)
:= match s with
   | SmallStmt _ => 0%N
   | Switch _ cases default =>
      let fix max_loop_count_cases (l: list case) := 
                match l with
                | nil => 0%N
                | (Case _ body) :: t => N.max (max_loop_count_block body) (max_loop_count_cases t)
                end
      in let d := match default with
                  | Some b => max_loop_count_block b
                  | None => 0%N
                  end
      in N.max (max_loop_count_cases cases) d
   | Loop _ count body => N.max (Z.to_N (Z_of_uint256 count)) (max_loop_count_block body)
   end
with max_loop_count_block {C: VyperConfig} (b: block)
:= let '(Block body) := b in
   let fix max_loop_count_stmt_list (l: list stmt) :=
            match l with
            | nil => 0%N
            | h :: t => N.max (max_loop_count_stmt h) (max_loop_count_stmt_list t)
            end
   in max_loop_count_stmt_list body.

Definition max_loop_count_decl {C: VyperConfig} (d: L40.AST.decl)
:= let '(L40.AST.FunDecl _ _ body) := d in
   L40.AST.max_loop_count_block body.

Definition max_loop_count_decl_list {C: VyperConfig} (l: list L40.AST.decl)
:= List.fold_right N.max 0%N (List.map max_loop_count_decl l).

Definition max_loop_count_decl_map {C: VyperConfig} (l: string_map L40.AST.decl)
:= let _ := string_map_impl in
   max_loop_count_decl_list (List.map snd (Map.items l)).

Lemma enough_iterations_for_decl {C: VyperConfig}
                                 {declmap: string_map decl}
                                 {name: string}
                                 {d: decl}
                                 (Found: L10.Base.map_lookup declmap name = Some d)
                                 {m: N}
                                 (EnoughForEverything: (max_loop_count_decl_map declmap < m)%N):
  (max_loop_count_decl d < m)%N.
Proof.
unfold max_loop_count_decl_map in EnoughForEverything.
unfold L10.Base.map_lookup in Found.
rewrite Map.items_ok in Found.
remember (Map.items declmap) as alist. clear Heqalist.
induction alist as [|(k,v)]. { easy. }
cbn in Found.
destruct string_dec.
{
  inversion Found. subst v. clear Found.
  cbn in EnoughForEverything.
  now apply N.max_lub_lt_iff in EnoughForEverything.
}
apply (IHalist Found).
cbn in EnoughForEverything.
now apply N.max_lub_lt_iff in EnoughForEverything.
Qed.