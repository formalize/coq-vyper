From Coq Require Import List String NArith ZArith DecimalString HexString.

From Vyper Require Import Config FSet.
From Vyper Require L10.Base.

(* The exprs are back! *)
Inductive expr {C: VyperConfig}
:= Const (val: uint256)
 | LocalVar (index: N)
 | LoopOffset (deBruijnIndex: N)
 | LoopCursor (deBruijnIndex: N)
 | PrivateCall (name: string) (args: list expr)
 | BuiltinCall (name: string) (args: list expr).

Fixpoint expr_ind' {C: VyperConfig}
                   (P: expr -> Prop)
                   (HConst: forall val, P (Const val))
                   (HLocalVar: forall name, P (LocalVar name))
                   (HLoopStart: forall index, P (LoopOffset index))
                   (HLoopCursor: forall index, P (LoopCursor index))
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
      | LoopOffset index => HLoopStart index
      | LoopCursor index => HLoopCursor index
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