From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Reals.Reals. Open Scope R_scope.
From MRC Require Import Maps.


Inductive value : Type :=
  | V_Nat (n : nat)
  | V_Int (z : Z)
  | V_Real (r : R).

Definition value_to_R (v : value) :=
match v with
  | V_Nat n => INR n
  | V_Int z => IZR z
  | V_Real r => r
end.

Definition state := partial_map value.

Definition functional_frel (frel : list value -> value -> Prop) :=
  forall args v1 v2, frel args v1 -> frel args v2 -> v1 = v2.

Inductive func_def : Type :=
  | FuncDef (n_params : nat) (frel : list value -> value -> Prop) 
    (Hfnal: functional_frel frel).

Definition fcontext := partial_map func_def.

Inductive term : Type :=
  | T_Const (v : value)
  | T_Var (x : string)
  | T_Func (symbol : string) (args : list term).

Inductive pred_def : Type :=
  | PredDef (n_params : nat) (pred : state -> fcontext -> list term -> bool -> Prop).

Definition pcontext := partial_map pred_def.

Inductive simple_formula : Type :=
  | AT_True
  | AT_False
  | AT_Pred (symbol : string) (args : list term).

Inductive formula : Type :=
  | F_Simple (sf : simple_formula)
  | F_Not (f : formula)
  | F_And (f1 f2 : formula)
  | F_Or (f1 f2 : formula)
  | F_Implies (f1 f2 : formula)
  | F_Iff (f1 f2 : formula)
  | F_Exists (x : string) (f : formula)  
  | F_Forall (x : string) (f : formula).

Coercion V_Nat : nat >-> value.
Coercion V_Int : Z >-> value.
Coercion V_Real : R >-> value.

Coercion T_Const : value >-> term.
Coercion T_Var : string >-> term.
Coercion F_Simple : simple_formula >-> formula.


Declare Custom Entry formula.
Declare Scope formula_scope.
Declare Custom Entry formula_aux.
Bind Scope formula_scope with simple_formula.
Delimit Scope formula_scope with formula.


Notation "<[ e ]>" := e (e custom formula_aux) : formula_scope.
Notation "e" := e (in custom formula_aux at level 0, e custom formula) : formula_scope.

Notation "( x )" := x (in custom formula, x at level 99) : formula_scope.
Notation "'`' f x .. y '`'" := (.. (f x) .. y)
                  (in custom formula at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : formula_scope.
Notation "x" := x (in custom formula at level 0, x constr at level 0) : formula_scope.

Notation "x + y" := (T_Func "+" x y) (in custom formula at level 50, left associativity).
Notation "x - y" := (T_Func "-" x y) (in custom formula at level 50, left associativity).
Notation "x * y" := (T_Func "*" x y) (in custom formula at level 50, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'" := (AT_True) (in custom formula at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := (AT_False) (in custom formula at level 0).
Notation "x = y" := (AT_Pred "=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <> y" := (AT_Pred "<>" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity, only parsing).
Notation "x ≠ y" := (AT_Pred "<>" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity, only printing).
Notation "x < y" := (AT_Pred "<" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <= y" := (AT_Pred "<=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x > y" := (AT_Pred ">" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x >= y" := (AT_Pred ">=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "'~' x" := (F_Not x) (in custom formula at level 75, only parsing).
Notation "'¬' x" := (F_Not x) (in custom formula at level 75, only printing).
Notation "x /\ y" := (F_And x y) (in custom formula at level 80, only parsing, left associativity).
Notation "x ∧ y" := (F_And x y) (in custom formula at level 80, only printing, left associativity).
Notation "x \/ y" := (F_Or x y) (in custom formula at level 80, left associativity, only parsing).
Notation "x ∨ y" := (F_Or x y) (in custom formula at level 80, left associativity, only printing).
Notation "x => y" := (F_Implies x y) (in custom formula at level 80, only parsing).
Notation "x ⇒ y" := (F_Implies x y) (in custom formula at level 80, only printing).
Notation "x <=> y" := (F_Implies x y) (in custom formula at level 80, only parsing).
Notation "x ⇔ y" := (F_Implies x y) (in custom formula at level 80, only printing).
Notation "'exists' x .. y ',' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only parsing).
Notation "'∃' x .. y '●' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only printing).
Notation "'forall' x .. y ',' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).
Notation "'∀' x .. y '●' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).
Notation "f '(' x ',' .. ',' y ')'" := (T_Func f (@cons term x .. (@cons term y nil) ..)) (in custom formula at level 40).

Open Scope formula_scope.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Definition f : string := "f".

Inductive fdef_eval (fdef : func_def) (argsv : list value) : value -> Prop :=
  | FN_Eval : forall n_args fn Hfnal value, 
    fdef = FuncDef n_args fn Hfnal ->
    fn argsv value ->
    fdef_eval fdef argsv value.

Inductive teval (st : state) (fctx : fcontext) : term -> value -> Prop :=
  | EvalConst : forall v, teval st fctx (T_Const v) v
  | EvalVar : forall x v, st x = Some v -> teval st fctx (T_Var x) v
  | EvalFunc : forall f fdef args argsv fval,
    args_eval st fctx args argsv ->
    fctx f = Some fdef ->
    fdef_eval fdef argsv fval ->
    teval st fctx (T_Func f args) (fval)
with args_eval (st : state) (fctx : fcontext) : list term -> list value -> Prop :=
  | ArgsEval_nil : args_eval st fctx [] []
  | ArgsEval_cons : forall t ts v vs, 
    teval st fctx t v ->
    args_eval st fctx ts vs ->
    args_eval st fctx (t::ts) (v::vs).


Inductive eq_prel (st : state) (pctx : fcontext) : list term -> bool -> Prop :=
  | EQValue_True : forall t1 v1 t2 v2, 
    teval st pctx t1 v1 ->
    teval st pctx t2 v2 ->
    v1 = v2 ->
    eq_prel st pctx [T_Const v1; T_Const v2] true
  | EQValue_False : forall t1 v1 t2 v2, 
      teval st pctx t1 v1 ->
      teval st pctx t2 v2 ->
      v1 <> v2 ->
      eq_prel st pctx [T_Const v1; T_Const v2] true
  | EQ_FuncSym : forall f args1 argsv1 args2 argsv2,
    args_eval st pctx args1 argsv1 ->
    args_eval st pctx args2 argsv2 ->
    eq_prel st pctx [(T_Func f args1); (T_Func f args2)] true.

Inductive pdef_eval (st : state) (fctx : fcontext) (pdef : pred_def) (args : list term) : bool -> Prop :=
  | Pred_Eval : forall n_args prel pbool,
    pdef = PredDef n_args prel ->
    prel st fctx args pbool ->
    pdef_eval st fctx pdef args pbool.

Inductive sfeval (st : state) (fctx : fcontext) (pctx : pcontext) : simple_formula -> bool -> Prop :=
  | SFEval_True : sfeval st fctx pctx AT_True true
  | SFEval_False : sfeval st fctx pctx AT_False false
  | SFEval_Pred : forall f args pdef peval, 
    pctx f = Some pdef -> 
    pdef_eval st fctx pdef args peval ->
    sfeval st fctx pctx (AT_Pred f args) peval.

Inductive feval (st : state) (fctx : fcontext) (pctx : pcontext) : formula -> bool -> Prop :=
  | FEval_Simple : forall sf sfval, 
    sfeval st fctx pctx sf sfval ->
    feval st fctx pctx (F_Simple sf) sfval
  | FEval_Not : forall f fval, 
    feval st fctx pctx f fval ->
    feval st fctx pctx (F_Not f) (negb fval)
  | FEval_And : forall f1 f1val f2 f2val, 
    feval st fctx pctx (f1) f1val ->
    feval st fctx pctx (f2) f2val ->
    feval st fctx pctx (F_And f1 f2) (andb f1val f2val)
  | FEval_Or1 : forall f1 f2, 
    feval st fctx pctx (f1) true ->
    feval st fctx pctx (F_Or f1 f2) true
  | FEval_Or2 : forall f1 f2, 
    feval st fctx pctx (f2) true ->
    feval st fctx pctx (F_Or f1 f2) true
  | FEval_Or_False : forall f1 f2, 
    feval st fctx pctx (f1) false ->
    feval st fctx pctx (f2) false ->
    feval st fctx pctx (F_Or f1 f2) false
  | FEval_Implies1 : forall f1 f2,
    feval st fctx pctx f1 false ->
    feval st fctx pctx (F_Implies f1 f2) true
  | FEval_Implies2 : forall f1 f2,
    feval st fctx pctx f2 true ->
    feval st fctx pctx (F_Implies f1 f2) true
  | FEval_Iff : forall f1 f1val f2 f2val, 
    feval st fctx pctx (f1) f1val ->
    feval st fctx pctx (f2) f2val ->
    feval st fctx pctx (F_Iff f1 f2) (Bool.eqb f1val f2val)
  | FEval_Exists : forall x f, 
    (exists v, feval (x !-> v ; st) fctx pctx (f) true) ->
    feval st fctx pctx (F_Exists x f)  true
  | FEval_Forall : forall x f, 
    (forall v, feval (x !-> v ; st) fctx pctx (f) true) ->
    feval st fctx pctx (F_Forall x f) true.

Definition formula_implies (f1 f2 : formula) fctx pctx : Prop :=
  forall f1val st,
    feval st fctx pctx f1 f1val ->
    (f1val = false) \/ (feval st fctx pctx f2 true).

(* 

Notation "P '==>' Q" := (formula_implies P Q fctx pctx)
                  (at level 80).

Notation "P == Q" := (P ==> Q /\ Q ==> P)
                          (at level 80). 
                          
*)

(* term_equals *)
(* formula_implies *)
(* formula_equiv *)

Definition simple_formula_prop (sf : simple_formula) :=
  match sf with
  | AT_True => True
  | AT_False => False
  | AT_Pred => 

Definition formula_prop (f : formula) :=
  match f with
  | 

Axiom law1_1