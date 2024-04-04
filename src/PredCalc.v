From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Reals.Reals.
From MRC Require Import Maps.

Inductive value : Type :=
  | V_Nat (n : nat)
  | V_Int (z : Z)
  | V_Real (r : R).

Definition state := partial_map value.

Inductive func_def : Type :=
  | FuncDef (n_params : nat) (fn : list value -> option value).

Definition fcontext := partial_map func_def.

Inductive term : Type :=
  | T_Const (v : value)
  | T_Var (x : string)
  | T_Func (symbol : string) (args : list term).

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
  | F_Forall (x : string) (f : formula)
  | F_Exists (x : string) (f : formula).

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
Notation "x <> y" := (AT_Pred "<>" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x < y" := (AT_Pred "<" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <= y" := (AT_Pred "<=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x > y" := (AT_Pred ">" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x >= y" := (AT_Pred ">=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "'~' x" := (F_Not x) (in custom formula at level 75).
Notation "x /\ y" := (F_And x y) (in custom formula at level 80, left associativity).
Notation "x \/ y" := (F_Or x y) (in custom formula at level 80, left associativity).
Notation "x => y" := (F_Implies x y) (in custom formula at level 80).
Notation "x <=> y" := (F_Implies x y) (in custom formula at level 80).
Notation "'exists' x .. y ',' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85).
Notation "'forall' x .. y ',' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).
Notation "f '(' x ',' .. ',' y ')'" := (T_Func f (@cons term x .. (@cons term y nil) ..)) (in custom formula at level 40).

Open Scope formula_scope.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Definition f : string := "f".

Locate length.

Definition fdef_eval (f : func_def) (argsv : list value) :=
  match f with
  | FuncDef n_params fn => if n_params =? List.length argsv
    then (fn argsv)
    else None
  end.

Inductive teval : state -> fcontext -> term -> value -> Prop :=
  | EvalConst : forall st fctx v, teval st fctx (T_Const v) v
  | EvalVar : forall st fctx x v, st x = Some v -> teval st fctx (T_Var x) v
  | EvalFunc : forall st fctx f fdef args argsv fval,
    args_eval st fctx args argsv ->
    fctx f = Some fdef ->
    fdef_eval fdef argsv = Some fval ->
    teval st fctx (T_Func f args) (fval)
with args_eval : state -> fcontext -> list term -> list value -> Prop :=
  | ArgsEval_nil : forall st fctx, args_eval st fctx [] []
  | ArgsEval_cons : forall st fctx t ts v vs, 
    teval st fctx t v ->
    args_eval st fctx ts vs ->
    args_eval st fctx (t::ts) (v::vs).

Definition binary_arith_fdef (on_N : nat -> nat -> nat) (on_Z : Z -> Z -> Z) (on_R : R -> R -> R) :=
  FuncDef 2 (fun args => match args with 
    | [V_Nat n1; V_Nat n2] => @Some value (on_N n1 n2)
    | [V_Int z1; V_Int z2] => @Some value (on_Z z1 z2)
    | [V_Nat n1; V_Int z2] => @Some value (on_Z (Z.of_nat n1) z2)
    | [V_Int z1; V_Nat n2] => @Some value (on_Z z1 (Z.of_nat n2))
    | [V_Real r1; V_Real r2] => @Some value (on_R r1 r2)
    | [V_Nat n1; V_Real r2] => @Some value (on_R (INR n1) r2)
    | [V_Real r1; V_Nat n2] => @Some value (on_R r1 (INR n2))
    | [V_Int z1; V_Real r2] => @Some value (on_R (IZR z1) r2)
    | [V_Real r1; V_Int z2] => @Some value (on_R r1 (IZR z2))  
    | _ => None
    end).  

Definition value_to_R (v : value) :=
  match v with
  | V_Nat n => INR n
  | V_Int z => IZR z
  | V_Real r => r
  end.

Definition plus_fdef := 
  binary_arith_fdef Nat.add Z.add Rplus.

Definition minus_fdef := 
  binary_arith_fdef Nat.sub Z.sub Rminus.

Definition mult_fdef :=
  binary_arith_fdef Nat.mul Z.mul Rmult.

Definition div_fdef := FuncDef 2 (fun args =>
  match args with
  | [v1; v2] => @Some value (Rdiv (value_to_R v1) (value_to_R v2))
  | _ => None
  end).

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