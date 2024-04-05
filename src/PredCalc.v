From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Reals.Reals.
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

Notation "x + y" := (T_Func "+" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "x - y" := (T_Func "-" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "x * y" := (T_Func "*" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
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

Definition formula_equiv (f1 f2 : formula) fctx pctx : Prop :=
  formula_implies f1 f2 fctx pctx /\
  formula_implies f2 f1 fctx pctx.

Fixpoint appears_in_term x t :=
  match t with
  | T_Const v => false
  | T_Var y => if (y =? x)%string 
    then true
    else false
  | T_Func sym args => 
    fold_right orb false (map (fun arg => appears_in_term x arg) args)
  end.

Definition appears_in_simple_formula x sf :=
  match sf with
  | AT_Pred sym args => 
    fold_right orb false (map (fun arg => appears_in_term x arg) args)
  | _ => false
  end.

Fixpoint is_free_in x f :=
  match f with
  | F_Simple sf => appears_in_simple_formula x sf
  | F_Not f1 => is_free_in x f1
  | F_And f1 f2 => (orb (is_free_in x f1) (is_free_in x f2))
  | F_Or f1 f2 => (orb (is_free_in x f1) (is_free_in x f2))
  | F_Implies f1 f2 => (orb (is_free_in x f1) (is_free_in x f2))
  | F_Iff f1 f2 => (orb (is_free_in x f1) (is_free_in x f2))
  | F_Exists y f1 => if (y =? x)%string 
    then false
    else (is_free_in x f1)
  | F_Forall y f1 => if (y =? x)%string 
    then false
    else (is_free_in x f1)
  end.

Fixpoint subst_term t x a :=
  match t with
  | T_Const v => T_Const v
  | T_Var y => if (y =? x)%string 
    then a
    else T_Var y
  | T_Func sym args => T_Func sym (map (fun arg => subst_term arg x a) args)
  end.

Definition subst_simple_formula sf x a :=
  match sf with
  | AT_Pred sym args => AT_Pred sym (map (fun arg => subst_term arg x a) args)
  | _ => sf
  end.

(* only characters from 33 to 254 (inclusive) have visual symbols *)
Definition ascii_succ ch :=
  let nch := Ascii.nat_of_ascii ch in
  let nres := if (andb (32 <=? nch) (nch <=? 253))%nat 
    then (nch + 1)%nat 
    else (33)%nat in
  Ascii.ascii_of_nat nres.

(* Fixpoint ascii_succ_n ch n :=
  match n with
  | 0 => ch
  | S n => ascii_succ (ascii_succ_n ch n)
  end.

Theorem ascii_succ_n_works : forall n i,
  0 <= i <= 222 ->
  33 <= n <= 254 ->
  ascii_succ_n (Ascii.ascii_of_nat n) i 
  = (Ascii.ascii_of_nat (((n + i - 33) mod 222) + 33)).
Proof.
  intros n i Hi Hn. induction i.
  - rewrite Nat.add_0_r. destruct n.
    + inversion Hn. inversion H.
    + destruct (())
  - simpl. destruct (Nat.eqb_spec (S i) 0).
    + clear IHi. inversion e.
    + rewrite IHi; try lia. unfold ascii_succ.
      rewrite Ascii.nat_ascii_embedding; try lia.
      assert (32 <= n + i). { lia. }
      rewrite 
  - inversion H. inversion H0.
  - inversion H as [H1 H2]; clear H. destruct (Nat.eqb_spec n 32).
    + subst. clear. destruct i.
      * simpl. reflexivity.
      * simpl.

Theorem ascii_succ_cycles : forall n,
  33 <= n <= 254 ->
  ascii_succ_n (Ascii.ascii_of_nat n) 222 = (Ascii.ascii_of_nat n).
Proof. 
  intros n H. induction n.
  - inversion H. inversion H0.
  - inversion H as [H1 H2]. clear H. destruct (Nat.eqb_spec n 32). *)

Fixpoint fresh_quantifier_n qch qf a n :=
  match n with
  | 0 => "!"%char
  | S n => 
    let qx := (String qch "") in
    if (orb (is_free_in qx qf) (appears_in_term qx a)) then
      fresh_quantifier_n (ascii_succ qch) qf a n
    else
      qch
  end.

Definition fresh_quantifier qx qf a :=
  match qx with
  | EmptyString => String (fresh_quantifier_n "a"%char qf a 222) ""
  | String qch qs => match qs with
    | EmptyString => if (appears_in_term qx a)
      then String (fresh_quantifier_n (ascii_succ qch) qf a 221) ""
      else String qch ""
    | _ => String (fresh_quantifier_n "a"%char qf a 222) ""
    end
  end.

Fixpoint formula_rank f :=
  match f with
  | F_Simple sf => 1
  | F_Not f => 1 + formula_rank f
  | F_And f1 f2 => 1 + max (formula_rank f1) (formula_rank f2)
  | F_Or f1 f2 => 1 + max (formula_rank f1) (formula_rank f2)
  | F_Implies f1 f2 => 1 + max (formula_rank f1) (formula_rank f2)
  | F_Iff f1 f2 => 1 + max (formula_rank f1) (formula_rank f2)
  | F_Exists y f => 1 + (formula_rank f)
  | F_Forall y f => 1 + (formula_rank f)
  end.  

Theorem formula_rank__ge_1 : forall f,
  formula_rank f >= 1.
Proof.
  intros f. induction f; simpl; try lia.
Qed.

Fixpoint quantifier_rank f :=
  match f with
  | F_Simple sf => 0
  | F_Not f => quantifier_rank f
  | F_And f1 f2 => max (quantifier_rank f1) (quantifier_rank f2)
  | F_Or f1 f2 => max (quantifier_rank f1) (quantifier_rank f2)
  | F_Implies f1 f2 => max (quantifier_rank f1) (quantifier_rank f2)
  | F_Iff f1 f2 => max (quantifier_rank f1) (quantifier_rank f2)
  | F_Exists y f => 1 + (quantifier_rank f)
  | F_Forall y f => 1 + (quantifier_rank f)
  end.      

Fixpoint subst_formula_qrank qrank :=
  fix subst_aux f x a :=
    match f with
    | F_Simple sf => F_Simple (subst_simple_formula sf x a)
    | F_Not f => F_Not (subst_aux f x a)
    | F_And f1 f2 => F_And 
      (subst_aux f1 x a) 
      (subst_aux f2 x a)
    | F_Or f1 f2 => F_Or 
      (subst_aux f1 x a) 
      (subst_aux f2 x a)
    | F_Implies f1 f2 => F_Implies 
      (subst_aux f1 x a) 
      (subst_aux f2 x a)
    | F_Iff f1 f2 => F_Iff 
      (subst_aux f1 x a) 
      (subst_aux f2 x a)
    | F_Exists y f => if (y =? x)%string
      then F_Exists y f
      else let y' := fresh_quantifier y f a in
      match qrank with
      | 0 => f
      | S qrank => F_Exists y' 
          (subst_formula_qrank qrank (subst_aux f y (T_Var y')) x a)
      end
    | F_Forall y f => if (y =? x)%string 
      then F_Forall y f
      else let y' := fresh_quantifier y f a in
      match qrank with
      | 0 => f
      | S qrank => F_Forall y' 
          (subst_formula_qrank qrank (subst_aux f y (T_Var y')) x a)
      end
end.

Definition formula_subst f x a :=
  subst_formula_qrank (quantifier_rank f) f x a.

Notation "f [ x \ a ]" := (formula_subst f x a)
  (at level 10, x at next level, a custom formula) : formula_scope.

(* 

Notation "P '==>' Q" := (formula_implies P Q fctx pctx)
                  (at level 80).

Notation "P == Q" := (P ==> Q /\ Q ==> P)
                          (at level 80). 
                          
*)