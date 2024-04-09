From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Reals.Reals.
From MRC Require Import Maps.
From MRC Require Import Tactics.

Open Scope bool_scope.


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

Definition func_rel := list value -> value -> Prop.

Definition functional_frel (frel : func_rel) :=
  forall args v1 v2, frel args v1 -> frel args v2 -> v1 = v2.

Inductive func_def : Type :=
  | FuncDef (n_params : nat) (frel : func_rel) 
    (Hfnal: functional_frel frel).

Definition fcontext := partial_map func_def.

Inductive term : Type :=
  | T_Const (v : value)
  | T_Var (x : string)
  | T_Func (symbol : string) (args : list term).

Definition pred_rel := state -> fcontext -> list term -> bool -> Prop.

Definition functional_prel (prel : pred_rel) :=
  forall st fctx args b1 b2,
    prel st fctx args b1 ->
    prel st fctx args b2 ->
    b1 = b2.

Inductive pred_def : Type :=
  | PredDef (n_params : nat) 
    (pred : pred_rel)
    (Hfnal : functional_prel pred).

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
Notation "f '(' x ',' .. ',' y ')'" := (T_Func f (@cons term x .. (@cons term y nil) ..)) (in custom formula at level 40).

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
Notation "x <=> y" := (F_Iff x y) (in custom formula at level 80, only parsing).
Notation "x ⇔ y" := (F_Iff x y) (in custom formula at level 80, only printing).
Notation "'exists' x .. y ',' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only parsing).
Notation "'∃' x .. y '●' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only printing).
Notation "'forall' x .. y ',' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).
Notation "'∀' x .. y '●' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).

Open Scope formula_scope.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Definition f : string := "f".

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

Declare Scope formula_props.
Open Scope formula_props.

Notation "'rank' A" := (formula_rank A + quantifier_rank A)
  (at level 20) : formula_props.

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
  (at level 10, left associativity,
   x at next level) : formula_scope.

Notation "f [ x \ a ]" := (formula_subst f x a)
  (in custom formula at level 74, left associativity,
    f custom formula,
    x constr at level 0, a custom formula) : formula_scope.

Theorem simpl_subst_not : forall f x a,
  <[ (~ f)[x \ a] ]> = <[ ~ (f[x \ a]) ]>.
Proof with auto.
  intros f x a. unfold formula_subst.
  assert (H: quantifier_rank <[ ~f ]> = quantifier_rank f).
  { reflexivity. } rewrite H. clear H. destruct (quantifier_rank f);
    reflexivity.
Qed.

Ltac fold_qrank_subst n f x a := 
  let R := fresh in
  let H := fresh in
  let H' := fresh in
  remember (subst_formula_qrank n f x a) as R eqn:H;
  assert (H' := H); simpl in H'; rewrite H in H'; rewrite <- H' in *;
  clear H'; clear H; clear R.

Theorem strong :
  (forall m, 
    (forall n B, n < m -> rank B = n ->
      forall r' x a, quantifier_rank B <= r' ->
                      subst_formula_qrank r' B x a =
                      subst_formula_qrank (quantifier_rank B) B x a)
    -> forall A r' x a, rank A = m ->
                    quantifier_rank A <= r' ->
                      subst_formula_qrank r' A x a =
                      subst_formula_qrank (quantifier_rank A) A x a) ->
  forall m A r' x a, rank A < m ->
    quantifier_rank A <= r' ->
      subst_formula_qrank r' A x a =
      subst_formula_qrank (quantifier_rank A) A x a.
Proof with auto.
  intros IH m. induction m; intros A r' x a Hrm Hr'.
  - lia.
  - apply IH with (rank A)... intros n B H Hn r'' x' a' Hr''. subst. 
    apply IHm; lia.
Qed.

Theorem xxx_rank0 : forall A r x a,  
  quantifier_rank A = 0 ->
  subst_formula_qrank r A x a = subst_formula_qrank 0 A x a.
Proof with auto.
  induction A; intros r x a H.
  - destruct r; simpl...
  - destruct r; simpl... fold_qrank_subst 0 A x a.
    fold_qrank_subst (S r) A x a. simpl in H. f_equal...
  - destruct r; simpl... fold_qrank_subst 0 A2 x a.
    fold_qrank_subst 0 A1 x a. fold_qrank_subst (S r) A2 x a.
    fold_qrank_subst (S r) A1 x a. simpl in H.
    assert (HMax := (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + lia.
    + rewrite H2 in *. assert (quantifier_rank A2 = 0) by lia.
      rewrite H0 in *. rewrite H in *. f_equal...
  - destruct r; simpl... fold_qrank_subst 0 A2 x a.
    fold_qrank_subst 0 A1 x a. fold_qrank_subst (S r) A2 x a.
    fold_qrank_subst (S r) A1 x a. simpl in H.
    assert (HMax := (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + lia.
    + rewrite H2 in *. assert (quantifier_rank A2 = 0) by lia.
      rewrite H0 in *. rewrite H in *. f_equal...
  - destruct r; simpl... fold_qrank_subst 0 A2 x a.
    fold_qrank_subst 0 A1 x a. fold_qrank_subst (S r) A2 x a.
    fold_qrank_subst (S r) A1 x a. simpl in H.
    assert (HMax := (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + lia.
    + rewrite H2 in *. assert (quantifier_rank A2 = 0) by lia.
      rewrite H0 in *. rewrite H in *. f_equal...
  - destruct r; simpl... fold_qrank_subst 0 A2 x a.
    fold_qrank_subst 0 A1 x a. fold_qrank_subst (S r) A2 x a.
    fold_qrank_subst (S r) A1 x a. simpl in H.
    assert (HMax := (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + lia.
    + rewrite H2 in *. assert (quantifier_rank A2 = 0) by lia.
      rewrite H0 in *. rewrite H in *. f_equal...
  - simpl in H. lia.
  - simpl in H. lia.
Qed.

Theorem formula_rank__gt__0 : forall A, formula_rank A > 0.
Proof.
  intros A. destruct A; simpl; lia.
Qed.

Theorem formula_rank0 : forall A,
  formula_rank A <> 0.
Proof.
  intros A. assert (formula_rank A > 0) by apply formula_rank__gt__0.
  lia.
Qed.

Hint Resolve formula_rank0 : core.

Hint Extern 2 =>
  match goal with [H : formula_rank _ = 0 |- _] =>
    apply formula_rank0 in H; destruct H end : core.

Hint Extern 2 =>
  match goal with [H : 0 = formula_rank _ |- _] =>
    apply eq_sym in H; apply formula_rank0 in H;
    destruct H end : core.

Theorem formula_rank1 : forall A,
  formula_rank A = 1 -> 
  exists sf, A = F_Simple sf.
Proof with auto.
  intros A Hr. destruct A;
    try solve [inversion Hr; auto];
    try solve [inversion Hr;
    destruct (Nat.max_spec (formula_rank A1) (formula_rank A2)) 
      as [[_ H] | [_ H]]; rewrite H0 in *; auto].
  - exists sf...
Qed.

Theorem rank_induction : forall P,
  (forall n,
    (forall m, m < n -> 
      forall B, formula_rank B + quantifier_rank B = m -> P B) ->
    (forall A, formula_rank A + quantifier_rank A = n -> P A)) -> 
  forall n A, formula_rank A + quantifier_rank A < n -> P A.
Proof with auto.
  intros P Hind n. induction n; intros A Hrank.
  - assert (formula_rank A > 0). { apply formula_rank__gt__0. }
    lia.
  - apply Hind with (formula_rank A + quantifier_rank A)...
    intros m Hlt B HB. apply IHn. lia.
Qed.

Definition is_quantifier P :=
  match P with
  | F_Exists y f1 => true
  | F_Forall y f1 => true
  | _ => false
  end.

Definition fcons_same A B :=
  match A, B with
  | F_Simple _, F_Simple _ => true
  | F_Not _, F_Not _ => true
  | F_And _ _, F_And _ _  => true
  | F_Or _ _, F_Or _ _ => true
  | F_Implies _ _, F_Implies _ _ => true
  | F_Iff _ _, F_Iff _ _ => true
  | F_Exists _ _, F_Exists _ _ => true
  | F_Forall _ _, F_Forall _ _ => true
  | _, _ => false
  end.

Fixpoint fstruct_same A B :=
  match A, B with
  | F_Simple _, F_Simple _ => true
  | F_Not A, F_Not B => fstruct_same A B
  | F_And A1 A2, F_And B1 B2 => 
    fstruct_same A1 B1 &&
    fstruct_same A2 B2
  | F_Or A1 A2, F_Or B1 B2 => 
    fstruct_same A1 B1 &&
    fstruct_same A2 B2
  | F_Implies A1 A2, F_Implies B1 B2 =>
    fstruct_same A1 B1 &&
    fstruct_same A2 B2  
  | F_Iff A1 A2, F_Iff B1 B2 =>
    fstruct_same A1 B1 &&
    fstruct_same A2 B2  
  | F_Exists _ A, F_Exists _ B =>
    fstruct_same A B
  | F_Forall _ A, F_Forall _ B =>
    fstruct_same A B
  | _, _ => false
  end.
  
Theorem fstruct_same__fcons_same : forall A B,
  fstruct_same A B = true -> 
    fcons_same A B = true.
Proof with auto.
  intros. destruct A; destruct B; try discriminate...
Qed.

Theorem fcons_same_simple : forall sf B,
  fcons_same (F_Simple sf) B = true ->
  exists sf', B = F_Simple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Theorem fstruct_same_simple : forall sf B,
  fstruct_same (F_Simple sf) B = true ->
  exists sf', B = F_Simple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Theorem fcons_same_not : forall A1 B,
  fcons_same <[ ~ A1 ]> B = true ->
  exists B1, B = <[ ~ B1 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Theorem fstruct_same_not : forall A1 B,
  fstruct_same <[ ~ A1 ]> B = true ->
  exists B1, B = <[ ~ B1 ]> /\ fstruct_same A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Theorem fcons_same_and : forall A1 A2 B,
  fcons_same <[ A1 /\ A2 ]> B = true ->
  exists B1 B2, B = <[ B1 /\ B2 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem fstruct_same_and : forall A1 A2 B,
  fstruct_same <[ A1 /\ A2 ]> B = true ->
  exists B1 B2, B = <[ B1 /\ B2 ]> /\
    fstruct_same A1 B1 = true /\
    fstruct_same A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem fcons_same_or : forall A1 A2 B,
  fcons_same <[ A1 \/ A2 ]> B = true ->
  exists B1 B2, B = <[ B1 \/ B2 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem fstruct_same_or : forall A1 A2 B,
  fstruct_same <[ A1 \/ A2 ]> B = true ->
  exists B1 B2, B = <[ B1 \/ B2 ]> /\
    fstruct_same A1 B1 = true /\
    fstruct_same A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem fcons_same_implies : forall A1 A2 B,
  fcons_same <[ A1 => A2 ]> B = true ->
  exists B1 B2, B = <[ B1 => B2 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem fstruct_same_implies : forall A1 A2 B,
  fstruct_same <[ A1 => A2 ]> B = true ->
  exists B1 B2, B = <[ B1 => B2 ]> /\
    fstruct_same A1 B1 = true /\
    fstruct_same A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem fcons_same_iff : forall A1 A2 B,
  fcons_same <[ A1 <=> A2 ]> B = true ->
  exists B1 B2, B = <[ B1 <=> B2 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem fstruct_same_iff : forall A1 A2 B,
  fstruct_same <[ A1 <=> A2 ]> B = true ->
  exists B1 B2, B = <[ B1 <=> B2 ]> /\
    fstruct_same A1 B1 = true /\
    fstruct_same A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem fcons_same_exists : forall x A1 B,
  fcons_same <[ exists x, A1 ]> B = true ->
  exists y B1, B = <[ exists y, B1 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x1, B...
Qed.

Theorem fstruct_same_exists : forall x A1 B,
  fstruct_same <[ exists x, A1 ]> B = true ->
  exists y B1, B = <[ exists y, B1 ]> /\ fstruct_same A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x1, B...
Qed.

Theorem fcons_same_forall : forall x A1 B,
  fcons_same <[ forall x, A1 ]> B = true ->
  exists y B1, B = <[ forall y, B1 ]>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x1, B...
Qed.

Theorem fstruct_same_forall : forall x A1 B,
  fstruct_same <[ forall x, A1 ]> B = true ->
  exists y B1, B = <[ forall y, B1 ]> /\ fstruct_same A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x1, B...
Qed.

Theorem fstruct_same_refl : forall A,
  fstruct_same A A = true.
Proof with auto.
  intros. induction A; simpl; auto; apply Bool.andb_true_iff...
Qed.

Definition rank_preservation A := forall B x a r,
  formula_rank A = formula_rank B /\ 
  quantifier_rank A = quantifier_rank B /\
  fstruct_same A B = true /\
  (quantifier_rank A > 0 \/ is_quantifier A = false) ->
  (quantifier_rank (subst_formula_qrank r B x a) > 0 \/ is_quantifier (subst_formula_qrank r B x a) = false) /\
  fstruct_same A (subst_formula_qrank r B x a) = true /\
  formula_rank A = formula_rank (subst_formula_qrank r B x a) /\
  quantifier_rank A = quantifier_rank (subst_formula_qrank r B x a).


Theorem final : forall A, rank_preservation A.
Proof with auto.
  intros A.
  apply (rank_induction rank_preservation) with (S (rank A))...
  clear A. intros n IH. destruct A; 
    intros Hr B x a r [Hab1 [Hab2 [Hsame Hq0]]].
  - apply fstruct_same_simple in Hsame as [sf' HB]. rewrite HB.
    destruct r; simpl in *...
  - apply fstruct_same_not in Hsame as [B' [HB1 HB2]]; subst.
    specialize IH with (rank B') B'.
    destruct r; simpl in *...
    + fold_qrank_subst 0 B' x a.
      forward IH; try lia. forward IH...
      rewrite Hab2. inversion Hab1. rewrite H0. 
      destruct (IH B' x a 0) as [H1 [H2 [H3 H4]]]...
      * split... split... split... apply fstruct_same_refl.

    + fold_qrank_subst (S r) A x a. repeat forward IH by lia; auto.
      destruct (IH x a (S r)) as [H1 H2]...
  - specialize IH with (rank A1) A1 as IH1.
    specialize IH with (rank A2) A2 as IH2.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        repeat forward IH1 by lia; auto.
        repeat forward IH2 by lia; auto.
        destruct (IH1 x a 0) as [H11 H12].
        rewrite <- H11. rewrite <- H12.
        destruct (IH2 x a 0) as [H21 H22].
        rewrite <- H21. rewrite <- H22. rewrite H2...
      * fold_qrank_subst (S r) A2 x a.
        fold_qrank_subst (S r) A1 x a.
        repeat forward IH1 by lia; auto.
        repeat forward IH2 by lia; auto.
        destruct (IH1 x a (S r)) as [H11 H12].
        rewrite <- H11. rewrite <- H12.
        destruct (IH2 x a (S r)) as [H21 H22].
        rewrite <- H21. rewrite <- H22. rewrite H2...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        repeat forward IH1 by lia; auto.
        repeat forward IH2 by lia; auto.
        destruct (IH1 x a 0) as [H11 H12].
        rewrite <- H11. rewrite <- H12.
        destruct (IH2 x a 0) as [H21 H22].
        rewrite <- H21. rewrite <- H22. rewrite H2...
      * fold_qrank_subst (S r) A2 x a.
        fold_qrank_subst (S r) A1 x a.
        repeat forward IH1 by lia; auto.
        repeat forward IH2 by lia; auto.
        destruct (IH1 x a (S r)) as [H11 H12].
        rewrite <- H11. rewrite <- H12.
        destruct (IH2 x a (S r)) as [H21 H22].
        rewrite <- H21. rewrite <- H22. rewrite H2...
  - admit. - admit. - admit.
  - destruct r; simpl in *.
    + admit.
    + fold_qrank_subst (S r) A x0 (fresh_quantifier x0 A a).
      destruct (eqb_spec x0 x); try lia... split.
      * unfold formula_rank. fold formula_rank. 
        simpl. f_equal. 
        fold_qrank_subst (S r) A x0 (fresh_quantifier x0 A a).

      unfold quantifier_rank.
      simpl.
      *



  
  apply rank_induction.
Theorem fff_rank0 : forall A r' x a,
  quantifier_rank A = 0 ->
  quantifier_rank (subst_formula_qrank r' A x a) = 0.
Proof with auto.
  induction A; intros r' x a Hr0.
  - destruct r'...
  - destruct r'; simpl in *.
    + fold_qrank_subst 0 A x a. apply IHA...
    + fold_qrank_subst (S r') A x a. apply IHA...
  - simpl in *.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    destruct r'; simpl in *.
    + fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
      rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      rewrite IHA1... rewrite IHA2...
    +
      rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      fold_qrank_subst (S r') A2 x a.
      fold_qrank_subst (S r') A1 x a.
      rewrite IHA1... rewrite IHA2...
  - simpl in *.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    destruct r'; simpl in *.
    + fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
      rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      rewrite IHA1... rewrite IHA2...
    + rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      fold_qrank_subst (S r') A2 x a.
      fold_qrank_subst (S r') A1 x a.
      rewrite IHA1... rewrite IHA2...
  - simpl in *.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    destruct r'; simpl in *.
    + fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
      rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      rewrite IHA1... rewrite IHA2...
    + rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      fold_qrank_subst (S r') A2 x a.
      fold_qrank_subst (S r') A1 x a.
      rewrite IHA1... rewrite IHA2...
  - simpl in *.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    destruct r'; simpl in *.
    + fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
      rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      rewrite IHA1... rewrite IHA2...
    + rewrite H2 in *. rewrite Hr0 in H1. inversion H1.
      fold_qrank_subst (S r') A2 x a.
      fold_qrank_subst (S r') A1 x a.
      rewrite IHA1... rewrite IHA2...
  - inversion Hr0.
  - inversion Hr0.
Qed.

Theorem kkk : forall A r' x a,
  quantifier_rank A <= r' ->
  1 < quantifier_rank A ->
  exists B, quantifier_rank A = S (quantifier_rank B) /\
    subst_formula_qrank r' A x a =
    subst_formula_qrank (Nat.pred r') B x a.
Proof with auto.
  induction A; intros r' x a Hr' Hr.
  - simpl in Hr. lia.
  - destruct r'; simpl in *; try lia.
    fold_qrank_subst (S r') A x a.


    destruct (IHA (S r') x a) as [B [HB1 HB2]]... simpl in *.
    fold_qrank_subst (S r') A x a.
     exists B. 
    split... simpl in *. fold_qrank_subst (S r') A x a.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct r'; simpl in *; try lia.
    fold_qrank_subst (S r') A x0 (fresh_quantifier x0 A a).
    destruct (eqb_spec x0 x).
    + exists A. split... subst. apply IHA.



Theorem fff : forall A r' x a B,
  quantifier_rank A <= r' ->
  quantifier_rank B = quantifier_rank A ->
  quantifier_rank A = quantifier_rank (subst_formula_qrank r' B x a).
Proof with auto.
  
  intros A. induction A; intros r' x a B Hr' H.
  - simpl in *. symmetry. apply fff_rank0...
  - destruct r'; simpl in *.
    + fold_qrank_subst 0 B x a. apply IHA...
    + fold_qrank_subst (S r') B x a. apply IHA...
  - simpl in *.
    assert (HMax := 
        (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]].
    + destruct r'; rewrite H2 in *; simpl in *; try lia.  
      fold_qrank_subst (S r') B x a.
      rewrite (IHA2 (S r') x a B)...
    + rewrite H2. apply IHA1; try lia.
  - simpl in *.
    assert (HMax := 
        (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]].
    + destruct r'; rewrite H2 in *; simpl in *; try lia.  
      fold_qrank_subst (S r') B x a.
      rewrite (IHA2 (S r') x a B)...
    + rewrite H2. apply IHA1; try lia.
  - simpl in *.
    assert (HMax := 
        (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]].
    + destruct r'; rewrite H2 in *; simpl in *; try lia.  
      fold_qrank_subst (S r') B x a.
      rewrite (IHA2 (S r') x a B)...
    + rewrite H2. apply IHA1; try lia.
  - simpl in *.
    assert (HMax := 
        (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]].
    + destruct r'; rewrite H2 in *; simpl in *; try lia.  
      fold_qrank_subst (S r') B x a.
      rewrite (IHA2 (S r') x a B)...
    + rewrite H2. apply IHA1; try lia.
  - simpl in *. destruct r'; simpl in *; try lia...
    fold_qrank_subst (S r') B x a. rewrite (IHA (S r') x a B).
    + 
    + lia Hr'.
    + rewrite H2. apply IHA1; try lia.
      replace (quantifier_rank (subst_formula_qrank (S r') A1 x a))
        with (quantifier_rank A1).
      replace (quantifier_rank (subst_formula_qrank (S r') A2 x a))
        with (quantifier_rank A2)...
      apply IHA1; lia.
    + destruct r'; rewrite H2 in *; simpl in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        replace (quantifier_rank (subst_formula_qrank 0 A1 x a))
          with (quantifier_rank A1).
        replace (quantifier_rank (subst_formula_qrank 0 A2 x a))
          with (quantifier_rank A2)...
        apply IHA2; lia.
        apply IHA1; lia.
      * fold_qrank_subst (S r') A2 x a.
        fold_qrank_subst (S r') A1 x a.
        replace (quantifier_rank (subst_formula_qrank (S r') A1 x a))
          with (quantifier_rank A1).
        replace (quantifier_rank (subst_formula_qrank (S r') A2 x a))
          with (quantifier_rank A2)...
        apply IHA2; lia.
        apply IHA1; lia.
  - admit.
  - admit.
  - admit.
  - destruct r'; simpl in *; try lia. destruct (eqb_spec x0 x)...
    unfold quantifier_rank. rewrite <- Nat.add_1_l.
    Search (?x + _ = ?x + _). apply Nat.add_cancel_l.
    fold quantifier_rank.
    fold_qrank_subst (S r') A x0 (fresh_quantifier x0 A a).
    apply IHA.
    fold_qrank_subst (S r') A x a.

        lia.
    destruct r'; simpl in *.
    + fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
      apply IHA1.
Theorem xxx : forall A r' x a,
  quantifier_rank A <= r' ->
    subst_formula_qrank r' A x a =
    subst_formula_qrank (quantifier_rank A) A x a.
Proof with auto.
  intros A r' x a. 
  apply strong with (rank A + 1); try lia. 
  clear. intros m IH A r' x a Hr Hrr'.
  destruct A.
  - destruct m; simpl; destruct r'; simpl...
  - simpl in *. subst. destruct (quantifier_rank A) eqn:E1;
     destruct r' eqn:E2; simpl...
    + fold (subst_formula_qrank 0 A x a).
      fold_qrank_subst (S n) A x a.
      f_equal. apply xxx_rank0...
    + lia.
    + fold_qrank_subst (S n0) A x a. fold_qrank_subst (S n) A x a.
      f_equal. rewrite <- E1. apply IH with (rank A); try lia.
  - simpl in *. 
    assert (HMax := (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; rewrite H2 in *.
    + clear H2. destruct (quantifier_rank A2) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      simpl in *. fold_qrank_subst (S n0) A2 x a.
      fold_qrank_subst (S n0) A1 x a. 
      fold_qrank_subst (S n) A2 x a.
      fold_qrank_subst (S n) A1 x a. f_equal.
      * replace (subst_formula_qrank (S n) A1 x a)
          with (subst_formula_qrank (quantifier_rank A1) A1 x a).
        replace (subst_formula_qrank (S n0) A1 x a)
          with (subst_formula_qrank (quantifier_rank A1) A1 x a).
        reflexivity.
        symmetry. apply IH with (rank A1); try lia.
        symmetry. apply IH with (rank A1); try lia.
      * replace (subst_formula_qrank (S n) A2 x a)
          with (subst_formula_qrank (quantifier_rank A2) A2 x a).
        replace (subst_formula_qrank (S n0) A2 x a)
          with (subst_formula_qrank (quantifier_rank A2) A2 x a).
        reflexivity.
        symmetry. apply IH with (rank A2); try lia.
        symmetry. apply IH with (rank A2); try lia.
    + clear H2. destruct (quantifier_rank A1) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      * simpl in *.  fold_qrank_subst (S n) A2 x a.
        fold_qrank_subst (S n) A1 x a. 
        fold_qrank_subst 0 A2 x a.
        fold_qrank_subst 0 A1 x a. inversion H1. rewrite H0.
        f_equal; apply xxx_rank0; assumption.
      * fold_qrank_subst (S n) A2 x a.
        fold_qrank_subst (S n) A1 x a. 
        fold_qrank_subst (S n0) A2 x a.
        fold_qrank_subst (S n0) A1 x a. 
        f_equal.
        --
          replace (subst_formula_qrank (S n) A1 x a)
            with (subst_formula_qrank (quantifier_rank A1) A1 x a).
          replace (subst_formula_qrank (S n0) A1 x a)
            with (subst_formula_qrank (quantifier_rank A1) A1 x a).
          reflexivity.
          symmetry. apply IH with (rank A1); try lia.
          symmetry. apply IH with (rank A1); try lia.
        --
          replace (subst_formula_qrank (S n) A2 x a)
            with (subst_formula_qrank (quantifier_rank A2) A2 x a).
          replace (subst_formula_qrank (S n0) A2 x a)
            with (subst_formula_qrank (quantifier_rank A2) A2 x a).
          reflexivity.
          symmetry. apply IH with (rank A2); try lia.
          symmetry. apply IH with (rank A2); try lia.
  - admit.
  - admit.
  - admit.
  - simpl in *. destruct r'; try lia... simpl in *.
    fold_qrank_subst (S (quantifier_rank A)) A x0 (fresh_quantifier x0 A a).
    fold_qrank_subst (S r') A x0 (fresh_quantifier x0 A a).
    destruct (eqb_spec x0 x)... clear n. f_equal.
    assert (
      quantifier_rank 
       (subst_formula_qrank (S (quantifier_rank A)) A x0
       (fresh_quantifier x0 A a))
      = quantifier_rank A
    ).
    {
      
      admit.
      (* apply IH. *)
    }
    replace 
     (subst_formula_qrank (S r') A x0 (fresh_quantifier x0 A a))
     with (subst_formula_qrank (S (quantifier_rank A)) A x0
      (fresh_quantifier x0 A a)).
    apply IH.

Theorem xxx : forall f x a r',
  quantifier_rank f <= r' ->
  subst_formula_qrank (quantifier_rank f) f x a 
    = subst_formula_qrank r' f x a.
Proof with auto.
  intros f. induction f; intros x a r' H.
  - admit.
  - simpl in *. destruct (quantifier_rank f0) eqn:E1;
     destruct r' eqn:E2; simpl.
    + reflexivity. 
    + fold (subst_formula_qrank 0 f0 x a).
      fold_qrank_subst (S n) f0 x a. f_equal. apply IHf.
      lia.
    + lia.
    + simpl in IHf. fold_qrank_subst (S n0) f0 x a.
      fold_qrank_subst (S n) f0 x a. f_equal...
  - simpl in *. 
    assert (HMax := (Nat.max_spec (quantifier_rank f1) (quantifier_rank f2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + rewrite H2. clear H2. destruct (quantifier_rank f2) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      simpl in *. fold_qrank_subst (S n0) f2 x a.
      fold_qrank_subst (S n0) f1 x a. 
      fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. f_equal.
      * apply Nat.max_lub_iff in H as [_ H]. 
        rewrite <- (IHf1 x a (S n)); try lia.
        rewrite <- (IHf1 x a (S n0)); try lia...
      * apply Nat.max_lub_iff in H as [_ H]. apply IHf2...
    + rewrite H2. clear H2. destruct (quantifier_rank f1) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      * inversion H1. rewrite H2 in *. clear H2 H1.
      simpl in *. fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. 
      fold_qrank_subst 0 f2 x a. 
      fold_qrank_subst 0 f1 x a. f_equal...
      * fold_qrank_subst (S n0) f2 x a.
        fold_qrank_subst (S n0) f1 x a.
        fold_qrank_subst (S n) f2 x a.
        simpl in IHf1. fold_qrank_subst (S n) f1 x a.
        apply Nat.max_lub_iff in H as [H0 _]. f_equal.
        -- rewrite <- (IHf1 x a (S n0)); try lia...
        -- rewrite <- (IHf2 x a (S n))...
          rewrite <- (IHf2 x a (S n0))... try lia.
  - simpl in *. 
    assert (HMax := (Nat.max_spec (quantifier_rank f1) (quantifier_rank f2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + rewrite H2. clear H2. destruct (quantifier_rank f2) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      simpl in *. fold_qrank_subst (S n0) f2 x a.
      fold_qrank_subst (S n0) f1 x a. 
      fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. f_equal.
      * apply Nat.max_lub_iff in H as [_ H]. 
        rewrite <- (IHf1 x a (S n)); try lia.
        rewrite <- (IHf1 x a (S n0)); try lia...
      * apply Nat.max_lub_iff in H as [_ H]. apply IHf2...
    + rewrite H2. clear H2. destruct (quantifier_rank f1) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      * inversion H1. rewrite H2 in *. clear H2 H1.
      simpl in *. fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. 
      fold_qrank_subst 0 f2 x a. 
      fold_qrank_subst 0 f1 x a. f_equal...
      * fold_qrank_subst (S n0) f2 x a.
        fold_qrank_subst (S n0) f1 x a.
        fold_qrank_subst (S n) f2 x a.
        simpl in IHf1. fold_qrank_subst (S n) f1 x a.
        apply Nat.max_lub_iff in H as [H0 _]. f_equal.
        -- rewrite <- (IHf1 x a (S n0)); try lia...
        -- rewrite <- (IHf2 x a (S n))...
          rewrite <- (IHf2 x a (S n0))... try lia.
  - simpl in *. 
    assert (HMax := (Nat.max_spec (quantifier_rank f1) (quantifier_rank f2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + rewrite H2. clear H2. destruct (quantifier_rank f2) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      simpl in *. fold_qrank_subst (S n0) f2 x a.
      fold_qrank_subst (S n0) f1 x a. 
      fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. f_equal.
      * apply Nat.max_lub_iff in H as [_ H]. 
        rewrite <- (IHf1 x a (S n)); try lia.
        rewrite <- (IHf1 x a (S n0)); try lia...
      * apply Nat.max_lub_iff in H as [_ H]. apply IHf2...
    + rewrite H2. clear H2. destruct (quantifier_rank f1) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      * inversion H1. rewrite H2 in *. clear H2 H1.
      simpl in *. fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. 
      fold_qrank_subst 0 f2 x a. 
      fold_qrank_subst 0 f1 x a. f_equal...
      * fold_qrank_subst (S n0) f2 x a.
        fold_qrank_subst (S n0) f1 x a.
        fold_qrank_subst (S n) f2 x a.
        simpl in IHf1. fold_qrank_subst (S n) f1 x a.
        apply Nat.max_lub_iff in H as [H0 _]. f_equal.
        -- rewrite <- (IHf1 x a (S n0)); try lia...
        -- rewrite <- (IHf2 x a (S n))...
          rewrite <- (IHf2 x a (S n0))... try lia.
  - simpl in *. 
    assert (HMax := (Nat.max_spec (quantifier_rank f1) (quantifier_rank f2))).
    destruct HMax as [[H1 H2] | [H1 H2]].
    + rewrite H2. clear H2. destruct (quantifier_rank f2) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      simpl in *. fold_qrank_subst (S n0) f2 x a.
      fold_qrank_subst (S n0) f1 x a. 
      fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. f_equal.
      * apply Nat.max_lub_iff in H as [_ H]. 
        rewrite <- (IHf1 x a (S n)); try lia.
        rewrite <- (IHf1 x a (S n0)); try lia...
      * apply Nat.max_lub_iff in H as [_ H]. apply IHf2...
    + rewrite H2. clear H2. destruct (quantifier_rank f1) eqn:E1;
      destruct r' eqn:E2; simpl; try lia...
      * inversion H1. rewrite H2 in *. clear H2 H1.
      simpl in *. fold_qrank_subst (S n) f2 x a.
      fold_qrank_subst (S n) f1 x a. 
      fold_qrank_subst 0 f2 x a. 
      fold_qrank_subst 0 f1 x a. f_equal...
      * fold_qrank_subst (S n0) f2 x a.
        fold_qrank_subst (S n0) f1 x a.
        fold_qrank_subst (S n) f2 x a.
        simpl in IHf1. fold_qrank_subst (S n) f1 x a.
        apply Nat.max_lub_iff in H as [H0 _]. f_equal.
        -- rewrite <- (IHf1 x a (S n0)); try lia...
        -- rewrite <- (IHf2 x a (S n))...
          rewrite <- (IHf2 x a (S n0))... try lia.
  - simpl in *. destruct r' eqn:E1; try lia.
    simpl in *. destruct (eqb_spec x0 x)... f_equal. 
    fold_qrank_subst (S n) f0 x0 (fresh_quantifier x0 f0 a). 
    fold_qrank_subst (S (quantifier_rank f0)) f0 x0 (fresh_quantifier x0 f0 a).
    assert ((subst_formula_qrank (S (quantifier_rank f0)) f0 x0
    (fresh_quantifier x0 f0 a)) = 
    (subst_formula_qrank (S n) f0 x0 (fresh_quantifier x0 f0 a))).
    { rewrite <- (IHf x0 (fresh_quantifier x0 f0 a))...
      rewrite <- (IHf x0 (fresh_quantifier x0 f0 a) (S n))... lia. }
    rewrite H0. clear H0. rewrite <- (IHf x _ n); try lia.
    fold_qrank_subst n (subst_formula_qrank (S n) f0 x0 (fresh_quantifier x0 f0 a)) x a.
      
    + simpl.

  intros f x a r'. 
  generalize dependent f. induction r'; intros f H.
  - apply Nat.le_0_r in H. rewrite H. reflexivity.
  - destruct f.
    + reflexivity.
    + simpl in H. simpl.
      
     destruct (quantifier_rank f0) eqn:E.
      * simpl. specialize IHr' with f0. forward IHr' by lia.
        rewrite E in IHr'. simpl in IHr'. rewrite IHr'.
        fold_qrank_subst r' f0 x a.

      * admit.
      * simpl. reflexivity. simpl. 
  generalize dependent f. induction r.
  - intros f Hr r' H. induction f.
    + admit.
    +
  intros f qrank x a H. induction f.
  - destruct qrank...
  - simpl in H. forward IHf by assumption. destruct qrank; simpl.
    + reflexivity.
    + 

Theorem xxx : forall f qrank x a,
  quantifier_rank f = 0 ->
  subst_formula_qrank qrank f x a = subst_formula_qrank 0 f x a.
Proof with auto.
  intros f qrank x a H. induction f.
  - destruct qrank...
  - simpl in H. forward IHf by assumption. destruct qrank; simpl.
    + reflexivity.
    + 


Theorem simpl_subst_and : forall f1 f2 x a,
  <[ (f1 /\ f2)[x \ a] ]> = <[ (f1 [x \ a]) /\ (f2 [x \ a]) ]>.
Proof with auto.
  intros. unfold formula_subst. simpl.
  assert (H := (Nat.max_spec (quantifier_rank f1) (quantifier_rank f2))).
  destruct H.
  - destruct H as [H1 H2]. rewrite H2.
    destruct (quantifier_rank f2).
    + lia.
    + simpl. f_equal. destruct (quantifier_rank f1) eqn:E.
      * induction f1...
        -- 
      * simpl. reflexivity.
  destruct (Nat.ltb_spec (quantifier_rank f1) (quantifier_rank f2)).
  - rewrite Nat.max_spec.
  

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
  | Pred_Eval : forall n_args prel Hfnal pbool,
    pdef = PredDef n_args prel Hfnal ->
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
  | FEval_Implies_False : forall f1 f2,
    feval st fctx pctx f1 true ->
    feval st fctx pctx f2 false ->
    feval st fctx pctx (F_Implies f1 f2) false    
  | FEval_Iff : forall f1 f1val f2 f2val, 
    feval st fctx pctx (f1) f1val ->
    feval st fctx pctx (f2) f2val ->
    feval st fctx pctx (F_Iff f1 f2) (Bool.eqb f1val f2val)
  | FEval_Exists : forall x f, 
    (exists v, feval st fctx pctx (f[x \ v]) true) ->
    feval st fctx pctx (F_Exists x f) true
  | FEval_Exists_False : forall x f,
    (forall v, feval st fctx pctx (f[x \ v]) false) ->
    feval st fctx pctx (F_Exists x f) false
  | FEval_Forall : forall x f, 
    (forall v, feval st fctx pctx (f[x \ v]) true) ->
    feval st fctx pctx (F_Forall x f) true
  | FEval_Forall_False : forall x f,
    (exists v, feval st fctx pctx (f[x \ v]) false) ->
    feval st fctx pctx (F_Forall x f) false.

Hint Constructors feval : core.

Definition formula_implies (f1 f2 : formula) fctx pctx : Prop :=
  forall f1val st,
    feval st fctx pctx f1 f1val ->
    (f1val = false) \/ (feval st fctx pctx f2 true).

Definition formula_equiv (f1 f2 : formula) fctx pctx : Prop :=
  formula_implies f1 f2 fctx pctx /\
  formula_implies f2 f1 fctx pctx.

Declare Scope general_fassertion_scope.
Declare Custom Entry fassertion.

Notation "P '==>' Q" := (forall fctx pctx, formula_implies P Q fctx pctx)
                  (at level 50) : general_fassertion_scope.

Notation "P '==' Q" := (forall fctx pctx, 
                    (formula_implies P Q fctx pctx) /\ (formula_implies Q P fctx pctx))
                          (at level 50) : general_fassertion_scope. 