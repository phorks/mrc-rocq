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

Unset Elimination Schemes.
Inductive formula : Type :=
  | F_Simple (sf : simple_formula)
  | F_Not (f : formula)
  | F_And (f1 f2 : formula)
  | F_Or (f1 f2 : formula)
  | F_Implies (f1 f2 : formula)
  | F_Iff (f1 f2 : formula)
  | F_Exists (x : string) (f : formula)  
  | F_Forall (x : string) (f : formula).
Set Elimination Schemes.
Scheme formula_ind_naive := Induction for formula Sort Type.

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
      | 0 => F_Exists y f
      | S qrank => F_Exists y' 
          (subst_formula_qrank qrank (subst_aux f y (T_Var y')) x a)
      end
    | F_Forall y f => if (y =? x)%string 
      then F_Forall y f
      else let y' := fresh_quantifier y f a in
      match qrank with
      | 0 => F_Forall y f
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
      forall B, rank B = m -> P B) ->
    (forall A, rank A = n -> P A)) -> 
  forall n A, rank A < n -> P A.
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
  intros. induction A using formula_ind_naive; simpl; auto; apply Bool.andb_true_iff...
Qed.

Theorem fstruct_same_sym : forall A B,
  fstruct_same A B = true ->
  fstruct_same B A = true.
Proof with auto.
  induction A using formula_ind_naive; destruct B; try discriminate; simpl; auto;
  try repeat rewrite Bool.andb_true_iff; intros [H1 H2]...
Qed.

Theorem fstruct_same_trans : forall A B C,
  fstruct_same A B = true ->
  fstruct_same B C = true ->
  fstruct_same A C = true.
Proof with auto.
  induction A using formula_ind_naive; intros B C HAB HBC; destruct B; try discriminate;
    destruct C; try discriminate; simpl; 
    try solve [inversion HAB; inversion HBC;
      apply Bool.andb_true_iff in H0 as [H2 H3];
      apply Bool.andb_true_iff in H1 as [H0 H1];
      rewrite IHA1 with B1 C1; auto;
      rewrite IHA2 with B2 C2; auto];
    try solve [apply IHA with B; auto]...
Qed.

Theorem ranks_equal_if_fstruct_same : forall A B,
  fstruct_same A B = true ->
    formula_rank A = formula_rank B /\
    quantifier_rank A = quantifier_rank B.
Proof with auto.
  assert (Hfr: forall A B, fstruct_same A B = true ->
    formula_rank A = formula_rank B). {
    intros A; induction A using formula_ind_naive; destruct B; try discriminate; 
    intros H; simpl; auto;
    try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2]; 
      auto). }
    assert (Hqr: forall A B, fstruct_same A B = true ->
      quantifier_rank A = quantifier_rank B). {
    intros A. induction A using formula_ind_naive; destruct B; try discriminate; 
    intros H; simpl; auto;
    try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2]; 
      auto).
  }
  auto.
Qed.

Ltac deduce_rank_eq Hsame := 
  let Htemp := fresh in
  let Hfr := fresh "Hfr" in
  let Hqr := fresh "Hqr" in
  apply ranks_equal_if_fstruct_same in Hsame as Htemp;
  destruct Htemp as [Hfr Hqr].

Hint Extern 2 (fstruct_same ?A ?A = true) =>
  apply fstruct_same_refl : core.

Theorem subst_preserves_structure : forall A x a r,
  fstruct_same A (subst_formula_qrank r A x a) = true.
Proof with auto.
  intros A.
  apply (rank_induction (fun P => forall x a r,
      fstruct_same P (subst_formula_qrank r P x a) = true))
    with (S (rank A))...
  clear A. intros n IH. destruct A;
    intros Hr x a r.
  - destruct r; simpl in *...
  - specialize IH with (m:=rank A) (B:=A).
    destruct r; simpl in *...
    + fold_qrank_subst 0 A x a. apply IH; try lia...
    + fold_qrank_subst (S r) A x a. apply IH; try lia...
  - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1.
    specialize IH with (m:=rank A2) (B:=A2) as IH2.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a. 
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a.
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
  - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1.
    specialize IH with (m:=rank A2) (B:=A2) as IH2.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a. 
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a.
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
  - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1.
    specialize IH with (m:=rank A2) (B:=A2) as IH2.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a. 
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a.
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
  - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1.
    specialize IH with (m:=rank A2) (B:=A2) as IH2.
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a. 
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) A2 x a.
        fold_qrank_subst (S r) A1 x a.
        apply Bool.andb_true_iff. split; 
          [apply IH1|apply IH2]; lia...                              
  - subst. destruct r; simpl in *.
    + destruct (eqb_spec x0 x)...
    + fold_qrank_subst (S r) A x0 (fresh_quantifier x0 A a).
      destruct (eqb_spec x0 x); try lia...
      remember (subst_formula_qrank (S r) A x0 (fresh_quantifier x0 A a))
        as F1. (* the first substitution *)
      remember (subst_formula_qrank r F1 x a)
        as F2. (* the second substituion *)
      specialize IH with (m:=rank A) (B:=A) as IHA.
      specialize IH with (m:=rank F1) (B:=F1) as IHF1.
      forward IHA by lia. forward IHA by auto.      
      specialize (IHA x0 (fresh_quantifier x0 A a) (S r)). (* F1 *)
      forward IHF1. { deduce_rank_eq IHA. rewrite HeqF1. lia. }
      forward IHF1 by reflexivity. specialize (IHF1 x a r).
      rewrite <- HeqF1 in *. rewrite <- HeqF2 in *.
      apply fstruct_same_trans with F1...
  - subst. destruct r; simpl in *.
    + destruct (eqb_spec x0 x)...
    + fold_qrank_subst (S r) A x0 (fresh_quantifier x0 A a).
      destruct (eqb_spec x0 x); try lia...
      remember (subst_formula_qrank (S r) A x0 (fresh_quantifier x0 A a))
        as F1. (* the first substitution *)
      remember (subst_formula_qrank r F1 x a)
        as F2. (* the second substituion *)
      specialize IH with (m:=rank A) (B:=A) as IHA.
      specialize IH with (m:=rank F1) (B:=F1) as IHF1.
      forward IHA by lia. forward IHA by auto.      
      specialize (IHA x0 (fresh_quantifier x0 A a) (S r)). (* F1 *)
      forward IHF1. { deduce_rank_eq IHA. rewrite HeqF1. lia. }
      forward IHF1 by reflexivity. specialize (IHF1 x a r).
      rewrite <- HeqF1 in *. rewrite <- HeqF2 in *.
      apply fstruct_same_trans with F1...
Qed.

Theorem formula_ind : forall P,
  (forall sf, P (F_Simple sf)) ->
  (forall f, P f -> P <[ ~ f ]>) ->
  (forall f1 f2, P f1 -> P f2 -> P <[ f1 /\ f2 ]>) ->
  (forall f1 f2, P f1 -> P f2 -> P <[ f1 \/ f2 ]>) ->
  (forall f1 f2, P f1 -> P f2 -> P <[ f1 => f2 ]>) ->
  (forall f1 f2, P f1 -> P f2 -> P <[ f1 <=> f2 ]>) ->
  (forall x f, (forall v, P (f[x \ v])) -> P <[ exists x, f ]>) ->
  (forall x f, (forall v, P (f[x \ v])) -> P <[ forall x, f ]>) ->
  forall A, P A.
Proof with auto.
  intros P Hsf Hnot Hand Hor Himpl Hiff Hsome Hall A.
  apply rank_induction with (formula_rank A + quantifier_rank A + 1).
  - clear A. intros n IH. destruct A; intros Hrank.
    + apply Hsf.
    + simpl in *. assert (PA: P A). {
      apply IH with (formula_rank A + quantifier_rank A)...
      lia. }
      apply Hnot. assumption.
    + simpl in *. assert (PA1: P A1). { 
      apply IH with (formula_rank A1 + quantifier_rank A1)...
      lia. } assert (PA2: P A2). { 
      apply IH with (formula_rank A2 + quantifier_rank A2)...
      lia. } auto.
    + simpl in *. assert (PA1: P A1). { 
      apply IH with (formula_rank A1 + quantifier_rank A1)...
      lia. } assert (PA2: P A2). { 
      apply IH with (formula_rank A2 + quantifier_rank A2)...
      lia. } auto.
    + simpl in *. assert (PA1: P A1). { 
      apply IH with (formula_rank A1 + quantifier_rank A1)...
      lia. } assert (PA2: P A2). { 
      apply IH with (formula_rank A2 + quantifier_rank A2)...
      lia. } auto.
    + simpl in *. assert (PA1: P A1). { 
      apply IH with (formula_rank A1 + quantifier_rank A1)...
      lia. } assert (PA2: P A2). { 
      apply IH with (formula_rank A2 + quantifier_rank A2)...
      lia. } auto.
    + simpl in *. assert (PA: forall v, P (A[x0 \ v])). {
      intros v.
      apply IH with (rank (A[x0 \ v]))...
      assert (fstruct_same A <[ A [x0 \ v] ]> = true). {
        apply subst_preserves_structure. }
      deduce_rank_eq H.
      lia. } apply Hsome...
    + simpl in *. assert (PA: forall v, P (A[x0 \ v])). {
      intros v.
      apply IH with (rank (A[x0 \ v]))...
      assert (fstruct_same A <[ A [x0 \ v] ]> = true). {
        apply subst_preserves_structure. }
      deduce_rank_eq H.
      lia. } apply Hall...
  - lia.
Qed.

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