From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From MRC Require Import PredCalc.
From MRC Require Import Tactics.

Open Scope general_fassertion_scope.

Theorem feval_inversion_and : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> true ->
  feval st fctx pctx A true /\ feval st fctx pctx B true.
Proof.
  intros st fctx pctx A B H. inversion H; subst.
  apply Bool.andb_true_iff in H2 as [H1 H2]; subst.
  simpl. split; assumption.
Qed.

Theorem feval_inversion_and_false : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> false ->
  feval st fctx pctx A false \/ feval st fctx pctx B false.
Proof.
  intros st fctx pctx A B H. inversion H; subst.
  apply Bool.andb_false_iff in H2 as [H1 | H1]; subst.
  - simpl. left. assumption.
  - rewrite Bool.andb_comm. simpl. right. assumption.
Qed.

Theorem feval_inversion_or : forall st fctx pctx A B,
  feval st fctx pctx <[ A \/ B ]> true ->
  feval st fctx pctx A true \/ feval st fctx pctx B true.
Proof.
  intros st fctx pctx A B H. 
  inversion H; subst; [left | right]; assumption.
Qed.

Theorem feval_inversion_or_false : forall st fctx pctx A B,
  feval st fctx pctx <[ A \/ B ]> false ->
  feval st fctx pctx A false /\ feval st fctx pctx B false.
Proof.
  intros st fctx pctx A B H.
  inversion H; subst. split; assumption.
Qed.

Theorem feval_inversion_not : forall st fctx pctx A,
  feval st fctx pctx <[ ~ A ]> true ->
  feval st fctx pctx <[ A ]> false.
Proof.
  intros st fctx pctx A H. 
  inversion H; subst. apply Bool.negb_true_iff in H1. 
  subst. assumption.
Qed.

Theorem feval_inversion_not_false : forall st fctx pctx A,
  feval st fctx pctx <[ ~ A ]> false ->
  feval st fctx pctx <[ A ]> true.
Proof.
  intros st fctx pctx A H. 
  inversion H; subst. apply Bool.negb_false_iff in H1. 
  subst. assumption.
Qed.

Theorem feval_inversion_implication : forall st fctx pctx A B,
  feval st fctx pctx <[ A => B ]> true ->
    feval st fctx pctx <[ A ]> false \/ 
    feval st fctx pctx <[ B ]> true.
Proof.
  intros st fctx pctx A B H. inversion H; subst.
  - left. assumption.
  - right. assumption.
Qed.

Theorem feval_inversion_implication_false : forall st fctx pctx A B,
  feval st fctx pctx <[ A => B ]> false ->
    feval st fctx pctx <[ A ]> true /\
    feval st fctx pctx <[ B ]> false.
Proof.
  intros st fctx pctx A B H. inversion H; subst. split; assumption.
Qed.

Theorem feval_inversion_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A <=> B ]> true ->
    (feval st fctx pctx <[ A ]> true /\ 
      feval st fctx pctx <[ B ]> true) \/
    (feval st fctx pctx <[ A ]> false /\ 
      feval st fctx pctx <[ B ]> false).
Proof with auto.
  intros st fctx pctx A B H. inversion H; subst.
  destruct f1val, f2val...
  - simpl in H2. discriminate H2.
  - simpl in H2. discriminate.
Qed.

Theorem feval_inversion_iff_false : forall st fctx pctx A B,
  feval st fctx pctx <[ A <=> B ]> false ->
    (feval st fctx pctx <[ A ]> true /\ 
      feval st fctx pctx <[ B ]> false) \/
    (feval st fctx pctx <[ A ]> false /\ 
      feval st fctx pctx <[ B ]> true).
Proof with auto.
  intros st fctx pctx A B H. inversion H; subst.
  destruct f1val, f2val... simpl in H2. discriminate H2.
Qed.

Theorem feval_inversion_false : forall st fctx pctx,
  ~ feval st fctx pctx <[ false ]> true.
Proof.
  intros st fctx pctx contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_inversion_true_false : forall st fctx pctx,
  ~ feval st fctx pctx <[ true ]> false.
Proof.
  intros st fctx pctx contra. inversion contra; subst. inversion H0.
Qed.

Theorem and_true_if : forall st fctx pctx A B,
  feval st fctx pctx A true ->
  feval st fctx pctx B true ->
  feval st fctx pctx <[ A /\ B ]> true.
Proof.
  intros st fctx pctx A B H1 H2. 
  replace true with (andb true true) by auto.
  apply FEval_And; assumption.
Qed.

Theorem not_true_if : forall st fctx pctx A,
  feval st fctx pctx <[ A ]> false -> 
  feval st fctx pctx <[ ~ A ]> true.
Proof.
  intros st fctx pctx A H. 
  replace true with (negb false) by reflexivity.
  apply FEval_Not. assumption.
Qed.

Theorem true_is_true : forall st fctx pctx,
  feval st fctx pctx <[ true ]> true.
Proof.
  intros st fctx pctx. apply FEval_Simple. apply SFEval_True.
Qed.

Theorem false_is_false : forall st fctx pctx,
  feval st fctx pctx <[ false ]> false.
Proof.
  intros st fctx pctx. apply FEval_Simple. apply SFEval_False.
Qed.

Hint Resolve true_is_true : core.
Hint Resolve false_is_false : core.
Hint Resolve feval_inversion_and : core.
Hint Extern 2 (feval _ _ _ (<[ _ /\ _ ]>) true) =>
  apply and_true_if; auto : core.

Hint Extern 4 (feval _ _ _ (<[ _ \/ _ ]>) true) =>
  try solve [apply FEval_Or1; auto]; 
  try solve [apply FEval_Or2; auto] : core.

Theorem equiv_refl : forall A, A == A.
Proof.
  intros A fctx pctx. split; intros val st H; destruct val; auto.
Qed.

Theorem and_comm : forall A B,
  <[ A /\ B ]> == <[ B /\ A ]>.
Proof with auto. 
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_and in H as [H1 H2]...
  - destruct val... right. 
    apply feval_inversion_and in H as [H1 H2]...
Qed.

Theorem or_comm : forall A B,
  <[ A \/ B ]> == <[ B \/ A ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - inversion H; subst...
  - inversion H; subst...
Qed.

Theorem and_idemp : forall A,
  <[ A /\ A ]> == <[ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_and in H as [H _]. assumption.
  - destruct val...
Qed.

Theorem or_idemp : forall A,
  <[ A \/ A ]> == <[ A ]>.
Proof with auto.
  intros f fctx pctx. split; intros val st H.
  - destruct val... right. inversion H; subst...
  - destruct val...
Qed.

Theorem and_assoc : forall A B C,
  <[ A /\ (B /\ C) ]> == <[ (A /\ B) /\ C ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_and in H2 as [H2 H3]...
  - destruct val... right.
    apply feval_inversion_and in H as [H1 H3].
    apply feval_inversion_and in H1 as [H1 H2]...
Qed.

Theorem or_assoc : forall A B C,
  <[ A \/ (B \/ C) ]> == <[ (A \/ B) \/ C ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_or in H as [H | H]...
    apply feval_inversion_or in H as [H | H]...
  - destruct val... right.
    apply feval_inversion_or in H as [H | H]...
    apply feval_inversion_or in H as [H | H]...
Qed.

Theorem and_absorption : forall A B,
  <[ A /\ (A \/ B) ]> == A.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_and in H as [H1 H2]...
  - destruct val...
Qed.

Theorem or_absorption : forall A B,
  <[ A \/ (A /\ B) ]> == A.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_or in H as [H | H]...
    apply feval_inversion_and in H as [H1 H2]...
  - destruct val...
Qed.

Theorem and_or_distr : forall A B C,
  <[ A /\ (B \/ C) ]> == <[ (A /\ B) \/ (A /\ C) ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_or in H2 as [H2 | H2]...
  - destruct val... right.
    apply feval_inversion_or in H as [H | H];
    apply feval_inversion_and in H as [H1 H2]...
Qed.

Theorem or_and_distr : forall A B C,
  <[ A \/ (B /\ C) ]> == <[ (A \/ B) /\ (A \/ C) ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_or in H as [H | H];
    [| apply feval_inversion_and in H as [H1 H2]]...
  - destruct val... right. 
    apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_or in H1 as [H1 | H1];
    apply feval_inversion_or in H2 as [H2 | H2]...
Qed.

Theorem and_true : forall A,
  <[ A /\ true ]> == A.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_and in H as [H1 H2]...
  - destruct val...
Qed.

Theorem or_true : forall A,
  <[ A \/ true ]> == <[ true ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val...
Qed.

Theorem and_false : forall A,
  <[ A /\ false ]> == <[ false ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right.
    apply feval_inversion_and in H as [H1 H2]...
  - destruct val... apply feval_inversion_false in H.
    destruct H.
Qed.

Theorem or_false : forall A,
  <[ A \/ false ]> == <[ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_or in H as [H | H]...
    apply feval_inversion_false in H. destruct H. 
  - destruct val...
Qed.

Theorem not_true : <[ ~ true ]> == <[ false ]>.
Proof with auto.
  intros fctx pctx. split; intros val st H.
  - destruct val... right. apply feval_inversion_not in H.
    apply feval_inversion_true_false in H. destruct H.
  - destruct val... right. apply feval_inversion_false in H.
    destruct H.
Qed. 

Theorem not_false : <[ ~ false ]> == <[ true ]>.
Proof with auto.
  intros fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val... right. apply not_true_if...
Qed.

Theorem A_and_not_A : forall A,
  <[ A /\ ~ A ]> == <[ false ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... exfalso.
    apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_not in H2.
    induction A.
    + induction sf.
      * apply feval_inversion_true_false in H2. destruct H2.
      * apply feval_inversion_false in H1. destruct H1.
      * inversion H1; subst; clear H1. inversion H0; subst; clear H0.
        inversion H2; subst; clear H2. inversion H0; subst; clear H0.
        inversion H5; subst; clear H5. inversion H6; subst; clear H6.
        rewrite H2 in H3. inversion H3; subst. clear H2. clear H3.
        apply (Hfnal _ _ _ _ false) in H0... discriminate H0.
    + apply feval_inversion_not in H1. 
      apply feval_inversion_not_false in H2.
      apply IHA; assumption.
    + apply feval_inversion_and in H1 as [H0 H1].
      apply feval_inversion_and_false in H2 as [H2 | H2]...
    + apply feval_inversion_or_false in H2 as [H2 H3].
      apply feval_inversion_or in H1 as [H1 | H1]...
    + apply feval_inversion_implication_false in H2 as [H2 H3].
      apply feval_inversion_implication in H1 as [H1 | H1]...
    + apply feval_inversion_iff in H1 as [[H0 H1] | [H0 H1]];
      apply feval_inversion_iff_false in H2 as [[H2 H3] | [H2 H3]]...
    + inversion H1; subst. inversion H2; subst.
      destruct H3 as [v Hv]. specialize H4 with v.
      apply H with v...
    + inversion H1; subst. inversion H2; subst.
      destruct H4 as [v Hv]. specialize H3 with v.
      apply H with v...
  - destruct val... right. apply feval_inversion_false in H.
    destruct H.
Qed.