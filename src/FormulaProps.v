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

Theorem formula_rank__gt__0 : forall A, formula_rank A > 0.
Proof.
  intros A. destruct A; simpl; lia.
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

Theorem subst_preserves_rank : forall A x y,
  formula_rank (A[x \ y]) = formula_rank A.
Proof with auto.
  assert (strong: forall x y, 
    (forall n, 
      (forall m, m < n -> 
        forall B, formula_rank B = m -> 
          formula_rank (B [x \ y]) = formula_rank B) ->
      forall A, formula_rank A = n ->
        formula_rank (A [x \ y]) = formula_rank A) ->
    (forall n A, formula_rank A < n ->
      formula_rank (A [x \ y]) = formula_rank A)).
  {
    intros x y Hind n. induction n; intros A Hrank.
    - assert (formula_rank A > 0). { apply formula_rank__gt__0. }
      lia.
    - apply Hind with (formula_rank A)... intros m Hlt B HrankB.
      apply IHn. lia.
  }
  intros A x y.
  apply strong with (formula_rank A + 1); try lia.
  clear A. intros n m B IH. destruct B...
  - simpl. unfold formula_subst. unfold subst_formula_qrank.
    
  
  intros A x y. remember (formula_rank A) as rank.
  generalize dependent A. induction rank; intros A Hrank.
  - admit.
  - destruct A

Theorem xxx : forall P,
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
  intros P Hsf Hnot Hand Hor Himpl Hiff Hex Hall A.
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
    + simpl in *. assert (PA: forall v, P (A[x \ v])). {
      intros v.
      apply IH with (formula_rank (A[x \ v]) + quantifier_rank (A[x \ v]))...
      lia. } auto.
    + simpl in *. assert (PA: P A). {
      apply IH with (formula_rank A + quantifier_rank A)...
      lia. } auto.
  - lia.
Qed.

Theorem A_and_not_A : forall A,
  <[ A /\ ~ A ]> == <[ false ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... exfalso. 
    apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_not in H2 as H2.
    generalize dependent H2. generalize dependent H1.
    apply (xxx (
      fun f => feval st fctx pctx f true 
        -> feval st fctx pctx f false 
        -> False)).
    + intros sf H1 H2. induction sf. 
      * apply feval_inversion_true_false in H2. destruct H2.
      * apply feval_inversion_false in H1. destruct H1.
      * inversion H1; subst; clear H1. inversion H0; subst; clear H0.
        inversion H2; subst; clear H2. inversion H0; subst; clear H0.
        inversion H5; subst; clear H5. inversion H6; subst; clear H6.
        rewrite H2 in H3. inversion H3; subst. clear H2. clear H3.
        apply (Hfnal _ _ _ _ false) in H0... discriminate H0.
    + intros f IH H1 H2. 
      apply feval_inversion_not in H1. 
      apply feval_inversion_not_false in H2.
      apply IH; assumption.
    + intros f1 f2 IH1 IH2 H1 H2. 
      apply feval_inversion_and in H1 as [H0 H1].
      apply feval_inversion_and_false in H2 as [H2 | H2]...
    + intros f1 f2 IH1 IH2 H1 H2. 
      apply feval_inversion_or_false in H2 as [H2 H3].
      apply feval_inversion_or in H1 as [H1 | H1]...
    + intros f1 f2 IH1 IH2 H1 H2.  
      apply feval_inversion_implication_false in H2 as [H2 H3].
      apply feval_inversion_implication in H1 as [H1 | H1]...
    + intros f1 f2 IH1 IH2 H1 H2. 
      apply feval_inversion_iff in H1 as [[H0 H1] | [H0 H1]];
      apply feval_inversion_iff_false in H2 as [[H2 H3] | [H2 H3]]...
    + intros x f IH H1 H2.
      inversion H1; subst. destruct H0 as [v Hv].
     inversion H1; subst. inversion H2; subst.
      destruct H0 as [v Hv]. specialize H3 with v. 
      apply IHA in H3.
  - destruct val... right. apply feval_inversion_false in H.
    destruct H.
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
      destruct H0 as [v Hv]. specialize H3 with v. 
      apply IHA in H3.
  - destruct val... right. apply feval_inversion_false in H.
    destruct H.
Qed.