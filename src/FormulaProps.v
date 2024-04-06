From MRC Require Import PredCalc.

Open Scope general_fassertion_scope.

Theorem feval_inversion_and : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> true ->
  feval st fctx pctx A true /\ feval st fctx pctx B true.
Proof.
  intros st fctx pctx A B H. inversion H; subst.
  apply Bool.andb_true_iff in H2 as [H1 H2]; subst.
  simpl. split; assumption.
Qed.

Theorem feval_inversion_or : forall st fctx pctx A B,
  feval st fctx pctx <[ A \/ B ]> true ->
  feval st fctx pctx A true \/ feval st fctx pctx B true.
Proof.
  intros st fctx pctx A B H. 
  inversion H; subst; [left | right]; assumption.
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