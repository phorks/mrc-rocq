From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From MRC Require Import PredCalc.
From MRC Require Import Tactics.

Open Scope general_fassertion_scope.

Theorem feval_inversion_and : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> true ->
  feval st fctx pctx A true /\ feval st fctx pctx B true.
Proof.
  intros st fctx pctx A B H. inversion H; subst. split; assumption.
Qed.

Theorem feval_inversion_and_false : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> false ->
  feval st fctx pctx A false \/ feval st fctx pctx B false.
Proof.
  intros st fctx pctx A B H. inversion H; subst.
  - left. assumption.
  - right. assumption.
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

Theorem feval_inversion_true_false : forall {st} {fctx} {pctx},
  ~ feval st fctx pctx <[ true ]> false.
Proof.
  intros st fctx pctx contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_inversion_false_true : forall {st} {fctx} {pctx},
  ~ feval st fctx pctx <[ false ]> true.
Proof.
  intros st fctx pctx contra. inversion contra; subst. inversion H0.
Qed.

Theorem and_true_if : forall st fctx pctx A B,
  feval st fctx pctx A true ->
  feval st fctx pctx B true ->
  feval st fctx pctx <[ A /\ B ]> true.
Proof.
  intros st fctx pctx A B [H1 H2]. 
  replace true with (andb true true) by auto.
  apply FEval_And; assumption.
Qed.

Theorem and_false_if : forall st fctx pctx A B,
  feval st fctx pctx A false \/ feval st fctx pctx B false ->
  feval st fctx pctx <[ A /\ B ]> false.
Proof.
  intros st fctx pctx A B [H | H].
  - apply FEVal_And_False1. assumption.
  - apply FEVal_And_False2. assumption.
Qed.

Theorem or_true_if : forall st fctx pctx A B,
  feval st fctx pctx A true \/
  feval st fctx pctx B true ->
  feval st fctx pctx <[ A \/ B ]> true.
Proof.
  intros st fctx pctx A B [H | H].
  - replace true with (orb true true) by auto. 
    apply FEval_Or1. assumption.
  - replace true with (orb true true) by auto. 
    apply FEval_Or2. assumption.
Qed.

Theorem or_false_if : forall st fctx pctx A B,
  feval st fctx pctx A false ->
  feval st fctx pctx B false ->
  feval st fctx pctx <[ A \/ B ]> false.
Proof.
  intros st fctx pctx A B H1 H2.
  replace false with (orb false false) by auto. 
  apply FEval_Or_False; assumption.
Qed.

Theorem implication_true_if : forall st fctx pctx A B,
  feval st fctx pctx A false \/
  feval st fctx pctx B true ->
  feval st fctx pctx <[ A => B ]> true.
Proof with auto.
  intros st fctx pctx A B [H | H].
  - apply FEval_Implies1...
  - apply FEval_Implies2...
Qed.

Theorem implication_false_if : forall st fctx pctx A B,
  feval st fctx pctx A true ->
  feval st fctx pctx B false ->
  feval st fctx pctx <[ A => B ]> false.
Proof with auto.
  intros st fctx pctx A B H1 H2. apply FEval_Implies_False...
Qed.

Theorem not_true_if : forall st fctx pctx A,
  feval st fctx pctx <[ A ]> false -> 
  feval st fctx pctx <[ ~ A ]> true.
Proof.
  intros st fctx pctx A H. 
  replace true with (negb false) by reflexivity.
  apply FEval_Not. assumption.
Qed.

Theorem not_false_if : forall st fctx pctx A,
  feval st fctx pctx <[ A ]> true -> 
  feval st fctx pctx <[ ~ A ]> false.
Proof.
  intros st fctx pctx A H. 
  replace true with (negb false) by reflexivity.
  replace false with (negb true) by reflexivity.
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

(* Since our function and predicate symbol interpretations are 
  relations instead of computable functions, our evaluation
  process might fail evaluating some fomrulas; i.e., it might
  not evaluate a formula as either false or true. In such cases
  (A \/ ~ A) does not hold. 
  
  Example: P(0, 1), when pctx does not contain P, is neither
    true not false. Meanwhile, even if the symbols has an
    interpretation in pctx, it might be the case that neither
    (0, 1) |-> true nor (0, 1) |-> false are in P.
  
  We admit this as an axiom, since the book includes it.
  *)
Axiom feval_excluded_middle : forall A st fctx pctx,
  feval st fctx pctx A true \/ feval st fctx pctx A false.

Theorem feval_functional : forall A st fctx pctx,
  feval st fctx pctx A true ->
  feval st fctx pctx A false ->
  False.
Proof with auto.
  intros A st fctx pctx HT HF. induction A.
  - induction sf.
    + inversion HF; subst. inversion H0.
    + inversion HT; subst. inversion H0.
    + inversion HT; subst. inversion HF; subst.
      inversion H0; subst. inversion H1; subst.
      inversion H5; subst. inversion H7; subst.
      rewrite H4 in H3. inversion H3; subst.
      apply (Hfnal _ _ _ _ false) in H2... discriminate.
  - apply feval_inversion_not in HT. 
    apply feval_inversion_not_false in HF.
    apply IHA; assumption.
  - apply feval_inversion_and in HT as [H0 H1].
    apply feval_inversion_and_false in HF as [HF | HF]...
  - apply feval_inversion_or_false in HF as [HF1 HF2].
    apply feval_inversion_or in HT as [HT | HT]...
  - apply feval_inversion_implication_false in HF as [HF1 HF2].
    apply feval_inversion_implication in HT as [HT1 | HT1]...
  - apply feval_inversion_iff in HT as [[HT1 HT2] | [HT1 HT2]];
    apply feval_inversion_iff_false in HF as [[HF1 HF2] | [HF1 HF2]]...
  - inversion HT; subst. inversion HF; subst.
    destruct H1 as [v Hv]. specialize H2 with v.
    apply H with v...
  - inversion HT; subst. inversion HF; subst.
    destruct H2 as [v Hv]. specialize H1 with v.
    apply H with v...
Qed.

Theorem fequiv_refl : forall A,
  A == A.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val...
Qed.

Theorem fequiv_sym : forall A B,
  A == B ->
  B == A.
Proof with auto.
  intros A B Hequiv fctx pctx. split; intros val st H.
  - destruct val... right. 
    specialize Hequiv with fctx pctx as [_ Himpl].
    apply Himpl in H as [H | H]... discriminate.
  - destruct val... right. 
    specialize Hequiv with fctx pctx as [Himpl _].
    apply Himpl in H as [H | H]... discriminate.
Qed.

Theorem fequiv_trans : forall A B C,
  A == B ->
  B == C ->
  A == C.
Proof with auto.
  intros A B C H1 H2 fctx pctx. split; intros val st H.
  - destruct val... right. 
    specialize H1 with fctx pctx as [H1 _]. apply H1 in H as [H | H].
    + discriminate.
    + specialize H2 with fctx pctx as [H2 _].
      apply H2 in H as [H | H]... discriminate.
  - destruct val... right. 
    specialize H2 with fctx pctx as [_ H2]. apply H2 in H as [H | H].
    + discriminate.
    + specialize H1 with fctx pctx as [_ H1].
      apply H1 in H as [H | H]... discriminate.
Qed.      

Hint Resolve true_is_true : core.
Hint Resolve false_is_false : core.
Hint Resolve feval_inversion_and : core.
Hint Extern 2 (feval _ _ _ (<[ _ /\ _ ]>) true) =>
  apply and_true_if; auto : core.

Hint Extern 4 (feval _ _ _ (<[ _ \/ _ ]>) true) =>
  try solve [apply FEval_Or1; auto]; 
  try solve [apply FEval_Or2; auto] : core.

Ltac prove_equiv :=
  repeat match goal with
    | H : feval _ _ _ (F_Not _) true |- _ =>
      apply feval_inversion_not in H
    | H : feval _ _ _ (F_Not _) false |- _ =>
      apply feval_inversion_false in H
    | H : feval _ _ _ (F_And _ _) true |- _ =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      apply feval_inversion_and in H as [H1 H2]
    | H : feval _ _ _ (F_And _ _) false |- _ =>
      apply feval_inversion_and_false in H as [H | H]
    | H : feval _ _ _ (F_Or _ _) true |- _ =>
      apply feval_inversion_or in H as [H | H]
    | H : feval _ _ _ (F_Or _ _) false |- _ =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      apply feval_inversion_or_false in H as [H1 H2]
    | H : feval _ _ _ (F_Implies _ _) true |- _ =>
      apply feval_inversion_implication in H as [H | H]
    | H : feval _ _ _ (F_Implies _ _) false |- _ =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      apply feval_inversion_implication_false in H as [H1 H2]
    | H : feval _ _ _ (F_Iff _ _) true |- _ =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      apply feval_inversion_iff in H as [[H1 H2] | [H1 H2]]
    | H : feval _ _ _ (F_And _ _) true |- _ =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      apply feval_inversion_iff_false in H as [[H1 H2] | [H1 H2]] 
  end;
  repeat match goal with
    | [|- feval _ _ _ (F_Not _) true] =>
      apply not_true_if
    | [|- feval _ _ _ (F_Not _) false] =>
      apply not_false_if      
    | [|- feval _ _ _ (F_And _ _) true] =>
      apply and_true_if
    | [|- feval _ _ _ (F_And _ _) false] =>
      apply and_false_if
    | [|- feval _ _ _ (F_Or _ _) true] =>
      apply or_true_if
    | [|- feval _ _ _ (F_Or _ _) false] =>
      apply or_false_if               
    | [|- feval _ _ _ (F_Implies _ _) true] =>
      apply implication_true_if
    | [|- feval _ _ _ (F_Implies _ _) false] =>
      apply implication_false_if            
  end;
  auto.

Theorem and_comm : forall A B,
  <[ A /\ B ]> == <[ B /\ A ]>.
Proof with auto. 
  intros A B fctx pctx. split; intros val st H.
  - destruct val... rewrite and_true_if. destruct val... right.
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
  - destruct val... right. apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_not in H2.
    destruct (feval_functional _ _ _ _ H1 H2).
  - destruct val... right. apply feval_inversion_false in H.
    destruct H.
Qed.

Theorem excluded_middle : forall A,
  <[ A \/ ~ A ]> == <[ true ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val... right. apply or_true_if.
    destruct (feval_excluded_middle A st fctx pctx).
    + left...
    + right. apply not_true_if...
Qed. 

Theorem not_involutive : forall A,
  <[ ~ ~ A ]> == <[ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. apply feval_inversion_not in H.
    apply feval_inversion_not_false in H...
  - destruct val... right. apply not_true_if.
    apply not_false_if...
Qed.

Theorem not_and : forall A B,
  <[ ~ (A /\ B) ]> == <[ ~ A \/ ~ B ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. apply feval_inversion_not in H.
    apply or_true_if. 
    apply feval_inversion_and_false in H as [H | H].
    + left. apply not_true_if...
    + right. apply not_true_if...
  - destruct val... right. apply not_true_if. apply and_false_if.
    apply feval_inversion_or in H as [H | H]; 
      apply feval_inversion_not in H...
Qed.

Theorem not_or : forall A B,
  <[ ~ (A \/ B) ]> == <[ ~ A /\ ~ B ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. apply feval_inversion_not in H.
    apply feval_inversion_or_false in H as [H1 H2].
    apply and_true_if; apply not_true_if...
  - destruct val... right. apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_not in H1, H2. apply not_true_if.
    apply or_false_if...
Qed.

Theorem or_neg_absorption : forall A B,
  <[ A \/ (~ A /\ B) ]> == <[ A \/ B ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. apply or_true_if.
    apply feval_inversion_or in H as [H | H]...
    apply feval_inversion_and in H as [_ H]...
  - destruct val... right. apply or_true_if.
    apply feval_inversion_or in H as [H | H]...
    destruct (feval_excluded_middle A st fctx pctx).
    + left...
    + right. apply and_true_if... apply not_true_if...
Qed.

Theorem and_neg_absorption : forall A B,
  <[ A /\ (~ A \/ B) ]> == <[ A /\ B ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_or in H2 as [H2 | H2].
    + apply feval_inversion_not in H2. 
      destruct (feval_functional _ _ _ _ H1 H2).
    + apply and_true_if...
  - destruct val... right. apply feval_inversion_and in H as [H1 H2].
    apply and_true_if...
Qed.

(* A.22 *)
Theorem implication_equiv_or : forall A B,
  <[ A => B ]> == <[ ~ A \/ B ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_implication in H as [H | H].
    + apply or_true_if. left. apply not_true_if...
    + apply or_true_if...
  - destruct val... right. apply feval_inversion_or in H as [H | H].
    + apply feval_inversion_not in H. apply implication_true_if...
    + apply implication_true_if...
Qed.

(* A.23 *)
Theorem A_implies_A__true : forall A,
  <[ A => A ]> == <[ true ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val... right. apply implication_true_if.
    destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.24 *)
Theorem implication_as_not_and : forall A B,
  <[ A => B ]> == <[ ~ (A /\ ~ B) ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply not_true_if. apply and_false_if.
    apply feval_inversion_implication in H as [H | H]...
    right. apply not_false_if...
  - destruct val... right. apply feval_inversion_not in H.
    apply implication_true_if.
    apply feval_inversion_and_false in H as [H | H]...
    apply feval_inversion_not_false in H...
Qed.

(* A.25 *)
Theorem not_implication_as_and : forall A B,
  <[ ~ (A => B) ]> == <[ A /\ ~ B ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. apply feval_inversion_not in H.
    apply feval_inversion_implication_false in H as [H1 H2].
    apply and_true_if... apply not_true_if...
  - destruct val... right. apply feval_inversion_and in H as [H1 H2].
    apply feval_inversion_not in H2. apply not_true_if.
    apply implication_false_if...
Qed.

(* A.26 *)
Theorem contrapositive_law : forall A B,
  <[ A => B ]> == <[ ~ B => ~ A ]>.
Proof with auto.
  intros A B fctx pctx. split; intros val st H.
  - destruct val... right. apply implication_true_if.
    apply feval_inversion_implication in H as [H | H].
    + right. apply not_true_if...
    + left. apply not_false_if...
  - destruct val... right. apply implication_true_if.
    apply feval_inversion_implication in H as [H | H].
    + apply feval_inversion_not_false in H. right...
    + apply feval_inversion_not in H. left... 
Qed.

(* A.27 *)
Theorem everything_implies_true : forall A,
  <[ A => true ]> == <[ true ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val...
Qed.

(* A.28 *)
Theorem true_implies_A : forall A,
  <[ true => A ]> == <[ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_implication in H as [H | H]...
    destruct (feval_inversion_true_false H).
  - destruct val...
Qed.

(* A.29 *)
Theorem A_implies_false : forall A,
  <[ A => false ]> == <[ ~ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. apply not_true_if. 
    apply feval_inversion_implication in H as [H | H]...
    destruct (feval_inversion_false_true H).
  - destruct val... right. apply feval_inversion_not in H.
    apply implication_true_if...
Qed.

(* A.30 *)
Theorem false_implies_everything : forall A,
  <[ false => A ]> == <[ true ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val...
Qed.

(* A.31 *)
Theorem A_implies_not_A : forall A,
  <[ A => ~ A ]> == <[ ~ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. apply not_true_if.
    apply feval_inversion_implication in H as [H | H]...
    apply feval_inversion_not in H...
  - destruct val... 
Qed.

(* A.32 *)
Theorem not_A_implies_A : forall A,
  <[ ~ A => A ]> == <[ A ]>.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val... right. 
    apply feval_inversion_implication in H as [H | H]...
    apply feval_inversion_not_false in H...
  - destruct val...
Qed.

(* A.33 *)
Theorem implication_distr1 : forall A B C,
  <[ C => (A /\ B) ]> == <[ (C => A) /\ (C => B) ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... prove_equiv.
  - destruct val... prove_equiv.
Qed.

(* A.34 *)
Theorem implication_distr2 : forall A B C,
  <[ (A \/ B) => C ]> == <[ (A => C) /\ (B => C) ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... prove_equiv.
  - destruct val... prove_equiv.
Qed.

(* A.35 *)
Theorem implication_distr3 : forall A B C,
  <[ C => (A \/ B) ]> == <[ (C => A) \/ (C => B) ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... prove_equiv.
  - destruct val... prove_equiv.
Qed.

(* A.36 *)
Theorem implication_distr4 : forall A B C,
  <[ (A /\ B) => C ]> == <[ (A => C) \/ (B => C) ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... prove_equiv.
  - destruct val... prove_equiv.
Qed.

(* A.37 *)
Theorem successive_hypotheses : forall A B C,
  <[ A => (B => C) ]> == <[ (A /\ B) => C ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... prove_equiv.
  - destruct val... prove_equiv.
Qed.

(* A.37 *)
Theorem successive_hypotheses' : forall A B C,
  <[ B => (A => C) ]> == <[ (A /\ B) => C ]>.
Proof with auto.
  intros A B C fctx pctx. split; intros val st H.
  - destruct val... prove_equiv.
  - destruct val... prove_equiv.
Qed.

(* A.38 *)
Theorem def_by_cases : forall A B C,
  <[ (A => B) /\ (~A => C) ]> == <[ (A /\ B) \/ (~A /\ C) ]>.
Proof with auto.
  intros A B Cfctx pctx. split; intros val st H.
  - destruct val... prove_equiv; right; apply or_true_if.
    + left. rewrite and_true_if.
  - destruct val... prove_equiv.
Qed.

