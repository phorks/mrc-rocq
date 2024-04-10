From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From MRC Require Import PredCalc.
From MRC Require Import PredCalcProps.
From MRC Require Import Tactics.

Open Scope general_fassertion_scope.

Ltac prove_equiv_by_inversion :=
  let HTT := fresh "HTT" in
  let HFF := fresh "HFF" in
  assert (HTT:=feval_true_true);
  assert (HFF:=feval_false_false);
  right;
  repeat match goal with
  | H : feval _ _ _ (F_Not _) true |- _ =>
    apply feval_not_true_iff in H
  | H : feval _ _ _ (F_Not _) false |- _ =>
    apply feval_not_false_iff in H
  | H : feval _ _ _ (F_And _ _) true |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply feval_and_true_iff in H as [H1 H2]
  | H : feval _ _ _ (F_And _ _) false |- _ =>
    apply feval_and_false_iff in H as [H | H]
  | H : feval _ _ _ (F_Or _ _) true |- _ =>
    apply feval_or_true_iff in H as [H | H]
  | H : feval _ _ _ (F_Or _ _) false |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply feval_or_false_iff in H as [H1 H2]
  | H : feval _ _ _ (F_Implies _ _) true |- _ =>
    apply feval_implication_true_iff in H as [H | H]
  | H : feval _ _ _ (F_Implies _ _) false |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply feval_implication_false_iff in H as [H1 H2]
  | H : feval _ _ _ (F_Iff _ _) true |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply feval_iff_true_iff in H as [[H1 H2] | [H1 H2]]
  | H : feval _ _ _ (F_Iff _ _) false |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply feval_iff_false_iff in H as [[H1 H2] | [H1 H2]] 
  | H : feval _ _ _ (F_Exists _ _) true |- _ =>
    apply feval_exists_true_iff in H
  | H : feval _ _ _ (F_Exists _ _) false |- _ =>
    apply feval_exists_false_iff in H
  | H : feval _ _ _ (F_Forall _ _) true |- _ =>
    apply feval_forall_true_iff in H
  | H : feval _ _ _ (F_Forall _ _) false |- _ =>
    apply feval_forall_false_iff in H    
  | H : feval _ _ _ (F_Simple AT_False) true |- _ =>
    apply feval_inversion_false_true in H; destruct H
  | H : feval _ _ _ (F_Simple AT_True) false |- _ =>
    apply feval_inversion_true_false in H; destruct H
  | H1 : feval _ _ _ ?A true |- _ =>
    match goal with 
    | H2 : feval _ _ _ A false |- _ =>
      destruct (feval_functional _ _ _ _ H1 H2)
    end
  end;
  repeat match goal with
    | [|- context[feval _ _ _ (F_Not _) true]] =>
      rewrite feval_not_true_iff
    | [|- context[feval _ _ _ (F_Not _) false]] =>
      rewrite feval_not_false_iff
    | [|- context[feval _ _ _ (F_And _ _) true]] =>
      rewrite feval_and_true_iff
    | [|- context[feval _ _ _ (F_And _ _) false]] =>
      rewrite feval_and_false_iff
    | [|- context[feval _ _ _ (F_Or _ _) true]] =>
      rewrite feval_or_true_iff
    | [|- context[feval _ _ _ (F_Or _ _) false]] =>
      rewrite feval_or_false_iff         
    | [|- context[feval _ _ _ (F_Implies _ _) true]] =>
      rewrite feval_implication_true_iff
    | [|- context[feval _ _ _ (F_Implies _ _) false]] =>
      rewrite feval_implication_false_iff
    | [|- context[feval _ _ _ (F_Iff _ _) true]] =>
      rewrite feval_iff_true_iff
    | [|- context[feval _ _ _ (F_Iff _ _) false]] =>
      rewrite feval_iff_false_iff
  end;
  auto;
  clear HTT;
  clear HFF.

Ltac prove_equiv := 
    intros; split; intros val; intros; destruct val; auto; 
    prove_equiv_by_inversion.

Theorem and_comm : forall A B,
  <[ A /\ B ]> == <[ B /\ A ]>.
Proof. prove_equiv. Qed.

Theorem or_comm : forall A B,
  <[ A \/ B ]> == <[ B \/ A ]>.
Proof. prove_equiv. Qed.

Theorem and_idemp : forall A,
  <[ A /\ A ]> == <[ A ]>.
Proof. prove_equiv. Qed.

Theorem or_idemp : forall A,
  <[ A \/ A ]> == <[ A ]>.
Proof. prove_equiv. Qed.

Theorem and_assoc : forall A B C,
  <[ A /\ (B /\ C) ]> == <[ (A /\ B) /\ C ]>.
Proof. prove_equiv. Qed.

Theorem or_assoc : forall A B C,
  <[ A \/ (B \/ C) ]> == <[ (A \/ B) \/ C ]>.
Proof. prove_equiv. Qed.

Theorem and_absorption : forall A B,
  <[ A /\ (A \/ B) ]> == A.
Proof. prove_equiv. Qed.

Theorem or_absorption : forall A B,
  <[ A \/ (A /\ B) ]> == A.
Proof. prove_equiv. Qed.

Theorem and_or_distr : forall A B C,
  <[ A /\ (B \/ C) ]> == <[ (A /\ B) \/ (A /\ C) ]>.
Proof. prove_equiv. Qed.

Theorem or_and_distr : forall A B C,
  <[ A \/ (B /\ C) ]> == <[ (A \/ B) /\ (A \/ C) ]>.
Proof. prove_equiv. Qed.  

Theorem and_true : forall A,
  <[ A /\ true ]> == A.
Proof. prove_equiv. Qed.

Theorem or_true : forall A,
  <[ A \/ true ]> == <[ true ]>.
Proof. prove_equiv. Qed.

Theorem and_false : forall A,
  <[ A /\ false ]> == <[ false ]>.
Proof. prove_equiv. Qed.

Theorem or_false : forall A,
  <[ A \/ false ]> == <[ A ]>.
Proof. prove_equiv. Qed.

Theorem not_true : <[ ~ true ]> == <[ false ]>.
Proof. prove_equiv. Qed.

Theorem not_false : <[ ~ false ]> == <[ true ]>.
Proof. prove_equiv. Qed.

Theorem A_and_not_A : forall A,
  <[ A /\ ~ A ]> == <[ false ]>.
Proof. prove_equiv. Qed.

Theorem excluded_middle : forall A,
  <[ A \/ ~ A ]> == <[ true ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed. 

Theorem not_involutive : forall A,
  <[ ~ ~ A ]> == <[ A ]>.
Proof. prove_equiv. Qed.  

Theorem not_and : forall A B,
  <[ ~ (A /\ B) ]> == <[ ~ A \/ ~ B ]>.
Proof. prove_equiv. Qed.

Theorem not_or : forall A B,
  <[ ~ (A \/ B) ]> == <[ ~ A /\ ~ B ]>.
Proof. prove_equiv. Qed.

Theorem or_neg_absorption : forall A B,
  <[ A \/ (~ A /\ B) ]> == <[ A \/ B ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

Theorem and_neg_absorption : forall A B,
  <[ A /\ (~ A \/ B) ]> == <[ A /\ B ]>.
Proof. prove_equiv. Qed.

(* A.22 *)
Theorem implication_equiv_or : forall A B,
  <[ A => B ]> == <[ ~ A \/ B ]>.
Proof. prove_equiv. Qed.

(* A.23 *)
Theorem A_implies_A__true : forall A,
  <[ A => A ]> == <[ true ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.24 *)
Theorem implication_as_not_and : forall A B,
  <[ A => B ]> == <[ ~ (A /\ ~ B) ]>.
Proof. prove_equiv. Qed.

(* A.25 *)
Theorem not_implication_as_and : forall A B,
  <[ ~ (A => B) ]> == <[ A /\ ~ B ]>.
Proof. prove_equiv. Qed.

(* A.26 *)
Theorem contrapositive_law : forall A B,
  <[ A => B ]> == <[ ~ B => ~ A ]>.
Proof. prove_equiv. Qed.

(* A.27 *)
Theorem everything_implies_true : forall A,
  <[ A => true ]> == <[ true ]>.
Proof. prove_equiv. Qed.

(* A.28 *)
Theorem true_implies_A : forall A,
  <[ true => A ]> == <[ A ]>.
Proof. prove_equiv. Qed.

(* A.29 *)
Theorem A_implies_false : forall A,
  <[ A => false ]> == <[ ~ A ]>.
Proof. prove_equiv. Qed.

(* A.30 *)
Theorem false_implies_everything : forall A,
  <[ false => A ]> == <[ true ]>.
Proof. prove_equiv. Qed.

(* A.31 *)
Theorem A_implies_not_A : forall A,
  <[ A => ~ A ]> == <[ ~ A ]>.
Proof. prove_equiv. Qed.

(* A.32 *)
Theorem not_A_implies_A : forall A,
  <[ ~ A => A ]> == <[ A ]>.
Proof. prove_equiv. Qed.

(* A.33 *)
Theorem implication_distr1 : forall A B C,
  <[ C => (A /\ B) ]> == <[ (C => A) /\ (C => B) ]>.
Proof. prove_equiv. Qed.

(* A.34 *)
Theorem implication_distr2 : forall A B C,
  <[ (A \/ B) => C ]> == <[ (A => C) /\ (B => C) ]>.
Proof. prove_equiv. Qed.

(* A.35 *)
Theorem implication_distr3 : forall A B C,
  <[ C => (A \/ B) ]> == <[ (C => A) \/ (C => B) ]>.
Proof. prove_equiv. Qed.

(* A.36 *)
Theorem implication_distr4 : forall A B C,
  <[ (A /\ B) => C ]> == <[ (A => C) \/ (B => C) ]>.
Proof. prove_equiv. Qed.

(* A.37 *)
Theorem successive_hypotheses : forall A B C,
  <[ A => (B => C) ]> == <[ (A /\ B) => C ]>.
Proof. prove_equiv. Qed.

(* A.37 *)
Theorem successive_hypotheses' : forall A B C,
  <[ B => (A => C) ]> == <[ (A /\ B) => C ]>.
Proof. prove_equiv. Qed.

(* A.38 *)
Theorem def_by_cases : forall A B C,
  <[ (A => B) /\ (~A => C) ]> == <[ (A /\ B) \/ (~A /\ C) ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.39 *)
Theorem iff_equiv1 : forall A B,
  <[ A <=> B ]> == <[ (A => B) /\ (B => A) ]>.
Proof. prove_equiv. Qed.

(* A.40 *)
Theorem iff_equiv2 : forall A B,
  <[ A <=> B ]> == <[ (A /\ B) \/ ~(A \/ B) ]>.
Proof. prove_equiv. Qed.

(* A.41 *)
Theorem iff_equiv3 : forall A B,
  <[ A <=> B ]> == <[ ~A <=> ~B ]>.
Proof. prove_equiv. Qed.

(* A.42 *)
Theorem A_iff_A : forall A,
  <[ A <=> A]> == <[ true ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.43 *)
Theorem A_iff_not_A : forall A,
  <[ A <=> ~ A ]> == <[ false ]>.
Proof. prove_equiv. Qed.

(* A.44 *)
Theorem iff_true_id : forall A,
  <[ A <=> true ]> == <[ A ]>.
Proof. prove_equiv. Qed.

(* A.45 *)
Theorem iff_false_neg : forall A,
  <[ A <=> false ]> == <[ ~A ]>.
Proof. prove_equiv. Qed.

(* A.46 *)
Theorem implication_equiv_iff1 : forall A B,
  <[ A => B ]> == <[ A <=> (A /\ B) ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.47 *)
Theorem implication_equiv_iff2 : forall A B,
  <[ B => A ]> == <[ A <=> (A \/ B) ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.48 *)
Theorem or_equiv_iff : forall A B C,
  <[ A \/ (B <=> C) ]> == <[ (A \/ B) <=> (A \/ C) ]>.
Proof with auto. 
  prove_equiv.
  destruct (feval_excluded_middle A st fctx pctx)...
Qed.

(* A.49 *)
Theorem equiv_comm : forall A B,
  <[ A <=> B ]> == <[ B <=> A ]>.
Proof. prove_equiv. Qed.

(* A.50 *)
Theorem equiv_assoc : forall A B C,
  <[ A <=> (B <=> C) ]> == <[ (A <=> B) <=> C ]>.
Proof. prove_equiv. Qed.

(* A.56 *)
Theorem universal_one_point : forall x a A,
  appears_in_term x a = false ->
  <[ forall x, x = a => A ]> == <[ A[x \ a] ]>.
Proof with auto. prove_equiv. 
  - inversion H0; subst. clear H0. rename H2 into H1. 
    specialize H1 with a. rewrite simpl_subst_implication in H1.
    apply feval_implication_true_iff in H1 as [H1 | H1].
    + rewrite simpl_subst_simple_formula in H1. simpl in H1.
      rewrite (String.eqb_refl) in H1.
      rewrite subst_term_id_when_not_in_term in H1...
      apply feval_eq_refl in H1. destruct H1.
    + assumption.
  - apply feval_forall_true_iff. intros v.
    rewrite simpl_subst_implication. 
    apply feval_implication_true_iff.
    rewrite simpl_subst_simple_formula.
    simpl. rewrite (String.eqb_refl). 
    rewrite subst_term_id_when_not_in_term...
    destruct (feval_excluded_middle <[ v = a ]> st fctx pctx)...
    inversion H1; subst. inversion H3; subst. right.
    apply subst_eq_congr with (t:=a)...
    destruct (pctx_eq_semantics pctx) as [peq [Hpeq Heq_sem]].
    apply FEval_Simple. apply SFEval_Pred with peq...
    unfold eq_prel_sem in Heq_sem. 
    destruct (Heq_sem st fctx) as [_ [Hrefl _]]. clear Heq_sem.
    specialize Hrefl with v a true.
    rewrite Hpeq in H5. inversion H5; subst pdef. clear H5 Hpeq.
    destruct peq. simpl in *. inversion H7; subst. 
    inversion H2; subst. apply Pred_Eval with n_args prel0 Hfnal...
Qed.