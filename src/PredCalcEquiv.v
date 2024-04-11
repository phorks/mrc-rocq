From MRC Require Import PredCalc.
From MRC Require Import PredCalcProps.
From Coq Require Import Setoid Morphisms.

Definition formula_implies (f1 f2 : formula) : Prop :=
  forall fctx pctx f1val st,
    feval st fctx pctx f1 f1val ->
    (f1val = false) \/ (feval st fctx pctx f2 true).

Definition formula_equiv (f1 f2 : formula) : Prop := 
  formula_implies f1 f2 /\
  formula_implies f2 f1.

Declare Scope general_fassertion_scope.
Declare Custom Entry fassertion.

Notation "P '===>' Q" := (formula_implies P Q)
                  (at level 50) : general_fassertion_scope.

Notation "P '===' Q" := (formula_equiv P Q)
                          (at level 50) : general_fassertion_scope. 

Open Scope general_fassertion_scope.

Theorem formula_equiv_spec : forall fctx pctx st A B b,
  formula_equiv A B ->
  feval st fctx pctx A b ->
  feval st fctx pctx B b.
Proof with auto.
  intros fctx pctx st A B b [H1 H2] HA.
  unfold formula_implies in H1, H2.
  specialize (H1 fctx pctx). specialize (H2 fctx pctx).
  destruct b.
  - destruct (H1 true st HA)... discriminate H.
  - specialize H2 with true st.
    assert (EM := feval_excluded_middle B st fctx pctx).
    destruct EM...  apply H2 in H. destruct H.
    + discriminate H.
    + destruct (feval_functional _ _ _ _ H HA).
Qed.

Theorem fequiv_refl : forall A,
  A === A.
Proof with auto.
  intros A. split; intros fctx pctx val st H.
  - destruct val...
  - destruct val...
Qed.

Theorem fequiv_sym : forall A B,
  formula_equiv A B ->
  formula_equiv B A.
Proof with auto.
  intros A B Hequiv. split; intros fctx pctx val st H.
  - destruct val... right. 
    apply Hequiv in H as [H | H]... discriminate.
  - destruct val... right. 
    apply Hequiv in H as [H | H]... discriminate.
Qed.

Theorem fequiv_trans : forall A B C,
  formula_equiv A B ->
  formula_equiv B C ->
  formula_equiv A C.
Proof with auto.
  intros A B C H1 H2. split; intros fctx pctx val st H.
  - destruct val... right.
    apply H1 in H as [H | H].
    + discriminate.
    + apply H2 in H as [H | H]... discriminate.
  - destruct val... right. 
    apply H2 in H as [H | H].
    + discriminate.
    + apply H1 in H as [H | H]... discriminate.
Qed.      

Add Relation (formula) (formula_equiv)
  reflexivity proved by (fequiv_refl)
  symmetry proved by (fequiv_sym)
  transitivity proved by (fequiv_trans)
  as fequiv_rel.

Add Morphism F_Not
  with signature formula_equiv ==>
                  formula_equiv as fnot_mor.
Proof with auto.
  intros A B Hequiv. split; intros fctx pctx val st H.
  - destruct val... right. apply feval_not_true_iff in H.
    apply feval_not_true_iff.
    apply formula_equiv_spec with A...
  - destruct val... right. apply feval_not_true_iff in H.
    apply feval_not_true_iff.
    apply formula_equiv_spec with B... symmetry...
Qed.

Add Morphism F_And
  with signature formula_equiv ==>
                  formula_equiv ==>
                  formula_equiv as fand_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros fctx pctx val st H.
  - destruct val... right. apply feval_and_true_iff in H as [H1 H2].
    apply feval_and_true_iff. split.
    + apply formula_equiv_spec with A1...
    + apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_and_true_iff in H as [H1 H2].
    apply feval_and_true_iff. split.
    + apply formula_equiv_spec with A2... symmetry...
    + apply formula_equiv_spec with B2... symmetry...
Qed.

Add Morphism F_Or
  with signature formula_equiv ==>
                  formula_equiv ==>
                  formula_equiv as for_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros fctx pctx val st H.
  - destruct val... right. apply feval_or_true_iff. 
    apply feval_or_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A1...
    + right. apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_or_true_iff. 
    apply feval_or_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A2... symmetry...
    + right. apply formula_equiv_spec with B2... symmetry...
Qed.

Add Morphism F_Implies
  with signature formula_equiv ==>
                  formula_equiv ==>
                  formula_equiv as fimplication_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros fctx pctx val st H.
  - destruct val... right. apply feval_implication_true_iff. 
    apply feval_implication_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A1...
    + right. apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_implication_true_iff. 
    apply feval_implication_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A2... symmetry...
    + right. apply formula_equiv_spec with B2... symmetry...
Qed.

Add Morphism F_Iff
  with signature formula_equiv ==>
                  formula_equiv ==>
                  formula_equiv as fiff_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros fctx pctx val st H.
  - destruct val... right. apply feval_iff_true_iff. 
    apply feval_iff_true_iff in H as [[H1 H2] | [H1 H2]].
    + left. split. 
      * apply formula_equiv_spec with A1...
      * apply formula_equiv_spec with B1...
    + right. split. 
      * apply formula_equiv_spec with A1...
      * apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_iff_true_iff. 
    apply feval_iff_true_iff in H as [[H1 H2] | [H1 H2]].
    + left. split. 
      * apply formula_equiv_spec with A2... symmetry...
      * apply formula_equiv_spec with B2... symmetry...
    + right. split. 
      * apply formula_equiv_spec with A2... symmetry...
      * apply formula_equiv_spec with B2... symmetry...
Qed.