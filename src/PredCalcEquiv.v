From MRC Require Import PredCalc.
From MRC Require Import PredCalcProps.
From Coq Require Import Setoid Morphisms.

Definition formula_implies fctx pctx (f1 f2 : formula) : Prop :=
  forall f1val st,
    feval st fctx pctx f1 f1val ->
    (f1val = false) \/ (feval st fctx pctx f2 true).

Definition formula_equiv fctx pctx (f1 f2 : formula) : Prop :=
  formula_implies fctx pctx f1 f2 /\
  formula_implies fctx pctx f2 f1.

Declare Scope general_fassertion_scope.
Declare Custom Entry fassertion.

Notation "P '===>' Q" := (forall fctx pctx, formula_implies fctx pctx P Q)
                  (at level 50) : general_fassertion_scope.

Notation "P '===' Q" := (forall fctx pctx, (formula_equiv fctx pctx P Q))
                          (at level 50) : general_fassertion_scope. 

Open Scope general_fassertion_scope.

Theorem formula_equiv_spec : forall fctx pctx st A B b,
  formula_equiv fctx pctx A B ->
  feval st fctx pctx A b ->
  feval st fctx pctx B b.
Proof with auto.
  intros fctx pctx st A B b [H1 H2] HA.
  unfold formula_implies in H1, H2.
  destruct b.
  - destruct (H1 true st HA)... discriminate H.
  - specialize H2 with true st.
    assert (EM := feval_excluded_middle B st fctx pctx).
    destruct EM...  apply H2 in H. destruct H.
    + discriminate H.
    + destruct (feval_functional _ _ _ _ H HA).
Qed.

Theorem fequiv_refl : forall fctx pctx A,
  formula_equiv fctx pctx A A.
Proof with auto.
  intros A fctx pctx. split; intros val st H.
  - destruct val...
  - destruct val...
Qed.

Theorem fequiv_sym : forall fctx pctx A B,
  formula_equiv fctx pctx A B ->
  formula_equiv fctx pctx B A.
Proof with auto.
  intros fctx pctx A B Hequiv. split; intros val st H.
  - destruct val... right. 
    apply Hequiv in H as [H | H]... discriminate.
  - destruct val... right. 
    apply Hequiv in H as [H | H]... discriminate.
Qed.

Theorem fequiv_trans : forall fctx pctx A B C,
  formula_equiv fctx pctx A B ->
  formula_equiv fctx pctx B C ->
  formula_equiv fctx pctx A C.
Proof with auto.
  intros fctx pctx A B C H1 H2. split; intros val st H.
  - destruct val... right.
    apply H1 in H as [H | H].
    + discriminate.
    + apply H2 in H as [H | H]... discriminate.
  - destruct val... right. 
    apply H2 in H as [H | H].
    + discriminate.
    + apply H1 in H as [H | H]... discriminate.
Qed.      

Add Parametric Relation fctx pctx : (formula) (formula_equiv fctx pctx)
  reflexivity proved by (fequiv_refl fctx pctx)
  symmetry proved by (fequiv_sym fctx pctx)
  transitivity proved by (fequiv_trans fctx pctx)
  as fequiv_rel.

Add Parametric Morphism fctx pctx : F_Not
  with signature (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) as fnot_mor.
Proof with auto.
  intros A B Hequiv. split; intros val st H.
  - destruct val... right. apply feval_not_true_iff in H.
    apply feval_not_true_iff.
    apply formula_equiv_spec with A...
  - destruct val... right. apply feval_not_true_iff in H.
    apply feval_not_true_iff.
    apply formula_equiv_spec with B... symmetry...
Qed.

Add Parametric Morphism fctx pctx : F_And
  with signature (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) as fand_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros val st H.
  - destruct val... right. apply feval_and_true_iff in H as [H1 H2].
    apply feval_and_true_iff. split.
    + apply formula_equiv_spec with A1...
    + apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_and_true_iff in H as [H1 H2].
    apply feval_and_true_iff. split.
    + apply formula_equiv_spec with A2... symmetry...
    + apply formula_equiv_spec with B2... symmetry...
Qed.

Add Parametric Morphism fctx pctx : F_Or
  with signature (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) as for_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros val st H.
  - destruct val... right. apply feval_or_true_iff. 
    apply feval_or_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A1...
    + right. apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_or_true_iff. 
    apply feval_or_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A2... symmetry...
    + right. apply formula_equiv_spec with B2... symmetry...
Qed.

Add Parametric Morphism fctx pctx : F_Implies
  with signature (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) as fimplication_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros val st H.
  - destruct val... right. apply feval_implication_true_iff. 
    apply feval_implication_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A1...
    + right. apply formula_equiv_spec with B1...
  - destruct val... right. apply feval_implication_true_iff. 
    apply feval_implication_true_iff in H as [H | H].
    + left. apply formula_equiv_spec with A2... symmetry...
    + right. apply formula_equiv_spec with B2... symmetry...
Qed.

Add Parametric Morphism fctx pctx : F_Iff
  with signature (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) ==>
                  (formula_equiv fctx pctx) as fiff_mor.
Proof with auto.
  intros A1 A2 HequivA B1 B2 HequivB. split; intros val st H.
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