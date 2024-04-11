From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.
From MRC Require Import Tactics.

(* Open Scope general_fassertion_scope. *)

Theorem pctx_eq_semantics : forall pctx,
  exists eq_pdef,
    (pctx_map pctx) "="%string = Some eq_pdef /\
    eq_prel_sem (pdef_prel (eq_pdef)).
Proof.
  intros pctx. destruct pctx. destruct has_eq_sem as [eq_pdef H].
  exists eq_pdef. simpl. assumption.
Qed.

Theorem feval_not_true_iff : forall st fctx pctx A,
  feval st fctx pctx <[ ~ A ]> true <->
  feval st fctx pctx <[ A ]> false.
Proof with auto.
  intros st fctx pctx A. split.
  - intros H. inversion H; subst. apply Bool.negb_true_iff in H1. 
    subst...
  - intros H. replace true with (negb false)...
Qed.

Theorem feval_not_false_iff : forall st fctx pctx A,
  feval st fctx pctx <[ ~ A ]> false <->
  feval st fctx pctx <[ A ]> true.
Proof with auto.
  intros st fctx pctx A. split.
  - intros H. inversion H; subst. apply Bool.negb_false_iff in H1. 
    subst...
  - intros H. replace false with (negb true)...
Qed.

Theorem feval_and_true_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> true <->
  feval st fctx pctx A true /\ feval st fctx pctx B true.
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst...
  - intros [H1 H2]...
Qed.

Theorem feval_and_false_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A /\ B ]> false <->
  feval st fctx pctx A false \/ feval st fctx pctx B false.
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst...
  - intros [H | H]...
Qed.

Theorem feval_or_true_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A \/ B ]> true <->
  feval st fctx pctx A true \/ feval st fctx pctx B true.
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst; [left | right]...
  - intros [H | H]...
Qed.

Theorem feval_or_false_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A \/ B ]> false <->
  feval st fctx pctx A false /\ feval st fctx pctx B false.
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst. split...
  - intros [H1 H2]...
Qed.

Theorem feval_implication_true_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A => B ]> true <->
    feval st fctx pctx <[ A ]> false \/ 
    feval st fctx pctx <[ B ]> true.
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst...
  - intros [H | H]...
Qed.

Theorem feval_implication_false_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A => B ]> false <->
    feval st fctx pctx <[ A ]> true /\
    feval st fctx pctx <[ B ]> false.
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst...
  - intros [H1 H2]...
Qed.

Theorem feval_iff_true_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A <=> B ]> true <->
    (feval st fctx pctx <[ A ]> true /\ 
      feval st fctx pctx <[ B ]> true) \/
    (feval st fctx pctx <[ A ]> false /\ 
      feval st fctx pctx <[ B ]> false).
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst. destruct f1val, f2val...
    + simpl in H2. discriminate H2.
    + simpl in H2. discriminate.
  - intros [[H1 H2] | [H1 H2]].
    + replace true with (Bool.eqb true true)...
    + replace true with (Bool.eqb false false)...
Qed.

Theorem feval_iff_false_iff : forall st fctx pctx A B,
  feval st fctx pctx <[ A <=> B ]> false <->
    (feval st fctx pctx <[ A ]> true /\ 
      feval st fctx pctx <[ B ]> false) \/
    (feval st fctx pctx <[ A ]> false /\ 
      feval st fctx pctx <[ B ]> true).
Proof with auto.
  intros st fctx pctx A B. split.
  - intros H. inversion H; subst.
    destruct f1val, f2val... simpl in H2. discriminate H2.
  - intros [[H1 H2] | [H1 H2]].
    + replace false with (Bool.eqb true false)...
    + replace false with (Bool.eqb false true)...
Qed.

Theorem feval_exists_true_iff : forall st fctx pctx x A,
  feval st fctx pctx <[ exists x, A ]> true <->
  exists v, feval st fctx pctx (A[x \ v]) true.
Proof with auto.
  intros st fctx pctx x A. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_exists_false_iff : forall st fctx pctx x A,
  feval st fctx pctx <[ exists x, A ]> false <->
  forall v, feval st fctx pctx (A[x \ v]) false.
Proof with auto.
  intros st fctx pctx x A. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_forall_true_iff : forall st fctx pctx x A,
  feval st fctx pctx <[ forall x, A ]> true <->
  forall v, feval st fctx pctx (A[x \ v]) true.
Proof with auto.
  intros st fctx pctx x A. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_forall_false_iff : forall st fctx pctx x A,
  feval st fctx pctx <[ forall x, A ]> false <->
  exists v, feval st fctx pctx (A[x \ v]) false.
Proof with auto.
  intros st fctx pctx x A. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.


Theorem feval_inversion_false_true : forall st fctx pctx,
  ~ feval st fctx pctx <[ false ]> true.
Proof.
  intros st fctx pctx contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_inversion_true_false : forall {st} {fctx} {pctx},
  ~ feval st fctx pctx <[ true ]> false.
Proof.
  intros st fctx pctx contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_true_true : forall st fctx pctx,
  feval st fctx pctx <[ true ]> true.
Proof.
  intros st fctx pctx. apply FEval_Simple. apply SFEval_True.
Qed.

Theorem feval_false_false : forall st fctx pctx,
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
  - apply feval_not_true_iff in HT. 
    apply feval_not_false_iff in HF.
    apply IHA; assumption.
  - apply feval_and_true_iff in HT as [H0 H1].
    apply feval_and_false_iff in HF as [HF | HF]...
  - apply feval_or_false_iff in HF as [HF1 HF2].
    apply feval_or_true_iff in HT as [HT | HT]...
  - apply feval_implication_false_iff in HF as [HF1 HF2].
    apply feval_implication_true_iff in HT as [HT1 | HT1]...
  - apply feval_iff_true_iff in HT as [[HT1 HT2] | [HT1 HT2]];
    apply feval_iff_false_iff in HF as [[HF1 HF2] | [HF1 HF2]]...
  - inversion HT; subst. inversion HF; subst.
    destruct H1 as [v Hv]. specialize H2 with v.
    apply H with v...
  - inversion HT; subst. inversion HF; subst.
    destruct H2 as [v Hv]. specialize H1 with v.
    apply H with v...
Qed.

Theorem feval_eq_refl : forall t st fctx pctx,
  ~ feval st fctx pctx (F_Simple (AT_Pred "="%string [t; t])) false.
Proof with auto.
  intros t st fctx pctx contra. inversion contra; subst.
  inversion H0; subst. 
  destruct (pctx_eq_semantics pctx) as [eq_pdef [Heqp1 Heqp2]].
  rewrite Heqp1 in H2. inversion H2. subst pdef.
  destruct (Heqp2 st fctx) as [Heqp_refl _].
  specialize (Heqp_refl t).
  assert (feval st fctx pctx <[ t = t ]> true).
  { apply FEval_Simple. apply SFEval_Pred with eq_pdef...
    destruct eq_pdef.
    apply Pred_Eval with n_params prel Hfnal... }
  destruct (feval_functional _ _ _ _ H contra).
Qed.  

Theorem higher_qrank__subst_eq : forall A x a r',
  quantifier_rank A <= r' ->
    subst_formula_qrank (quantifier_rank A) A x a = 
    subst_formula_qrank r' A x a.
Proof with auto.
  intros A.   
  apply (rank_induction (fun P => forall x a r',
    quantifier_rank P <= r' ->
    subst_formula_qrank (quantifier_rank P) P x a = 
    subst_formula_qrank r' P x a))
    with (S (rank A))...
  clear A. intros r IH. destruct A; intros Hr x0 a r' H.
  - destruct r'...
  - simpl.
    destruct (quantifier_rank A) eqn:HrA; destruct r' eqn:Hr'; 
      simpl in *...
    + fold_qrank_subst 0 A x0 a. fold_qrank_subst (S n) A x0 a.
      f_equal. rewrite <- HrA. apply IH with (rank A); lia...
    + lia.
    + fold_qrank_subst (S n) A x0 a.
      fold_qrank_subst (S n0) A x0 a.
      f_equal. rewrite <- HrA. apply IH with (rank A); lia.
  - simpl. 
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank A2) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- assert (quantifier_rank A1 = 0) by lia. rewrite <- H0.
          symmetry. apply IH with (rank A1); lia.
        -- rewrite <- HrA. apply IH with (rank A2); lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                        subst_formula_qrank (S n) A1 x0 a).
            { apply IH with (rank A1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                         subst_formula_qrank (S n0) A1 x0 a).
            { apply IH with (rank A1); lia. }
            rewrite <- Heq1...
        -- rewrite <- HrA. apply IH with (rank A2); lia.
    + destruct (quantifier_rank A1) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- rewrite <- H2. apply IH with (rank A2); lia.
      * lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                        subst_formula_qrank (S n) A2 x0 a).
            { apply IH with (rank A2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                         subst_formula_qrank (S n0) A2 x0 a).
            { apply IH with (rank A2); lia. }
            rewrite <- Heq1...
  - simpl. 
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank A2) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- assert (quantifier_rank A1 = 0) by lia. rewrite <- H0.
          symmetry. apply IH with (rank A1); lia.
        -- rewrite <- HrA. apply IH with (rank A2); lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                        subst_formula_qrank (S n) A1 x0 a).
            { apply IH with (rank A1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                         subst_formula_qrank (S n0) A1 x0 a).
            { apply IH with (rank A1); lia. }
            rewrite <- Heq1...
        -- rewrite <- HrA. apply IH with (rank A2); lia.
    + destruct (quantifier_rank A1) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- rewrite <- H2. apply IH with (rank A2); lia.
      * lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                        subst_formula_qrank (S n) A2 x0 a).
            { apply IH with (rank A2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                         subst_formula_qrank (S n0) A2 x0 a).
            { apply IH with (rank A2); lia. }
            rewrite <- Heq1...   
  - simpl. 
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank A2) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- assert (quantifier_rank A1 = 0) by lia. rewrite <- H0.
          symmetry. apply IH with (rank A1); lia.
        -- rewrite <- HrA. apply IH with (rank A2); lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                        subst_formula_qrank (S n) A1 x0 a).
            { apply IH with (rank A1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                         subst_formula_qrank (S n0) A1 x0 a).
            { apply IH with (rank A1); lia. }
            rewrite <- Heq1...
        -- rewrite <- HrA. apply IH with (rank A2); lia.
    + destruct (quantifier_rank A1) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- rewrite <- H2. apply IH with (rank A2); lia.
      * lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                        subst_formula_qrank (S n) A2 x0 a).
            { apply IH with (rank A2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                         subst_formula_qrank (S n0) A2 x0 a).
            { apply IH with (rank A2); lia. }
            rewrite <- Heq1...                 
  - simpl. 
    assert (HMax := 
      (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank A2) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- assert (quantifier_rank A1 = 0) by lia. rewrite <- H0.
          symmetry. apply IH with (rank A1); lia.
        -- rewrite <- HrA. apply IH with (rank A2); lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                        subst_formula_qrank (S n) A1 x0 a).
            { apply IH with (rank A1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A1) A1 x0 a =
                         subst_formula_qrank (S n0) A1 x0 a).
            { apply IH with (rank A1); lia. }
            rewrite <- Heq1...
        -- rewrite <- HrA. apply IH with (rank A2); lia.
    + destruct (quantifier_rank A1) eqn:HrA; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a.
        fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
        f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- rewrite <- H2. apply IH with (rank A2); lia.
      * lia.
      * fold_qrank_subst (S n0) A2 x0 a.
        fold_qrank_subst (S n0) A1 x0 a.
        fold_qrank_subst (S n) A2 x0 a.
        fold_qrank_subst (S n) A1 x0 a. f_equal.
        -- rewrite <- HrA. apply IH with (rank A1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                        subst_formula_qrank (S n) A2 x0 a).
            { apply IH with (rank A2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank A2) A2 x0 a =
                         subst_formula_qrank (S n0) A2 x0 a).
            { apply IH with (rank A2); lia. }
            rewrite <- Heq1...
  - destruct r'; simpl in *.
    + lia.
    + fold_qrank_subst (S r') A x (fresh_quantifier x A a).
      fold_qrank_subst (S (quantifier_rank A)) A x (fresh_quantifier x A a).
      f_equal.
      destruct (String.eqb_spec x x0); try lia...
      f_equal.
      assert (subst_formula_qrank (S (quantifier_rank A)) A x (fresh_quantifier x A a)
            = subst_formula_qrank (quantifier_rank A) A x (fresh_quantifier x A a)).
      {
        symmetry. apply IH with (m:=rank A); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_qrank (S r') A x (fresh_quantifier x A a)
            = subst_formula_qrank (quantifier_rank A) A x (fresh_quantifier x A a)).
      {
        symmetry. apply IH with (m:=rank A); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_qrank (quantifier_rank A) A x (fresh_quantifier x A a))
        as inner.
      assert (HsameInnerA := subst_preserves_structure A x (fresh_quantifier x A a) (quantifier_rank A)). 
      deduce_rank_eq HsameInnerA.   
      replace (quantifier_rank A) with (quantifier_rank inner).
      apply IH with (m:=rank A); try rewrite Heqinner; lia...
      rewrite Heqinner...
  - destruct r'; simpl in *.
    + lia.
    + fold_qrank_subst (S r') A x (fresh_quantifier x A a).
      fold_qrank_subst (S (quantifier_rank A)) A x (fresh_quantifier x A a).
      f_equal.
      destruct (String.eqb_spec x x0); try lia...
      f_equal.
      assert (subst_formula_qrank (S (quantifier_rank A)) A x (fresh_quantifier x A a)
            = subst_formula_qrank (quantifier_rank A) A x (fresh_quantifier x A a)).
      {
        symmetry. apply IH with (m:=rank A); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_qrank (S r') A x (fresh_quantifier x A a)
            = subst_formula_qrank (quantifier_rank A) A x (fresh_quantifier x A a)).
      {
        symmetry. apply IH with (m:=rank A); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_qrank (quantifier_rank A) A x (fresh_quantifier x A a))
        as inner.
      assert (HsameInnerA := subst_preserves_structure A x (fresh_quantifier x A a) (quantifier_rank A)). 
      deduce_rank_eq HsameInnerA.   
      replace (quantifier_rank A) with (quantifier_rank inner).
      apply IH with (m:=rank A); try rewrite Heqinner; lia...
      rewrite Heqinner...
Qed.

Theorem simpl_subst_simple_formula : forall sf x a,
  formula_subst (F_Simple sf) x a =
  F_Simple (subst_simple_formula sf x a).
Proof with auto.
  intros A x a. unfold formula_subst. simpl. reflexivity.
Qed.

Theorem simpl_subst_not : forall A x a,
  <[ (~ A)[x \ a] ]> = <[ ~ (A[x \ a]) ]>.
Proof with auto.
  intros A x a. unfold formula_subst.
  assert (H: quantifier_rank <[ ~A ]> = quantifier_rank A).
  { reflexivity. } rewrite H. clear H. destruct (quantifier_rank A);
    reflexivity.
Qed.

Theorem simpl_subst_and : forall A B x a,
  <[ (A /\ B)[x \ a] ]> = <[ (A[x \ a]) /\ (B[x \ a])]>.
Proof with auto.
  intros A B x a. unfold formula_subst.
  assert (HMax := 
    (Nat.max_spec (quantifier_rank A) (quantifier_rank B))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <[ A /\ B ]> = quantifier_rank B).
    { simpl. lia. } rewrite H. destruct (quantifier_rank B) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) B x a. 
    fold_qrank_subst (S n) A x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <[ A /\ B ]> = quantifier_rank A).
    { simpl. lia. } rewrite H. destruct (quantifier_rank A) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) B x a. 
      fold_qrank_subst (S n) A x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.
    
Theorem simpl_subst_or : forall A B x a,
  <[ (A \/ B)[x \ a] ]> = <[ (A[x \ a]) \/ (B[x \ a])]>.
Proof with auto.
  intros A B x a. unfold formula_subst.
  assert (HMax := 
    (Nat.max_spec (quantifier_rank A) (quantifier_rank B))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <[ A \/ B ]> = quantifier_rank B).
    { simpl. lia. } rewrite H. destruct (quantifier_rank B) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) B x a. 
    fold_qrank_subst (S n) A x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <[ A \/ B ]> = quantifier_rank A).
    { simpl. lia. } rewrite H. destruct (quantifier_rank A) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) B x a. 
      fold_qrank_subst (S n) A x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_implication : forall A B x a,
  <[ (A => B)[x \ a] ]> = <[ (A[x \ a]) => (B[x \ a])]>.
Proof with auto.
  intros A B x a. unfold formula_subst.
  assert (HMax := 
    (Nat.max_spec (quantifier_rank A) (quantifier_rank B))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <[ A => B ]> = quantifier_rank B).
    { simpl. lia. } rewrite H. destruct (quantifier_rank B) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) B x a. 
    fold_qrank_subst (S n) A x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <[ A => B ]> = quantifier_rank A).
    { simpl. lia. } rewrite H. destruct (quantifier_rank A) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) B x a. 
      fold_qrank_subst (S n) A x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_iff : forall A B x a,
  <[ (A <=> B)[x \ a] ]> = <[ (A[x \ a]) <=> (B[x \ a])]>.
Proof with auto.
  intros A B x a. unfold formula_subst.
  assert (HMax := 
    (Nat.max_spec (quantifier_rank A) (quantifier_rank B))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <[ A <=> B ]> = quantifier_rank B).
    { simpl. lia. } rewrite H. destruct (quantifier_rank B) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) B x a. 
    fold_qrank_subst (S n) A x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <[ A <=> B ]> = quantifier_rank A).
    { simpl. lia. } rewrite H. destruct (quantifier_rank A) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) B x a. 
      fold_qrank_subst (S n) A x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_exists_neq : forall y A x a,
  y <> x ->
  let y' := fresh_quantifier y A a in
  <[ (exists y, A)[x\a] ]> = <[ (exists y', A[y\y'][x\a]) ]>.
Proof.
  intros y A x a Hneq. simpl. unfold formula_subst. simpl.
  apply String.eqb_neq in Hneq. rewrite Hneq. f_equal.
  fold_qrank_subst (S (quantifier_rank A)) A y (fresh_quantifier y A a).
  f_equal.
  - assert (H:=subst_preserves_structure A y 
      (fresh_quantifier y A a) (quantifier_rank A)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_exists_same : forall y A x a,
  y = x ->
  <[ (exists y, A)[x\a] ]> = <[ exists y, A ]>.
Proof with auto.
  intros y A x a Heq. unfold formula_subst. simpl.
  apply String.eqb_eq in Heq. rewrite Heq...
Qed.

Theorem simpl_subst_forall_neq : forall y A x a,
  y <> x ->
  let y' := fresh_quantifier y A a in
  <[ (forall y, A)[x\a] ]> = <[ (forall y', A[y\y'][x\a]) ]>.
Proof.
  intros y A x a Hneq. simpl. unfold formula_subst. simpl.
  apply String.eqb_neq in Hneq. rewrite Hneq. f_equal.
  fold_qrank_subst (S (quantifier_rank A)) A y (fresh_quantifier y A a).
  f_equal.
  - assert (H:=subst_preserves_structure A y 
      (fresh_quantifier y A a) (quantifier_rank A)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_forall_same : forall y A x a,
  y = x ->
  <[ (forall y, A)[x\a] ]> = <[ forall y, A ]>.
Proof with auto.
  intros y A x a Heq. unfold formula_subst. simpl.
  apply String.eqb_eq in Heq. rewrite Heq...
Qed.
    

Theorem subst_eq_congr : forall st fctx pctx A x t u b,
  feval st fctx pctx <[ t = u ]> true ->
  feval st fctx pctx <[ A[x\t] ]> b ->
  feval st fctx pctx <[ A[x\u] ]> b.
Proof with auto.
Admitted.

Theorem subst_term_id_when_not_in_term : forall x t a,
  appears_in_term x t = false ->
  (subst_term t x a) = t.
Proof with auto. 
  intros x t a H. induction t...
  - simpl. destruct (String.eqb_spec x0 x)... rewrite e in H.
    simpl in H. rewrite String.eqb_refl in H. discriminate H.
  - simpl. f_equal. induction args... simpl in H. 
    apply Bool.orb_false_iff in H as [H1 H2].
    simpl. f_equal.
    + apply H0... simpl...
    + apply IHargs.
      * intros arg HIn Hap. apply H0... simpl...
      * simpl. apply H2.
Qed.