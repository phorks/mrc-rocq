From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.
From MRC Require Import Tactics.
From stdpp Require Import gmap fin_maps.

(* TODO: Change this to explain why LEM is required for specification power *)
(* Since our function and predicate symbol interpretations are
  relations instead of computable functions, our evaluation
  process might fail evaluating some formulas; i.e., it might
  not evaluate a formula as either false or true. In such cases
  (φ \/ ~ φ) does not hold.

  Example: P(0, 1), when pctx does not contain P, is neither
    true nor false. Meanwhile, even if the symbol has an
    interpretation in pctx, it might be the case that neither
    (0, 1) |-> true nor (0, 1) |-> false are in P.

  We admit this as an axiom, since the book includes it.
  *)
Axiom feval_lem : forall M σ φ, feval M σ φ \/ ~ feval M σ φ.

Theorem feval_dec : forall M σ φ, Decidable.decidable (feval M σ φ).
Proof. exact feval_lem. Qed.

(* Theorem pctx_eq_semantics : forall pctx, *)
(*   exists eq_pdef, *)
(*     (pctx_map pctx) "="%string = Some eq_pdef /\ *)
(*     eq_prel_sem (pdef_prel (eq_pdef)). *)
(* Proof. *)
(*   intros pctx. destruct pctx. destruct has_eq_sem as [eq_pdef H]. *)
(*   exists eq_pdef. simpl. assumption. *)
(* Qed. *)

(* φxiom fresh_quantifier_spec : forall x φ a, *)
(*   (appears_in_term x a = false /\ x = fresh_quantifier x φ a) \/ *)
(*   (appears_in_term (fresh_quantifier x φ a) a = false /\ *)
(*     (appears_in_term x a = true -> *)
(*       is_free_in (fresh_quantifier x φ a) φ = false)). *)
(* This doesn't actually hold, if [a] contains all lowercase
    ascii characters, x' in a appear as free *)

(* TODO: Change this to explain why LEM is required for specification power *)
(* Since our function and predicate symbol interpretations are
  relations instead of computable functions, our evaluation
  process might fail evaluating some formulas; i.e., it might
  not evaluate a formula as either false or true. In such cases
  (φ \/ ~ φ) does not hold.

  Example: P(0, 1), when pctx does not contain P, is neither
    true nor false. Meanwhile, even if the symbol has an
    interpretation in pctx, it might be the case that neither
    (0, 1) |-> true nor (0, 1) |-> false are in P.

  We admit this as an axiom, since the book includes it.
  *)
Theorem feval_dne : forall M σ φ,
  ~ ~ feval M σ φ <-> feval M σ φ.
Proof with auto.
  intros.
  apply (Decidable.not_not_iff _ (feval_dec M σ φ)).
Qed.

Theorem higher_qrank__subst_eq : forall φ x a r',
  quantifier_rank φ <= r' ->
    subst_formula_qrank (quantifier_rank φ) φ x a =
    subst_formula_qrank r' φ x a.
Proof with auto.
  induction φ using formula_rank_ind.
  destruct φ; intros x0 a r' Hrank; subst.
  - destruct r'...
  - simpl. destruct (quantifier_rank φ) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *; subst...
    + fold_qrank_subst 0 φ x0 a. fold_qrank_subst (S n) φ x0 a.
      f_equal. rewrite <- Hrφ. apply H with (rank φ); lia...
    + lia.
    + fold_qrank_subst (S n) φ x0 a.
      fold_qrank_subst (S n0) φ x0 a.
      f_equal. rewrite <- Hrφ. apply H with (rank φ); lia.
  - simpl.
    assert (HMax :=
      (Nat.max_spec (quantifier_rank φ1) (quantifier_rank φ2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank φ2) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a.
        fold_qrank_subst 0 φ2 x0 a. fold_qrank_subst 0 φ1 x0 a.
        f_equal.
        -- assert (quantifier_rank φ1 = 0) by lia. rewrite <- H0.
          symmetry. apply H with (rank φ1); lia.
        -- rewrite <- Hrφ. apply H with (rank φ2); lia.
      * fold_qrank_subst (S n0) φ2 x0 a.
        fold_qrank_subst (S n0) φ1 x0 a.
        fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank φ1) φ1 x0 a =
                        subst_formula_qrank (S n) φ1 x0 a).
            { apply H with (rank φ1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank φ1) φ1 x0 a =
                         subst_formula_qrank (S n0) φ1 x0 a).
            { apply H with (rank φ1); lia. }
            rewrite <- Heq1...
        -- rewrite <- Hrφ. apply H with (rank φ2); lia.
    + destruct (quantifier_rank φ1) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a.
        fold_qrank_subst 0 φ2 x0 a. fold_qrank_subst 0 φ1 x0 a.
        f_equal.
        -- rewrite <- Hrφ. apply H with (rank φ1); lia.
        -- rewrite <- H2. apply H with (rank φ2); lia.
      * lia.
      * fold_qrank_subst (S n0) φ2 x0 a.
        fold_qrank_subst (S n0) φ1 x0 a.
        fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a. f_equal.
        -- rewrite <- Hrφ. apply H with (rank φ1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank φ2) φ2 x0 a =
                        subst_formula_qrank (S n) φ2 x0 a).
            { apply H with (rank φ2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank φ2) φ2 x0 a =
                         subst_formula_qrank (S n0) φ2 x0 a).
            { apply H with (rank φ2); lia. }
            rewrite <- Heq1...
  - simpl.
    assert (HMax :=
      (Nat.max_spec (quantifier_rank φ1) (quantifier_rank φ2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank φ2) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a.
        fold_qrank_subst 0 φ2 x0 a. fold_qrank_subst 0 φ1 x0 a.
        f_equal.
        -- assert (quantifier_rank φ1 = 0) by lia. rewrite <- H0.
          symmetry. apply H with (rank φ1); lia.
        -- rewrite <- Hrφ. apply H with (rank φ2); lia.
      * fold_qrank_subst (S n0) φ2 x0 a.
        fold_qrank_subst (S n0) φ1 x0 a.
        fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank φ1) φ1 x0 a =
                        subst_formula_qrank (S n) φ1 x0 a).
            { apply H with (rank φ1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank φ1) φ1 x0 a =
                         subst_formula_qrank (S n0) φ1 x0 a).
            { apply H with (rank φ1); lia. }
            rewrite <- Heq1...
        -- rewrite <- Hrφ. apply H with (rank φ2); lia.
    + destruct (quantifier_rank φ1) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a.
        fold_qrank_subst 0 φ2 x0 a. fold_qrank_subst 0 φ1 x0 a.
        f_equal.
        -- rewrite <- Hrφ. apply H with (rank φ1); lia.
        -- rewrite <- H2. apply H with (rank φ2); lia.
      * lia.
      * fold_qrank_subst (S n0) φ2 x0 a.
        fold_qrank_subst (S n0) φ1 x0 a.
        fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a. f_equal.
        -- rewrite <- Hrφ. apply H with (rank φ1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank φ2) φ2 x0 a =
                        subst_formula_qrank (S n) φ2 x0 a).
            { apply H with (rank φ2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank φ2) φ2 x0 a =
                         subst_formula_qrank (S n0) φ2 x0 a).
            { apply H with (rank φ2); lia. }
            rewrite <- Heq1...
  - simpl.
    assert (HMax :=
      (Nat.max_spec (quantifier_rank φ1) (quantifier_rank φ2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
    + destruct (quantifier_rank φ2) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *...
      * lia.
      * fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a.
        fold_qrank_subst 0 φ2 x0 a. fold_qrank_subst 0 φ1 x0 a.
        f_equal.
        -- assert (quantifier_rank φ1 = 0) by lia. rewrite <- H0.
          symmetry. apply H with (rank φ1); lia.
        -- rewrite <- Hrφ. apply H with (rank φ2); lia.
      * fold_qrank_subst (S n0) φ2 x0 a.
        fold_qrank_subst (S n0) φ1 x0 a.
        fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a. f_equal.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank φ1) φ1 x0 a =
                        subst_formula_qrank (S n) φ1 x0 a).
            { apply H with (rank φ1); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank φ1) φ1 x0 a =
                         subst_formula_qrank (S n0) φ1 x0 a).
            { apply H with (rank φ1); lia. }
            rewrite <- Heq1...
        -- rewrite <- Hrφ. apply H with (rank φ2); lia.
    + destruct (quantifier_rank φ1) eqn:Hrφ; destruct r' eqn:Hr';
      simpl in *...
      * fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a.
        fold_qrank_subst 0 φ2 x0 a. fold_qrank_subst 0 φ1 x0 a.
        f_equal.
        -- rewrite <- Hrφ. apply H with (rank φ1); lia.
        -- rewrite <- H2. apply H with (rank φ2); lia.
      * lia.
      * fold_qrank_subst (S n0) φ2 x0 a.
        fold_qrank_subst (S n0) φ1 x0 a.
        fold_qrank_subst (S n) φ2 x0 a.
        fold_qrank_subst (S n) φ1 x0 a. f_equal.
        -- rewrite <- Hrφ. apply H with (rank φ1); lia.
        -- assert (Heq1: subst_formula_qrank (quantifier_rank φ2) φ2 x0 a =
                        subst_formula_qrank (S n) φ2 x0 a).
            { apply H with (rank φ2); lia. }
           assert (Heq2: subst_formula_qrank (quantifier_rank φ2) φ2 x0 a =
                         subst_formula_qrank (S n0) φ2 x0 a).
            { apply H with (rank φ2); lia. }
            rewrite <- Heq1...
  - destruct r'; simpl in *.
    + lia.
    + fold_qrank_subst (S r') φ x (fresh_quantifier x φ a).
      fold_qrank_subst (S (quantifier_rank φ)) φ x (fresh_quantifier x φ a).
      f_equal.
      destruct (String.eqb_spec x x0); try lia...
      f_equal.
      assert (subst_formula_qrank (S (quantifier_rank φ)) φ x (fresh_quantifier x φ a)
            = subst_formula_qrank (quantifier_rank φ) φ x (fresh_quantifier x φ a)).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_qrank (S r') φ x (fresh_quantifier x φ a)
            = subst_formula_qrank (quantifier_rank φ) φ x (fresh_quantifier x φ a)).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_qrank (quantifier_rank φ) φ x (fresh_quantifier x φ a))
        as inner.
      assert (HsameInnerφ := subst_preserves_shape φ x (fresh_quantifier x φ a) (quantifier_rank φ)).
      deduce_rank_eq HsameInnerφ.
      replace (quantifier_rank φ) with (quantifier_rank inner).
      apply H with (m:=rank φ); try rewrite Heqinner; lia...
      rewrite Heqinner...
  - destruct r'; simpl in *.
    + lia.
    + fold_qrank_subst (S r') φ x (fresh_quantifier x φ a).
      fold_qrank_subst (S (quantifier_rank φ)) φ x (fresh_quantifier x φ a).
      f_equal.
      destruct (String.eqb_spec x x0); try lia...
      f_equal.
      assert (subst_formula_qrank (S (quantifier_rank φ)) φ x (fresh_quantifier x φ a)
            = subst_formula_qrank (quantifier_rank φ) φ x (fresh_quantifier x φ a)).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_qrank (S r') φ x (fresh_quantifier x φ a)
            = subst_formula_qrank (quantifier_rank φ) φ x (fresh_quantifier x φ a)).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_qrank (quantifier_rank φ) φ x (fresh_quantifier x φ a))
        as inner.
      assert (HsameInnerφ := subst_preserves_shape φ x (fresh_quantifier x φ a) (quantifier_rank φ)).
      deduce_rank_eq HsameInnerφ.
      replace (quantifier_rank φ) with (quantifier_rank inner).
      apply H with (m:=rank φ); try rewrite Heqinner; lia...
      rewrite Heqinner...
Qed.

Theorem simpl_subst_simple_formula : forall sf x a,
  formula_subst (F_Simple sf) x a =
  F_Simple (subst_simple_formula sf x a).
Proof with auto.
  intros φ x a. unfold formula_subst. simpl. reflexivity.
Qed.

Theorem simpl_subst_not : forall φ x a,
  <! (~ φ)[x \ a] !> = <! ~ (φ[x \ a]) !>.
Proof with auto.
  intros φ x a. unfold formula_subst.
  assert (H: quantifier_rank <! ~φ !> = quantifier_rank φ).
  { reflexivity. } rewrite H. clear H. destruct (quantifier_rank φ);
    reflexivity.
Qed.

Theorem simpl_subst_and : forall φ ψ x a,
  <! (φ /\ ψ)[x \ a] !> = <! (φ[x \ a]) /\ (ψ[x \ a])!>.
Proof with auto.
  intros φ ψ x a. unfold formula_subst.
  assert (HMax :=
    (Nat.max_spec (quantifier_rank φ) (quantifier_rank ψ))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <! φ /\ ψ !> = quantifier_rank ψ).
    { simpl. lia. } rewrite H. destruct (quantifier_rank ψ) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) ψ x a.
    fold_qrank_subst (S n) φ x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <! φ /\ ψ !> = quantifier_rank φ).
    { simpl. lia. } rewrite H. destruct (quantifier_rank φ) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) ψ x a.
      fold_qrank_subst (S n) φ x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_or : forall φ ψ x a,
  <! (φ \/ ψ)[x \ a] !> = <! (φ[x \ a]) \/ (ψ[x \ a])!>.
Proof with auto.
  intros φ ψ x a. unfold formula_subst.
  assert (HMax :=
    (Nat.max_spec (quantifier_rank φ) (quantifier_rank ψ))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <! φ \/ ψ !> = quantifier_rank ψ).
    { simpl. lia. } rewrite H. destruct (quantifier_rank ψ) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) ψ x a.
    fold_qrank_subst (S n) φ x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <! φ \/ ψ !> = quantifier_rank φ).
    { simpl. lia. } rewrite H. destruct (quantifier_rank φ) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) ψ x a.
      fold_qrank_subst (S n) φ x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_implication : forall φ ψ x a,
  <! (φ => ψ)[x \ a] !> = <! (φ[x \ a]) => (ψ[x \ a])!>.
Proof with auto.
  intros φ ψ x a. unfold formula_subst.
  assert (HMax :=
    (Nat.max_spec (quantifier_rank φ) (quantifier_rank ψ))).
  destruct HMax as [[H1 H2] | [H1 H2]].
  - assert (H: quantifier_rank <! φ => ψ !> = quantifier_rank ψ).
    { simpl. lia. } rewrite H. destruct (quantifier_rank ψ) eqn:E;
       try lia...
    simpl. fold_qrank_subst (S n) ψ x a.
    fold_qrank_subst (S n) φ x a. f_equal.
    symmetry. apply higher_qrank__subst_eq. lia.
  - assert (H: quantifier_rank <! φ => ψ !> = quantifier_rank φ).
    { simpl. lia. } rewrite H. destruct (quantifier_rank φ) eqn:E;
       try lia...
    + inversion H1. rewrite H3. simpl...
    + simpl. fold_qrank_subst (S n) ψ x a.
      fold_qrank_subst (S n) φ x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_iff : forall φ ψ x a,
  <! (φ <=> ψ)[x \ a] !> = <! (φ[x \ a]) <=> (ψ[x \ a])!>.
Proof with auto.
  intros. rewrite simpl_subst_and. do 2 rewrite simpl_subst_implication...
Qed.

Theorem simpl_subst_exists_ne : forall y φ x a,
  y <> x ->
  let y' := fresh_quantifier y φ a in
  <! (exists y, φ)[x\a] !> = <! (exists y', φ[y\y'][x\a]) !>.
Proof.
  intros y φ x a Hneq. simpl. unfold formula_subst. simpl.
  apply String.eqb_neq in Hneq. rewrite Hneq. f_equal.
  fold_qrank_subst (S (quantifier_rank φ)) φ y (fresh_quantifier y φ a).
  f_equal.
  - assert (H:=subst_preserves_shape φ y
      (fresh_quantifier y φ a) (quantifier_rank φ)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_exists_eq : forall y φ x a,
  y = x ->
  <! (exists y, φ)[x\a] !> = <! exists y, φ !>.
Proof with auto.
  intros y φ x a Heq. unfold formula_subst. simpl.
  apply String.eqb_eq in Heq. rewrite Heq...
Qed.

Theorem simpl_subst_forall_ne : forall y φ x a,
  y <> x ->
  let y' := fresh_quantifier y φ a in
  <! (forall y, φ)[x\a] !> = <! (forall y', φ[y\y'][x\a]) !>.
Proof.
  intros y φ x a Hneq. simpl. unfold formula_subst. simpl.
  apply String.eqb_neq in Hneq. rewrite Hneq. f_equal.
  fold_qrank_subst (S (quantifier_rank φ)) φ y (fresh_quantifier y φ a).
  f_equal.
  - assert (H:=subst_preserves_shape φ y
      (fresh_quantifier y φ a) (quantifier_rank φ)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_forall_eq : forall y φ x a,
  y = x ->
  <! (forall y, φ)[x\a] !> = <! forall y, φ !>.
Proof with auto.
  intros y φ x a Heq. unfold formula_subst. simpl.
  apply String.eqb_eq in Heq. rewrite Heq...
Qed.


Theorem simpl_subst_forall : forall y φ x a,
    y = x ->
    (y = x -> <! (forall y, φ)[x\a] !> = <! forall y, φ !>) /\
      (y <> x ->
       let y' := fresh_quantifier y φ a in
       <! (forall y, φ)[x\a] !> = <! (forall y', φ[y\y'][x\a]) !>).
Proof with auto.
  intros. split.
  - apply simpl_subst_forall_eq.
  - apply simpl_subst_forall_ne.
Qed.

Theorem fresh_quantifier_not_in_term : forall φ x t,
    negb $ appears_in_term x t ->
    fresh_quantifier x φ t = x.
Proof.
  intros φ x t H. unfold fresh_quantifier.
  apply negb_prop_elim in H. unfold not in H.
  apply Is_true_false_1 in H. rewrite H. reflexivity.
Qed.

Theorem fresh_quantifier_for_var_ne : forall φ x x',
    x <> x' ->
    fresh_quantifier x φ x' = x.
Proof with auto.
  intros φ x x' H.
  apply fresh_quantifier_not_in_term. simpl. apply String.eqb_neq in H.
  rewrite String.eqb_sym in H. rewrite H. simpl...
Qed.

Theorem fresh_quantifier_for_value_term : forall φ x (v : value),
    fresh_quantifier x φ v = x.
Proof with auto.
  intros φ x v. apply fresh_quantifier_not_in_term. simpl...
Qed.

Theorem fresh_quantifier_ne : forall φ x t,
    fresh_quantifier x φ t <> x -> appears_in_term x t.
Proof with auto.
  intros φ x t. destruct (appears_in_term x t) eqn:H...
  unfold fresh_quantifier. rewrite H. contradiction.
Qed.

Theorem subst_same_term : forall t x,
    subst_term t x x = t.
Proof with auto.
  intros t x. induction t using term_ind; simpl...
  - destruct (String.eqb_spec x0 x)... inversion e...
  - f_equal. induction args; simpl... f_equal.
    * apply H. simpl. left...
    * apply IHargs. intros. apply H. simpl. right...
Qed.
Hint Resolve subst_same_term : core.

Theorem subst_same_sf : forall sf x,
    subst_simple_formula sf x x = sf.
Proof with auto.
  intros sf x. destruct sf...
  - simpl... f_equal...
  - simpl. f_equal. induction args... rewrite map_cons. f_equal...
Qed.
Hint Resolve subst_same_sf : core.

(* TODO: rename this *)
Theorem subst_same_formula : forall φ x,
    formula_subst φ x x = φ.
Proof with auto.
  induction φ; intros x₀.
  - rewrite simpl_subst_simple_formula. rewrite subst_same_sf...
  - rewrite simpl_subst_not. f_equal...
  - rewrite simpl_subst_and. f_equal...
  - rewrite simpl_subst_or. f_equal...
  - rewrite simpl_subst_implication. f_equal...
  - destruct (String.eqb_spec x₀ x).
    + rewrite simpl_subst_exists_eq...
    + rewrite simpl_subst_exists_ne... rewrite fresh_quantifier_for_var_ne...
      f_equal. etrans.
      * apply H. unfold formula_subst. apply shape_eq_sym. apply subst_preserves_shape.
      * apply H. apply shape_eq_refl.
  - destruct (String.eqb_spec x₀ x).
    + rewrite simpl_subst_forall_eq...
    + rewrite simpl_subst_forall_ne... rewrite fresh_quantifier_for_var_ne...
      f_equal. etrans.
      * apply H. unfold formula_subst. apply shape_eq_sym. apply subst_preserves_shape.
      * apply H. apply shape_eq_refl.
Qed.
Hint Resolve subst_same_formula : core.

Theorem subst_term_not_free : forall t x t',
    negb $ appears_in_term x t ->
    subst_term t x t' = t.
Proof with auto.
  intros t x t' H. induction t using term_ind; simpl...
  - simpl in H. destruct (String.eqb_spec x0 x)... simpl in H. contradiction.
  - simpl in H. f_equal. induction args... rewrite map_cons. simpl in H.
    rewrite negb_orb in H. apply andb_prop_elim in H as [? ?]. f_equal.
    * apply H0... simpl. left...
    * apply IHargs... intros. apply H0... simpl. right...
Qed.

Theorem subst_commute_term : forall t x₁ t₁ x₂ t₂,
    x₁ <> x₂ ->
    negb $ appears_in_term x₁ t₂ ->
    negb $ appears_in_term x₂ t₁ ->
    subst_term (subst_term t x₁ t₁) x₂ t₂ = subst_term (subst_term t x₂ t₂) x₁ t₁.
Proof with auto.
  intros t x₁ t₁ x₂ t₂ Hneq H₁ H₂. induction t using term_ind; simpl...
  - destruct (String.eqb_spec x x₁); destruct (String.eqb_spec x x₂); subst.
    + contradiction.
    + simpl. rewrite String.eqb_refl. apply subst_term_not_free...
    + simpl. rewrite String.eqb_refl. symmetry. apply subst_term_not_free...
    + simpl. rewrite (proj2 (String.eqb_neq x x₁) n). rewrite (proj2 (String.eqb_neq x x₂) n0)...
  - f_equal. induction args; simpl... f_equal.
    + apply H. left...
    + apply IHargs. intros. apply H. right...
Qed.

Theorem subst_commute_sf : forall sf x₁ t₁ x₂ t₂,
    x₁ <> x₂ ->
    negb $ appears_in_term x₁ t₂ ->
    negb $ appears_in_term x₂ t₁ ->
    subst_simple_formula (subst_simple_formula sf x₁ t₁) x₂ t₂ =
      subst_simple_formula (subst_simple_formula sf x₂ t₂) x₁ t₁.
Proof with auto.
  intros. destruct sf; simpl...
  - f_equal; auto using subst_commute_term.
  - f_equal. induction args... repeat rewrite map_cons. f_equal... apply subst_commute_term...
Qed.
(* NOTE: Subst doesn't commute in feval:
          consider (∃ x, x₁ = x)[x₁ \ x][x₂ \ y] and (∃ x, x₁ = x)[x₂ \ y][x₁ \ x]:
          its behavior depends on how fresh_quantifier picks a new quantifier
          LHS:  since to avoid capture, x must be renamed in theree exists,
                if the algorithm picks x₂ (it can because it is free in both the body and the value being substituted for (x))
                then LHS becomes:  (∃ x₂, x = x₂)[x₂\y] ≡ (∃) )*)

Lemma is_free_in_term_iff : forall x t,
    Is_true $ appears_in_term x t <-> (x ∈ term_fvars t).
Proof with auto.
  intros x t. induction t; simpl.
  - rewrite elem_of_empty... 
  - destruct (String.eqb_spec x0 x); subst...
    + rewrite elem_of_singleton. split...
    + rewrite elem_of_singleton. split... contradiction.
  - rename H into IH. induction args.
    + simpl. rewrite elem_of_empty. split...
    + simpl. destruct (appears_in_term x a) eqn:E.
      * simpl. split... intros _. apply elem_of_union_l. apply IH... left...
      * simpl. split; intros H.
        -- apply elem_of_union_r. apply IHargs... intros. apply IH. right...
        -- apply elem_of_union in H. destruct H.
           ++ apply IH in H. rewrite E in H. contradiction. left...
           ++ apply IHargs... intros. apply IH. right...
Qed.

Lemma is_free_in_sf_iff : forall x sf,
    Is_true $ appears_in_simple_formula x sf <-> (x ∈ simple_formula_fvars sf).
Proof with auto.
  destruct sf; simpl.
  - rewrite elem_of_empty...
  - rewrite elem_of_empty...
  - split; intros H.
    + apply orb_True in H.
      destruct H; [apply elem_of_union_l | apply elem_of_union_r]; apply is_free_in_term_iff...
    + rewrite elem_of_union in H. apply orb_True.
      destruct H; [left | right]; apply is_free_in_term_iff...
  - induction args; simpl.
    + rewrite elem_of_empty...
    + destruct (appears_in_term x a) eqn:E.
      * simpl. split... intros _. apply elem_of_union_l. apply is_free_in_term_iff...
      * simpl. split; intros H.
        -- apply elem_of_union_r. apply IHargs...
        -- apply elem_of_union in H. destruct H.
           ++ apply is_free_in_term_iff in H. rewrite E in H. contradiction.
           ++ apply IHargs...
Qed.

Lemma is_free_iff : forall x φ,
    Is_true $ is_free_in x φ <-> (x ∈ formula_fvars φ).
Proof with auto.
  induction φ; simpl.
  - apply is_free_in_sf_iff.
  - assumption.
  - rewrite orb_True. rewrite elem_of_union.
    split; (destruct 1; [left; apply IHφ1 | right; apply IHφ2])...
  - rewrite orb_True. rewrite elem_of_union.
    split; (destruct 1; [left; apply IHφ1 | right; apply IHφ2])...
  - rewrite orb_True. rewrite elem_of_union.
    split; (destruct 1; [left; apply IHφ1 | right; apply IHφ2])...
  - destruct (String.eqb_spec x0 x); subst.
    + split; intros; try contradiction. apply not_elem_of_difference in H0... right.
      apply elem_of_singleton...
    + split; intros H'.
      * apply elem_of_difference. split; [apply H | apply not_elem_of_singleton]...
      * apply elem_of_difference in H'. destruct H'. apply H...
  - destruct (String.eqb_spec x0 x); subst.
    + split; intros; try contradiction. apply not_elem_of_difference in H0... right.
      apply elem_of_singleton...
    + split; intros H'.
      * apply elem_of_difference. split; [apply H | apply not_elem_of_singleton]...
      * apply elem_of_difference in H'. destruct H'. apply H...
Qed.

(* Lemma fresh_quantifier_in_eq_sf_eq_iff : forall x t₁ t₂ t x', *)
(*     let φ := <! t₁ = t₂ !> in *)
(*     fresh_quantifier x φ t = x' -> *)
(*       (negb $ appears_in_term x t /\ x = x') \/ *)
(*         (appears_in_term x t /\ negb $ is_free_in x' φ). *)
(* Proof with auto. *)
(*   simpl. intros x t₁ t₂ t x' H.  *)
(*   destruct (appears_in_term x t) eqn:E.  *)
(*   2: {  left. split... admit. } *)
(*   - right. split... induction t₁; induction t₂; simpl in *... *)
(*     + unfold fresh_quantifier in H. *)
(*       assert (Heq : formula_fvars <! v = x0 !> = {[x0]}). *)
(*       { simpl. rewrite union_empty_l_L... } rewrite E, Heq in H. *)
(*       rewrite size_singleton in H...  *)
(*     +  *)
(*   simpl. induction t₁. *)

(*   - induction t₂. *)
(*     +  *)
(*   intros  *)

Lemma fresh_quantifier_eq_iff : forall x φ t x',
    fresh_quantifier x φ t = x' ->
      (negb $ appears_in_term x t /\ x = x') \/
        (appears_in_term x t /\ negb $ is_free_in x' φ).
Proof with auto.
  admit.
Admitted.
  (* intros x φ t x' H. destruct (appears_in_term x t) eqn:E. *)
  (* - right. split... induction φ. *)
  (*   + destruct sf. *)
  (*     * simpl... *)
  (*     * simpl... *)
  (*     * simpl. unfold fresh_quantifier in H. rewrite E in H.  *)
  (*     * simpl. *)




  (*   remember (formula_fvars φ) as fvars. *)
  (*   generalize dependent φ. *)
  (*   induction fvars using set_ind_L; try rename H into H1; intros φ Heqfvars H. *)
  (*   + destruct (is_free_in x' φ) eqn:E'... *)
  (*     apply Is_true_eq_left in E'. apply is_free_iff in E'. *)
  (*     rewrite <- Heqfvars in E'. apply elem_of_empty in E'... *)
  (*   + rewrite size_union in H. rewrite size_singleton in H. simpl in H. *)
  (*     destruct (String.eqb_spec (x ++ "_" ++ "0")%string x0). *)
  (*     * rewrite e in H. *)
  (*       assert (x0 ∈ {[x0]} ∪ X). { apply elem_of_union_l. apply elem_of_singleton... } *)
  (*       destruct (decide (x0 ∈ {[x0]} ∪ X)) eqn:E'. *)
  (*       rewrite <- bool_decide_spec in H1.  *)
  (*       replace (decide (x0 ∈ {[x0]} ∪ X)) with (left H1) in H. *)
  (*       rewrite Is_true_eq_true in H1. *)
  (*       rewrite H1 in H. *)
  (*     rewrite E' in H. *)
  (*     rewrite elem_of_equiv_empty in E. specialize E with x'. contradiction. *)



  (*   induction (size $ formula_fvars φ) eqn:E. *)
  (*   + subst. apply size_empty_inv in E. unfold negb. destruct (is_free_in x' φ) eqn:E'... *)
  (*     apply Is_true_eq_left in E'. apply is_free_iff in E'. *)
  (*     rewrite elem_of_equiv_empty in E. specialize E with x'. contradiction. *)
  (*   + simpl in *. assert (E' : size (formula_fvars φ) > 0) by lia. *)
  (*     apply size_pos_elem_of in E' as [x₀ H₀]. *)
  (*     destruct (decide ((x ++ "_" ++ "0")%string ∈ formula_fvars φ)) eqn:E'; simpl in *. *)
  (*     * apply IHn.  *)

Lemma fresh_quantifier_free : forall x φ t,
    (negb $ appears_in_term x t /\ x = fresh_quantifier x φ t) \/
      (appears_in_term x t /\ negb $ is_free_in (fresh_quantifier x φ t) φ).
Proof with auto.
  admit.
Admitted.
(* Lemma fresh_quantifier_free : forall , *)
(*     appears_ fresh_quantifier x φ t *)

(* Theorem feval_subst_commute : forall M σ φ x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ appears_in_term x₁ t₂ -> *)
(*     negb $ appears_in_term x₂ t₁ -> *)
(*     feval M σ <! φ[x₁ \ t₁][x₂ \ t₂] !> <-> feval M σ <! φ[x₂ \ t₂][x₁ \ t₁] !>. *)
(* Proof with auto. *)
(*   intros M σ φ. generalize dependent σ. *)
(*   induction φ using formula_ind; intros σ x₁ t₁ x₂ t₂ Hneq Hf1 Hf2. *)
(*   - unfold formula_subst. simpl. rewrite subst_commute_sf... *)
(*   - do 4 rewrite simpl_subst_not. simpl. rewrite IHφ... *)
(*   - do 4 rewrite simpl_subst_and. simpl. rewrite IHφ1... rewrite IHφ2... *)
(*   - do 4 rewrite simpl_subst_or. simpl. rewrite IHφ1... rewrite IHφ2... *)
(*   - do 4 rewrite simpl_subst_implication. simpl. rewrite IHφ1... rewrite IHφ2... *)
(*   - destruct (String.eqb_spec x x₁); destruct (String.eqb_spec x x₂); subst. *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_eq... *)
(*       rewrite simpl_subst_exists_eq... *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*       rewrite simpl_subst_exists_eq... apply fresh_quantifier_not_in_term... *)
(*     + rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_eq... *)
(*       2: { apply fresh_quantifier_not_in_term... } *)
(*       rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*     + rewrite simpl_subst_exists_ne... *)
(*       destruct (String.eqb_spec (fresh_quantifier x φ t₁) x₂). *)
(*       * rewrite simpl_subst_exists_eq... *)
(*         assert (H1 := fresh_quantifier_free x φ t₁). subst. *)
(*         destruct H1. 1:{ destruct H0 as [_ H0]. contradiction. } *)
(*         subst. rewrite simpl_subst_exists_ne... *)
(*         destruct (String.eqb_spec (fresh_quantifier x φ t₂) x₁); subst. *)
(*         -- apply not_eq_sym in n, n0. apply fresh_quantifier_ne in n, n0. *)
(*            exfalso. apply Hneq. unfold fresh_quantifier. *)
(*            apply Is_true_true in n, n0. rewrite n. rewrite n0. reflexivity. *)
(*         -- apply not_eq_sym in n0. apply fresh_quantifier_ne in n0. *)

(*            clear Hf2. *)
(*            rewrite simpl_subst_exists_ne... simpl. split; intros [v Hv]; exists v. *)
(*            ++ *)
(*              remember (fresh_quantifier x φ t₁) as xf₁. *)
(*              remember (fresh_quantifier x φ t₂) as xf₂. *)
(*              assert (Heq : xf₁ =  fresh_quantifier xf₂ <! φ [x \ xf₂] [xf₁ \ t₂] !> t₁). *)
(*              { subst.  } *)

(* (*         -- apply  *) *)


(* (*            split. intros [v Hv]; exists v. *) *)
(* (*            apply H... *) *)
(* (*            exfalso. apply hneq. unfold fresh_quantifier. *) *)
(* (*            apply is_true_true in n, n0. rewrite n. rewrite n0. reflexivity. *) *)
(* (* -  *) *)

(*         -- rewrite simpl_subst_exists_ne... simpl. split; intros [v Hv]; exists v. *)
(*            ++ *)
(*            admit. admit. *)
(*       * admit. *)
(*            fresh_quantifier_idem. *)
(*            ++ apply H... *)

(*            Search (Is_true ?b -> ?b = true). *)


(*            rewrite Is_true_eq_true in n. *)


(*           rewrite simpl_subst_exists_eq... subst. simpl. split; intros [v Hv]; exists v. *)
(*            ++ apply H... *)
(*               ** apply not_eq_sym in n. apply fresh_quantifier_ne in n. *)

(*               2: { apply fresh_quantifier_not_in_term... } *)
(*   - *)
(*     formula_subst (formula_subst φ x₁ t₁) x₂ t₂ = *)
(*       formula_subst (formula_subst φ x₂ t₂) x₁ t₁. *)


(* Theorem subst_commute_formula : forall φ x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ appears_in_term x₁ t₂ -> *)
(*     negb $ appears_in_term x₂ t₁ -> *)
(*     formula_subst (formula_subst φ x₁ t₁) x₂ t₂ = *)
(*       formula_subst (formula_subst φ x₂ t₂) x₁ t₁. *)
(* Proof with auto. *)
(*   induction φ; intros x₁ t₁ x₂ t₂ Hneq H1 H2. *)
(*   - rewrite simpl_subst_simple_formula. unfold formula_subst. simpl. *)
(*     rewrite subst_commute_sf... *)
(*   - do 4 rewrite simpl_subst_not. f_equal. apply IHφ... *)
(*   - do 4 rewrite simpl_subst_and. f_equal; [apply IHφ1 | apply IHφ2]... *)
(*   - do 4 rewrite simpl_subst_or. f_equal; [apply IHφ1 | apply IHφ2]... *)
(*   - do 4 rewrite simpl_subst_implication. f_equal; [apply IHφ1 | apply IHφ2]... *)
(*   - destruct (String.eqb_spec x x₁); destruct (String.eqb_spec x x₂); subst. *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_eq... *)
(*       rewrite simpl_subst_exists_eq... *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*       rewrite simpl_subst_exists_eq... apply fresh_quantifier_not_in_term... *)
(*     + rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_eq... *)
(*       2: { apply fresh_quantifier_not_in_term... } *)
(*       rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*     + rewrite simpl_subst_exists_ne... *)
(*       destruct (String.eqb_spec (fresh_quantifier x φ t₁) x₂). *)
(*       * rewrite simpl_subst_exists_eq... subst. rewrite simpl_subst_exists_ne... *)
(*         destruct (String.eqb_spec (fresh_quantifier x φ t₂) x₁). *)
(*         -- rewrite simpl_subst_exists_eq... subst. f_equal... *)
(*       2: { apply fresh_quantifier_not_in_term... } *)


(*   - rewrite simpl)sy *)
(*     simpl. *)
(*     f_equal. *)
(*   - rewrite simpl_subst_and. f_equal... *)
(*   - rewrite simpl_subst_or. f_equal... *)
(*   - rewrite simpl_subst_implication. f_equal... *)
(*   - destruct (String.eqb_spec x₀ x). *)
(*     + rewrite simpl_subst_exists_eq... *)
(*     + rewrite simpl_subst_exists_ne... rewrite fresh_quantifier_for_var_ne... *)
(*       f_equal. etrans. *)
(*       * apply H. unfold formula_subst. apply shape_eq_sym. apply subst_preserves_shape. *)
(*       * apply H. apply shape_eq_refl. *)
(*   - destruct (String.eqb_spec x₀ x). *)
(*     + rewrite simpl_subst_forall_eq... *)
(*     + rewrite simpl_subst_forall_ne... rewrite fresh_quantifier_for_var_ne... *)
(*       f_equal. etrans. *)
(*       * apply H. unfold formula_subst. apply shape_eq_sym. apply subst_preserves_shape. *)
(*       * apply H. apply shape_eq_refl. *)

(* Theorem subst_eq_congr : forall M σ φ x t u b, *)
(*   feval M σ <! t = u !> -> *)
(*   feval M σ <! φ[x\t] !> b -> *)
(*   feval M σ <! φ[x\u] !> b. *)
(* Proof with auto. *)

Theorem subst_term_id_when_not_in_term : forall x t a,
  appears_in_term x t = false ->
  subst_term t x a = t.
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

Theorem teval_subst : forall {M σ t t' x} {v' v : value} (H : teval M σ t' v'),
  teval M (<[x:=v']>σ) t v <-> teval M σ (subst_term t x t') v.
Proof with auto.
 intros M σ t t' x v' v. split.
  - intros H'. generalize dependent t'. generalize dependent v.
    assert (Hind:=teval_ind_mut M (<[x:=v']>σ)
      (λ t v _, forall t', teval M σ t' v' -> teval M σ (subst_term t x t') v)
      (λ args vargs _, forall t', teval M σ t' v' -> teval_args M σ (map (λ arg, subst_term arg x t') args) vargs)).
    simpl in Hind. apply Hind; clear Hind.
    + constructor.
    + rename x into x'. intros x v H t' Heval. destruct (String.eqb_spec x x').
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H₁ H₂]].
        -- assumption.
        -- exfalso. apply H₁...
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H₁ H₂]].
        -- contradiction.
        -- constructor...
    + intros.
      (* TODO: rename TEval_Func to TEval_App and argsv to vargs  *)
      apply TEval_Func with argsv...
    + constructor.
    + constructor; [apply H | apply H0]...
  - remember (subst_term t x t') as tpre. intros H'.
    assert (Hind:=teval_ind_mut M σ
      (λ t v _, forall t', teval M σ t' v' -> forall tpre, t = subst_term tpre x t' -> teval M (<[x:=v']>σ) tpre v)
      (λ args vargs _, forall t', teval M σ t' v' -> forall args',
            args = (map (λ arg, subst_term arg x t') args') ->
            teval_args M (<[x:=v']>σ) args' vargs)).
    generalize dependent Heqtpre. generalize dependent t. generalize dependent H.
    generalize dependent t'. generalize dependent H'. generalize dependent v.
    generalize dependent tpre. simpl in Hind. apply Hind; clear Hind.
    + intros. destruct tpre; simpl in H0.
      * inversion H0. subst. constructor.
      * destruct (String.eqb_spec x0 x); try discriminate. subst. inversion H; subst.
        constructor. apply lookup_insert_Some...
      * discriminate.
    + intros. destruct tpre; simpl in H0; try discriminate.
      simpl in H0. destruct (String.eqb_spec x1 x); subst.
      * apply TEval_Var. inversion H; subst. rewrite e in H1. inversion H1. apply lookup_insert_Some...
      * inversion H0. subst. apply TEval_Var.  apply lookup_insert_Some...
    + intros. destruct tpre; simpl in H1; try discriminate.
      * destruct (String.eqb_spec x0 x); try discriminate. inversion H1; subst.
        inversion H0; subst. inversion H6; subst. inversion f0; subst.
        rewrite H1 in H5. inversion H5; subst fdef0. clear H5.
        assert (Heq := teval_args_det H4 t0). subst.
        assert (Heq := UIP_nat _ _ hlen hlen0 ). subst.
        assert (Heq := fdef_functional _ H3 H7). subst.
        constructor. apply lookup_insert_Some...
      * inversion H1. subst. apply TEval_Func with argsv... apply H with t'...
    + intros. symmetry in H0. apply map_eq_nil in H0. subst. constructor...
    + intros. symmetry in H2. apply map_eq_cons in H2. destruct H2 as (y&ys&H3&H4&H5).
      subst. constructor.
      * apply H with t'...
      * apply H0 with t'...
Qed.

Theorem teval_args_subst : forall {M σ x t} {v : value} {args vargs},
    teval M σ t v ->
    teval_args M (<[x:=v]>σ) args vargs <->
    teval_args M σ (map (λ arg : term, subst_term arg x t) args) vargs.
Proof with auto.
  intros M σ x t v args vargs Ht. split.
  - induction 1.
    + constructor.
    + constructor; [(apply (teval_subst Ht); assumption)|]. assumption.
  - remember (map (λ arg, subst_term arg x v) args) as args'.
    generalize dependent vargs.
    generalize dependent args'.
    induction args; intros args' Heq vargs H.
    + subst. inversion H; subst. constructor.
    + subst. inversion H; subst. constructor; [(apply (teval_subst Ht); assumption)|].
      eapply IHargs.
      * reflexivity.
      * assumption.
Qed.

Theorem sfeval_subst : forall {M σ sf x t} {v : value},
    teval M σ t v ->
    sfeval M (<[x:=v]>σ) sf <-> sfeval M σ (subst_simple_formula sf x t).
Proof with auto.
  intros M σ sf x t v Ht. split.
  - destruct sf; simpl; intros H...
    + apply SFEval_True.
    + inversion H.
    + inversion H; subst. apply (teval_subst Ht) in H2, H3. apply SFEval_Eq with v0; assumption.
    + inversion H; subst. apply SFEval_Pred with vargs.
      * apply (teval_args_subst Ht). assumption.
      * assumption.
  - destruct sf; simpl; intros H...
    + apply SFEval_True.
    + inversion H.
    + inversion H; subst. apply (teval_subst Ht) in H2, H3. apply SFEval_Eq with v0; assumption.
    + inversion H; subst. apply SFEval_Pred with vargs.
      * apply (teval_args_subst Ht). assumption.
      * assumption.
Qed.

(* TODO: The other one should be called aux *)
Theorem subst_preserves_shape_aux : forall φ x a,
  shape_eq φ (φ[x \ a]) = true.
Proof with auto. intros. unfold formula_subst. apply subst_preserves_shape. Qed.

Theorem subst_preserves_shape_aux' : forall φ x a,
  shape_eq (φ[x \ a]) φ  = true.
Proof with auto. intros. apply shape_eq_sym. apply subst_preserves_shape_aux. Qed.


Lemma teval_delete_nonfree_variable_in_context : ∀ M σ t x₀ v₀ v,
    negb (appears_in_term x₀ t) -> teval M (<[x₀:=v₀]> σ) t v ↔ teval M σ t v.
Proof with auto.
  intros M σ t x₀ v₀ v Hfree. split.
  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M (<[x₀:=v₀]> σ) t v -> negb (appears_in_term x₀ t) -> teval M σ t v)
         (λ args vargs _, forallb (λ arg, negb (appears_in_term x₀ arg)) args ->
                              teval_args M (<[x₀:=v₀]> σ) args vargs -> teval_args M σ args vargs)).
    + intros. constructor.
    + intros x v H H' Hfree. constructor. simpl in Hfree.
      destruct (String.eqb_spec x x₀); subst; simpl.
      * simpl in Hfree. contradiction.
      * apply (lookup_insert_Some σ) in H as [[contra _]|[_ H]].
        -- symmetry in contra. contradiction.
        -- assumption.
    + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_Func with vargs...
      apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
      rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree as [? ?].
      simpl. apply andb_prop_intro. split...
    + constructor.
    + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
      apply andb_prop_elim in Hfree as [Hfree Hfrees].
      constructor.
      * apply IH...
      * apply IHargs...
  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M σ t v -> negb (appears_in_term x₀ t) -> teval M (<[x₀:=v₀]> σ) t v)
         (λ args vargs _, forallb (λ arg, negb (appears_in_term x₀ arg)) args ->
                              teval_args M σ args vargs -> teval_args M (<[x₀:=v₀]> σ) args vargs)).
    + intros. constructor.
    + intros x v H H' Hfree. constructor. simpl in Hfree.
      destruct (String.eqb_spec x x₀); subst; simpl.
      * simpl in Hfree. contradiction.
      * apply (lookup_insert_Some σ). right. split...
    + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_Func with vargs...
      apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
      rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree as [? ?].
      simpl. apply andb_prop_intro. split...
    + constructor.
    + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
      apply andb_prop_elim in Hfree as [Hfree Hfrees].
      constructor.
      * apply IH...
      * apply IHargs...
Qed.

Theorem teval_args_delete_nonfree_variable_in_context : forall M σ x (v : value) args vargs,
    forallb (λ arg, negb (appears_in_term x arg)) args ->
    teval_args M (<[x:=v]>σ) args vargs <->
    teval_args M σ args vargs.
Proof with auto.
  intros M σ x v args vargs Hfree. split.
  - induction 1.
    + constructor.
    + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. constructor.
      * apply teval_delete_nonfree_variable_in_context in H...
      * apply IHteval_args...
  - induction 1.
    + constructor.
    + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. constructor.
      * apply teval_delete_nonfree_variable_in_context...
      * apply IHteval_args...
Qed.

Lemma sfeval_delete_nonfree_variable_in_context: ∀ M σ sf x₀ v₀,
    negb (appears_in_simple_formula x₀ sf) -> sfeval M (<[x₀:=v₀]> σ) sf ↔ sfeval M σ sf.
Proof with auto.
  intros M σ sf x₀ v₀ Hfree. intros. destruct sf; simpl.
  - split; constructor.
  - split; inversion 1.
  - simpl in Hfree. rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree as [? ?].
    split; inversion 1; subst.
    + apply SFEval_Eq with v.
      * apply teval_delete_nonfree_variable_in_context in H4...
      * apply teval_delete_nonfree_variable_in_context in H5...
    + apply SFEval_Eq with v.
      * apply teval_delete_nonfree_variable_in_context...
      * apply teval_delete_nonfree_variable_in_context...
  - simpl in Hfree. split; inversion 1; subst.
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_nonfree_variable_in_context in H2...
      clear H0 H3 H2 vargs H v₀ symbol. induction args... simpl in *.
      rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree as [? ?].
      apply andb_prop_intro. split...
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_nonfree_variable_in_context...
      clear H3 H2 vargs H v₀ symbol. induction args... simpl in *.
      rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree as [? ?].
      apply andb_prop_intro. split...
Qed.

Theorem feval_delete_nonfree_variable_in_context : forall M σ φ x v,
    negb $ is_free_in x φ ->
    feval M (<[x:=v]> σ) φ <-> feval M σ φ.
Proof with auto.
  intros M σ φ. generalize dependent σ.
  induction φ using formula_ind; simpl; intros σ x₀ v₀ Hfree;
    try (rewrite negb_orb in Hfree; apply andb_prop_elim in Hfree; destruct Hfree as [H₁ H₂]).
  - apply sfeval_delete_nonfree_variable_in_context...
  - split; intros H contra.
    + apply H. simpl in Hfree. apply IHφ...
    + apply H. simpl in Hfree. apply (IHφ σ x₀ v₀)...
  - split; intros [? ?].
    + split.
      * apply (IHφ1 σ x₀ v₀)...
      * apply (IHφ2 σ x₀ v₀)...
    + split.
      * apply (IHφ1 σ x₀ v₀)...
      * apply (IHφ2 σ x₀ v₀)...
  - split; intros [?|?].
    + left. apply (IHφ1 σ x₀ v₀)...
    + right. apply (IHφ2 σ x₀ v₀)...
    + left. apply (IHφ1 σ x₀ v₀)...
    + right. apply (IHφ2 σ x₀ v₀)...
  - split; intros Himpl H.
    + apply (IHφ2 σ x₀ v₀)... apply Himpl. apply (IHφ1 σ x₀ v₀)...
    + apply (IHφ2 σ x₀ v₀)... apply Himpl. apply (IHφ1 σ x₀ v₀)...
  - split; intros [v Hv]; exists v.
    + destruct (String.eqb_spec x x₀); subst; simpl.
      * rewrite (insert_insert σ) in Hv...
      * rewrite (insert_commute σ) in Hv... apply H in Hv...
    + destruct (String.eqb_spec x x₀); subst; simpl.
      * rewrite (insert_insert σ)...
      * rewrite (insert_commute σ)... apply H...
  - split; intros Hv v; specialize Hv with v.
    + destruct (String.eqb_spec x x₀); subst; simpl.
      * rewrite (insert_insert σ) in Hv...
      * rewrite (insert_commute σ) in Hv... apply H in Hv...
    + destruct (String.eqb_spec x x₀); subst; simpl.
      * rewrite (insert_insert σ)...
      * rewrite (insert_commute σ)... apply H...
Qed.

(* Theorem feval_subst_subst_context : forall M σ φ (x x' : string) (v : value), *)
(*     negb $ is_free_in x' φ -> *)
(*     feval M (<[x':=v]> σ) <! φ [x \ x'] !> <-> feval M σ <! φ [x \ v] !>. *)
(* Proof with auto. *)
(*   intros M σ φ x x₀' v Hfree. generalize dependent v. generalize dependent x. *)
(*   generalize dependent σ. *)
(*   induction φ using formula_ind; intros σ x₀ v₀; simpl in Hfree. *)
(*   - admit. *)
(*   - do 2 rewrite simpl_subst_not. simpl. split; intros H; intros contra; *)
(*     apply H; apply IHφ; assumption. *)
(*   - rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree. destruct Hfree as [H₁ H₂]. *)
(*     do 2 rewrite simpl_subst_and. simpl. split. *)
(*     + intros [? ?]. split; [apply IHφ1 | apply IHφ2]; assumption. *)
(*     + intros [? ?]. split; [apply IHφ1 | apply IHφ2]; assumption. *)
(*   - rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree. destruct Hfree as [H₁ H₂]. *)
(*     do 2 rewrite simpl_subst_or. simpl. split. *)
(*     + intros [? | ?]; [left; apply IHφ1 | right; apply IHφ2]; assumption. *)
(*     + intros [? | ?]; [left; apply IHφ1 | right; apply IHφ2]; assumption. *)
(*   - rewrite negb_orb in Hfree. apply andb_prop_elim in Hfree. destruct Hfree as [H₁ H₂]. *)
(*     do 2 rewrite simpl_subst_implication. simpl. split. *)
(*     + intros Himp H.  apply IHφ2... apply Himp. apply IHφ1... *)
(*     + intros Himp H.  apply IHφ2... apply Himp. apply IHφ1... *)
(*   - destruct (String.eqb_spec x x₀); destruct (String.eqb_spec x₀ x₀'); subst; simpl. *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_eq... simpl. split. *)
(*       * intros [v H₁]. subst. exists v. rewrite (insert_insert σ) in H₁. assumption. *)
(*       * intros [v H₁]. subst. exists v. rewrite (insert_insert σ). assumption. *)
(*     + rewrite (proj2 (String.eqb_neq x₀ x₀') n) in Hfree. *)
(*       rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_eq... *)
(*       simpl. split. *)
(*       * intros [v H₁]. exists v. rewrite (insert_commute σ) in H₁... *)
(*         apply feval_delete_nonfree_variable_in_context in H₁... *)
(*       * intros [v H₁]. exists v. rewrite (insert_commute σ)... *)
(*         apply feval_delete_nonfree_variable_in_context... *)
(*     + rewrite (proj2 (String.eqb_neq x x₀') n) in Hfree. *)
(*       rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_ne... *)
(*       rewrite fresh_quantifier_for_var_ne... simpl. split. *)
(*       * intros [v H₁]. exists v. rewrite fresh_quantifier_for_value_term. *)
(*         repeat rewrite subst_same_formula in *. apply H... *)
(*         rewrite subst_same_formula. rewrite (insert_commute σ)... *)
(*       * intros [v H₁]. exists v. rewrite fresh_quantifier_for_value_term in H₁. *)
(*         repeat rewrite subst_same_formula in *. apply H in H₁... *)
(*         rewrite subst_same_formula in H₁. rewrite (insert_commute σ) in H₁... *)
(*     + destruct (String.eqb_spec x x₀'); simpl in *; subst. *)
(*       * rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_ne... *)
(*         rewrite fresh_quantifier_for_value_term. simpl. split. *)
(*         -- intros [v Hv]. exists v. rewrite subst_same_formula. *)
(*            rewrite (insert_commute σ) in Hv... *)
(*            2:{ admit. } *)
(*            apply H in Hv... *)
(*            2:{ apply subst_preserves_shape_aux'. } *)
(*            2:{ admit. } *)



(*         admit. *)
(*       * simpl in Hfree. *)


(*       rewrite (proj2 (String.eqb_neq x x₀') n) in Hfree. *)
(*       rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_ne... *)
(*       rewrite fresh_quantifier_for_var_ne... simpl. split. *)
(*       * intros [v H₁]. exists v. rewrite fresh_quantifier_for_value_term. *)
(*         repeat rewrite subst_same_formula in *. apply H... *)
(*         rewrite subst_same_formula. rewrite (insert_commute σ)... *)
(*       * intros [v H₁]. exists v. rewrite fresh_quantifier_for_value_term in H₁. *)
(*         repeat rewrite subst_same_formula in *. apply H in H₁... *)
(*         rewrite subst_same_formula in H₁. rewrite (insert_commute σ) in H₁... *)
(*     + rewrite *)
(*       * *)
(*         rewrite H in H₁. *)
(*         rewrite (insert_commute σ) in H₁... *)
(*         apply feval_delete_nonfree_variable_in_context in H₁... *)
(*       * intros [v H₁]. exists v. rewrite (insert_commute σ)... *)
(*         apply feval_delete_nonfree_variable_in_context... *)
(*       * *)
(*     + *)
(*       * *)

(*       assert (Hneq := String.eqb_neq x₀ x₀'). *)

(*       rewrite <- String.eqb_neq in n. simpl in Hfree. rewrite n in Hfree. *)
(*     + *)
(*       * *)
(*       * intros [v H1]. subst. simpl. exists v. rewrite (insert_insert σ). assumption. *)
(*       * *)
(*       * intros [v' H']. exists v'. apply H. *)
(*   - induction φ using formula_ind; simpl in *. *)
(*     + apply sfeval_subst in H. admit. *)
(*     + rewrite simpl_subst_not in *. simpl in *. *)
(*   - *)
(*   - split. *)
(*   ∃ v : value, *)
(*     feval M (<[fresh_quantifier x φ v₀:=v]> σ) <! φ [x \ (fresh_quantifier x φ v₀)] [x₀ \ v₀] !> *)


Theorem feval_subst : forall {M σ φ x t} {v : value},
    teval M σ t v ->
    feval M (<[x:=v]>σ) φ <-> feval M σ (φ[x \ t]).
Proof with auto.
  intros M σ φ. generalize dependent σ. induction φ using formula_ind; intros σ x₀ t v₀ Ht.
  - split; apply sfeval_subst...
  - rewrite simpl_subst_not. simpl. split;
      intros H contra; apply H; apply (IHφ _ _ _ _ Ht); assumption.
  - rewrite simpl_subst_and. split; intros [? ?];
      (split; [apply (IHφ1 _ _ _ _ Ht)|apply (IHφ2 _ _ _ _ Ht)]; assumption).
  - rewrite simpl_subst_or. split;
      (intros [?|?]; [left; apply (IHφ1 _ _ _ _ Ht) | right; apply (IHφ2 _ _ _ _ Ht)]; auto).
  - rewrite simpl_subst_implication. simpl. split;
      (intros; apply (IHφ2 _ _ _ _ Ht); apply H; apply (IHφ1 _ _ _ _ Ht); auto).
  - destruct (String.eqb_spec x x₀).
    + rewrite simpl_subst_exists_eq... split.
      * intros [v H1]. subst. rewrite (insert_insert σ) in H1. exists v. assumption.
      * intros [v H1]. subst. simpl. exists v. rewrite (insert_insert σ). assumption.
    + rewrite simpl_subst_exists_ne... simpl. split.
      * intros [v H1]. exists v.
        destruct (String.eqb_spec (fresh_quantifier x φ t) x₀).
        -- subst. apply not_eq_sym in n.
           assert (Hne := n). apply fresh_quantifier_ne in Hne.
           assert (Ht' : teval M (<[fresh_quantifier x φ t:=v]>σ) t v). { admit. }
           rewrite <- H.
           2: { apply subst_preserves_shape_aux'. }
           2: { apply Ht'. } clear Ht'.
           rewrite <- H...
           2: { apply TEval_Var. apply lookup_insert_Some... }
           admit.
        --

          destruct (String.eqb_spec (fresh_quantifier x φ t) x₀).
        -- subst. apply not_eq_sym in n. apply fresh_quantifier_ne in n.





           rewrite <- H...
           2:{ apply TEval_Var. apply lookup_insert_Some... }

        rewrite <- H...
        2: {



        assert (H := H φ). forward H by apply shape_eq_refl.
        assert (H := H (<[x₀:=v₀]> (<[fresh_quantifier x φ v₀:=v]> σ)) x (fresh_quantifier x φ v₀)).
        rewrite <- H by apply subst_preserves_shape_aux'.
        destruct (String.eqb_spec (fresh_quantifier x φ v₀) x₀); subst; simpl.
        -- rewrite (insert_insert σ). apply H. apply subst_preserves_shape_aux'.
           admit.
        -- rewrite (insert_commute σ). rewrite <- H by apply subst_preserves_shape_aux'.
        rewrite <- H.


      split.
      * intros [v0 H1]. exists v0. apply <- H. simpl.

      * simpl. left. apply IHφ1...
      *
    + split.
      * simpl. intros. apply IHφ1.
    + rewrite simpl_subst_and.
      * apply IHφ1; assumption.
  - induction φ using formula_ind; simpl.
    + apply sfeval_subst.
    + intros. rewrite simpl_subst_not. simpl. intros contra. apply H. admit.
    + intros [H₁ H₂]. rewrite simpl_subst_and. split...
    + intros [H|H]; rewrite simpl_subst_or; simpl; [left|right]...
    + intros H. rewrite simpl_subst_implication. simpl. intros H1.

    + intros [H₁ H₂]. rewrite simpl_subst_and. split...
    + intros [H₁ H₂]. rewrite simpl_subst_and. split...
    + intros [H₁ H₂]. rewrite simpl_subst_and. split...
    +
      * apply IHφ1; assumption.
  - induction φ using formula_rank_ind. destruct φ; simpl; intros.
    + apply sfeval_subst. assumption.
    + apply feval_not_iff in H1. apply H with (rank (<! (~ φ) !>)).
      * subst.
)).

    (* apply rank_induction with (P:=λ φ, feval M (<[x:=v]> σ) φ → feval M σ <! φ [x \ v] !>); simpl. *)
    + intros. apply sfeval_subst. assumption.
    + admit.
    + intros. destruct (F_And φ₁ φ₂); simpl. unfold feval.
    + clear φ. intros. unfold not in H0.

Theorem feval_not_iff : forall M σ φ,
  feval M σ <! ~ φ !> <->
  ~ feval M σ <! φ !>.
Proof. auto. Qed.

Theorem feval_not_false_iff : forall M σ φ,
  ~ feval M σ <! ~ φ !> <->
  feval M σ <! φ !>.
Proof with auto.
  intros M σ φ. split... simpl. apply feval_dne.
Qed.

Theorem feval_and_iff : forall M σ φ ψ,
  feval M σ <! φ /\ ψ !> <->
  feval M σ φ /\ feval M σ ψ.
Proof with auto.
  intros. simpl. auto.
Qed.

Theorem feval_not_and_iff : forall M σ φ ψ,
  ~ feval M σ <! φ /\ ψ !> <->
  ~ feval M σ φ \/ ~ feval M σ ψ.
Proof with auto.
  intros. simpl. split...
  - intros H. destruct (feval_lem M σ φ); destruct (feval_lem M σ ψ)...
  - intros H. destruct H.
    + intros [contra _]...
    + intros [_ contra]...
Qed.

Theorem feval_or_true_iff : forall M σ φ ψ,
  feval M σ <! φ \/ ψ !> <->
  feval M σ φ \/ feval M σ ψ.
Proof with auto.
  intros. simpl. split...
Qed.

Theorem feval_not_or_iff : forall M σ φ ψ,
  ~ feval M σ <! φ \/ ψ !> <->
  ~ feval M σ φ /\ ~ feval M σ ψ.
Proof with auto.
  simpl. split... intros [H₁ H₂] [H|H]; contradiction.
Qed.

Theorem feval_implication_iff : forall M σ φ ψ,
  feval M σ <! φ => ψ !> <->
    ~ feval M σ <! φ !> \/
    feval M σ <! ψ !>.
Proof with auto.
  simpl. intros. split.
  - intros H. destruct (feval_lem M σ φ); destruct (feval_lem M σ ψ)...
  - intros [H|H] H'... contradiction.
Qed.

Theorem feval_not_implication_iff : forall M σ φ ψ,
  ~ feval M σ <! φ => ψ !> <->
    feval M σ <! φ !> /\
    ~ feval M σ <! ψ !>.
Proof with auto.
  intros. rewrite feval_implication_iff.
  rewrite (Decidable.not_or_iff (~ feval M σ φ) (feval M σ ψ)).
  split; intros [H₁ H₂]...
  rewrite (feval_dne M σ φ) in H₁...
Qed.

Theorem feval_iff_iff : forall M σ φ ψ,
  feval M σ <! φ <=> ψ !> <->
    (feval M σ <! φ !> /\
      feval M σ <! ψ !>) \/
    (~ feval M σ <! φ !> /\
      ~ feval M σ <! ψ !>).
Proof with auto.
  intros. simpl. split...
  - intros [H₁ H₂]. destruct (feval_lem M σ φ)...
    right...
  - intros [[H₁ H₂]|[H₁ H₂]]; split; auto; intros; contradiction.
Qed.

Theorem feval_iff_not_iff : forall M σ φ ψ,
  ~ feval M σ <! φ <=> ψ !> <->
    (feval M σ <! φ !> /\
      ~ feval M σ <! ψ !>) \/
    (~ feval M σ <! φ !> /\
      feval M σ <! ψ !>).
Proof with auto.
  intros. rewrite feval_iff_iff. split.
  - intros H. apply Decidable.not_or_iff in H. destruct H as [H₁ H₂].
    rewrite Decidable.not_and_iff in H₁, H₂.
    destruct (feval_lem M σ φ)... right. rewrite (feval_dne M σ ψ) in H₂...
  - intros [[H₁ H₂] | [H₁ H₂]].
    + intros [[? ?] | [? ?]]; contradiction.
    + intros [[? ?] | [? ?]]; contradiction.
Qed.

Theorem feval_exists_true_iff : forall M σ x φ,
  feval M σ <! exists x, φ !> true <->
  exists v, feval M σ (φ[x \ v]) true.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_exists_false_iff : forall M σ x φ,
  feval M σ <! exists x, φ !> false <->
  forall v, feval M σ (φ[x \ v]) false.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_forall_true_iff : forall M σ x φ,
  feval M σ <! forall x, φ !> true <->
  forall v, feval M σ (φ[x \ v]) true.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_forall_false_iff : forall M σ x φ,
  feval M σ <! forall x, φ !> false <->
  exists v, feval M σ (φ[x \ v]) false.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.


Theorem feval_inversion_false_true : forall M σ,
  ~ feval M σ <! false !> true.
Proof.
  intros st contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_inversion_true_false : forall {st},
  ~ feval M σ <! true !> false.
Proof.
  intros st contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_true_true : forall M σ,
  feval M σ <! true !> true.
Proof.
  intros st. apply FEval_Simple. apply SFEval_True.
Qed.

Theorem feval_false_false : forall M σ,
  feval M σ <! false !> false.
Proof.
  intros st. apply FEval_Simple. apply SFEval_False.
Qed.

Theorem feval_functional : forall φ st,
  feval M σ φ true ->
  feval M σ φ false ->
  False.
Proof with auto.
  intros φ st HT HF. induction φ.
  - induction sf.
    + inversion HF; subst. inversion H0.
    + inversion HT; subst. inversion H0.
    + inversion HT; subst. inversion HF; subst.
      inversion H0; subst. inversion H1; subst.
      inversion H5; subst. inversion H7; subst.
      subst pdef. inversion H3. subst.
      apply (pdef_functional (sym_pdef)) in H2.
      rewrite H4 in H3. inversion H3; subst.
      apply (Hfnal _ _ _ _ false) in H2... discriminate.
  - apply feval_not_true_iff in HT.
    apply feval_not_false_iff in HF.
    apply IHφ; assumption.
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

Theorem feval_eq_refl : forall t st,
  ~ feval M σ (F_Simple (φT_Pred "="%string [t; t])) false.
Proof with auto.
  intros t st contra. inversion contra; subst.
  inversion H0; subst.
  destruct (pctx_eq_semantics pctx) as [eq_pdef [Heqp1 Heqp2]].
  rewrite Heqp1 in H2. inversion H2. subst pdef.
  destruct (Heqp2 st fctx) as [Heqp_refl _].
  specialize (Heqp_refl t).
  assert (feval M σ fctx pctx <! t = t !> true).
  { apply FEval_Simple. apply SFEval_Pred with eq_pdef...
    destruct eq_pdef.
    apply Pred_Eval with n_params prel Hfnal... }
  destruct (feval_functional _ _ _ _ H contra).
Qed.
