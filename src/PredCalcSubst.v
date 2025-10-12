From Stdlib Require Import Strings.String.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.
From MRC Require Import Tactics.
From stdpp Require Import gmap fin_maps.

Lemma higher_qrank__subst_eq : forall φ x a r',
  quantifier_rank φ <= r' ->
    subst_formula_aux (quantifier_rank φ) φ x a =
    subst_formula_aux r' φ x a.
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
        -- assert (Heq1: subst_formula_aux (quantifier_rank φ1) φ1 x0 a =
                        subst_formula_aux (S n) φ1 x0 a).
            { apply H with (rank φ1); lia. }
           assert (Heq2: subst_formula_aux (quantifier_rank φ1) φ1 x0 a =
                         subst_formula_aux (S n0) φ1 x0 a).
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
        -- assert (Heq1: subst_formula_aux (quantifier_rank φ2) φ2 x0 a =
                        subst_formula_aux (S n) φ2 x0 a).
            { apply H with (rank φ2); lia. }
           assert (Heq2: subst_formula_aux (quantifier_rank φ2) φ2 x0 a =
                         subst_formula_aux (S n0) φ2 x0 a).
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
        -- assert (Heq1: subst_formula_aux (quantifier_rank φ1) φ1 x0 a =
                        subst_formula_aux (S n) φ1 x0 a).
            { apply H with (rank φ1); lia. }
           assert (Heq2: subst_formula_aux (quantifier_rank φ1) φ1 x0 a =
                         subst_formula_aux (S n0) φ1 x0 a).
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
        -- assert (Heq1: subst_formula_aux (quantifier_rank φ2) φ2 x0 a =
                        subst_formula_aux (S n) φ2 x0 a).
            { apply H with (rank φ2); lia. }
           assert (Heq2: subst_formula_aux (quantifier_rank φ2) φ2 x0 a =
                         subst_formula_aux (S n0) φ2 x0 a).
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
        -- assert (Heq1: subst_formula_aux (quantifier_rank φ1) φ1 x0 a =
                        subst_formula_aux (S n) φ1 x0 a).
            { apply H with (rank φ1); lia. }
           assert (Heq2: subst_formula_aux (quantifier_rank φ1) φ1 x0 a =
                         subst_formula_aux (S n0) φ1 x0 a).
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
        -- assert (Heq1: subst_formula_aux (quantifier_rank φ2) φ2 x0 a =
                        subst_formula_aux (S n) φ2 x0 a).
            { apply H with (rank φ2); lia. }
           assert (Heq2: subst_formula_aux (quantifier_rank φ2) φ2 x0 a =
                         subst_formula_aux (S n0) φ2 x0 a).
            { apply H with (rank φ2); lia. }
            rewrite <- Heq1...
  - destruct r'; simpl in *.
    + lia.
    + fold_qrank_subst_fresh (S r') φ x x0 a.
      fold_qrank_subst_fresh (S (quantifier_rank φ)) φ x x0 a.
      f_equal.
      destruct (quant_subst_skip_cond x φ x0); try lia...
      f_equal.
      assert (subst_formula_aux (S (quantifier_rank φ)) φ x (fresh_var x (quant_subst_fvars φ x0 a))
            = subst_formula_aux (quantifier_rank φ) φ x (fresh_var x (quant_subst_fvars φ x0 a))).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_aux (S r') φ x (fresh_var x (quant_subst_fvars φ x0 a))
            = subst_formula_aux (quantifier_rank φ) φ x (fresh_var x (quant_subst_fvars φ x0 a))).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_aux (quantifier_rank φ) φ x (fresh_var x (quant_subst_fvars φ x0 a)))
        as inner.
      assert (HsameInnerφ := subst_preserves_shape_aux φ x (fresh_var x (quant_subst_fvars φ x0 a)) (quantifier_rank φ)).
      deduce_rank_eq HsameInnerφ.
      replace (quantifier_rank φ) with (quantifier_rank inner).
      apply H with (m:=rank φ); try rewrite Heqinner; lia...
      rewrite Heqinner...
  - destruct r'; simpl in *.
    + lia.
    + fold_qrank_subst_fresh (S r') φ x x0 a.
      fold_qrank_subst_fresh (S (quantifier_rank φ)) φ x x0 a.
      f_equal.
      destruct (quant_subst_skip_cond x φ x0); try lia...
      f_equal.
      assert (subst_formula_aux (S (quantifier_rank φ)) φ x (fresh_var x (quant_subst_fvars φ x0 a))
            = subst_formula_aux (quantifier_rank φ) φ x (fresh_var x (quant_subst_fvars φ x0 a))).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_aux (S r') φ x (fresh_var x (quant_subst_fvars φ x0 a))
            = subst_formula_aux (quantifier_rank φ) φ x (fresh_var x (quant_subst_fvars φ x0 a))).
      {
        symmetry. apply H with (m:=rank φ); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_aux (quantifier_rank φ) φ x (fresh_var x (quant_subst_fvars φ x0 a)))
        as inner.
      assert (HsameInnerφ := subst_preserves_shape_aux φ x (fresh_var x (quant_subst_fvars φ x0 a)) (quantifier_rank φ)).
      deduce_rank_eq HsameInnerφ.
      replace (quantifier_rank φ) with (quantifier_rank inner).
      apply H with (m:=rank φ); try rewrite Heqinner; lia...
      rewrite Heqinner...
Qed.

Lemma simpl_subst_sf : forall sf x a,
  subst_formula (F_Simple sf) x a =
  F_Simple (subst_sf sf x a).
Proof with auto.
  intros φ x a. unfold subst_formula. simpl. reflexivity.
Qed.

Lemma simpl_subst_not : forall φ x a,
  <! (~ φ)[x \ a] !> = <! ~ (φ[x \ a]) !>.
Proof with auto.
  intros φ x a. unfold subst_formula.
  assert (H: quantifier_rank <! ~φ !> = quantifier_rank φ).
  { reflexivity. } rewrite H. clear H. destruct (quantifier_rank φ);
    reflexivity.
Qed.

Lemma simpl_subst_and : forall φ ψ x a,
  <! (φ /\ ψ)[x \ a] !> = <! (φ[x \ a]) /\ (ψ[x \ a])!>.
Proof with auto.
  intros φ ψ x a. unfold subst_formula.
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

Lemma simpl_subst_or : forall φ ψ x a,
  <! (φ \/ ψ)[x \ a] !> = <! (φ[x \ a]) \/ (ψ[x \ a])!>.
Proof with auto.
  intros φ ψ x a. unfold subst_formula.
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

Lemma simpl_subst_implication : forall φ ψ x a,
  <! (φ => ψ)[x \ a] !> = <! (φ[x \ a]) => (ψ[x \ a])!>.
Proof with auto.
  intros φ ψ x a. unfold subst_formula.
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

Lemma simpl_subst_iff : forall φ ψ x a,
  <! (φ <=> ψ)[x \ a] !> = <! (φ[x \ a]) <=> (ψ[x \ a])!>.
Proof with auto.
  intros. rewrite simpl_subst_and. do 2 rewrite simpl_subst_implication...
Qed.

Lemma simpl_subst_exists_skip : forall y φ x a,
  y = x \/ x ∉ formula_fvars φ ->
  <! (exists y, φ)[x\a] !> = <! exists y, φ !>.
Proof with auto.
  intros y φ x a Heq. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y φ x)... destruct Heq; contradiction.
Qed.

Lemma simpl_subst_exists_propagate : forall y φ x a,
  y <> x ->
  x ∈ formula_fvars φ ->
  let y' := fresh_var y (quant_subst_fvars φ x a) in
  <! (exists y, φ)[x\a] !> = <! (exists y', φ[y\y'][x\a]) !>.
Proof.
  intros y φ x a Hneq Hfree. simpl. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y φ x)...
  1: { destruct H; contradiction. } f_equal.
  fold_qrank_subst_fresh (S (quantifier_rank φ)) φ y x a.
  f_equal.
  - assert (H:=subst_preserves_shape_aux φ y
      (fresh_var y (quant_subst_fvars φ x a)) (quantifier_rank φ)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Lemma simpl_subst_forall_skip : forall y φ x a,
  y = x \/ x ∉ formula_fvars φ ->
  <! (forall y, φ)[x\a] !> = <! forall y, φ !>.
Proof with auto.
  intros y φ x a Heq. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y φ x)... destruct Heq; contradiction.
Qed.

Lemma simpl_subst_forall_propagate : forall y φ x a,
  y <> x ->
  x ∈ formula_fvars φ ->
  let y' := fresh_var y (quant_subst_fvars φ x a) in
  <! (forall y, φ)[x\a] !> = <! (forall y', φ[y\y'][x\a]) !>.
Proof.
  intros y φ x a Hneq Hfree. simpl. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y φ x)...
  1: { destruct H; contradiction. } f_equal.
  fold_qrank_subst_fresh (S (quantifier_rank φ)) φ y x a.
  f_equal.
  - assert (H:=subst_preserves_shape_aux φ y
      (fresh_var y (quant_subst_fvars φ x a)) (quantifier_rank φ)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Lemma subst_formula_ind {x t} : forall P,
  (forall sf, P (F_Simple $ subst_sf sf x t) (F_Simple sf)) ->
  (forall φ, P <! φ[x \ t] !> φ -> P <! ~ (φ[x \ t]) !> <! ~ φ !>) ->
  (forall φ₁ φ₂, P <! φ₁[x \ t] !> φ₁ -> P <! φ₂[x \ t] !> φ₂ -> P <! φ₁[x \ t] /\ φ₂[x \ t] !> <! φ₁ /\ φ₂ !>) ->
  (forall φ₁ φ₂, P <! φ₁[x \ t] !> φ₁ -> P <! φ₂[x \ t] !> φ₂ -> P <! φ₁[x \ t] \/ φ₂[x \ t] !> <! φ₁ \/ φ₂ !>) ->
  (forall φ₁ φ₂, P <! φ₁[x \ t] !> φ₁ -> P <! φ₂[x \ t] !> φ₂ -> P <! φ₁[x \ t] => φ₂[x \ t] !> <! φ₁ => φ₂ !>) ->
  (forall y φ, (forall ψ, shape_eq ψ φ = true -> P <! ψ[x \ t] !> ψ) ->
          (y = x \/ x ∉ formula_fvars φ ->
           P <! exists y, φ !> <! exists y, φ !>)) ->
  (forall y φ, (forall ψ, shape_eq ψ φ = true -> P <! ψ[x \ t] !> ψ) ->
          (y <> x -> x ∈ formula_fvars φ ->
           let y' := fresh_var y (quant_subst_fvars φ x t) in
           P <! exists y', φ[y \ y'][x \ t] !> <! exists y, φ !>)) ->
  (forall y φ, (forall ψ, shape_eq ψ φ = true -> P <! ψ[x \ t] !> ψ) ->
          (y = x \/ x ∉ formula_fvars φ ->
           P <! forall y, φ !> <! forall y, φ !>)) ->
  (forall y φ, (forall ψ, shape_eq ψ φ = true -> P <! ψ[x \ t] !> ψ) ->
          (y <> x -> x ∈ formula_fvars φ ->
           let y' := fresh_var y (quant_subst_fvars φ x t) in
           P <! forall y', φ[y \ y'][x \ t] !> <! forall y, φ !>)) ->
  forall φ, P <! φ[x \ t] !> φ.
Proof with auto.
  simpl.
  intros P Hsf Hnot Hand Hor Himpl Hexists1 Hexists2 Hforall1 Hforall2  φ.
  induction φ using formula_ind.
  - apply Hsf.
  - rewrite simpl_subst_not. apply Hnot...
  - rewrite simpl_subst_and. apply Hand...
  - rewrite simpl_subst_or. apply Hor...
  - rewrite simpl_subst_implication. apply Himpl...
  - rename x0 into y. destruct (quant_subst_skip_cond y φ x).
    + rewrite simpl_subst_exists_skip...
    + rewrite simpl_subst_exists_propagate; try contradiction...
  - rename x0 into y. destruct (quant_subst_skip_cond y φ x).
    + rewrite simpl_subst_forall_skip...
    + rewrite simpl_subst_forall_propagate; try contradiction...
Qed.

Lemma subst_term_id : forall t x,
    subst_term t x x = t.
Proof with auto.
  intros t x. induction t using term_ind; simpl...
  - destruct (decide (x0 = x))... inversion e...
  - f_equal. induction args; simpl... f_equal.
    * apply H. simpl. left...
    * apply IHargs. intros. apply H. simpl. right...
Qed.

Lemma subst_sf_id : forall sf x,
    subst_sf sf x x = sf.
Proof with auto.
  intros sf x. destruct sf...
  - simpl... f_equal; apply subst_term_id.
  - simpl. f_equal. induction args... rewrite map_cons. f_equal; auto; apply subst_term_id.
Qed.

Hint Resolve simpl_subst_sf : core.
Hint Resolve simpl_subst_not : core.
Hint Rewrite simpl_subst_and : core.
Hint Rewrite simpl_subst_or : core.
Hint Rewrite simpl_subst_implication : core.
Hint Rewrite simpl_subst_iff : core.
Hint Rewrite subst_term_id : core.
Hint Rewrite subst_sf_id : core.

Lemma subst_term_not_free : forall t x t',
    x ∉ term_fvars t ->
    subst_term t x t' = t.
Proof with auto.
  intros t x t' H. induction t using term_ind; simpl...
  - simpl in H. destruct (decide (x0 = x))... apply not_elem_of_singleton in H. symmetry in e.
    contradiction.
  - simpl in H. f_equal. induction args... rewrite map_cons. simpl in H.
    apply not_elem_of_union in H as [H1 H2]. f_equal.
    * apply H0... simpl. left...
    * apply IHargs... intros. apply H0... simpl. right...
Qed.

Lemma subst_sf_not_free : forall sf x t,
    x ∉ simple_formula_fvars sf ->
    subst_sf sf x t = sf.
Proof with auto.
  intros. destruct sf; simpl; try reflexivity.
  - simpl in H. apply not_elem_of_union in H as [? ?]. f_equal; apply subst_term_not_free...
  - f_equal. simpl in H. induction args... simpl in *. apply not_elem_of_union in H as [? ?].
    f_equal.
    + simpl in H. apply subst_term_not_free...
    + apply IHargs...
Qed.

Lemma subst_term_commute : forall t x₁ t₁ x₂ t₂,
    x₁ ≠ x₂ ->
    x₁ ∉ term_fvars t₂ ->
    x₂ ∉ term_fvars t₁ ->
    subst_term (subst_term t x₁ t₁) x₂ t₂ = subst_term (subst_term t x₂ t₂) x₁ t₁.
Proof with auto.
  intros t x₁ t₁ x₂ t₂ Hneq H₁ H₂. induction t using term_ind; simpl...
  - destruct (decide (x = x₁)); destruct (decide (x = x₂)); subst.
    + contradiction.
    + simpl. destruct (decide (x₁ = x₁)); try contradiction. apply subst_term_not_free...
    + simpl. destruct (decide (x₂ = x₂)); try contradiction. symmetry. apply subst_term_not_free...
    + simpl. destruct (decide (x = x₂)); destruct (decide (x = x₁)); try contradiction...
  - f_equal. induction args; simpl... f_equal.
    + apply H. left...
    + apply IHargs. intros. apply H. right...
Qed.

Lemma subst_sf_commute : forall sf x₁ t₁ x₂ t₂,
    x₁ <> x₂ ->
    x₁ ∉ term_fvars t₂ ->
    x₂ ∉ term_fvars t₁ ->
    subst_sf (subst_sf sf x₁ t₁) x₂ t₂ =
      subst_sf (subst_sf sf x₂ t₂) x₁ t₁.
Proof with auto.
  intros. destruct sf; simpl...
  - f_equal; auto using subst_term_commute.
  - f_equal. induction args... repeat rewrite map_cons. f_equal... apply subst_term_commute...
Qed.

Lemma teval_delete_state_var : ∀ x {M σ t v},
    x ∉ term_fvars t ->
    teval M σ t v ↔ teval M (delete x σ) t v.
Proof with auto.
  intros x₀ M σ t v Hfree. split.
  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M σ t v -> x₀ ∉ term_fvars t -> teval M (delete x₀ σ) t v)
         (λ args vargs _, forallb (λ arg, bool_decide (x₀ ∉ term_fvars arg)) args ->
                              teval_args M σ args vargs -> teval_args M (delete x₀ σ) args vargs)).
    + intros. constructor.
    + intros x v H H' Hfree. constructor. simpl in Hfree.
      destruct (decide (x = x₀)); subst; simpl.
      * apply not_elem_of_singleton in Hfree. contradiction.
      * apply lookup_delete_Some. split...
    + intros f args vargs v Hargs IHargs Hfn H Hfree. apply Teval_App with vargs...
      apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
      apply not_elem_of_union in Hfree as [H1 H2].
      simpl. apply andb_prop_intro. split...
    + constructor.
    + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
      apply andb_prop_elim in Hfree as [Hfree Hfrees]. apply bool_decide_unpack in Hfree.
      constructor.
      * apply IH...
      * apply IHargs...

  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M (delete x₀ σ) t v -> x₀ ∉ term_fvars t -> teval M σ t v)
         (λ args vargs _, forallb (λ arg, bool_decide (x₀ ∉ term_fvars arg)) args ->
                              teval_args M (delete x₀ σ) args vargs -> teval_args M σ args vargs)).
    + intros. constructor.
    + intros x v H H' Hfree. constructor. simpl in Hfree.
      destruct (decide (x = x₀)); subst; simpl.
      * apply not_elem_of_singleton in Hfree. contradiction.
      * apply lookup_delete_Some in H as [? ?]...
    + intros f args vargs v Hargs IHargs Hfn H Hfree. apply Teval_App with vargs...
      apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
      apply not_elem_of_union in Hfree as [? ?].
      simpl. apply andb_prop_intro. split...
    + constructor.
    + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
      apply andb_prop_elim in Hfree as [Hfree Hfrees]. apply bool_decide_unpack in Hfree.
      constructor.
      * apply IH...
      * apply IHargs...
Qed.

Lemma teval_args_delete_state_var : forall x {M σ args vargs},
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args ->
    teval_args M σ args vargs <->
    teval_args M (delete x σ) args vargs.
Proof with auto.
  intros x M σ args vargs Hfree. split.
  - induction 1.
    + constructor.
    + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
      constructor.
      * apply teval_delete_state_var...
      * apply IHteval_args...
  - induction 1.
    + constructor.
    + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
      constructor.
      * apply teval_delete_state_var in H...
      * apply IHteval_args...
Qed.

Lemma sfeval_delete_state_var : ∀ x {M σ sf},
    x ∉ simple_formula_fvars sf -> sfeval M σ sf ↔ sfeval M (delete x σ) sf.
Proof with auto.
  intros x₀ M σ sf Hfree. intros. destruct sf; simpl.
  - split; constructor.
  - split; inversion 1.
  - simpl in Hfree. apply not_elem_of_union in Hfree as [? ?].
    split; inversion 1; subst.
    + apply SFEval_Eq with v; apply teval_delete_state_var...
    + apply SFEval_Eq with v;
        [apply teval_delete_state_var in H4 | apply teval_delete_state_var in H5]...
  - simpl in Hfree. split; inversion 1; subst.
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_state_var...
      clear H3 H2 vargs H symbol. induction args... simpl in *.
      apply not_elem_of_union in Hfree as [? ?].
      apply andb_prop_intro. split...
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_state_var in H2...
      clear H0 H3 H2 vargs H symbol. induction args... simpl in *.
      apply not_elem_of_union in Hfree as [? ?].
      apply andb_prop_intro. split...
Qed.

Lemma feval_delete_state_var : forall x {M σ φ},
    x ∉ formula_fvars φ ->
    feval M σ φ <-> feval M (delete x σ) φ.
Proof with auto.
  intros x M σ φ. generalize dependent x. generalize dependent σ.
  induction φ using formula_ind; simpl; intros σ x₀ Hfree;
    try (apply not_elem_of_union in Hfree as [H₁ H₂]).
  - apply sfeval_delete_state_var...
  - split; intros H contra.
    + apply H. apply <- IHφ; [exact contra|]...
    + apply H. apply IHφ...
  - split; intros [? ?].
    + split.
      * apply (IHφ1 σ x₀)...
      * apply (IHφ2 σ x₀)...
    + split.
      * apply (IHφ1 σ x₀)...
      * apply (IHφ2 σ x₀)...
  - split; intros [?|?].
    + left. apply (IHφ1 σ x₀)...
    + right. apply (IHφ2 σ x₀)...
    + left. apply (IHφ1 σ x₀)...
    + right. apply (IHφ2 σ x₀)...
  - split; intros Himpl H.
    + apply (IHφ2 σ x₀)... apply Himpl. apply (IHφ1 σ x₀)...
    + apply (IHφ2 σ x₀)... apply Himpl. apply (IHφ1 σ x₀)...
  - destruct (decide (x₀ = x)); subst; simpl.
    + setoid_rewrite (insert_delete_insert σ)...
    + apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
      setoid_rewrite <- (delete_insert_ne σ)... destruct Hfree; try contradiction.
      split; intros [v Hv]; exists v.
      * apply H...
      * apply H in Hv...
  - destruct (decide (x₀ = x)); subst; simpl.
    + setoid_rewrite (insert_delete_insert σ)...
    + apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
      setoid_rewrite <- (delete_insert_ne σ)... destruct Hfree; try contradiction.
      split; intros Hv v; specialize Hv with v.
      * apply H...
      * apply H in Hv...
Qed.

Lemma teval_delete_state_var_head : ∀ x M σ t v₀ v,
    x ∉ term_fvars t -> teval M (<[x:=v₀]> σ) t v ↔ teval M σ t v.
Proof with auto.
  intros. etrans.
  - apply teval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- teval_delete_state_var...
Qed.

Lemma teval_args_delete_state_var_head : forall x M σ (v : value) args vargs,
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args ->
    teval_args M (<[x:=v]>σ) args vargs <->
    teval_args M σ args vargs.
Proof with auto.
  intros. etrans.
  - apply teval_args_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- teval_args_delete_state_var...
Qed.

Lemma sfeval_delete_state_var_head : ∀ x M σ sf v,
    x ∉ simple_formula_fvars sf -> sfeval M (<[x:=v]> σ) sf ↔ sfeval M σ sf.
Proof with auto.
  intros. etrans.
  - apply sfeval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- sfeval_delete_state_var...
Qed.

Lemma feval_delete_state_var_head : forall x  M σ φ v,
    x ∉ formula_fvars φ ->
    feval M (<[x:=v]> σ) φ <-> feval M σ φ.
Proof with auto.
  intros. etrans.
  - apply feval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- feval_delete_state_var...
Qed.

Lemma teval_subst : forall {M σ t t' x} {v' v : value} (H : teval M σ t' v'),
  teval M (<[x:=v']>σ) t v <-> teval M σ (subst_term t x t') v.
Proof with auto.
 intros M σ t t' x v' v. split.
  - intros H'. generalize dependent t'. generalize dependent v.
    assert (Hind:=teval_ind_mut M (<[x:=v']>σ)
      (λ t v _, forall t', teval M σ t' v' -> teval M σ (subst_term t x t') v)
      (λ args vargs _, forall t', teval M σ t' v' -> teval_args M σ (map (λ arg, subst_term arg x t') args) vargs)).
    simpl in Hind. apply Hind; clear Hind.
    + constructor.
    + rename x into x'. intros x v H t' Heval. destruct (decide (x = x')).
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H₁ H₂]].
        -- assumption.
        -- exfalso. apply H₁...
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H₁ H₂]].
        -- contradiction.
        -- constructor...
    + intros. apply Teval_App with vargs...
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
      * destruct (decide (x0 = x)); try discriminate. subst. inversion H; subst.
        constructor. apply lookup_insert_Some...
      * discriminate.
    + intros. destruct tpre; simpl in H0; try discriminate.
      simpl in H0. destruct (decide (x1 = x)); subst.
      * apply TEval_Var. inversion H; subst. rewrite e in H1. inversion H1. apply lookup_insert_Some...
      * inversion H0. subst. apply TEval_Var.  apply lookup_insert_Some...
    + intros. destruct tpre; simpl in H1; try discriminate.
      * destruct (decide (x0 = x)); try discriminate. inversion H1; subst.
        inversion H0; subst. inversion H6; subst. inversion f0; subst.
        rewrite H1 in H5. inversion H5; subst fdef0. clear H5.
        pose proof (Heq := teval_args_det H4 t). subst.
        pose proof (Heq := UIP_nat _ _ hlen hlen0 ). subst.
        pose proof (Heq := fdef_functional _ H3 H7). subst.
        constructor. apply lookup_insert_Some...
      * inversion H1. subst. apply Teval_App with vargs... apply H with t'...
    + intros. symmetry in H0. apply map_eq_nil in H0. subst. constructor...
    + intros. symmetry in H2. apply map_eq_cons in H2. destruct H2 as (y&ys&H3&H4&H5).
      subst. constructor.
      * apply H with t'...
      * apply H0 with t'...
Qed.

Lemma teval_args_subst : forall {M σ x t} {v : value} {args vargs},
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

Lemma sfeval_subst : forall {M σ sf x t} {v : value},
    teval M σ t v ->
    sfeval M (<[x:=v]>σ) sf <-> sfeval M σ (subst_sf sf x t).
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

Lemma feval_subst : forall v M σ φ x t,
    teval M σ t v ->
    feval M (<[x:=v]>σ) φ <-> feval M σ (φ[x \ t]).
Proof with auto.
  intros v M σ φ. generalize dependent σ. generalize dependent v.
  induction φ using formula_ind; intros v₀ σ x₀ t Ht.
  - split; apply sfeval_subst...
  - rewrite simpl_subst_not. simpl. split;
      intros H contra; apply H; apply (IHφ _ _ _ _ Ht); assumption.
  - rewrite simpl_subst_and. split; intros [? ?];
      (split; [apply (IHφ1 _ _ _ _ Ht)|apply (IHφ2 _ _ _ _ Ht)]; assumption).
  - rewrite simpl_subst_or. split;
      (intros [?|?]; [left; apply (IHφ1 _ _ _ _ Ht) | right; apply (IHφ2 _ _ _ _ Ht)]; auto).
  - rewrite simpl_subst_implication. simpl. split;
      (intros; apply (IHφ2 _ _ _ _ Ht); apply H; apply (IHφ1 _ _ _ _ Ht); auto).
  - destruct (decide (x = x₀)).
    + rewrite simpl_subst_exists_skip... subst. simpl. setoid_rewrite (insert_insert σ)...
    + rename H into IH. destruct (decide (x₀ ∈ formula_fvars φ)).
      2: { rewrite simpl_subst_exists_skip... apply feval_delete_state_var_head...
           simpl. apply not_elem_of_difference... }
      pose proof (Hfresh := fresh_var_fresh x (quant_subst_fvars φ x₀ t))...
      apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3).
      rewrite simpl_subst_exists_propagate... simpl.
      remember (fresh_var x (quant_subst_fvars φ x₀ t)) as x'.
      enough (forall v, feval M (<[x:=v]> (<[x₀:=v₀]> σ)) φ
                   <-> feval M (<[x':=v]> σ) <! φ[x \ x'][x₀ \ t] !>) as H.
      { split; intros [v Hv]; exists v; apply H... }
      intros v. etrans.
      { apply (feval_delete_state_var x')... }
      symmetry. etrans.
      {
        rewrite <- IH; [|auto|].
        2: { apply teval_delete_state_var_head... apply Ht. }
        rewrite (insert_commute σ); [|auto].
        rewrite <- IH; [|auto|].
        2: { apply TEval_Var. apply lookup_insert. }
        rewrite feval_delete_state_var...
        exact H1.
      }
      destruct (decide (x = x')).
      * rewrite <- e0 in *. rewrite (delete_insert_delete (<[x:=v]> (<[x₀:=v₀]> σ)))...
      * rewrite (delete_insert_ne (<[x':=v]> (<[x₀:=v₀]> σ)))...
         rewrite (delete_insert_delete (<[x₀:=v₀]> σ)).
         rewrite (delete_insert_ne (<[x₀:=v₀]> σ))...
  - destruct (decide (x = x₀)).
    + rewrite simpl_subst_forall_skip... subst. simpl. setoid_rewrite (insert_insert σ)...
    + rename H into IH. destruct (decide (x₀ ∈ formula_fvars φ)).
      2: { rewrite simpl_subst_forall_skip... apply feval_delete_state_var_head...
           simpl. apply not_elem_of_difference... }
      pose proof (Hfresh := fresh_var_fresh x (quant_subst_fvars φ x₀ t))...
      apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3).
      rewrite simpl_subst_forall_propagate... simpl.
      remember (fresh_var x (quant_subst_fvars φ x₀ t)) as x'.
      enough (forall v, feval M (<[x:=v]> (<[x₀:=v₀]> σ)) φ
                   <-> feval M (<[x':=v]> σ) <! φ[x \ x'][x₀ \ t] !>) as H.
      { split; intros v Hv; apply H... }
      intros v. etrans.
      { apply (feval_delete_state_var x')... }
      symmetry. etrans.
      {
        rewrite <- IH; [|auto|].
        2: { apply teval_delete_state_var_head... apply Ht. }
        rewrite (insert_commute σ); [|auto].
        rewrite <- IH; [|auto|].
        2: { apply TEval_Var. apply lookup_insert. }
        rewrite feval_delete_state_var...
        exact H1.
      }
      destruct (decide (x = x')).
      * rewrite <- e0 in *. rewrite (delete_insert_delete (<[x:=v]> (<[x₀:=v₀]> σ)))...
      * rewrite (delete_insert_ne (<[x':=v]> (<[x₀:=v₀]> σ)))...
         rewrite (delete_insert_delete (<[x₀:=v₀]> σ)).
         rewrite (delete_insert_ne (<[x₀:=v₀]> σ))...
Qed.
