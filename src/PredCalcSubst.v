From Stdlib Require Import Strings.String.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.
From MRC Require Import Tactics.
From stdpp Require Import gmap fin_maps.


Theorem higher_qrank__subst_eq : forall φ x a r',
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
      assert (HsameInnerφ := subst_preserves_shape φ x (fresh_var x (quant_subst_fvars φ x0 a)) (quantifier_rank φ)).
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
      assert (HsameInnerφ := subst_preserves_shape φ x (fresh_var x (quant_subst_fvars φ x0 a)) (quantifier_rank φ)).
      deduce_rank_eq HsameInnerφ.
      replace (quantifier_rank φ) with (quantifier_rank inner).
      apply H with (m:=rank φ); try rewrite Heqinner; lia...
      rewrite Heqinner...
Qed.

Theorem simpl_subst_simple_formula : forall sf x a,
  subst_formula (F_Simple sf) x a =
  F_Simple (subst_simple_formula sf x a).
Proof with auto.
  intros φ x a. unfold subst_formula. simpl. reflexivity.
Qed.

Theorem simpl_subst_not : forall φ x a,
  <! (~ φ)[x \ a] !> = <! ~ (φ[x \ a]) !>.
Proof with auto.
  intros φ x a. unfold subst_formula.
  assert (H: quantifier_rank <! ~φ !> = quantifier_rank φ).
  { reflexivity. } rewrite H. clear H. destruct (quantifier_rank φ);
    reflexivity.
Qed.

Theorem simpl_subst_and : forall φ ψ x a,
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

Theorem simpl_subst_or : forall φ ψ x a,
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

Theorem simpl_subst_implication : forall φ ψ x a,
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

Theorem simpl_subst_iff : forall φ ψ x a,
  <! (φ <=> ψ)[x \ a] !> = <! (φ[x \ a]) <=> (ψ[x \ a])!>.
Proof with auto.
  intros. rewrite simpl_subst_and. do 2 rewrite simpl_subst_implication...
Qed.

Theorem simpl_subst_exists_skip : forall y φ x a,
  y = x \/ x ∉ formula_fvars φ ->
  <! (exists y, φ)[x\a] !> = <! exists y, φ !>.
Proof with auto.
  intros y φ x a Heq. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y φ x)... destruct Heq; contradiction.
Qed.

Theorem simpl_subst_exists_propagate : forall y φ x a,
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
  - assert (H:=subst_preserves_shape φ y
      (fresh_var y (quant_subst_fvars φ x a)) (quantifier_rank φ)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem simpl_subst_forall_skip : forall y φ x a,
  y = x \/ x ∉ formula_fvars φ ->
  <! (forall y, φ)[x\a] !> = <! forall y, φ !>.
Proof with auto.
  intros y φ x a Heq. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y φ x)... destruct Heq; contradiction.
Qed.

Theorem simpl_subst_forall_propagate : forall y φ x a,
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
  - assert (H:=subst_preserves_shape φ y
      (fresh_var y (quant_subst_fvars φ x a)) (quantifier_rank φ)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Theorem subst_formula_ind {x t} : forall P,
  (forall sf, P (F_Simple $ subst_simple_formula sf x t) (F_Simple sf)) ->
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

(* Lemma teval_something : forall M σ t (x x' : variable) (v' v : value), *)
(*     teval M (<[x':=v']> σ) t v <-> teval M (<[x':=v']> σ) (subst_term t x' v') v. *)

(*   ∀ σ : state, *)
(*     (∃ v : value, sfeval M (<[x:=v]> σ) sf) *)
(*     ↔ ∃ v : value, sfeval M (<[x':=v]> σ) (subst_simple_formula sf x x') *)
Lemma feval_exists_equiv : forall M σ x x' φ,
    x' ∉ formula_fvars φ ->
    feval M σ <! exists x, φ !> <-> feval M σ <! exists x', φ[x \ x'] !>.
Proof with auto.
  intros. generalize dependent σ. induction φ.
  - simpl.  admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - simpl. intros σ. split; intros [v Hv]; exists v.
    + destruct Hv as [v' Hv]. simpl in H.
      apply not_elem_of_difference in H. rewrite elem_of_singleton in H.
      destruct H.
      * admit.
      * subst.
      rewrite simpl_subst_exists_skip...
      2: { destruct H... }


  split; intros [v Hv]; exists v.
  -

(* (* if (Qy. φ)[x \ t] = (Qx. φ)[x \ t], then x ∉ FV(φ) hence ≡ (Qx. φ) *) *)
Lemma temp : forall M σ y φ x t,
    <! (exists y, φ)[x \ t] !> = <! exists x, φ[x \ t] !> ->
    feval M σ <! (exists y, φ)[x \ t] !> <-> feval M σ <! exists y, φ !>.
Proof with auto.
  intros. destruct (formula_).
  - rewrite simpl_subst_exists_skip...
  - apply Decidable.not_or in n as [H1 H2].
    destruct (decide (x ∈ formula_fvars φ)); try contradiction.
    clear H2. rename e into H2. rewrite simpl_subst_exists_propagate...
    simpl. split; intros [v Hv]; exists v.
    +


(*     rewrite simpl_subst_exists_propagate... *)
(*     + rewrite simpl_ subst. *)
