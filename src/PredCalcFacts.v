From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc PredCalcSubst PredCalcEquiv.
From stdpp Require Import gmap fin_maps.

Section facts.
  Context (M : model).
  Let V := value M.

  Implicit Types t : @term V.
  Implicit Types sf : @simple_formula V.
  Implicit Types A B C : @formula V.
  Implicit Types v : V.

  Lemma fequiv_subst_and_diag A x :
    <! A[x \ x] !> ≡ A ∧ ∀ σ t v, teval σ t v → feval (<[x:=v]> σ) A ↔ feval σ (A[x \ t]).
  Proof with auto.
    unfold V. generalize dependent x. induction A; intros.
    - unfold subst_formula. simpl. rewrite subst_sf_diag... split...
      intros. simp feval. apply sfeval_subst...
    - unfold V. setoid_rewrite simpl_subst_not. split.
      + destruct (IHA x) as [-> _]...
      + intros. destruct (IHA x) as [_ ?]. simp feval. rewrite H0...
    - unfold V. setoid_rewrite simpl_subst_and. split.
      + destruct (IHA1 x) as [-> _]... destruct (IHA2 x) as [-> _]...
      + intros. apply (proj2 (IHA1 x)) in H as H1. apply (proj2 (IHA2 x)) in H as H2.
        simp feval. rewrite H1. rewrite H2...
    - unfold V. setoid_rewrite simpl_subst_or. split.
      + destruct (IHA1 x) as [-> _]... destruct (IHA2 x) as [-> _]...
      + intros. apply (proj2 (IHA1 x)) in H as H1. apply (proj2 (IHA2 x)) in H as H2.
        simp feval. rewrite H1. rewrite H2...
    - rename x into y, x0 into x. split.
      { destruct (quant_subst_skip_cond y A x).
        - rewrite simpl_subst_exists_skip...
        - rewrite simpl_subst_exists_propagate... fold V. generalize_fresh_var y A x x as y'.
          intros σ. apply feval_exists_equiv_if. intros.
          pose proof (H':=H). forward (H (A[y\y'][x\x])). 1: { eapply shape_eq_trans... }
          destruct (H y') as [_ ?]. rewrite <- (H0 σ (TConst v) v)... clear H H0.
          pose proof (H:=H'). forward (H (A[y\y'])) by auto.
          destruct (H x) as [? _]. unfold V. etrans. { apply H0. }
          clear H H0. pose proof (H:=H'). forward (H A)... destruct (H y) as [_ ?].
          forward (H0 (<[y':=v]> σ) y' v). { apply TEval_Var. apply (lookup_insert σ). }
          etrans. { symmetry. apply H0. } clear H0. destruct (H y) as [_ ?].
          forward (H0 σ (TConst v) v)... symmetry. rewrite <- H0.
          destruct (decide (y = y')).
          + subst. rewrite (insert_insert σ)...
          + destruct H4 as [|]; [contradiction|]. rewrite (insert_commute σ)...
            rewrite (feval_delete_state_var_head _ y')... }
      intros. destruct (decide (y = x)).
      + subst. rewrite simpl_subst_exists_skip... apply feval_exists_equiv_if.
        intros. forward (H A)... destruct (H x) as [_ ?].
        rewrite <- (H1 (<[x:=v]> σ) (TConst v0) v0)...
        rewrite <- (H1 σ (TConst v0) v0)... rewrite (insert_insert σ)...
      + destruct (decide (x ∈ formula_fvars A)).
        2: { rewrite simpl_subst_exists_skip... rewrite feval_delete_state_var_head... simpl.
             set_solver. }
        rewrite simpl_subst_exists_propagate... fold V. generalize_fresh_var y A x t0 as x'.
        apply feval_exists_equiv_if. intros.
        pose proof (H':=H). forward (H (A[y\x'][x\t0])). { eapply shape_eq_trans... }
        destruct (H x') as [_ ?]. rewrite <- (H1 σ (TConst v0) v0)... clear H1 H.
        pose proof (H:=H'). forward (H (A[y\x'])). { eapply shape_eq_trans... }
        destruct (H x) as [_ ?]. specialize (H1 (<[x':=v0]> σ) t0 v). forward H1.
        { apply teval_delete_state_var_head... }
        symmetry. etrans. { symmetry. exact H1. } symmetry. clear H1 H.
        destruct (decide (y = x')).
        * subst. rename H' into H. forward (H A)...
          destruct (H x') as [? ?].
          symmetry. etrans. {  apply H1. } symmetry.
          forward (H2 (<[x:=v]> σ) (TConst v0) v0)...
          etrans. { symmetry. apply H2. } rewrite (insert_commute σ)...
        * destruct H3 as [|H3]; [contradiction|]. rewrite (insert_commute σ)...
          pose proof (H:=H'). forward (H A). { eapply shape_eq_trans... }
          destruct (H y) as [_ ?]. specialize (H1 (<[x':=v0]> (<[x:=v]> σ)) x' v0). forward H1.
          { constructor. rewrite (lookup_insert (<[x:=v]> σ))... }
          symmetry. etrans. { symmetry. apply H1. } symmetry. clear H1.
          rewrite (insert_commute (<[x:=v]> σ))... rewrite feval_delete_state_var_head...
          destruct (H y) as [_ ?]. specialize (H1 (<[x:=v]> σ) (TConst v0) v0). forward H1...
  Qed.

  Lemma feval_subst σ A x t v :
    teval σ t v →
    feval (<[x:=v]> σ) A ↔ feval σ (A[x \ t]).
  Proof. apply fequiv_subst_and_diag. Qed.

  Lemma fequiv_subst_diag A x :
    <! A[x \ x] !> ≡ A.
  Proof with auto. apply fequiv_subst_and_diag. Qed.

  Global Instance subst_proper : Proper ((≡@{@formula V}) ==> (=) ==> (=) ==> (≡@{@formula V})) subst_formula.
  Proof with auto.
    intros A B H x ? <- t ? <- σ; split; intros.
    - rewrite <- feval_subst...
    - apply feval_wf in H0 as ?.
      destruct (decide (x ∈ formula_fvars A)); destruct (decide (x ∈ formula_fvars B)).
      + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
        rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
      + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
        rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
      + exfalso. rewrite fequiv_subst_non_free in H0...
        rewrite feval_delete_state_var with (x:=x) in H0...
        apply H in H0. apply feval_wf in H0 as ?. apply formula_wf_state_covers in H2.
        set_solver.
      + rewrite fequiv_subst_non_free in H0... rewrite fequiv_subst_non_free... apply H...
    - apply feval_wf in H0 as ?.
      destruct (decide (x ∈ formula_fvars A)); destruct (decide (x ∈ formula_fvars B)).
      + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
        rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
      + exfalso. rewrite fequiv_subst_non_free in H0...
        rewrite feval_delete_state_var with (x:=x) in H0...
        apply H in H0. apply feval_wf in H0 as ?. apply formula_wf_state_covers in H2.
        set_solver.
      + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
        rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
      + rewrite fequiv_subst_non_free in H0... rewrite fequiv_subst_non_free... apply H...
  Qed.

Lemma fequiv_exists_alpha_equiv x x' τ A :
  x' ∉ formula_fvars A →
  <! exists x : τ, A !> ≡ <! exists x' : τ, A[x \ x'] !>.
Proof with auto.
  intros Hfree M σ b.
  apply feval_exists_equiv.
  intros. rewrite <- feval_subst with (v:=v).
  2: { constructor. apply lookup_insert_Some. left... }
  destruct (decide (x = x')).
  + subst. rewrite (insert_insert σ)...
  + rewrite (insert_commute σ)...
    rewrite (feval_delete_state_var_head x')...
Qed.

Lemma fequiv_forall_alpha_equiv x x' τ A :
    x' ∉ formula_fvars A →
    <! forall x : τ, A !> ≡ <! forall x' : τ, A[x \ x'] !>.
Proof with auto.
  intros. unfold FForall. rewrite fequiv_exists_alpha_equiv with (x':=x')...
  rewrite simpl_subst_not...
Qed.

Lemma fequiv_exists_non_free_binder x τ A :
  x ∉ formula_fvars A →
  ((∃ v, v ∈ τ) ∧ <! exists x : τ, A !> ≡ A) ∨
    ((value_ty_is_empty τ) ∧ <! exists x : τ, A !> ≡ <! false !>).
Proof with auto.
  intros H. destruct (value_ty_choice τ).
  - left. destruct s as [v Hv]. split; [eauto |].
    intros M σ b. split; intros.
    + inversion H0; subst.
      * destruct H5 as [v' [_ ?]]. apply feval_delete_state_var_head in H1...
      * apply H5 in Hv. apply feval_delete_state_var_head in Hv...
    + destruct b.
      * apply FEval_Exists_True. exists v. split... apply feval_delete_state_var_head...
      * apply FEval_Exists_False. intros. apply feval_delete_state_var_head...
  - right. split... split; intros.
    + inversion H0; subst.
      * destruct H5 as [? [contra _]]. apply n in contra as [].
      * constructor. constructor.
    + inversion H0; subst. inversion H2; subst. constructor. intros. apply n in H1 as [].
Qed.

Lemma fequiv_subst_trans : ∀ A (x1 x2 x3 : variable),
    x2 ∉ formula_fvars A →
    <! A[x1 \ x2][x2 \ x3] !> ≡ <! A[x1 \ x3] !>.
Proof with auto.
  intros.
  destruct (decide (x1 ∈ formula_fvars A)).
  2:{ rewrite fequiv_subst_non_free with (x:=x1)... rewrite fequiv_subst_non_free...
      rewrite fequiv_subst_non_free... }
  destruct (decide (x1 = x2)).
  1:{ subst. rewrite fequiv_subst_diag... }
  destruct (decide (x2 = x3)).
  1:{ subst. rewrite fequiv_subst_diag... }
  split; intros.
  - apply feval_wf in H0 as H1. apply formula_wf_subst_term_wf in H1.
    2:{ rewrite fvars_subst_free... set_solver. }
    apply term_wf_teval in H1 as [v3 Hv3]. rewrite <- feval_subst with (v:=v3) in H0...
    apply feval_wf in H0 as H1. apply formula_wf_subst_term_wf in H1...
    apply term_wf_teval in H1 as [v2 Hv2].
    inversion Hv2; subst. apply lookup_insert_Some in H2. destruct H2 as [[? ?] | [[] _]]...
    subst v2. clear H1. rewrite <- feval_subst with (v:=v3) in H0...
    rewrite (insert_commute σ) in H0... apply feval_delete_state_var_head in H0...
    rewrite <- feval_subst with (v:=v3)...
  - apply feval_wf in H0 as H1. apply formula_wf_subst_term_wf in H1...
    apply term_wf_teval in H1 as [v3 Hv3]. rewrite <- feval_subst with (v:=v3) in H0...
    rewrite <- feval_subst with (v:=v3)... rewrite <- feval_subst with (v:=v3)...
    2:{ constructor. apply lookup_insert. }
    rewrite (insert_commute σ)... rewrite feval_delete_state_var_head...
Qed.

Lemma fequiv_subst_commute : ∀ A x1 t1 x2 t2,
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    <! A[x1 \ t1][x2 \ t2] !> ≡ <! A[x2 \ t2][x1 \ t1] !>.
Proof with auto.
  intros. split; intros.
  - destruct (decide (x1 ∈ formula_fvars A)); destruct (decide (x2 ∈ formula_fvars A)).
    + apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3.
      2:{ rewrite fvars_subst_free... apply elem_of_union. left. apply elem_of_difference.
          rewrite not_elem_of_singleton. split... }
      apply term_wf_teval in H3 as [v2 Hv2].
      rewrite <- feval_subst with (v:=v2) in H2...
      apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3...
      apply term_wf_teval in H3 as [v1 Hv1].
      rewrite <- feval_subst with (v:=v1) in H2...
      rewrite teval_delete_state_var_head in Hv1...
      apply feval_subst with (v:=v1)... apply feval_subst with (v:=v2)...
      * apply teval_delete_state_var_head...
      * rewrite (insert_commute σ)...
    + rewrite fequiv_subst_non_free in H2.
      2:{ rewrite fvars_subst_free... apply not_elem_of_union. split...
          apply not_elem_of_difference. left... }
      apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3...
      apply term_wf_teval in H3 as [v1 Hv1].
      rewrite <- feval_subst with (v:=v1) in H2...
      apply feval_subst with (v:=v1)... rewrite fequiv_subst_non_free...
    + apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3...
      2:{ rewrite fvars_subst_non_free... }
      apply term_wf_teval in H3 as [v2 Hv2].
      rewrite <- feval_subst with (v:=v2) in H2...
      rewrite fequiv_subst_non_free in H2...
      rewrite fequiv_subst_non_free.
      2:{ rewrite fvars_subst_free...  apply not_elem_of_union. split...
          apply not_elem_of_difference. left... }
      apply feval_subst with (v:=v2)...
    + rewrite fequiv_subst_non_free in H2 by (rewrite fvars_subst_non_free; auto).
      rewrite fequiv_subst_non_free in H2...
      rewrite fequiv_subst_non_free by (rewrite fvars_subst_non_free; auto).
      rewrite fequiv_subst_non_free...
  - destruct (decide (x1 ∈ formula_fvars A)); destruct (decide (x2 ∈ formula_fvars A)).
    + apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3.
      2:{ rewrite fvars_subst_free... apply elem_of_union. left. apply elem_of_difference.
          rewrite not_elem_of_singleton. split... }
      apply term_wf_teval in H3 as [v1 Hv1].
      rewrite <- feval_subst with (v:=v1) in H2...
      apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3...
      apply term_wf_teval in H3 as [v2 Hv2].
      rewrite <- feval_subst with (v:=v2) in H2...
      rewrite teval_delete_state_var_head in Hv2...
      apply feval_subst with (v:=v2)... apply feval_subst with (v:=v1)...
      * apply teval_delete_state_var_head...
      * rewrite (insert_commute σ)...
    + apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3...
      2:{ rewrite fvars_subst_non_free... }
      apply term_wf_teval in H3 as [v1 Hv1].
      rewrite <- feval_subst with (v:=v1) in H2...
      rewrite fequiv_subst_non_free in H2...
      rewrite fequiv_subst_non_free.
      2:{ rewrite fvars_subst_free...  apply not_elem_of_union. split...
          apply not_elem_of_difference. left... }
      apply feval_subst with (v:=v1)...
    + rewrite fequiv_subst_non_free in H2.
      2:{ rewrite fvars_subst_free... apply not_elem_of_union. split...
          apply not_elem_of_difference. left... }
      apply feval_wf in H2 as H3. apply formula_wf_subst_term_wf in H3...
      apply term_wf_teval in H3 as [v2 Hv2].
      rewrite <- feval_subst with (v:=v2) in H2...
      apply feval_subst with (v:=v2)... rewrite fequiv_subst_non_free...
    + rewrite fequiv_subst_non_free in H2 by (rewrite fvars_subst_non_free; auto).
      rewrite fequiv_subst_non_free in H2...
      rewrite fequiv_subst_non_free by (rewrite fvars_subst_non_free; auto).
      rewrite fequiv_subst_non_free...
Qed.
(* Lemma fequiv_exists_subst_skip : ∀ y A x t, *)


(* Lemma subst_eq_congr : forall M σ φ x t u b, *)
(*   feval M σ <! t = u !> → *)
(*   feval M σ <! φ[x\t] !> b <→ *)
(*   feval M σ <! φ[x\u] !> b. *)
(* Proof with auto. *)

(* Lemma feval_eq_refl : forall t st, *)
(*   ~ feval M σ (F_Simple (φT_Pred "="%string [t; t])) false. *)
(* Proof with auto. *)
(*   intros t st contra. inversion contra; subst. *)
(*   inversion H0; subst. *)
(*   destruct (pctx_eq_semantics pctx) as [eq_pdef [Heqp1 Heqp2]]. *)
(*   rewrite Heqp1 in H2. inversion H2. subst pdef. *)
(*   destruct (Heqp2 st fctx) as [Heqp_refl _]. *)
(*   specialize (Heqp_refl t). *)
(*   assert (feval M σ fctx pctx <! t = t !> true). *)
(*   { apply FEval_Simple. apply SFEval_Pred with eq_pdef... *)
(*     destruct eq_pdef. *)
(*     apply Pred_Eval with n_params prel Hfnal... } *)
(*   destruct (feval_functional _ _ _ _ H contra). *)
(* Qed. *)
