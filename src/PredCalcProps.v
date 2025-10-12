From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import Tactics PredCalc PredCalcSubst PredCalcEquiv.
From stdpp Require Import gmap fin_maps.

Lemma fequiv_subst_id : forall A x,
    <! A[x \ x] !> ≡ A.
Proof with auto.
  intros A x. generalize dependent A.
  apply subst_formula_ind with (P:=λ A B, A ≡ B); intros...
  - rewrite subst_sf_id...
  - rewrite H. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - intros M σ. simpl.
    enough (forall v, feval M (<[y':=v]> σ) <! φ [y \ y'] [x \ x] !> <-> feval M (<[y:=v]> σ) φ).
    { split; intros [v Hv]; exists v; apply H2; apply Hv. }
    intros v.
    specialize H with (<! φ [y \ y'] !>). forward H by auto.
    pose proof (H M (<[y':=v]> σ)) as H. rewrite H. rewrite <- (feval_subst v).
    2: { apply TEval_Var. apply lookup_insert. }
    destruct (decide (y = y')).
    + unfold y' in *. rewrite <- e. rewrite (insert_insert σ)...
    + rewrite (insert_commute σ)...
      pose proof (fresh_var_fresh y (quant_subst_fvars φ x x)).
      apply quant_subst_fvars_inv in H2 as (?&?&?).
      rewrite (feval_delete_state_var_head y')...
  - intros M σ. simpl.
    enough (forall v, feval M (<[y':=v]> σ) <! φ [y \ y'] [x \ x] !> <-> feval M (<[y:=v]> σ) φ).
    { split; intros Hv v; apply H2... }
    intros v.
    specialize H with (<! φ [y \ y'] !>). forward H by auto.
    pose proof (H M (<[y':=v]> σ)) as H. rewrite H. rewrite <- (feval_subst v).
    2: { apply TEval_Var. apply lookup_insert. }
    destruct (decide (y = y')).
    + unfold y' in *. rewrite <- e. rewrite (insert_insert σ)...
    + rewrite (insert_commute σ)...
      pose proof (fresh_var_fresh y (quant_subst_fvars φ x x)).
      apply quant_subst_fvars_inv in H2 as (?&?&?).
      rewrite (feval_delete_state_var_head y')...
Qed.

Lemma fequiv_exists_alpha_equiv : forall x x' A,
    x' ∉ formula_fvars A ->
    <! exists x, A !> ≡ <! exists x', A[x \ x'] !>.
Proof with auto.
  intros x x' A Hfree M σ. simpl.
  enough (forall v, (feval M (<[x:=v]> σ) A
                  ↔ feval M (<[x':=v]> σ) <! A [x \ x'] !>)).
  { split; intros [v Hv]; exists v; apply H; apply Hv. }
  intros v. rewrite <- (feval_subst v).
  2: { apply TEval_Var. apply lookup_insert. }
  destruct (decide (x = x')).
  - subst. rewrite (insert_insert σ)...
  - rewrite (insert_commute σ)... rewrite (feval_delete_state_var_head x')...
Qed.

Lemma fequiv_forall_alpha_equiv : forall x x' A,
    x' ∉ formula_fvars A ->
    <! forall x, A !> ≡ <! forall x', A[x \ x'] !>.
Proof with auto.
  intros x x' A Hfree M σ. simpl.
  enough (forall v, (feval M (<[x:=v]> σ) A
                  ↔ feval M (<[x':=v]> σ) <! A [x \ x'] !>)).
  { split; intros Hv v; apply H... }
  intros v. rewrite <- (feval_subst v).
  2: { apply TEval_Var. apply lookup_insert. }
  destruct (decide (x = x')).
  - subst. rewrite (insert_insert σ)...
  - rewrite (insert_commute σ)... rewrite (feval_delete_state_var_head x')...
Qed.

Lemma fequiv_exists_subst_skip : ∀ y A x t,

(* HACK: subst_formula_not_free *)
(* HACK: subst_formula_commute *)

(* Lemma feval_subst_commute : forall M σ φ x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ is_free_in_term x₁ t₂ -> *)
(*     negb $ is_free_in_term x₂ t₁ -> *)
(*     feval M σ <! φ[x₁ \ t₁][x₂ \ t₂] !> <-> feval M σ <! φ[x₂ \ t₂][x₁ \ t₁] !>. *)
(* Proof with auto. *)

(* Lemma subst_eq_congr : forall M σ φ x t u b, *)
(*   feval M σ <! t = u !> -> *)
(*   feval M σ <! φ[x\t] !> b <-> *)
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
