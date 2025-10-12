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

Lemma fequiv_subst_not_free : forall A t x,
    x ∉ formula_fvars A ->
    <! A [x \ t] !> ≡ <! A !>.
Proof with auto.
  intros A t x. generalize dependent A.
  pose proof (@subst_formula_ind x t  (λ A B, x ∉ formula_fvars B -> A ≡ B)). simpl in H.
  apply H; clear H; intros...
  - rewrite subst_sf_not_free...
  - rewrite H... 
  - apply not_elem_of_union in H1 as [? ?]. rewrite H... rewrite H0...
  - apply not_elem_of_union in H1 as [? ?]. rewrite H... rewrite H0...
  - apply not_elem_of_union in H1 as [? ?]. rewrite H... rewrite H0...
  - intros M σ. simpl.
    remember (fresh_var y (quant_subst_fvars φ x t)) as y'.
    enough (forall v, feval M (<[y':=v]> σ) <! φ [y \ y'] [x \ t] !> ↔ feval M (<[y:=v]> σ) φ).
    { split; intros [v Hv]; exists v; apply H3... }
    intros v. apply not_elem_of_difference in H2 as [|]; [contradiction|].
    apply elem_of_singleton in H2. symmetry in H2. contradiction.
  - intros M σ. simpl.
    remember (fresh_var y (quant_subst_fvars φ x t)) as y'.
    enough (forall v, feval M (<[y':=v]> σ) <! φ [y \ y'] [x \ t] !> ↔ feval M (<[y:=v]> σ) φ).
    { split; intros v Hv; apply H3... }
    intros v. apply not_elem_of_difference in H2 as [|]; [contradiction|].
    apply elem_of_singleton in H2. symmetry in H2. contradiction.
Qed.

Lemma fequiv_subst_commute : ∀ A x₁ t₁ x₂ t₂,
    x₁ ≠ x₂ ->
    x₁ ∉ term_fvars t₂ →
    x₂ ∉ term_fvars t₁ →
    <! A[x₁ \ t₁][x₂ \ t₂] !> ≡ <! A[x₂ \ t₂][x₁ \ t₁] !>.
Proof with auto.
  induction A; intros.
  - unfold equiv. unfold fequiv. intros M σ. simpl. rewrite subst_sf_commute...
  - do 4 rewrite simpl_subst_not. rewrite IHA...
  - do 4 rewrite simpl_subst_and. rewrite IHA1... rewrite IHA2...
  - do 4 rewrite simpl_subst_or. rewrite IHA1... rewrite IHA2...
  - do 4 rewrite simpl_subst_implication. rewrite IHA1... rewrite IHA2...
  - destruct (quant_subst_skip_cond x A x₁); destruct (quant_subst_skip_cond x A x₂).
    + do 4 (rewrite simpl_subst_exists_skip; auto).
    + rewrite (simpl_subst_exists_skip)... rewrite simpl_subst_exists_propagate; auto...
      destruct (quant_subst_skip_cond (fresh_var x (quant_subst_fvars A x₂ t₂))
                  (A [x \ fresh_var x (quant_subst_fvars A x₂ t₂)][x₂ \ t₂]) x₁).
      * rewrite simpl_subst_exists_skip...
      * exfalso. destruct H3.
        -- subst x₁. admit.
        -- apply H3.
      intros M σ. simpl.


      rewrite (simpl_subst_exists_skip)... destruct H3.
      * subst.

      simpl.
      rewrite simpl_subst_exists_propagate; auto...
      do 2 (rewrite simpl_subst_exists_propagate; auto)...

      rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_skip...
      rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_skip...
Admitted.


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
