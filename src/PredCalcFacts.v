From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalcBasic PredCalcEquiv PredCalcSubst.

Section facts.
  Context {M : model}.

  Implicit Types t : term (value M).
  Implicit Types af : @atomic_formula (value M).
  Implicit Types A B C : formula (value M).
  Implicit Types v : value M.

  Local Lemma fequiv_subst_and_diag A x :
    <! A[x \ x] !> ≡ A ∧ ∀ σ t v, teval σ t v → feval (<[x:=v]> σ) A ↔ feval σ (A[x \ t]).
  Proof with auto.
    generalize dependent x. induction A; intros.
    - unfold subst_formula. simpl. rewrite subst_af_diag... split...
      intros. simp feval. apply afeval_subst...
    - setoid_rewrite simpl_subst_not. split.
      + destruct (IHA x) as [-> _]...
      + intros. destruct (IHA x) as [_ ?]. simp feval. rewrite H0...
    - setoid_rewrite simpl_subst_and. split.
      + destruct (IHA1 x) as [-> _]... destruct (IHA2 x) as [-> _]...
      + intros. apply (proj2 (IHA1 x)) in H as H1. apply (proj2 (IHA2 x)) in H as H2.
        simp feval. rewrite H1. rewrite H2...
    - setoid_rewrite simpl_subst_or. split.
      + destruct (IHA1 x) as [-> _]... destruct (IHA2 x) as [-> _]...
      + intros. apply (proj2 (IHA1 x)) in H as H1. apply (proj2 (IHA2 x)) in H as H2.
        simp feval. rewrite H1. rewrite H2...
    - rename x into y, x0 into x. split.
      { destruct (quant_subst_skip_cond y A x).
        - rewrite simpl_subst_exists_skip...
        - rewrite simpl_subst_exists_propagate... generalize_fresh_var y A x x as y'.
          intros σ. apply feval_exists_equiv_if. intros.
          pose proof (H':=H). forward (H (A[y\y'][x\x])). 1: { eapply shape_eq_trans... }
          destruct (H y') as [_ ?]. rewrite <- (H0 σ (TConst v) v)... clear H H0.
          pose proof (H:=H'). forward (H (A[y\y'])) by auto.
          destruct (H x) as [? _]. etrans. { apply H0. }
          clear H H0. pose proof (H:=H'). forward (H A)... destruct (H y) as [_ ?].
          forward (H0 (<[y':=v]> σ) y' v). { apply TEval_Var. rewrite (lookup_total_insert σ)... }
          etrans. { symmetry. apply H0. } clear H0. destruct (H y) as [_ ?].
          forward (H0 σ (TConst v) v)... symmetry. rewrite <- H0.
          destruct (decide (y = y')).
          + subst. rewrite (insert_insert σ)...
          + destruct H4 as [|]; [contradiction|]. rewrite (insert_commute σ)...
            rewrite (feval_delete_state_var_head y')... }
      intros. destruct (decide (y = x)).
      + subst. rewrite simpl_subst_exists_skip... apply feval_exists_equiv_if.
        intros. forward (H A)... destruct (H x) as [_ ?].
        rewrite <- (H1 (<[x:=v]> σ) (TConst v0) v0)...
        rewrite <- (H1 σ (TConst v0) v0)... rewrite (insert_insert σ)...
      + destruct (decide (x ∈ formula_fvars A)).
        2: { rewrite simpl_subst_exists_skip... rewrite feval_delete_state_var_head... simpl.
             set_solver. }
        rewrite simpl_subst_exists_propagate... generalize_fresh_var y A x t as x'.
        apply feval_exists_equiv_if. intros.
        pose proof (H':=H). forward (H (A[y\x'][x\t])). { eapply shape_eq_trans... }
        destruct (H x') as [_ ?]. rewrite <- (H1 σ (TConst v0) v0)... clear H1 H.
        pose proof (H:=H'). forward (H (A[y\x'])). { eapply shape_eq_trans... }
        destruct (H x) as [_ ?]. specialize (H1 (<[x':=v0]> σ) t v). forward H1.
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
          { constructor. rewrite (lookup_total_insert (<[x:=v]> σ))... }
          symmetry. etrans. { symmetry. apply H1. } symmetry. clear H1.
          rewrite (insert_commute (<[x:=v]> σ))... rewrite (feval_delete_state_var_head x')...
          destruct (H y) as [_ ?]. specialize (H1 (<[x:=v]> σ) (TConst v0) v0). forward H1...
  Qed.

  Lemma feval_subst {σ A x} v t :
    teval σ t v →
    feval σ (A[x \ t]) ↔ feval (<[x:=v]> σ) A .
  Proof with auto. symmetry. apply fequiv_subst_and_diag... Qed.

  Lemma fequiv_subst_diag A x :
    <! A[x \ x] !> ≡ A.
  Proof with auto. apply fequiv_subst_and_diag. Qed.

  Global Instance subst_proper : Proper ((≡@{@formula (value M)}) ==> (=) ==> (=) ==> (≡)) subst_formula.
  Proof with auto.
    intros A B H x ? <- t ? <- σ. pose proof (teval_total σ t) as [v Hv].
    rewrite (feval_subst v)... rewrite (feval_subst v)...
  Qed.

  Global Instance subst_proper_in_term : Proper ((=) ==> (=) ==> (≡@{@term (value M)}) ==> (≡)) subst_formula.
  Proof with auto.
    intros A ? <- x ? <- t1 t2 Hterm σ. pose proof (teval_total σ t1) as [v Hv].
    apply Hterm in Hv as Hv'. rewrite (feval_subst v)... rewrite (feval_subst v)...
  Qed.

  Global Instance fexists_proper : Proper ((=) ==> (≡@{@formula (value M)}) ==> (≡@{@formula (value M)})) FExists.
  Proof with auto.
    intros x ? <- A B H σ. apply feval_exists_equiv_if. intros v. rewrite H...
  Qed.

  Global Instance fforall_proper : Proper ((=) ==> (≡@{@formula (value M)}) ==> (≡@{@formula (value M)})) FForall.
  Proof with auto.
    intros x ? <- A B H σ. unfold FForall. rewrite H...
  Qed.

  Global Instance subst_proper_fent : Proper ((⇛@{M}) ==> (=) ==> (=) ==> (⇛)) subst_formula.
  Proof with auto.
    intros A B Hent x ? <- t ? <- σ. pose proof (teval_total σ t) as [v Hv].
    rewrite (feval_subst v)... rewrite (feval_subst v)...
  Qed.

  Global Instance fexists_proper_fent : Proper ((=) ==> (⇛) ==> (⇛@{M})) FExists.
  Proof with auto.
    intros x ? <- A B Hent σ H. simp feval. simp feval in H. destruct H as [v Hv].
    exists v. revert Hv. rewrite (feval_subst v)... rewrite (feval_subst v)...
  Qed.

  Global Instance fforall_proper_fent : Proper ((=) ==> (⇛) ==> (⇛@{M})) FForall.
  Proof with auto.
    intros x ? <- A B H. unfold FForall. apply f_ent_contrapositive.
    apply f_ent_contrapositive in H. rewrite H. reflexivity.
  Qed.

  Lemma fexists_alpha_equiv x x' A :
    x' ∉ formula_fvars A →
    <! ∃ x, A !> ≡ <! ∃ x', A[x \ x'] !>.
  Proof with auto.
    intros Hfree σ. apply feval_exists_equiv_if. intros.
    rewrite (feval_subst v)... rewrite (feval_subst v)...
    rewrite (feval_subst v). 2: { constructor. rewrite (lookup_total_insert σ)... }
    destruct (decide (x = x')).
    - subst. rewrite (insert_insert σ)...
    - rewrite (insert_commute σ)... rewrite feval_delete_state_var_head with (x:=x')...
  Qed.

  Lemma fforall_alpha_equiv x x' A :
    x' ∉ formula_fvars A →
    <! ∀ x, A !> ≡ <! ∀ x', A[x \ x'] !>.
  Proof with auto.
    intros. unfold FForall. rewrite fexists_alpha_equiv with (x':=x')...
    rewrite simpl_subst_not...
  Qed.

  Lemma fexists_unused x A :
    x ∉ formula_fvars A →
    <! ∃ x, A !> ≡ A.
  Proof with auto.
    intros H σ. simp feval. split.
    - intros [v Hv]. rewrite (feval_subst v) in Hv...
      rewrite feval_delete_state_var_head in Hv...
    - intros. exists ⊥. rewrite (feval_subst ⊥)... rewrite feval_delete_state_var_head...
  Qed.

  Lemma fforall_unused x A :
    x ∉ formula_fvars A →
    <! ∀ x, A !> ≡ A.
  Proof with auto.
    unfold FForall. intros. rewrite fexists_unused... intros σ.
    simp feval. rewrite feval_stable...
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
    intros σ. pose proof (teval_total σ x3) as [v3 Hv3].
    rewrite (feval_subst v3)... rewrite (feval_subst v3).
    2:{ constructor. rewrite (lookup_total_insert σ)... }
    rewrite (feval_subst v3)... rewrite (insert_commute σ)...
    rewrite (feval_delete_state_var_head x2)...
  Qed.

  Lemma fequiv_subst_commute A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    <! A[x1 \ t1][x2 \ t2] !> ≡ <! A[x2 \ t2][x1 \ t1] !>.
  Proof with auto.
    split; intros.
    - destruct (decide (x1 ∈ formula_fvars A)); destruct (decide (x2 ∈ formula_fvars A)).
      + pose proof (teval_total σ t1) as [v1 Hv1]. rewrite (feval_subst v1)...
        pose proof (teval_total (<[x1:=v1]> σ) t2) as [v2 Hv2]. rewrite (feval_subst v2)...
        rewrite (insert_commute σ)... apply (teval_delete_state_var_head) in Hv2...
        rewrite <- (teval_delete_state_var_head x2 v2) in Hv1...
        rewrite (feval_subst v2) in H2... rewrite (feval_subst v1) in H2...
      + rewrite fequiv_subst_non_free in H2.
        2: { rewrite fvars_subst_free... set_solver. }
        pose proof (teval_total σ t1) as [v1 Hv1]. rewrite (feval_subst v1)...
        rewrite fequiv_subst_non_free... rewrite <- feval_subst with (t:=t1)...
      + pose proof (teval_total σ t2) as [v2 Hv2]. rewrite (feval_subst v2) in H2...
        rewrite fequiv_subst_non_free in H2... rewrite <- feval_subst with (t:=t2) in H2...
        rewrite fequiv_subst_non_free... rewrite fvars_subst_free... set_solver.
      + rewrite fequiv_subst_non_free. 2: { rewrite fvars_subst_non_free... }
        rewrite fequiv_subst_non_free...
        rewrite fequiv_subst_non_free in H2. 2: { rewrite fvars_subst_non_free... }
        rewrite fequiv_subst_non_free in H2...
    - destruct (decide (x1 ∈ formula_fvars A)); destruct (decide (x2 ∈ formula_fvars A)).
      + pose proof (teval_total σ t2) as [v2 Hv2]. rewrite (feval_subst v2)...
        pose proof (teval_total (<[x2:=v2]> σ) t1) as [v1 Hv1]. rewrite (feval_subst v1)...
        rewrite (insert_commute σ)... apply (teval_delete_state_var_head) in Hv1...
        rewrite <- (teval_delete_state_var_head x1 v1) in Hv2...
        rewrite (feval_subst v1) in H2... rewrite (feval_subst v2) in H2...
      + pose proof (teval_total σ t1) as [v1 Hv1]. rewrite (feval_subst v1) in H2...
        rewrite fequiv_subst_non_free in H2... rewrite <- feval_subst with (t:=t1) in H2...
        rewrite fequiv_subst_non_free... rewrite fvars_subst_free... set_solver.
      + rewrite fequiv_subst_non_free in H2.
        2: { rewrite fvars_subst_free... set_solver. }
        pose proof (teval_total σ t2) as [v2 Hv2]. rewrite (feval_subst v2)...
        rewrite fequiv_subst_non_free... rewrite <- feval_subst with (t:=t2)...
      + rewrite fequiv_subst_non_free. 2: { rewrite fvars_subst_non_free... }
        rewrite fequiv_subst_non_free...
        rewrite fequiv_subst_non_free in H2. 2: { rewrite fvars_subst_non_free... }
        rewrite fequiv_subst_non_free in H2...
  Qed.

  Lemma simpl_feval_fimpl σ A B :
    feval σ <! A ⇒ B !> ↔ (feval σ A → feval σ B).
  Proof with auto.
    unfold FImpl. simp feval. split.
    - intros [|] ?... contradiction.
    - intros. destruct (feval_lem σ A)...
  Qed.

  Lemma simpl_feval_fiff σ A B :
    feval σ <! A ⇔ B !> ↔ (feval σ A ↔ feval σ B).
  Proof with auto.
    unfold FIff. simp feval. do 2 rewrite simpl_feval_fimpl. naive_solver.
  Qed.

  Lemma simpl_feval_fforall σ x A :
    feval σ <! ∀ x, A !> ↔ ∀ v, feval σ (A [x \ (TConst v)]).
  Proof with auto.
    unfold FForall. simp feval. setoid_rewrite (simpl_subst_not). split; intros.
    - destruct (feval_lem σ (A [x \ (TConst v)]))... exfalso. apply H. exists v. simp feval.
    - intros [v contra]. simp feval in contra...
  Qed.

End facts.
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
