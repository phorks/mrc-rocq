From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import Tactics PredCalc PredCalcSubst PredCalcEquiv.
From stdpp Require Import gmap fin_maps.

Lemma fequiv_subst_diag : forall A x,
    <! A[x \ x] !> ≡ A.
Proof with auto.
  intros A x. generalize dependent A.
  apply subst_formula_ind with (P:=λ A B, A ≡ B); intros...
  - rewrite subst_sf_diag...
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

Lemma fequiv_subst_non_free : forall A t x,
    x ∉ formula_fvars A ->
    <! A [x \ t] !> ≡ <! A !>.
Proof with auto.
  intros A t x. generalize dependent A.
  pose proof (@subst_formula_ind x t  (λ A B, x ∉ formula_fvars B -> A ≡ B)). simpl in H.
  apply H; clear H; intros...
  - rewrite subst_sf_non_free...
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

(* TODO: move it  *)
Lemma subst_fvars_superset A x t : formula_fvars (A[x \ t]) ⊆ formula_fvars A ∪ term_fvars t.
Proof with auto.
  destruct (decide (x ∈ formula_fvars A)).
  - rewrite subst_free_fvars... apply union_mono_r. apply subseteq_difference_l...
  - rewrite subst_non_free_fvars... apply union_subseteq_l.
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

Lemma fequiv_exists_non_free_binder x A :
  x ∉ formula_fvars A ->
  <! exists x, A !> ≡ A.
Proof with auto.
  intros. intros M σ. simpl. intros. split.
  - intros [v Hv]. rewrite feval_delete_state_var_head in Hv...
  - intros H'. exists value_unit. rewrite feval_delete_state_var_head...
Qed.

Lemma fequiv_forall_non_free_binder x A :
  x ∉ formula_fvars A ->
  <! forall x, A !> ≡ A.
Proof with auto.
  intros. intros M σ. simpl. intros. split.
  - intros Hv. specialize Hv with value_unit. rewrite feval_delete_state_var_head in Hv...
  - intros H' v. rewrite feval_delete_state_var_head...
Qed.

(* (* TODO: prove this and make morphisms *) *)
Lemma subst_proper : forall A B x t,
  A ≡ B ->
  A[x \ t] ≡ B[x \ t].
Proof.
  intros. unfold equiv, fequiv in *. intros M σ. specialize H with M σ.
  induction A.
  - admit.
  - simpl in H.
Admitted.

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
    + rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_propagate; auto...
      destruct (quant_subst_skip_cond (fresh_var x (quant_subst_fvars A x₂ t₂))
                  (A [x \ fresh_var x (quant_subst_fvars A x₂ t₂)][x₂ \ t₂]) x₁).
      * rewrite simpl_subst_exists_skip...
      * exfalso. destruct H3.
        -- subst x₁.
           pose proof (fresh_var_fresh x (quant_subst_fvars A x₂ t₂)).
           apply quant_subst_fvars_inv in H3 as (?&?&?).
           assert (x ∈ formula_fvars A).
           { destruct (decide (x ∈ formula_fvars A))... exfalso.
             pose proof (fresh_var_free x (quant_subst_fvars A x₂ t₂)).
             forward H10; try contradiction. set_solver. }
           rewrite subst_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7.
              apply elem_of_union in H7. rewrite elem_of_difference in H7.
              rewrite not_elem_of_singleton in H7. destruct H7 as [[? []]|]...
              rewrite elem_of_singleton in H7. exfalso. apply H6...
           ++ rewrite subst_free_fvars... rewrite elem_of_union.
              left. rewrite elem_of_difference. rewrite elem_of_singleton. split...
        -- apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction.
           apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction.
           simpl in H7. rewrite elem_of_singleton in H7. apply H6. symmetry...
    + admit.
    + rewrite simpl_subst_exists_propagate... rewrite (simpl_subst_exists_propagate) with (φ:=A)...
      rewrite simpl_subst_exists_propagate.
      * rewrite (simpl_subst_exists_propagate).
        -- remember (fresh_var x (quant_subst_fvars A x₁ t₁)) as y1'.
           remember (fresh_var y1' (quant_subst_fvars (A [x \ y1'] [x₁ \ t₁]) x₂ t₂)) as y1.
           remember (fresh_var x (quant_subst_fvars A x₂ t₂)) as y2'.
           remember (fresh_var y2' (quant_subst_fvars (A [x \ y2'] [x₂ \ t₂]) x₁ t₁)) as y2.
           pose proof (fresh_var_fresh x (quant_subst_fvars A x₁ t₁)). rewrite <- Heqy1' in H7.
           clear Heqy1'.
           pose proof (fresh_var_fresh x (quant_subst_fvars A x₂ t₂)). rewrite <- Heqy2' in H8.
           clear Heqy2'.
           pose proof (fresh_var_fresh y1' (quant_subst_fvars (A[x\y1'][x₁\t₁]) x₂ t₂)).
           rewrite <- Heqy1 in H9. clear Heqy1.
           pose proof (fresh_var_fresh y2' (quant_subst_fvars (A[x\y2'][x₂\t₂]) x₁ t₁)).
           rewrite <- Heqy2 in H10. clear Heqy2.
           unfold quant_subst_fvars in H7, H8, H9, H10.
           do 2 rewrite not_elem_of_union in H7. rewrite not_elem_of_singleton in H7.
           do 2 rewrite not_elem_of_union in H8. rewrite not_elem_of_singleton in H8.
           do 2 rewrite not_elem_of_union in H9. rewrite not_elem_of_singleton in H9.
           do 2 rewrite not_elem_of_union in H10. rewrite not_elem_of_singleton in H10.
           remember (fresh_var x (formula_fvars A ∪ term_fvars t₁ ∪
                                    term_fvars t₂ ∪ {[x₁; x₂; y1'; y1; y2'; y2]})) as x'.

           etrans.
           ++ rewrite fequiv_exists_alpha_equiv with (x':=x'); [reflexivity|].
              rewrite subst_free_fvars. rewrite subst_free_fvars. rewrite subst_free_fvars.
              rewrite subst_free_fvars.
              pose proof (fresh_var_fresh x (formula_fvars A ∪ term_fvars t₁ ∪
                                    term_fvars t₂ ∪ {[x₁; x₂; y1'; y1; y2'; y2]})) as H'.
              rewrite <- Heqx' in H'. set_solver.
              pose proof (fresh_var )
                     +++

                apply subst_fvars_superset. )
           }
           rewrite subst_free_fvars in H9...
           2: {  rewrite subst_free_fvars... }






          simpl. etrans.
           ++ rewrite fequiv_exists_alpha_equiv.
           pose proof (subst_fvars_superset )

          eapply elem_of_weaken in H7.
           2: {  }





          rewrite subst_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7.
              apply elem_of_union in H7. rewrite elem_of_difference in H7.
              rewrite not_elem_of_singleton in H7. destruct H7 as [[? []]|]...
              rewrite elem_of_singleton in H7. exfalso. apply H6...
           ++ rewrite subst_free_fvars... rewrite elem_of_union.
              left. rewrite elem_of_difference. rewrite elem_of_singleton. split...

              apply not_elem_of_union.
              rewrite elem_of_difference. rewrite elem_of_singleton.
              split...
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
           rewrite subst_non_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7. apply elem_of_singleton in H7...
           ++ rewrite subst_free_fvars... apply not_elem_of_union.
              rewrite elem_of_difference. rewrite elem_of_singleton.
              split...
              ** intros contra.
              ** rewrite subst_free_fvars in H7... apply elem_of_union in H7.
                 rewrite elem_of_difference in H7. rewrite elem_of_singleton in H7.
                 destruct H7 as [[? []]|]... simpl in H3. apply elem_of_singleton in H3...
              **
           ++ destruct (decide (x ∈ formula_fvars A)).
              ** rewrite subst_free_fvars... apply not_elem_of_union.
                 rewrite elem_of_difference. rewrite elem_of_singleton.
                 split.
                 --- intros [? ?].
                 destruct H7 as [[? []]|]... simpl in H3. apply elem_of_singleton in H3...
              ** rewrite subst_non_free_fvars in H7...
           pose proof (subst_fvars (A [x \ (fresh_var x (quant_subst_fvars A x₂ t₂))]) x₂ t₂).
           destruct H3 as [[? ?] | [? ?]].
           ++ rewrite H8 in *. clear H8. admit.
           ++
        -- apply H3. rewrite subst_fvars
      intros M σ. simpl.


      rewrite (simpl_subst_exists_skip)... destruct H3.
      * subst.

      simpl.
      rewrite simpl_subst_exists_propagate; auto...
      do 2 (rewrite simpl_subst_exists_propagate; auto)...

      rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_skip...
      rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_skip...
Admitted.


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
