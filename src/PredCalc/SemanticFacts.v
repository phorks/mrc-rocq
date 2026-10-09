From Equations Require Import Equations.
From stdpp Require Import fin_maps gmap.
From MRC Require Import Prelude.
From MRC Require Import Lib.
From MRC Require Import Model.
From MRC.PredCalc Require Import Basic Equiv SyntacticFacts.

Section subst.
  Context {M : model}.
  Local Notation term := (term M).
  Local Notation atomic_formula := (atomic_formula M).
  Local Notation formula := (formula M).

  Implicit Types x y z : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A B C : formula.
  Implicit Types v : value M.

  Lemma teval_delete_state_var x {σ t v} :
    x ∉ term_fvars t →
    teval σ t v ↔ teval (delete x σ) t v.
  Proof with auto.
    intros Hfree. split.
    - intros H. revert Hfree. assert (H':=H). revert H H'.
      generalize dependent v. generalize dependent t.
      apply (teval_ind_mut _
                (λ t v _, teval σ t v → x ∉ term_fvars t → teval (delete x σ) t v)
                (λ args vargs _, forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
                                teval_list σ args vargs → teval_list (delete x σ) args vargs)).
      + intros. constructor.
      + intros x' v H H' Hfree. constructor. simpl in Hfree.
        destruct (decide (x' = x)); subst; simpl.
        * apply not_elem_of_singleton in Hfree. contradiction.
        * pose proof (@lookup_total_delete_ne _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ)...
      + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_App with vargs...
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
      apply (teval_ind_mut _
                (λ t v _, teval (delete x σ) t v → x ∉ term_fvars t → teval σ t v)
                (λ args vargs _, forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
                                teval_list (delete x σ) args vargs → teval_list σ args vargs)).
      + intros. constructor.
      + intros x' v H H' Hfree. constructor. simpl in Hfree.
        destruct (decide (x' = x)); subst; simpl.
        * apply not_elem_of_singleton in Hfree. contradiction.
        * pose proof (@lookup_total_delete_ne _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ).
          rewrite H...
      + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_App with vargs...
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

  Lemma teval_list_delete_state_var {σ args vargs} x :
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
    teval_list σ args vargs ↔
      @teval_list M (delete x σ) args vargs.
  Proof with auto.
    intros Hfree. split.
    - induction 1.
      + constructor.
      + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
        constructor.
        * apply teval_delete_state_var...
        * apply IHteval_list...
    - induction 1.
      + constructor.
      + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
        constructor.
        * apply teval_delete_state_var in H...
        * apply IHteval_list...
  Qed.

  Lemma afeval_delete_state_var {σ af} x :
    x ∉ af_fvars af → afeval σ af ↔ afeval (delete x σ) af.
  Proof with auto.
    intros Hfree. destruct af; simpl.
    - split; inversion 1; subst; constructor.
    - split; inversion 1; subst; constructor.
    - simpl in Hfree. apply not_elem_of_union in Hfree as [? ?].
      split; intros (v&?&?); exists v.
      + split; apply teval_delete_state_var...
      + apply teval_delete_state_var in H1, H2...
    - simpl in Hfree. split; intros (v&?&?); exists v.
      + split... apply teval_delete_state_var...
      + apply teval_delete_state_var in H...
    - simpl in Hfree. split; intros (vargs&?&?); exists vargs.
      + split... apply teval_list_delete_state_var...
        clear H0 H vargs H p. induction args... simpl in *.
        apply not_elem_of_union in Hfree as [? ?].
        apply andb_prop_intro. split...
      + split... apply teval_list_delete_state_var in H...
        clear H0 H1 vargs H p. induction args... simpl in *.
        apply not_elem_of_union in Hfree as [? ?].
        apply andb_prop_intro. split...
  Qed.

  Lemma feval_delete_state_var {σ A} x :
    x ∉ formula_fvars A →
    feval σ A ↔ feval (delete x σ) A.
  Proof with auto.
    generalize dependent x. generalize dependent σ.
    induction A; simpl; intros σ x0 Hfree;
      try (apply not_elem_of_union in Hfree as [H1 H2]); simp feval.
    - split; subst; intros.
      + apply afeval_delete_state_var...
      + apply afeval_delete_state_var in H...
    - rewrite IHA with (x:=x0)...
    - rewrite IHA1 with (x:=x0)... rewrite IHA2 with (x:=x0)...
    - rewrite IHA1 with (x:=x0)... rewrite IHA2 with (x:=x0)...
    - apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
      setoid_rewrite <- H... destruct (decide (x0 = x)).
      + subst. destruct (decide (x ∈ formula_fvars A)).
        * rewrite fvars_subst_free... simpl. set_solver.
        * rewrite fvars_subst_non_free...
      + destruct Hfree; [| contradiction]. destruct (decide (x ∈ formula_fvars A)).
        * rewrite fvars_subst_free... simpl. set_solver.
        * rewrite fvars_subst_non_free...
  Qed.

  Lemma teval_delete_state_var_head {σ t vt} x v :
    x ∉ term_fvars t → teval (<[x:=v]> σ) t vt ↔ teval σ t vt.
  Proof with auto.
    intros. etrans.
    - apply teval_delete_state_var. exact H.
    - rewrite (delete_insert_delete σ). rewrite <- teval_delete_state_var...
  Qed.

  Lemma teval_list_delete_state_var_head x σ v args vargs :
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
    teval_list (<[x:=v]>σ) args vargs ↔ teval_list σ args vargs.
  Proof with auto.
    intros. etrans.
    - apply teval_list_delete_state_var. exact H.
    - rewrite (delete_insert_delete σ). rewrite <- teval_list_delete_state_var...
  Qed.

  Lemma afeval_delete_state_var_head {σ af v} x :
    x ∉ af_fvars af → afeval (<[x:=v]> σ) af ↔ afeval σ af.
  Proof with auto.
    intros. etrans.
    - apply afeval_delete_state_var. exact H.
    - rewrite (delete_insert_delete σ). rewrite <- afeval_delete_state_var...
  Qed.

  Lemma feval_delete_state_var_head {σ A v} x :
    x ∉ formula_fvars A →
    feval (<[x:=v]> σ) A ↔ feval σ A.
  Proof with auto.
    intros. etrans.
    - apply feval_delete_state_var. exact H.
    - rewrite (delete_insert_delete σ). rewrite <- feval_delete_state_var...
  Qed.

  Lemma teval_subst {σ t t' x v' v} (H : teval σ t' v') :
    teval (<[x:=v']> σ) t v ↔ teval σ (subst_term t x t') v.
  Proof with auto.
    split.
    - intros H'. generalize dependent t'. generalize dependent v.
      assert (Hind:=teval_ind_mut (<[x:=v']>σ)
        (λ t v _, ∀ t', teval σ t' v' → teval σ (subst_term t x t') v)
        (λ args vargs _, ∀ t', teval σ t' v' → teval_list σ (map (λ arg, subst_term arg x t') args) vargs)).
      simpl in Hind. apply Hind; clear Hind.
      + constructor.
      + rename x into x'. intros x v H t' Heval. destruct (decide (x = x')).
        * subst.
          pose proof (@lookup_total_insert _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ).
          rewrite H...
        * subst.
          pose proof (@lookup_total_insert_ne _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ).
          rewrite H...
      + intros. apply TEval_App with vargs...
      + constructor.
      + constructor; [apply H | apply H0]...
    - remember (subst_term t x t') as tpre. intros H'.
      assert (Hind:=teval_ind_mut σ
        (λ t v _, ∀ t', teval σ t' v' → ∀ tpre, t = subst_term tpre x t' → teval (<[x:=v']>σ) tpre v)
        (λ args vargs _, ∀ t', teval σ t' v' → ∀ args',
              args = (map (λ arg, subst_term arg x t') args') →
              teval_list (<[x:=v']>σ) args' vargs)).
      generalize dependent Heqtpre. generalize dependent t. generalize dependent H.
      generalize dependent t'. generalize dependent H'. generalize dependent v.
      generalize dependent tpre. simpl in Hind. apply Hind; clear Hind.
      + intros. destruct tpre; simpl in H0.
        * inversion H0. subst. constructor.
        * destruct (decide (x0 = x)); try discriminate. subst. inversion H; subst.
          constructor. rewrite (lookup_total_insert σ)...
        * discriminate.
      + intros. destruct tpre; simpl in H0; try discriminate.
        simpl in H0. destruct (decide (x1 = x)); subst.
        * apply TEval_Var. rewrite (lookup_total_insert σ). inversion H; subst...
        * inversion H0. subst. apply TEval_Var. rewrite (lookup_total_insert_ne σ)...
      + intros. destruct tpre; simpl in H1; try discriminate.
        * destruct (decide (x0 = x)); try discriminate. inversion H1; subst.
          inversion H0; subst.
          (* inversion f0; subst; rewrite H1 in H5; [| discriminate]. *)
          (* inversion H5; subst fdef0. clear H5. *)
          pose proof (Heq := teval_list_det _ _ _ H4 t). subst.
          pose proof (Heq := fn_eval_det f H6). subst.
          constructor. rewrite (lookup_total_insert σ)...
        * inversion H1. subst. apply TEval_App with vargs... apply H with t'...
      + intros. symmetry in H0. apply map_eq_nil in H0. subst. constructor...
      + intros. symmetry in H2. apply map_eq_cons in H2. destruct H2 as (y&ys&H3&H4&H5).
        subst. constructor.
        * apply H with t'...
        * apply H0 with t'...
  Qed.

  Lemma teval_list_subst {σ x t v args vargs} :
    teval σ t v →
    teval_list (<[x:=v]>σ) args vargs ↔
      teval_list σ (map (λ arg : term, subst_term arg x t) args) vargs.
  Proof with auto.
    intros Ht. split.
    - induction 1.
      + constructor.
      + constructor; [(apply (teval_subst Ht); assumption)|]. assumption.
    - remember (map (λ arg, subst_term arg x (TConst v)) args) as args'.
      generalize dependent vargs.
      generalize dependent args'.
      induction args; intros args' Heq vargs H.
      + subst. inversion H; subst. constructor.
      + subst. inversion H; subst. constructor; [(apply (teval_subst Ht); assumption)|].
        eapply IHargs.
        * reflexivity.
        * assumption.
  Qed.

  Lemma afeval_subst {σ af x t v} :
    teval σ t v →
    afeval (<[x:=v]>σ) af ↔ afeval σ (subst_af af x t).
  Proof with auto.
    intros Ht. split.
    - destruct af; simpl; inversion 1; subst...
      + destruct_and! H0. apply (teval_subst Ht) in H1, H2. eauto.
      + destruct H0 as []. apply (teval_subst Ht) in H0. eauto.
      + destruct H0 as []. apply (teval_list_subst Ht) in H0. eauto.
    - destruct af; simpl; inversion 1; subst...
      + destruct_and! H0. apply (teval_subst Ht) in H1, H2. eauto.
      + destruct H0 as []. apply (teval_subst Ht) in H0. eauto.
      + destruct H0 as []. apply (teval_list_subst Ht) in H0. eauto.
  Qed.

  Local Lemma fequiv_subst_and_diag A x :
    <! A[x \ x] !> ≡ A ∧
    ∀ σ t v, teval σ t v → feval (<[x:=v]> σ) A ↔ feval σ <! A[x \ t] !>.
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
          intros σ. apply feval_exists_equiv. intros.
          pose proof (H':=H). forward (H (A[!y\y'!][!x\x!])). 1: { eapply shape_eq_trans... }
          destruct (H y') as [_ ?]. rewrite <- (H0 σ (TConst v) v)... clear H H0.
          pose proof (H:=H'). forward (H (A[!y\y'!])) by auto.
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
      + subst. rewrite simpl_subst_exists_skip... apply feval_exists_equiv.
        intros. forward (H A)... destruct (H x) as [_ ?].
        rewrite <- (H1 (<[x:=v]> σ) (TConst v0) v0)...
        rewrite <- (H1 σ (TConst v0) v0)... rewrite (insert_insert σ)...
      + destruct (decide (x ∈ formula_fvars A)).
        2: { rewrite simpl_subst_exists_skip... rewrite feval_delete_state_var_head... simpl.
             set_solver. }
        rewrite simpl_subst_exists_propagate... generalize_fresh_var y A x t as x'.
        apply feval_exists_equiv. intros.
        pose proof (H':=H). forward (H (A[!y\x'!][!x\t!])). { eapply shape_eq_trans... }
        destruct (H x') as [_ ?]. rewrite <- (H1 σ (TConst v0) v0)... clear H1 H.
        pose proof (H:=H'). forward (H (A[!y\x'!])). { eapply shape_eq_trans... }
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
    feval σ (<! A[x \ t] !>) ↔ feval (<[x:=v]> σ) A .
  Proof with auto. symmetry. apply fequiv_subst_and_diag... Qed.

  Lemma fequiv_subst_diag A x :
    <! A[x \ x] !> ≡ A.
  Proof with auto. apply fequiv_subst_and_diag. Qed.

  Global Instance subst_proper :
    Proper ((≡@{formula}) ==> (=) ==> (≡@{term}) ==> (≡)) subst_formula.
  Proof with auto.
    intros A B H x ? <- t t' Ht σ. pose proof (teval_total σ t) as [v Hv].
    rewrite (feval_subst v)... rewrite (feval_subst v)... apply Ht...
  Qed.

  (** substitution doesn't respect [≡_{σ}].
      For example, [x = 0 ≡ y = 0] holds in σ = (x ↦ 0, y ↦ 0), yet
      [x=0 [x \ 5] ≡ y=0 [x \ 5]] doesn't hold in σ. Since [5 = 0 ≡ false] and [y = 0 ≡ true] *)

  Global Instance subst_proper_fent : Proper ((⇛ₗ@{M}) ==> (=) ==> (≡@{term}) ==> (⇛)) subst_formula.
  Proof with auto.
    intros A B Hent x ? <- t t' H σ. rewrite <- H. pose proof (teval_total σ t) as [v Hv].
    rewrite (feval_subst v)... rewrite (feval_subst v)...
  Qed.


  Global Instance f_exists_proper : Proper ((=) ==> (≡@{formula}) ==> (≡@{formula})) FExists.
  Proof with auto.
    intros x ? <- A B H σ. apply feval_exists_equiv. intros v. rewrite H...
  Qed.

  Global Instance f_exists_proper_fent : Proper ((=) ==> (⇛) ==> (⇛ₗ@{M})) FExists.
  Proof with auto.
    intros x ? <- A B Hent σ H. simp feval. simp feval in H. destruct H as [v Hv].
    exists v. revert Hv. rewrite (feval_subst v)... rewrite (feval_subst v)...
  Qed.

  Global Instance f_forall_proper : Proper ((=) ==> (≡@{formula}) ==> (≡@{formula})) FForall.
  Proof with auto. intros x ? <- A B H σ. unfold FForall. rewrite H... Qed.

  Lemma f_forall_proper_st σ A B x :
    (∀ t, <! A [x \ t] !> ≡_{σ} <! B [x \ t] !>) →
    <! ∀ x, A !> ≡_{σ} <! ∀ x, B !>.
  Proof.
    intros. unfold fequiv_st. unfold FForall. f_equiv. pose proof (@feval_exists_equiv _ σ σ).
    f_equiv. apply H0. intros. f_equiv. do 2 rewrite simpl_subst_not. f_equiv. apply H.
  Qed.

  Global Instance f_forall_proper_fent : Proper ((=) ==> (⇛) ==> (⇛ₗ@{M})) FForall.
  Proof with auto.
    intros x ? <- A B H. unfold FForall. apply f_ent_contrapositive.
    apply f_ent_contrapositive in H. rewrite H. reflexivity.
  Qed.

  Global Instance f_exists_ty_proper
    : Proper ((=) ==> (=) ==> (≡@{formula}) ==> (≡@{formula})) FExistsT.
  Proof with auto. intros x ? <- ty ? <- A B H σ. unfold FExistsT. rewrite H... Qed.

  Global Instance f_exists_ty_proper_fent : Proper ((=) ==> (=) ==> (⇛) ==> (⇛ₗ@{M})) FExistsT.
  Proof with auto. intros x ? <- ty ? <- A B H. unfold FExistsT. rewrite H... Qed.

  Global Instance f_forall_ty_proper
    : Proper ((=) ==> (=) ==> (≡@{formula}) ==> (≡@{formula})) FForallT.
  Proof with auto. intros x ? <- ty ? <- A B H σ. unfold FForallT. rewrite H... Qed.

  Global Instance f_forall_ty_proper_fent : Proper ((=) ==> (=) ==> (⇛) ==> (⇛ₗ@{M})) FForallT.
  Proof with auto. intros x ? <- ty ? <- A B H. unfold FForallT. rewrite H... Qed.

  Lemma subst_non_free' x t B {A} :
    x ∉ formula_fvars A →
    A ≡ B →
    <! B[x \ t] !> ≡ B.
  Proof with auto.
    intros. trans A... rewrite <- subst_non_free with (A:=A) (x:=x) (t:=t)... f_equiv...
  Qed.

  Lemma fexists_alpha_equiv x x' A :
    x' ∉ formula_fvars A →
    <! ∃ x, A !> ≡ <! ∃ x', A[x \ x'] !>.
  Proof with auto.
    intros Hfree σ. apply feval_exists_equiv. intros.
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

  Lemma simpl_subst_exists y A x t :
    y ∉ quant_subst_fvars y A x t →
    <! (∃ y, A)[x \ t] !> ≡ <! (∃ y, A [x \ t]) !>.
  Proof with auto.
    intros. apply not_elem_of_quant_subst_fvars_inv in H as [? []]. clear H.
    destruct (decide (x ∈ formula_fvars A)).
    2:{ rewrite simpl_subst_exists_skip... rewrite (subst_non_free A x t)... }
    (* rewrite simpl_subst_exists_propagate... generalize_fresh_var y A x t as y'. *)
    pose proof (fresh_var_fresh y (formula_fvars A ∪ term_fvars t ∪ {[x]})).
    remember (fresh_var y (formula_fvars A ∪ term_fvars t ∪ {[x]})) as y'.
    do 2 apply not_elem_of_union in H as []. apply not_elem_of_singleton in H2.
    rewrite simpl_subst_exists_propagate... rewrite (fresh_var_id y); [| set_solver].
    rewrite fequiv_subst_diag...
  Qed.

  Lemma simpl_subst_exists_rename y y' A x t :
    y' ∉ quant_subst_fvars y A x t →
    <! (∃ y, A)[x \ t] !> ≡ <! (∃ y', A [y \ y'] [x \ t]) !>.
  Proof with auto.
    intros. apply not_elem_of_quant_subst_fvars_inv in H as [? []]. destruct H.
    - subst. rewrite fequiv_subst_diag. apply simpl_subst_exists. set_solver.
    - rewrite (fexists_alpha_equiv y y')... apply simpl_subst_exists. set_solver.
  Qed.

  Lemma simpl_subst_forall y A x t :
    y ∉ quant_subst_fvars y A x t →
    <! (∀ y, A)[x \ t] !> ≡ <! (∀ y, A [x \ t]) !>.
  Proof with auto.
    intros. unfold FForall. rewrite simpl_subst_not. f_equiv. rewrite <- simpl_subst_not.
    apply simpl_subst_exists...
  Qed.

  Lemma simpl_subst_forall_rename y y' A x t :
    y' ∉ quant_subst_fvars y A x t →
    <! (∀ y, A)[x \ t] !> ≡ <! (∀ y', A [y \ y'] [x \ t]) !>.
  Proof with auto.
    intros. unfold FForall. rewrite simpl_subst_not. f_equiv.
    rewrite simpl_subst_exists_rename with (y':=y')... repeat rewrite simpl_subst_not...
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

  Lemma fequiv_subst_trans : ∀ A x1 x2 t,
      x2 ∉ formula_fvars A →
      <! A[x1 \ x2][x2 \ t] !> ≡ <! A[x1 \ t] !>.
  Proof with auto.
    intros. destruct (decide (x1 = x2)).
    1:{ subst. rewrite fequiv_subst_diag... }
    intros σ. pose proof (teval_total σ t) as [v Hv].
    rewrite (feval_subst v)... rewrite (feval_subst v).
    2:{ constructor. rewrite (lookup_total_insert σ)... }
    rewrite (feval_subst v)... rewrite (insert_commute σ)...
    rewrite (feval_delete_state_var_head x2)...
  Qed.

  Lemma fequiv_subst_comm A x1 t1 x2 t2 :
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
      + rewrite subst_non_free in H2.
        2: { rewrite fvars_subst_free... set_solver. }
        pose proof (teval_total σ t1) as [v1 Hv1]. rewrite (feval_subst v1)...
        rewrite subst_non_free... rewrite <- feval_subst with (t:=t1)...
      + pose proof (teval_total σ t2) as [v2 Hv2]. rewrite (feval_subst v2) in H2...
        rewrite subst_non_free in H2... rewrite <- feval_subst with (t:=t2) in H2...
        rewrite subst_non_free... rewrite fvars_subst_free... set_solver.
      + rewrite subst_non_free. 2: { rewrite fvars_subst_non_free... }
        rewrite subst_non_free...
        rewrite subst_non_free in H2. 2: { rewrite fvars_subst_non_free... }
        rewrite subst_non_free in H2...
    - destruct (decide (x1 ∈ formula_fvars A)); destruct (decide (x2 ∈ formula_fvars A)).
      + pose proof (teval_total σ t2) as [v2 Hv2]. rewrite (feval_subst v2)...
        pose proof (teval_total (<[x2:=v2]> σ) t1) as [v1 Hv1]. rewrite (feval_subst v1)...
        rewrite (insert_commute σ)... apply (teval_delete_state_var_head) in Hv1...
        rewrite <- (teval_delete_state_var_head x1 v1) in Hv2...
        rewrite (feval_subst v1) in H2... rewrite (feval_subst v2) in H2...
      + pose proof (teval_total σ t1) as [v1 Hv1]. rewrite (feval_subst v1) in H2...
        rewrite subst_non_free in H2... rewrite <- feval_subst with (t:=t1) in H2...
        rewrite subst_non_free... rewrite fvars_subst_free... set_solver.
      + rewrite subst_non_free in H2.
        2: { rewrite fvars_subst_free... set_solver. }
        pose proof (teval_total σ t2) as [v2 Hv2]. rewrite (feval_subst v2)...
        rewrite subst_non_free... rewrite <- feval_subst with (t:=t2)...
      + rewrite subst_non_free. 2: { rewrite fvars_subst_non_free... }
        rewrite subst_non_free...
        rewrite subst_non_free in H2. 2: { rewrite fvars_subst_non_free... }
        rewrite subst_non_free in H2...
  Qed.

  (* This one is reduntant since [simp feval] already simplifies it. However, it can be
      useful when rewriting. HACK: we might need to specify similar lemmas for other formulas *)
  Lemma simpl_feval_and σ A B : feval σ <! A ∧ B !> ↔ feval σ A ∧ feval σ B.
  Proof. simp feval. reflexivity. Qed.

  Lemma simpl_feval_impl σ A B :
    feval σ <! A ⇒ B !> ↔ (feval σ A → feval σ B).
  Proof with auto.
    unfold FImpl. simp feval. split.
    - intros [|] ?... contradiction.
    - intros. destruct (feval_lem σ A)...
  Qed.

  Lemma simpl_feval_iff σ A B :
    feval σ <! A ⇔ B !> ↔ (feval σ A ↔ feval σ B).
  Proof. unfold FIff. simp feval. do 2 rewrite simpl_feval_impl. naive_solver. Qed.

  Lemma simpl_feval_forall σ x A :
    feval σ <! ∀ x, A !> ↔ ∀ v, feval σ <! A [x \ $(TConst v)] !>.
  Proof with auto.
    unfold FForall. simp feval. setoid_rewrite (simpl_subst_not). split; intros.
    - destruct (feval_lem σ <! A [x \ $(TConst v)] !>)... exfalso. apply H. exists v. simp feval.
    - intros [v contra]. simp feval in contra...
  Qed.

  Lemma teval_delete_bottom_from_state σ x t v :
    x ∉ dom σ →
    teval (<[x:=⊥]> σ) t v ↔ teval σ t v.
  Proof with auto.
    intros. generalize dependent v. induction t; intros.
    - split; inversion 1...
    - split; inversion 1; subst x1.
      + destruct (decide (x = x0)).
        * subst x0. rewrite (lookup_total_insert σ) in H2. subst v0. constructor.
          rewrite (lookup_total_alt σ). apply (not_elem_of_dom σ) in H. rewrite H.
          simpl...
        * rewrite (lookup_total_insert_ne σ) in H2...
      + destruct (decide (x = x0)).
        * subst x0 v0. rewrite (lookup_total_alt σ) in H2. apply (not_elem_of_dom σ) in H.
          rewrite H in H2. simpl in H2. rewrite H2. constructor.
          rewrite (lookup_total_insert σ)...
        * constructor. rewrite (lookup_total_insert_ne σ)...
    - split; inversion 1; subst; apply TEval_App with (vargs:=vargs)...
      + clear H1 H6. generalize dependent vargs. induction args; intros.
        * inversion H4. subst. constructor.
        * inversion H4. subst. constructor.
          -- rewrite <- H0... left...
          -- apply IHargs... intros. apply H0. right...
      + clear H1 H6. generalize dependent vargs. induction args; intros.
        * inversion H4. subst. constructor.
        * inversion H4. subst. constructor.
          -- rewrite H0... left...
          -- apply IHargs... intros. apply H0. right...
  Qed.

  Lemma afeval_delete_bottom_from_state σ x af :
    x ∉ dom σ →
    afeval (<[x:=⊥]> σ) af ↔ afeval σ af.
  Proof with auto.
    intros. destruct af...
    1-2: simpl; setoid_rewrite teval_delete_bottom_from_state...
    simpl. split; intros (vargs&?&?); exists vargs; split; auto; clear H1;
    generalize dependent vargs; induction args; intros; inversion H0; subst;
    try constructor...
    - rewrite <- (teval_delete_bottom_from_state _ x a v)...
    - rewrite (teval_delete_bottom_from_state _ x a v)...
  Qed.

  Lemma feval_delete_bottom_from_state σ x A :
    x ∉ dom σ →
    feval (<[x:=⊥]> σ) A ↔ feval σ A.
  Proof with auto.
    intros. induction A; simp feval.
    2-5: naive_solver.
    apply afeval_delete_bottom_from_state...
  Qed.

  Lemma subst_subst_ne A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    <! A [x1 \ t1][x2 \ t2] !> ≡ <! A [x2 \ t2][x1 \ $(subst_term t1 x2 t2)] !>.
  Proof with auto.
    intros ? Hfree σ.
    opose proof (teval_total σ _) as [v1 ?].
    rewrite feval_subst with (v:=v1) by exact H0.
    opose proof (teval_total _ _) as [v2 ?].
    rewrite feval_subst with (v:=v2) by exact H1.
    opose proof (teval_total σ _) as [v3 ?].
    rewrite feval_subst with (v:=v3) by exact H2.
    opose proof (teval_total _ _) as [v4 ?].
    rewrite feval_subst with (v:=v4) by exact H3.
    f_equiv. unfold state. apply map_eq. intros x.
    destruct (decide (x = x1)); destruct (decide (x = x2)).
    1:{ subst. contradiction. }
    3:{ repeat rewrite lookup_insert_ne... }
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t1).
      + apply H1.
      + erewrite teval_subst; [exact H2|]...
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t2).
      + exact H0.
      + rewrite <- teval_delete_state_var_head; [exact H3|]...
  Qed.

  Lemma subst_subst_ne' A x1 t1 x2 t2 z :
    x1 ≠ x2 →
    z ≠ x1 →
    z ≠ x2 →
    z ∉ formula_fvars A →
    z ∉ term_fvars t1 →
    z ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    <! A [x1 \ t1][x2 \ t2] !> ≡ <! A [x2 \ t2[x1 \ z]][x1 \ t1][z \ x1] !>.
  Proof with auto.
    intros ? Hz1 Hz2 Hz3 Hz4 Hz5 Hfree σ.
    opose proof (teval_total σ _) as [v1 ?].
    rewrite feval_subst with (v:=v1) by exact H0.
    opose proof (teval_total _ _) as [v2 ?].
    rewrite feval_subst with (v:=v2) by exact H1.
    opose proof (teval_total σ _) as [v3 ?].
    rewrite feval_subst with (v:=v3) by exact H2.
    opose proof (teval_total _ _) as [v4 ?].
    rewrite feval_subst with (v:=v4) by exact H3.
    opose proof (teval_total _ _) as [v5 ?].
    rewrite feval_subst with (v:=v5) by exact H4.
    unfold state. rewrite insert_commute with (j:=z)...
    rewrite insert_commute with (j:=z)... rewrite feval_delete_state_var_head with (x:=z)...
    f_equiv. unfold state. apply map_eq. intros x.
    destruct (decide (x = x1)); destruct (decide (x = x2)).
    1:{ subst. contradiction. }
    3:{ repeat rewrite lookup_insert_ne... }
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t1).
      + rewrite <- teval_delete_state_var_head; [exact H1|]...
      + rewrite <- teval_delete_state_var_head; [exact H3|]...
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t2).
      + exact H0.
      + rewrite teval_delete_state_var_head in H4.
        2:{ intros ?. apply fvars_subst_term_superset in H5. set_solver. }
        erewrite teval_subst in H4; [|exact H2]. rewrite subst_term_trans in H4...
        rewrite subst_term_diag in H4...
  Qed.

  Lemma subst_subst_eq A x t u : <! A [x \ t] [x \ u] !> ≡ <! A [x \ t[x \ u]] !>.
  Proof with auto.
    intros σ.
    opose proof (teval_total σ _) as [v1 ?].
    rewrite feval_subst with (v:=v1) by exact H.
    opose proof (teval_total _ _) as [v2 ?].
    rewrite feval_subst with (v:=v2) by exact H0.
    opose proof (teval_total _ _) as [v3 ?].
    rewrite feval_subst with (v:=v3) by exact H1.
    f_equiv. unfold state. rewrite insert_insert.
    apply map_eq. intros y. destruct (decide (x = y)).
    2:{ repeat rewrite lookup_insert_ne... }
    subst. do 2 rewrite lookup_insert. f_equal. symmetry. eapply (teval_det <! t[ₜ y\u] !>).
    - exact H1.
    - erewrite <- teval_subst with (H:=H)...
  Qed.

  Lemma simpl_subst_forall_skip' y A x t  :
    x ∉ term_fvars t →
    <! A[x\t] !> ≡ <! A !> →
    <! (∀ y, A)[x\t] !> ≡ <! ∀ y, A !>.
  Proof with auto.
    intros Hfree H. destruct (decide (x = y)).
    - rewrite simpl_subst_forall_skip...
    - rewrite <- H. rewrite simpl_subst_forall_skip...
      right. intros contra. apply fvars_subst_superset' in contra. set_solver.
  Qed.

  Lemma simpl_subst_forall_skip'' (x y : variable) A t :
    y ∉ term_fvars t →
    <! A[x\t] !> ≡ <! A !> →
    <! (∀ y, A)[x\t] !> ≡ <! ∀ y, A !>.
  Proof with auto.
    intros Hfree ?. destruct (decide (x = y)).
    - rewrite simpl_subst_forall_skip...
    - mk_fresh (formula_fvars A ∪ {[x; y]} ∪ term_fvars t) as z.
      rewrite simpl_subst_forall_rename with (y':=z).
      2:{ unfold quant_subst_fvars. set_solver. }
      rewrite fforall_alpha_equiv with (x:=y) (x':=z).
      2:{ unfold quant_subst_fvars. set_solver. }
      f_equiv. rewrite subst_subst_ne... simpl. destruct (decide _).
      + subst. set_unfold in H0. destruct_and! H0. done.
      + rewrite <- H at 2...
  Qed.

End subst.
