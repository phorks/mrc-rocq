From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
From MRC Require Import Prelude.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section refinement.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation prog := (@prog M).
  Local Notation state := (@state M).
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).
  Local Notation final_formula := (final_formula value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  Implicit Types gs : list final_formula.
  (* Implicit Types ts : list term. *)

  (* TODO: reorder laws *)
  (* 1.8 *)
  Lemma r_absorb_assumption pre' w pre post `{FormulaFinal _ pre'} `{FormulaFinal _ pre} :
    <{ {pre'}; *w : [pre, post] }> ≡ <{ *w : [pre' ∧ pre, post] }>.
  Proof.
    split; intros A; simpl.
    - f_simpl. rewrite subst_initials_nil. rewrite f_and_assoc. reflexivity.
    - f_simpl. rewrite subst_initials_nil. rewrite f_and_assoc. reflexivity.
  Qed.

  (* Law 1.1 *)
  Lemma r_strengthen_post w pre post post' `{FormulaFinal _ pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl. f_simpl. rewrite <- Hent. reflexivity.
  Qed.

  (* Global Instance elem_of_ *)

  Global Instance set_unfold_elem_of_term_fvars x ts P1 P2 :
    (∀ t, SetUnfoldElemOf x (@term_fvars value t) (P1 t)) →
    (∀ t, SetUnfoldElemOf t ts (P2 t)) →
    SetUnfoldElemOf x
      (⋃ (term_fvars <$> ts))
      (∃ t, P1 t ∧ P2 t) | 10.
  Proof with auto.
    intros. constructor. rewrite elem_of_union_list. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_term_fvars_of_initial_vars x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
      (⋃ (term_fvars <$> (@TVar value <$> (initial_var_of <$> w))))
      (¬ var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (t&?&tx&->&x'&->&?). set_unfold in H0. subst x. split... apply H.
      rewrite to_final_var_initial_var_of...
    - intros []. exists x. simpl. split; [set_solver|]. exists x. split...
      exists (to_final_var x). apply H in H1. split... unfold var_final in H0.
      apply not_false_is_true in H0. unfold initial_var_of. destruct x. simpl. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_term_fvars_of_vars x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
      (⋃ (term_fvars <$> (@TVar value <$> (as_var <$> w))))
      (var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (t&?&tx&->&x'&->&?). set_unfold in H0. subst x. split... apply H.
      rewrite to_final_var_as_var...
    - intros []. exists x. simpl. split; [set_solver|]. exists x. split...
      exists (to_final_var x). apply H in H1. split... unfold var_final in H0.
      unfold to_final_var, as_var. destruct x. simpl. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_list_to_set_as_var_final_vars x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
      (list_to_set (as_var <$> w) : gset variable)
      (var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (x'&?&?). subst. split; [apply var_final_as_var |]... apply H.
      rewrite to_final_var_as_var...
    - intros []. exists (to_final_var x). set_unfold. split... unfold var_final in H.
      destruct x. cbv. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_subst_initials_var_fvars x A w P1 P2 :
    (∀ x', SetUnfoldElemOf x' w (P1 x')) →
    (∀ x', SetUnfoldElemOf (initial_var_of x') (formula_fvars A) (P2 x')) →
    SetUnfoldElemOf x
                      (subst_initials_var_fvars A w)
                      (∃ x' : final_variable, x = as_var x' ∧ P1 x' ∧ P2 x').
  Proof. constructor. rewrite <- elem_of_subst_initials_var_fvars. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_subst_initials x A w Q1 Q2 Q3 :
    SetUnfoldElemOf x (formula_fvars A) Q1 →
    SetUnfoldElemOf x (list_to_set (initial_var_of <$> w) : gset variable) Q2 →
    SetUnfoldElemOf x (subst_initials_var_fvars A w) Q3 →
    SetUnfoldElemOf x (formula_fvars <! A[_₀\ w] !>)
                      ((Q1 ∧ ¬Q2) ∨ Q3).
  Proof. constructor. rewrite fvars_subst_initials. set_solver. Qed.

  Global Instance set_unfold_initial_var_of_elem_of_formula_fvars_subst_initials x A w Q1 Q2 :
    SetUnfoldElemOf (initial_var_of x) (formula_fvars A) Q1 →
    SetUnfoldElemOf x w Q2 →
    SetUnfoldElemOf (initial_var_of x)
        (formula_fvars <! A[_₀\ w] !>)
        (Q1 ∧ ¬Q2).
  Proof with auto.
    constructor. split; intros.
    - set_unfold in H. set_unfold in H1. destruct H1 as [ [] | ].
      + split... intros ?. apply H2. exists x. set_solver.
      + destruct H1 as (x'&?&?&?). set_solver.
    - destruct H1. rewrite <- (@set_unfold_elem_of _ _ _ _ _ _ H) in H1.
      rewrite <- (@set_unfold_elem_of _ _ _ _ _ _ H0) in H2. clear H. clear H0.
      set_solver.
  Qed.

  Global Instance set_unfold_elem_of_list_to_set_intials_of_final_variables x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
        (list_to_set (initial_var_of <$> w) : gset variable)
        (¬ var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (x'&?&?). subst. split; [apply var_final_initial_var_of|]. apply H.
      rewrite to_final_var_initial_var_of...
    - intros []. exists (to_final_var x). set_unfold. split... unfold var_final in H0.
      apply not_false_is_true in H0. destruct x. simpl in H0. rewrite H0. f_equal.
  Qed.

  Global Instance set_unfold_elem_of_fvars_FAnd x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (@formula_fvars value <! A1 ∧ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FOr x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (@formula_fvars value <! A1 ∨ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FImpl x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (@formula_fvars value <! A1 ⇒ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FIff x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (@formula_fvars value <! A1 ⇔ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FExists x y A Q :
    SetUnfoldElemOf x (formula_fvars A) Q →
    SetUnfoldElemOf x (@formula_fvars value <! ∃ y, A !>) (x ≠ y ∧ Q).
  Proof with auto. intros. constructor. simpl. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FForall x y A Q :
    SetUnfoldElemOf x (formula_fvars A) Q →
    SetUnfoldElemOf x (@formula_fvars value <! ∀ y, A !>) (x ≠ y ∧ Q).
  Proof with auto. intros. constructor. simpl. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_FAndList x Bs P1 P2 :
    (∀ A, SetUnfoldElemOf A Bs (P1 A)) →
    (∀ A, SetUnfoldElemOf x (formula_fvars A) (P2 A)) →
    SetUnfoldElemOf x (@formula_fvars value <! ∧* Bs !>) (∃ A, P1 A ∧ P2 A).
  Proof with auto.
    intros. constructor. rewrite fvars_andlist. rewrite elem_of_union_list. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_fvars_FOrList x Bs P1 P2 :
    (∀ A, SetUnfoldElemOf A Bs (P1 A)) →
    (∀ A, SetUnfoldElemOf x (formula_fvars A) (P2 A)) →
    SetUnfoldElemOf x (@formula_fvars value <! ∨* Bs !>) (∃ A, P1 A ∧ P2 A).
  Proof with auto.
    intros. constructor. rewrite fvars_orlist. rewrite elem_of_union_list. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_fvars_FExistsList x (xs : list variable) A Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A) Q1 →
    SetUnfoldElemOf x (list_to_set xs : gset variable) Q2 →
    SetUnfoldElemOf x (formula_fvars <! ∃* xs, A !>) (Q1 ∧ ¬Q2).
  Proof with auto. intros. constructor. rewrite fvars_existslist. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_FForallList x (xs : list variable) A Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A) Q1 →
    SetUnfoldElemOf x (list_to_set xs : gset variable) Q2 →
    SetUnfoldElemOf x (formula_fvars <! ∀* xs, A !>) (Q1 ∧ ¬Q2).
  Proof with auto. intros. constructor. rewrite fvars_foralllist. set_solver. Qed.

  Lemma subst_initials_inverse_l A w `{FormulaFinal _ A} :
    <! A [; ↑ₓ w \ ⇑₀ w ;][_₀\ w] !> ≡ A.
  Proof with auto.
    rename H into Hfinal. induction w as [|x w IH].
    - simpl. rewrite subst_initials_nil...
    - simpl. erewrite (seqsubst_rewrite _ _ (↑ₓ w) _ (⇑₀ w)). Unshelve.
      2-3: unfold fmap; f_equal. destruct (decide (x ∈ w)).
      + rewrite fequiv_subst_non_free.
        2:{ intros contra. apply fvars_seqsubst_vars_not_free_in_terms_superset in contra...
            set_unfold in contra. destruct contra as [ [] |]; [|set_solver].
            apply not_and_l in H0 as [].
            - apply H0. apply var_final_as_var.
            - rewrite to_final_var_as_var in H0. contradiction. }
        rewrite subst_initials_cons. rewrite fequiv_subst_non_free.
        1:{ rewrite <- IH at 2. f_equiv. f_equiv. apply OfSameLength_pi. }
        set_solver.
      + rewrite subst_initials_perm with (xs':=w ++ [x]).
        2: { replace (x :: w) with ([x] ++ w) by auto. apply Permutation_app_comm. }
        rewrite subst_initials_snoc. rewrite fequiv_subst_trans.
        1:{ rewrite fequiv_subst_diag. rewrite <- IH at 2. f_equiv. f_equiv.
            apply OfSameLength_pi. }
        intros contra. apply fvars_seqsubst_vars_not_free_in_terms_superset in contra...
        set_unfold. destruct contra as [ [] | [] ].
        * apply Hfinal in H... apply var_final_initial_var_of in H as [].
        * rewrite to_final_var_initial_var_of in H0. contradiction.
  Qed.

  (* Law 5.1 *)
  Lemma r_strengthen_post_with_initials w pre post post' `{FormulaFinal _ pre} :
    <! pre[; ↑ₓ w \ ⇑₀ w ;] ∧ post' !> ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl.
    rewrite <- Hent. rewrite <- f_impl_curry. rewrite -> f_foralllist_impl_unused_l.
    2: { intros x ? ?. apply (fvars_seqsubst_vars_not_free_in_terms_superset) in H1...
         set_solver. }
    rewrite simpl_subst_initials_impl. rewrite subst_initials_inverse_l...
    rewrite <- (f_and_idemp pre) at 1. rewrite <- f_and_assoc. f_simpl.
    reflexivity.
  Qed.

  (* Law 1.2 *)
  Lemma r_weaken_pre w pre pre' post `{FormulaFinal _ pre} `{FormulaFinal _ pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A. simpl. f_simpl. assumption.
  Qed.

  Lemma r_permute_frame w w' pre post `{FormulaFinal _ pre} :
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros. split; intros A.
    - simpl. f_simpl. rewrite subst_initials_perm with (xs':=w')... f_equiv.
      rewrite f_foralllist_permute with (xs':=(fmap as_var w')).
      + reflexivity.
      + apply Permutation_map...
    - symmetry in H0. simpl. f_simpl. rewrite subst_initials_perm with (xs':=w)... f_equiv.
      rewrite f_foralllist_permute with (xs':=(fmap as_var w)).
      + reflexivity.
      + apply Permutation_map...
  Qed.
  Hint Rewrite to_final_var_initial_var_of : set_solver.


  (* Instance simpl_something w xs :  *)
  (* list_to_set ↑ₓ w ## ⋃ (term_fvars <$> ⇑ₓ xs) *)
  (* Global Instance simpl_something x P : SetUnfoldSimpl (P (to_final_var (as_var x))) (P x). *)
  (* Proof. rewrite to_final_var_as_var. constructor. constructor. reflexivity. Qed. *)
  (* Global Instance simpl_something_l x (X : list final_variable) P : *)
  (*   SetUnfoldElemOf x X P → *)
  (*   SetUnfoldElemOf (to_final_var (as_var x)) X P. *)
  (* Proof. rewrite to_final_var_as_var. auto. Qed. *)

  (* Law 5.4 *)
  Lemma r_contract_frame w xs pre post `{FormulaFinal _ pre} :
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs] ] }>.
  Proof with auto.
    intros Hdisjoint A. simpl. f_simpl.
    rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist by set_solver.
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    f_simpl. rewrite f_subst_initials_final_formula... reflexivity.
  Qed.

  (* Law 3.2 *)
  Lemma r_skip w pre post `{FormulaFinal _ pre} :
    pre ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A Hfinal. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    f_simpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite H0. rewrite f_impl_elim. rewrite f_foralllist_one_point...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 5.3 *)
  Lemma r_skip_with_initials w pre post `{FormulaFinal _ pre} :
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ pre !> ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A Hfinal. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    f_simpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite f_impl_dup_hyp. rewrite f_and_assoc. rewrite H0. rewrite f_impl_elim.
    rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 3.3 *)
  Lemma r_seq w pre mid post `{FormulaFinal _ pre} `{FormulaFinal _ mid} `{FormulaFinal _ post} :
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, mid]; *w : [mid, post] }>.
  Proof with auto.
    intros A. simpl. f_simpl. rewrite f_impl_and_r. f_simpl.
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_foralllist_impl_unused_r _ mid) by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* TODO: move it *)
  Lemma elem_of_fvars_final_formula_inv (A : formula) (x : variable) `{FormulaFinal _ A} :
    x ∈ formula_fvars A →
    var_final x.
  Proof. intros. apply H in H0. assumption. Qed.

  (* Law B.2 *)
  Lemma r_seq_frame w xs pre mid post `{FormulaFinal _ pre} `{FormulaFinal _ mid} :
    w ## xs →
    list_to_set (↑₀ xs) ## formula_fvars post →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs : [pre, mid]; *w, *xs : [mid, post] }>.
  Proof with auto.
    intros. intros A. simpl. f_simpl. rewrite f_impl_and_r. f_simpl.
    rewrite (subst_initials_app _ w xs).
    assert (formula_fvars <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> ## list_to_set (↑₀ xs)).
    { intros x ? ?. set_unfold in H3. destruct H3 as ([|]&?); [set_solver|].
      set_unfold. destruct H4 as [? _]. apply elem_of_fvars_final_formula_inv in H3... }
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials _ xs) at 1 by set_solver...
    rewrite (f_foralllist_impl_unused_r (↑ₓ xs)) at 1 by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  Lemma r_assignment w xs pre post ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ ⎡⇑₀ xs =* ⇑ₓ xs⎤ ∧ pre !> ⇛ <! post[[ ↑ₓ xs \ ⇑ₜ ts ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros Hlength Hnodup proviso A. simpl. rewrite wp_asgn.
    rewrite <- (f_subst_initials_final_formula pre (w ++ xs))...
    rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials. rewrite <- f_foralllist_one_point...
    rewrite f_foralllist_app. rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite (f_foralllist_elim_as_ssubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    2:{ apply NoDup_fmap... apply as_var_inj. }
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite fmap_app. reflexivity. }
    3: { do 2 rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_ssubst_impl.
    f_simpl. rewrite <- f_eqlist_app.
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    3: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    setoid_rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
    2: { apply ssubst_formula_final. }
    reflexivity.
    Unshelve. typeclasses eauto.
  Qed.

  Lemma f_or_elim A B C :
    A ⇛ C →
    B ⇛ C →
    <! A ∨ B !> ⇛ C.
  Proof.
    intros. intros σ. specialize (H σ). specialize (H0 σ). intros. simp feval in H1.
    destruct (feval_lem σ A); naive_solver.
  Qed.

  (* Lemma something A B P : *)
  (*   (∀ σ, feval σ A → P σ) ↔ (A ≡ <! true !> → ∀ σ, P σ). *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - specialize (H0 σ). apply H. apply H0. constructor. *)
  (*   - apply H. intros σ'. *)

  Lemma feval_or_elim A B C :
    (∀ σ, feval σ A → feval σ C) →
    (∀ σ, feval σ B → feval σ C) →
    ∀ σ, feval σ <! A ∨ B !> → feval σ C.
  Proof.
    intros. specialize (H σ). specialize (H0 σ). intros. simp feval in H1.
    destruct (feval_lem σ A); naive_solver.
  Qed.

  Lemma feval_or_elim_Prop A B (P : formula → Prop) :
    (P A → P <! A ∨ B !>)
    (∀ σ, feval σ A → P A) →
    (∀ σ, feval σ B → P B) →
    ∀ σ, feval σ <! A ∨ B !> → P <! A ∨ B !>.
  Proof.
    intros. specialize (H σ). specialize (H0 σ). intros. simp feval in H1.
    destruct (feval_lem σ A).
    - apply H in H2.
  Qed.

  Lemma f_or_elim_Prop A B C (P : formula → state → Prop) :
    Proper ((≡) ==> (=) ==> iff) P →
    (∀ σ, P A σ ∨ P A σ → P <! A ∨ B !> σ) →
    (∀ σ, P A σ) →
    (∀ σ, P B σ) →
    ∀ σ, P <! A ∨ B !> σ.
  Proof.
    intros. destruct (feval_lem σ <! A ∨ B !>).
    - admit.
      -
    -
    Admitted.
  (*   intros. intros σ. specialize (H0 σ). specialize (H1 σ). intros. destruct (feval_lem σ A). *)
  (*   -  *)
  (*   intros. intros σ *)
  (*   apply f_or_elim. intros σ. specialize (H σ). specialize (H0 σ). destruct (feval_lem σ A); intros. *)
  (*   - apply H. *)
  (*     f_or_intro_l *)
  (*   - *)

  (* Lemma f_weaken A P : *)
  (*   (∀ σ, feval σ A → P) → *)
  (*   (A ≡ <! true !> → P). *)
  (* Proof. *)
  (*   intros.  *)

  (* Lemma f_or_elim_Prop A B C (P : formula → formula) : *)
  (*   (P A ⇛ C) → *)
  (*   (P B ⇛ C) → *)
  (*   P <! A ∨ B !> ⇛ C. *)
  (* Proof. *)
  (*   intros. apply f_or_elim. intros σ. specialize (H σ). specialize (H0 σ). destruct (feval_lem σ A); intros. *)
  (*   - apply H. *)
  (*     f_or_intro_l *)
  (*   - *)
  (* Lemma f_destruct A C (P : formula → formula) : *)
  (*   (P <! true !> ⇛ C) → *)
  (*   (P <! false !> ⇛ C) → *)
  (*   P A ⇛ C. *)
  (* Proof. *)
  (*   intros σ. specialize (H σ). specialize (H0 σ). destruct (feval_lem σ A). *)
  (*   - intros. apply H. *)
  (*   - *)
  (*   intros. pose proof (f_lem A). *)
  (* Lemma f_destruct_Prop A (P : state → formula → Prop) : *)
  (*   (∀ σ, P σ <! true !>) → *)
  (*   (∀ σ, P σ <! false !>) → *)
  (*   ∀ σ, P σ A. *)
  (* Proof. *)
  (*   intros. destruct (feval_lem σ A). *)
  (*   -  *)
  (*   intros. pose proof (f_lem A). *)
  (* Lemma f_destruct_Prop A (P : state → Prop) : *)
  (*   (A ≡ <! true !> → ∀ σ, P σ) → *)
  (*   (A ≡ <! false !> → ∀ σ, P σ) → *)
  (*   ∀ σ, P σ. *)
  (* Proof. *)
  (*   intros. pose proof (f_lem A). *)
  (* Lemma f_or_elim_Prop A B (P : state → Prop) : *)
  (*   (<! A ∨ B !> ≡ A → ∀ σ, P σ) → *)
  (*   (<! A ∨ B !> ≡ B → ∀ σ, P σ) → *)
  (*   ∀ σ, P σ. *)
  (* Proof. *)
  (*   intros. pose proof (f_lem A). *)
  (*   <! A ∨ B ⇒ C !> ≡ <! true !>. *)
  (* Proof. *)
  (*   intros. pose proof (f_lem A). intros σ. split; intros. *)
  (*   - unfold FImpl in H1. simp feval in H1. destruct H1. *)
  (*     + destruct  *)
  (*   intros HA HB.  *)
  (*   (∀ σ, C ≡ <! B !> → P σ) → *)
  (*   ∀ σ, C ≡ <! A ∨ B !> → P σ. *)
  (* Proof. *)

  (* Lemma f_or_elim_Prop A B C (P : state → Prop) : *)
  (*   (∀ σ, C ≡ <! A !> → P σ) → *)
  (*   (∀ σ, C ≡ <! B !> → P σ) → *)
  (*   ∀ σ, C ≡ <! A ∨ B !> → P σ. *)
  (* Proof. *)
  (*   intros. destruct (feval_lem σ A). *)
  (*   - apply H. rewrite H1. intros σ'. *)
  (*   intros.  *)
  (* Lemma f_or_elim_Prop A P : *)
  (*   P <! true !> → *)
  (*   P <! false !> → *)
  (*   P A. *)
  (* Proof. *)
  (*   intros. pose proof  *)
  (*   (A ≡ <! true !> → P) → *)
  (*   (A ≡ <! false !> → P) → *)
  (*   P. *)
  (* Proof. *)
  (*   intros. pose proof (f_lem A).  *)

  Lemma r_alternation w pre post gs `{FormulaFinal _ pre} :
    pre ⇛ <! ∨* ⤊ gs !> →
    <{ *w : [pre, post] }> ⊑ <{ if | g : gs → *w : [g ∧ pre, post] fi }>.
  Proof with auto.
    intros proviso A. simpl. rewrite proviso. clear proviso. induction gs as [|g gs IH].
    - simpl. f_simpl. reflexivity.
    - simpl. fold (@fmap list _ final_formula formula).
      fold (@fmap list _ (final_formula * prog)).
      revert g.
      destruct
      destruct (feval_lem )
      forward IH.
      { rewrite proviso. simpl. fold (@fmap list _ final_formula). f_or_intro_l
      (* replace (list_fmap final_formula formula as_formula) with *)
      (*   (@fmap list _ final_formula _ as_formula)... *)
      (*   with (⤊ gs) by reflexivity. *)


  Lemma r_iteration w (I : formula) (v : variable) gcs :
    w : [inv, inv ∧ ¬ (gcomc_any_guard gcs)] ⊑ `PDo gcs`






Lemma assignment : forall pre post x E,
  pre ⇛ post[x \ E] ->
  <{ x : [pre, post] ⊑ x := E }>.
Proof.
  intros pre post w E H A Hfinal. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

