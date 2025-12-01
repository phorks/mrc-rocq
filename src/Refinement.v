From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
(* From Stdlib Require Import Strings.String. *)
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
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  (* Implicit Types ts : list term. *)

  (* TODO: reorder laws *)
  (* 1.8 *)
  Lemma r_absorb_assumption pre' w pre post `{FormulaFinal _ pre'} `{FormulaFinal _ pre} :
    <{ {pre'} *w : [pre, post] }> ≡ <{ *w : [pre' ∧ pre, post] }>.
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

  Lemma final_var_list_as_var_disjoint_term_fvars_initial_var_of (w : list final_variable) :
    list_to_set (as_var <$> w) ## ⋃ (term_fvars <$> (@TVar value <$> (initial_var_of <$> w))).
  Proof.
    intros x H1 H2. apply elem_of_union_list in H2 as (fvars&?&?).
    rewrite <- list_fmap_compose in H. set_unfold in H. destruct H as (x0&?&(x'&?&?)).
    subst. simpl in *. set_solver.
  Qed.

  Hint Resolve final_var_list_as_var_disjoint_term_fvars_initial_var_of : core.

  (* Global Instance elem_of_ *)

  Global Instance set_unfold_elem_of_term_fvars_of_initial_vars x w
    : SetUnfoldElemOf x
        (⋃ (term_fvars <$> (@TVar value <$> (initial_var_of <$> w))))
        (¬ var_final x ∧ to_final_var x ∈ w).
  Proof with auto.
    constructor. split.
    - intros. apply elem_of_union_list in H as (t&?&?). rewrite <- list_fmap_compose in H.
      set_unfold in H. destruct H as (x'&?&?&?&?). subst. simpl in H0. set_unfold in H0.
      subst. rewrite to_final_var_initial_var_of. split...
    - intros []. apply elem_of_union_list. exists ({[x]}). rewrite <- list_fmap_compose.
      set_unfold. split... exists x. split... exists (to_final_var x). split...
      unfold var_final in H. apply not_false_is_true in H. unfold to_final_var.
      unfold initial_var_of. destruct x. simpl. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_list_to_set_as_var_final_variables x w
    : SetUnfoldElemOf x
        (list_to_set (as_var <$> w) : gset variable)
        (var_final x ∧ (to_final_var x ∈ w)).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (x'&?&?). subst. split; [apply var_final_as_var | rewrite to_final_var_as_var]...
    - intros []. exists (to_final_var x). split... unfold var_final in H. destruct x.
      cbv. f_equal...
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
    SetUnfoldElemOf x
                      (formula_fvars <! A[_₀\ w] !>)
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

  (* Law 5.4 *)
  (* Lemma r_contract_frame w xs pre post `{FormulaFinal _ pre} : *)
  (*   w ## xs → *)
  (*   <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs] ] }>. *)
  (* Proof with auto. *)
  (*   intros Hdisjoint A. simpl. f_simpl. *)
  (*   rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm. *)
  (*   rewrite f_foralllist_elim_binders. rewrite subst_initials_app. *)
  (*   f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist. *)
  (*   2: { set_unfold. set_solver. } *)
  (*   2: { intros x. intros. apply elem_of_union_list in H1 as (fvars&?&?). *)
  (*        apply elem_of_list_to_set in H0. apply elem_of_list_fmap in H0 as (x'&?&?). *)
  (*        apply elem_of_list_fmap in H1 as (t&?&?). apply elem_of_list_fmap in H4 as (y'&?&?). *)
  (*        set_solver. } *)
  (*   f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl. *)
  (*   f_simpl. rewrite f_subst_initials_final_formula... reflexivity. *)
  (* Qed. *)

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
    rewrite (f_foralllist_impl_unused_r _ mid).
    2:{ rewrite fvars_foralllist. set_solver. }
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* TODO: move it *)
  Lemma final_variable_not_in_initials_set (A : formula) (x : variable) (xs : list final_variable) `{FormulaFinal _ A} :
    x ∈ formula_fvars A →
    x ∈ (list_to_set (↑₀ xs) : gset variable) → False.
  Proof.
    intros. apply H in H0. apply elem_of_list_to_set in H1. apply elem_of_list_fmap in H1.
    destruct H1 as (x'&?&?). rewrite H1 in H0. unfold var_final in H0. simpl in H0.
    discriminate.
  Qed.

  (* Law B.2 *)
  Lemma r_seq_frame w xs pre mid post `{FormulaFinal _ pre} `{FormulaFinal _ mid} :
    w ## xs →
    list_to_set (↑₀ xs) ## formula_fvars post →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs : [pre, mid]; *w, *xs : [mid, post] }>.
  Proof with auto.
    intros. intros A. simpl. f_simpl. rewrite f_impl_and_r. f_simpl.
    rewrite (subst_initials_app _ w xs).
    assert (formula_fvars <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> ## list_to_set (↑₀ xs)).
    { intros x ? ?. rewrite fvars_foralllist in H3. simpl in H3.
      apply elem_of_difference in H3 as []. apply elem_of_union in H3 as [|]...
      - set_solver.
      - eapply (final_variable_not_in_initials_set A x xs)... }
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials _ xs) at 1...
    2:{ rewrite fvars_foralllist. simpl. intros x ? ?.
        set_unfold in H4. destruct H4 as [ [|] ?].
        - apply H6. apply H0 in H4. unfold var_final in H4. exists (to_final_var x).
          split...
          + rewrite as_var_to_final_var.
            symmetry. rewrite var_with_is_initial_id...
          + set_solver.
        - apply fvars_subst_initials_superset in H4. set_solver. }
    rewrite (f_foralllist_impl_unused_r (↑ₓ xs)) at 1.
    2:{ apply set_eq. intros x. split; [| set_solver]; intros. exfalso.
        set_unfold in H4. destruct H4 as []. destruct H4 as (x'&?&?).
        apply fvars_subst_initials_superset in H5.
        rewrite fvars_foralllist in H5. set_solver. }
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
    pose proof (@f_foralllist_one_point M
                  (initial_var_of <$> (w ++ xs)) ((TVar <$> (as_var <$> (w++xs))))) as ->...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula'.
    2: { unfold formula_final. intros. apply fvars_ssubst_superset in H1.
         set_unfold. destruct H1.
         - apply final_formula_final in H1...
         - apply elem_of_union_list in H1 as (fvars&?&?).
           apply elem_of_list_fmap in H1 as (t&->&?).
           apply elem_of_list_fmap in H1 as (t'&->&?).
           pose proof (final_term_final t').
           apply H3... }
    reflexivity.
  Qed.


  Lemma r_alternation

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

