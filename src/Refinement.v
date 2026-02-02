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
  Context `{MNat : ModelWithNat M}.
  Local Notation value := (value M).
  Local Notation prog := (@prog M).
  Local Notation state := (state M).
  Local Notation term := (termM M).
  Local Notation formula := (formulaM M).
  Local Notation final_term := (final_termM M).
  Local Notation final_formula := (final_formulaM M).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  Implicit Types gs : list final_formula.
  Implicit Types rhs : list (@asgn_rhs_term M).
  Implicit Types p : prog.
  (* Implicit Types ts : list term. *)

  (* TODO: reorder laws *)
  (* 1.8 *)
  Lemma r_absorb_assumption pre' w pre post `{!FormulaFinal pre'} `{!FormulaFinal pre} :
    <{ {pre'}; *w : [pre, post] }> ≡ <{ *w : [pre' ∧ pre, post] }>.
  Proof with auto.
    intros A. simpl. repeat rewrite subst_initials_nil. fSimpl. rewrite f_and_assoc...
  Qed.

  (* Law 1.1 *)
  Lemma r_strengthen_post w pre post post' `{!FormulaFinal pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl. fSimpl. rewrite <- Hent. reflexivity.
  Qed.


  (* Law 5.1 *)
  Lemma r_strengthen_post_with_initials w pre post post' `{!FormulaFinal pre} :
    <! pre[; ↑ₓ w \ ⇑₀ w ;] ∧ post' !> ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl.
    rewrite <- Hent. rewrite <- f_impl_curry. rewrite -> f_foralllist_impl_unused_l.
    2: { intros x ? ?. apply (fvars_seqsubst_superset_vars_not_free_in_terms) in H0...
         set_solver. }
    rewrite simpl_subst_initials_impl. rewrite subst_initials_inverse_l by set_solver...
    rewrite <- (f_and_idemp pre) at 1. rewrite <- f_and_assoc. fSimpl.
    reflexivity.
  Qed.

  (* Law 1.2 *)
  Lemma r_weaken_pre w pre pre' post `{!FormulaFinal pre} `{!FormulaFinal pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A. simpl. fSimpl. assumption.
  Qed.

  Lemma r_permute_frame w w' pre post `{!FormulaFinal pre} :
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros H A. simpl. fSimpl. rewrite subst_initials_perm with (xs':=w')... f_equiv.
      rewrite f_foralllist_permute with (xs':=(fmap as_var w'))... apply Permutation_map...
  Qed.

  (* Law 5.4 *)
  Lemma r_contract_frame w xs pre post `{!FormulaFinal pre} :
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs]] }>.
  Proof with auto.
    intros Hdisjoint A. simpl. fSimpl.
    rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist by set_solver.
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    fSimpl. rewrite f_subst_initials_final_formula...
  Qed.

  Lemma fequiv_st_lem σ A B :
    A ≡_{σ} B ∨ ¬ A ≡_{σ} B.
  Proof with auto.
    destruct (feval_lem σ A); destruct (feval_lem σ B).
    - left. done.
    - right. intros []...
    - right. intros []...
    - left. done.
  Qed.

  Lemma r_expand_frame_1 xs w pre post `{!FormulaFinal pre} :
    w ## xs →
    <! post[_₀\ xs] !> ≡ post →
    <{ *w : [pre, post] }> ⊑ <{ *w, *xs : [pre, post ∧ ⎡⇑ₓ xs =* ⇑₀ xs⎤] }>.
  Proof with auto.
    intros Hdisjoint H A. simpl. fSimpl.
    unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite <- f_foralllist_one_point...
    erewrite (@eqlist_rewrite _ _ _ (⇑₀ (w ++ xs))). Unshelve.
    4-5: do 2 rewrite fmap_app; reflexivity.
    rewrite f_eqlist_app. rewrite fmap_app. rewrite foralllist_app.
    rewrite <- f_impl_curry. rewrite (f_foralllist_impl_unused_l (↑₀ xs)).
    2:{ intros ???. rewrite fvars_eqlist in H1. set_solver. }
    f_equiv. f_equiv.
    rewrite f_and_comm. rewrite <- f_impl_curry.
    rewrite fmap_app. rewrite foralllist_app.
    rewrite f_foralllist_comm.
    rewrite (f_foralllist_impl_unused_l (↑ₓ w) _ <! post ⇒ A !>).
    2:{ intros ???. rewrite fvars_eqlist in H1. set_solver. }
    setoid_rewrite (f_foralllist_one_point (↑ₓ xs))...
    rewrite f_foralllist_one_point... setoid_rewrite <- H at 2. rewrite fold_subst_initials.
    rewrite subst_initials_inverse_l...
    1: { rewrite H... }
    intros x ??. set_unfold. destruct H1. clear H2.
    destruct H1 as [[[] |] |]; [set_solver|set_solver|].
    apply formula_is_final in H1. naive_solver.
    Unshelve. typeclasses eauto.
  Qed.

  (* Law 3.2 *)
  Lemma r_skip w pre post `{!FormulaFinal pre} :
    pre ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    fSimpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite H. rewrite f_impl_elim. rewrite f_foralllist_one_point...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 5.3 *)
  Lemma r_skip_with_initials w pre post `{!FormulaFinal pre} :
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ pre !> ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    fSimpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite f_impl_dup_hyp. rewrite f_and_assoc. rewrite H. rewrite f_impl_elim.
    rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 3.4 *)
  Lemma r_skip_seq_l p :
    <{ $skip; $p }> ≡ p.
  Proof. intros A. unfold skip. simpl. rewrite subst_initials_nil. fSimpl. Qed.

  (* Law 3.4 *)
  Lemma r_skip_seq_r p :
    <{ $p; $skip }> ≡ p.
  Proof. intros A. unfold skip. simpl. rewrite subst_initials_nil. fSimpl. Qed.

  (* Law 3.3 *)
  Lemma r_seq w pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} `{!FormulaFinal post} :
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, mid]; *w : [mid, post] }>.
  Proof with auto.
    intros A. simpl. fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_foralllist_impl_unused_r _ mid) by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* Law B.2 *)
  Lemma r_seq_frame w xs pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} :
    w ## xs →
    list_to_set (↑₀ xs) ## formula_fvars post →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs : [pre, mid]; *w, *xs : [mid, post] }>.
  Proof with auto.
    intros. intros A. simpl. fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (subst_initials_app _ w xs).
    assert (formula_fvars <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> ## list_to_set (↑₀ xs)).
    { intros x ??. set_unfold in H1. destruct H1 as ([|]&?); [set_solver|].
      set_unfold. destruct H2 as [? _]. apply elem_of_fvars_final_formula_inv in H1... }
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials _ xs) at 1 by set_solver...
    rewrite (f_foralllist_impl_unused_r (↑ₓ xs)) at 1 by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  Lemma r_varlist_permute xs xs' (p : prog) :
    xs ≡ₚ xs' →
    <{ |[ var* xs ⦁ $p ]| }> ≡ <{ |[ var* xs' ⦁ $p ]| }>.
  Proof.
    intros Hperm A. do 2 rewrite wp_varlist. rewrite f_foralllist_permute; [reflexivity|].
    apply Permutation_map. assumption.
  Qed.

  Lemma r_varlist_app xs1 xs2 p :
    <{ |[ var* $(xs1 ++ xs2) ⦁ $p ]| }> ≡ <{ |[ var* $(xs2 ++ xs1) ⦁ $p ]| }>.
  Proof with auto.
    intros A. do 2 rewrite wp_varlist. do 2 rewrite fmap_app.
    do 2 rewrite foralllist_app. rewrite f_foralllist_comm...
  Qed.

  Lemma r_following_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!OfSameLength xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <{ *w, *xs : [pre, post] }> ⊑
    <{ *w, *xs : [pre, post[[↑ₓ xs \ ⇑ₜ ts]]]; *xs := *(FinalRhsTerm <$> ts) }>.
  Proof with auto.
    intros Hlength Hnodup A. simpl. rewrite wp_asgn. fSimpl. rewrite <- simpl_msubst_impl.
    f_equiv. rewrite fmap_app. do 2 rewrite foralllist_app. f_equiv.
    rewrite <- f_foralllist_idemp. rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !>)...
    - reflexivity.
    - rewrite length_fmap...
  Qed.

  Lemma r_leading_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!FormulaFinal <! pre[[↑ₓ xs \ ⇑ₜ ts]] !>} :
    w ## xs →
    NoDup w →
    NoDup xs →
    let ts₀ := (λ t : final_term, <! t[[ₜ ↑ₓ w, ↑ₓ xs \ ⇑₀ w, ⇑₀ xs]] !>) <$> ts in
    <{ *w, *xs : [pre[[↑ₓ xs \ ⇑ₜ ts]], post[[↑₀ xs \ *ts₀]]] }> ⊑
      <{ *xs := *(FinalRhsTerm <$> ts); *w, *xs : [pre, post] }>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 ? A. simpl. rewrite wp_asgn. rewrite simpl_msubst_and.
    fSimpl. unfold subst_initials at 1. rewrite subst_initials_app_comm.
    rewrite subst_initials_app. rewrite subst_initials_msubst.
    setoid_rewrite (msubst_trans _ (↑₀ xs) (↑ₓ xs) (⇑ₜ ts)); [| set_solver | |]...
    2:{ intros x ??. set_unfold. destruct H0 as [|]; [set_solver|].
        destruct H. destruct H0 as (x'&?&?&_&_). subst.
        rewrite to_final_var_as_var in H1. set_solver. }
    assert (zip_pair_functional ↑₀ xs ⇑ₜ ts).
    { apply NoDup_zip_pair_functional. apply NoDup_fmap... apply initial_var_of_inj. }
    assert (list_to_set ↑₀ xs ## ⋃ (term_fvars <$> ⇑ₜ ts)).
    { intros x ??. set_unfold in H0. set_unfold in H1. destruct H1 as (t&?&t'&?&?).
      subst. destruct H0 as []. apply final_term_final in H1. done. }
    assert (as_formula A ≡ <! A [[↑₀ xs \ *ts₀]] !>).
    { rewrite msubst_non_free... intros x ??. apply formula_is_final in H2. set_solver. }
    rewrite H1 at 1. clear H1. rewrite <- simpl_msubst_impl.
    assert (<! (∀* ↑ₓ (w ++ xs), (post ⇒ A) [ [↑₀ xs \ * ts₀] ]) !> ≡
              <! (∀* ↑ₓ (w ++ xs), (post ⇒ A)) [ [↑₀ xs \ * ts₀] ] !>).
    { rewrite simpl_msubst_foralllist; [auto|set_solver|]. intros x ??. set_unfold in H1.
      destruct H1 as []. set_unfold in H2. destruct H2 as (t&?&t'&?&?). subst.
      apply fvars_msubst_term_superset_vars_not_free_in_terms in H2...
      - set_unfold in H2. destruct H2 as [[] |].
        + apply Decidable.not_or in H4 as []. destruct H3.
          * apply H4. exists (to_final_var x). split... rewrite as_var_to_final_var.
            symmetry. apply var_with_is_initial_id. apply H1.
          * apply H6. exists (to_final_var x). split... rewrite as_var_to_final_var.
            symmetry. apply var_with_is_initial_id. apply H1.
        + destruct H2 as (t&?&?). destruct H4.
          * destruct H4 as (x'&->&?&?&?). simpl in H2. set_unfold in H2. subst x'.
            rewrite H4 in H1. unfold var_final in H1. simpl in H1. discriminate.
          * destruct H4 as (x'&->&?&?&?). simpl in H2. set_unfold in H2. subst x'.
            rewrite H4 in H1. unfold var_final in H1. simpl in H1. discriminate.
      - apply NoDup_app. do 2 rewrite NoDup_fmap by apply as_var_inj. set_solver.
      - apply disjoint_final_initial_vars; [set_solver|]. clear dependent x. intros x ??.
        rewrite <- fmap_app in H1. set_unfold in H1. destruct H1 as (t&?&x'&->&?).
        destruct H3; destruct H3 as (?&->&?); set_unfold in H1; subst x; done. }
    rewrite H1. clear H1.
    rewrite fold_subst_initials. rewrite subst_initials_app.
    rewrite (subst_initials_msubst xs). rewrite msubst_msubst_eq.
    2:{ apply NoDup_fmap... apply initial_var_of_inj. }
    rewrite subst_initials_msubst. rewrite msubst_msubst_disj.
    2:{ set_solver. }
    2-3: apply NoDup_fmap; auto; apply initial_var_of_inj.
    2:{ set_solver. }
    rewrite <- subst_initials_msubst. f_equiv. apply map_eq. intros x₀. unfold to_vtmap.
    destruct (decide (x₀ ∈ ↑₀ xs)).
    - apply elem_of_list_fmap in e as (x'&?&?). apply elem_of_list_lookup in H2 as (i&?).
      destruct (lookup_of_same_length_l ts H2) as (t&?). trans (Some (as_term t)).
      + rewrite lookup_list_to_map_zip_Some by typeclasses eauto. exists i. split_and!.
        * rewrite list_lookup_fmap. rewrite H2. simpl. rewrite H1...
        * unfold ts₀. repeat rewrite list_lookup_fmap. rewrite H3.
          simpl. f_equal.
          opose proof msubst_term_app. unfold to_vtmap in H4 at 2 3.
          assert (xs ## w) by set_solver.
          erewrite <- H4; clear H4... rewrite msubst_term_app_comm...
          opose proof (msubst_term_trans t (↑ₓ w ++ ↑ₓ xs) (↑₀ w ++ ↑₀ xs) (⇑ₓ w ++ ⇑ₓ xs)).
             trans (msubst_term t (to_vtmap (↑ₓ w ++ ↑ₓ xs) ((@TVar value _ <$> (as_var <$> w)) ++
                                                           (@TVar value _ <$> (as_var <$> xs))))).
             -- symmetry. etrans.
                ++ rewrite <- H4; clear dependent H4 H ts₀; [reflexivity| | | | ].
                   ** set_solver.
                   ** rewrite NoDup_app.
                      repeat rewrite NoDup_fmap; [| apply as_var_inj | apply as_var_inj].
                      set_solver.
                   ** rewrite <- fmap_app. apply NoDup_fmap; [apply initial_var_of_inj|].
                      apply NoDup_app...
                   ** clear dependent x₀ x'. intros x ??. set_unfold in H.
                      apply term_is_final in H1. destruct H as [[x' [? ?]] | [x' [? ?]]]; subst;
                        done.
                ++ f_equal. f_equal. unfold to_vtmap. f_equal. f_equal. rewrite fmap_app...
             -- unfold to_vtmap. repeat rewrite <- fmap_app. rewrite msubst_term_diag'...
                apply NoDup_fmap; [apply as_var_inj|]. apply NoDup_app...
        * intros. apply list_lookup_fmap_Some in H4 as (x''&?&?). rewrite H1 in H5.
          apply initial_var_of_inj in H5. subst x''. apply NoDup_lookup with (i:=i) in H4...
          lia.
      + symmetry. subst. apply lookup_list_to_map_zip_Some; [typeclasses eauto|]. exists i.
        split_and!...
        * rewrite list_lookup_fmap. rewrite H2. simpl...
        * rewrite list_lookup_fmap. rewrite H3. simpl...
        * intros. apply list_lookup_fmap_Some in H1 as (x''&?&?). apply initial_var_of_inj in H4.
          subst x''. apply NoDup_lookup with (i:=i) in H1... lia.
    - etrans.
      + apply lookup_list_to_map_zip_None... typeclasses eauto.
      + symmetry. apply lookup_list_to_map_zip_None... typeclasses eauto.
  Qed.


  (* Law 5.2 *)
  Lemma r_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} :
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
    rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite fmap_app. reflexivity. }
    3: { do 2 rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_msubst_impl.
    fSimpl. rewrite <- f_eqlist_app.
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    3: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    setoid_rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
    apply msubst_formula_final.
    Unshelve. typeclasses eauto.
  Qed.

  Local Lemma r_asgn_equiv' xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    asgn_opens (split_asgn_list xs1 rhs1) ≡ₚ asgn_opens (split_asgn_list xs2 rhs2) →
    (asgn_xs (split_asgn_list xs1 rhs1), asgn_ts (split_asgn_list xs1 rhs1)) ≡ₚₚ
      (asgn_xs (split_asgn_list xs2 rhs2), asgn_ts (split_asgn_list xs2 rhs2)) →
    <{ * xs1 := * rhs1 }> ≡ <{ * xs2 := * rhs2 }>.
  Proof with auto.
    intros Hnodup1 Hnodup2 Hopens Hclosed A. unfold PAsgnWithOpens.
    destruct (split_asgn_list xs1 rhs1) eqn:E1. simpl in *.
    destruct (split_asgn_list xs2 rhs2) eqn:E2. simpl in *. apply wp_proper_pequiv.
    rewrite r_varlist_permute.
    2:{ apply Hopens. }
    f_equiv. clear A Hopens. intros A. simpl. apply msubst_zip_pair_Permutation.
    - apply NoDup_fmap.
      + apply as_var_inj.
      + eapply submseteq_NoDup; [exact Hnodup1|].
        replace asgn_xs with (Prog.asgn_xs (split_asgn_list xs1 rhs1)).
        * apply asgn_xs_submseteq.
        * rewrite E1. reflexivity.
    - apply NoDup_fmap.
      + apply as_var_inj.
      + eapply submseteq_NoDup; [exact Hnodup2|].
        replace asgn_xs0 with (Prog.asgn_xs (split_asgn_list xs2 rhs2)).
        * apply asgn_xs_submseteq.
        * rewrite E2. reflexivity.
    - apply zip_pair_Permutation_fmap; try typeclasses eauto...
  Qed.

  Lemma r_asgn_equiv xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    (xs1, rhs1) ≡ₚₚ (xs2, rhs2) →
    <{ * xs1 := * rhs1 }> ≡ <{ * xs2 := * rhs2 }>.
  Proof with auto.
    intros. apply r_asgn_equiv'...
    - apply asgn_opens_Permutation...
    - apply asgn_xs_ts_Permutation...
  Qed.

  Lemma wp_asgn_equiv (A : final_formula) xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    (xs1, rhs1) ≡ₚₚ (xs2, rhs2) →
    wp (PAsgnWithOpens xs1 rhs1) A ≡ wp (PAsgnWithOpens xs2 rhs2) A.
  Proof with auto. intros. apply r_asgn_equiv... Qed.

  Lemma r_open_assignment_l x t xs rhs
      `{!OfSameLength xs rhs}
      `{!OfSameLength ([x] ++ xs) ([OpenRhsTerm] ++ rhs)}
      `{!OfSameLength ([x] ++ xs) ([FinalRhsTerm t] ++ rhs)} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs, rhs) → as_var x ∉ term_fvars t') →
    <{ x, *xs := ?, *rhs }> ⊑ <{ x, *xs := t, *rhs }>.
  Proof with auto.
    intros. intros A. unfold PAsgnWithOpens. simpl.
    destruct (split_asgn_list (x :: xs) (OpenRhsTerm :: rhs)) eqn:E1.
    destruct (split_asgn_list (x :: xs) (FinalRhsTerm (as_final_term t) :: rhs)) eqn:E2.
    rewrite split_asgn_list_cons_open with (OfSameLength0:=OfSameLength0) in E1.
    rewrite split_asgn_list_cons_closed with (Hl1:=OfSameLength0) in E2.
    unfold asgn_args_with_open in E1. unfold asgn_args_with_closed in E2.
    simpl in E1, E2. destruct (split_asgn_list xs rhs) eqn:E3.
    inversion E1. inversion E2. subst.
    assert (asgn_opens0 = Prog.asgn_opens (split_asgn_list xs rhs)) as Heq1 by (rewrite E3; done).
    assert (asgn_xs = Prog.asgn_xs (split_asgn_list xs rhs)) as Heq2 by (rewrite E3; done).
    assert (asgn_ts = Prog.asgn_ts (split_asgn_list xs rhs)) as Heq3 by (rewrite E3; done).
    clear E1 E2 E3. simpl. repeat rewrite wp_varlist. simpl.
    rewrite f_forall_elim with (t:=t). rewrite simpl_subst_foralllist.
    2:{ intros contra. apply elem_of_list_fmap in contra. destruct contra as (x'&?&?).
        apply as_var_inj in H3. subst. eapply elem_of_submseteq in H4;
          [| apply asgn_opens_submseteq]... }
    2:{ intros y ??. set_unfold in H3. destruct H3 as []. apply H1 with (x':=(to_final_var y)).
        - subst. apply elem_of_asgn_opens in H5...
        - rewrite as_var_to_final_var_final... }
    rewrite <- msubst_extract_r.
    - simpl. reflexivity.
    - intros contra. apply elem_of_list_fmap in contra as (x'&?&?). apply as_var_inj in H3.
      subst. eapply elem_of_submseteq in H4; [| apply asgn_xs_submseteq]. done.
    - clear dependent t. set_unfold. intros (?&?&t&->&?). subst.
      apply elem_of_asgn_ts_inv in H3 as (xt&?).
      apply elem_of_asgn_xs_ts in H3... apply H2 in H3. contradiction.
  Qed.

  (* Law 3.1 *)
  Lemma r_open_assignment_r x t xs rhs
      `{!OfSameLength xs rhs}
      `{!OfSameLength (xs ++ [x]) (rhs ++ [OpenRhsTerm])}
      `{!OfSameLength (xs ++ [x]) (rhs ++ [FinalRhsTerm t])} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs, rhs) → as_var x ∉ term_fvars t') →
    <{ *xs, x := *rhs, ? }> ⊑ <{ *xs, x := *rhs, t }>.
  Proof with auto.
    intros. intros A.
    rewrite wp_asgn_equiv with (xs2:=[x] ++ xs) (rhs2:=[OpenRhsTerm] ++ rhs).
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        apply zip_pair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite wp_asgn_equiv with (xs1:=xs ++ [x]) (xs2:=[x] ++ xs) (rhs2:=[FinalRhsTerm t] ++ rhs)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        rewrite as_final_term_as_term. apply zip_pair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite (r_open_assignment_l x t xs rhs H H0 H1 H2 A). simpl.
    rewrite as_final_term_as_term. reflexivity.
  Qed.

  Lemma r_open_assignment_middle x t xs0 xs1 rhs0 rhs1
      `{!OfSameLength xs0 rhs0}
      `{!OfSameLength xs1 rhs1}
      `{!OfSameLength (xs0 ++ [x] ++ xs1) (rhs0 ++ [OpenRhsTerm] ++ rhs1)}
      `{!OfSameLength (xs0 ++ [x] ++ xs1) (rhs0 ++ [FinalRhsTerm t] ++ rhs1)} :
    (∀ x', (x', OpenRhsTerm) ∈ (xs0, rhs0) → as_var x' ∉ term_fvars t) →
    (∀ x', (x', OpenRhsTerm) ∈ (xs1, rhs1) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs0, rhs0) → as_var x ∉ term_fvars t') →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs1, rhs1) → as_var x ∉ term_fvars t') →
    x ∉ xs0 →
    x ∉ xs1 →
    NoDup xs0 →
    NoDup xs1 →
    xs0 ## xs1 →
    <{ *xs0, x, *xs1 := *rhs0, ?, *rhs1 }> ⊑ <{ *xs0, x, *xs1 := *rhs0, t, *rhs1 }>.
  Proof with auto.
    intros. intros A.
    rewrite wp_asgn_equiv with (xs2:=[x] ++ xs0 ++ xs1) (rhs2:=[OpenRhsTerm] ++ rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons. split... }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm...
        2: typeclasses eauto. simpl. apply zip_pair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zip_pair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    rewrite wp_asgn_equiv with (xs1:=xs0 ++ [x] ++ xs1) (xs2:=[x] ++ xs0 ++ xs1)
                                                    (rhs2:=[FinalRhsTerm t] ++ rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons.
        split... }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm...
        2: typeclasses eauto. simpl. rewrite as_final_term_as_term.
        apply zip_pair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zip_pair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    opose proof (r_open_assignment_l x t (xs0 ++ xs1) (rhs0 ++ rhs1) _ _ _ _ A).
    1:{ set_solver. }
    1:{ apply NoDup_app. split_and!... }
    1:{ intros. apply elem_of_zip_pair_app in H8... destruct H8... }
    1:{ intros. apply elem_of_zip_pair_app in H8... destruct H8...
        - eapply H1. apply H8.
        - eapply H2. apply H8. }
    rewrite H8. simpl. rewrite as_final_term_as_term. reflexivity.
  Qed.

  (* Law 4.1 *)
  Lemma r_alternation w pre post gs `{!FormulaFinal pre} :
    pre ⇛ <! ∨* ⤊ gs !> →
    <{ *w : [pre, post] }> ⊑ <{ if | g : gs → *w : [g ∧ pre, post] fi }>.
  Proof with auto.
    intros proviso A. simpl. rewrite fent_fent_st. intros σ.
    rewrite fent_fent_st in proviso. specialize (proviso σ).
    induction gs as [|g gs IH].
    - rewrite proviso. simpl. fSimpl...
    - simpl in *. fold (@fmap list _ final_formula formula) in *.
      fold (@fmap list _ (final_formula * prog)).
      fLem g.
      + fSimpl. fSplit... fLem pre.
        2:{ fSimpl... }
        fLem <! ∨* ⤊ gs !>.
        * forward IH... fSimpl. rewrite IH. intros ?. simp feval in H2. destruct H2 as [].
          assumption.
        * clear IH proviso H H0 g. induction gs as [|g gs IH]; simpl...
          simpl in *. apply f_or_equiv_st_false in H1 as []. rewrite H. fSimpl.
          rewrite IH...
      + fSimpl. forward IH...
  Qed.

  (* TODO: move these *)
  Definition nat_to_term (n : nat) : term :=
    TConst (nat_to_value n).

  Coercion nat_to_term : nat >-> term.

  Arguments raw_initial_var name : simpl never.

  Global Instance fresh_var_final x fvars `{VarFinal x} : VarFinal (fresh_var x fvars).
  Proof with auto.
    unfold VarFinal. generalize dependent x. unfold fresh_var. induction (S (size fvars)); intros.
    - simpl. apply H.
    - simpl. destruct (decide (x ∈ fvars)).
      + apply IHn. unfold VarFinal, var_final in H. destruct x. simpl in H.
        rewrite H. reflexivity.
      + apply H.
  Qed.

  Lemma initial_var_of_eq_to_initial_var (x : final_variable) :
    initial_var_of x = to_initial_var x.
  Proof. cbv. reflexivity. Qed.

  Lemma set_to_list_as_var_set_list_to_set w :
    NoDup w →
    set_to_list (as_var_set (list_to_set w)) ≡ₚ ↑ₓ w.
  Proof with auto.
    intros. unfold as_var_set. rewrite set_to_list_set_map_perm by exact as_var_inj.
    apply fmap_Permutation. apply set_to_list_list_to_set...
  Qed.

  Lemma r_iteration (w : list final_variable) (g inv : final_formula) (var : final_term) (p : prog) :
    NoDup w →
    let var₀ := <! $(as_term var) [[ₜ ↑ₓ w \ ⇑₀ w ]] !> in
    <{ *w : [inv, inv ∧ ¬ g] }> ⊑
      <{ while g invariant inv variant var ⟶
         *w : [inv ∧ g, inv ∧ ⌜var ∈ ℕ⌝ ∧ ⌜0 ≤ var⌝ ∧ ⌜var < var₀⌝] end }>.
  Proof with auto.
    intros Hnodup ? A. simpl. unfold modified_vars. simpl.
    rewrite (f_foralllist_permute (set_to_list (as_var_set (list_to_set w))) (↑ₓ w)).
    2:{ apply set_to_list_as_var_set_list_to_set... }
    rewrite f_subst_initials_no_initials.
    2:{ rewrite fvars_foralllist. simpl. intros x ??. set_unfold. destruct H as [].
        destruct H0 as [? _]. destruct_or! H0; apply final_formula_final in H0... }
    intros σ. simp feval. simpl. repeat rewrite simpl_feval_foralllist. intros.
    destruct_and! H.
    assert (Haux1 : zip_pair_functional ↑ₓ w (@TConst _ (model_symbols M) <$> vs)) by
      (apply NoDup_zip_pair_functional; auto).
    assert (Haux2 : list_to_set ↑ₓ w ## ⋃ (@term_fvars _ (model_symbols M) <$> (TConst <$> vs))).
    { intros x ??. set_unfold in H3. destruct H3 as (t&?&vt&->&?). simpl in H3. set_solver. }
    rewrite seqsubst_msubst... epose proof (teval_vtmap_total σ _) as [mv ?].
    rewrite feval_msubst by exact H. simp feval. split_and!.
    - rewrite simpl_feval_fimpl. simp feval. intros. destruct_and! H3. split_and!...
      unfold subst_initials. rewrite seqsubst_msubst...
      epose proof (teval_vtmap_total _ _) as [mv0 ?].
      rewrite feval_msubst by exact H4. rewrite simpl_feval_foralllist. intros.
      rewrite seqsubst_msubst.
      2:{ apply NoDup_zip_pair_functional... }
      2:{ intros x ??. set_unfold in H9. destruct H9 as (?&?&?&->&?). simpl in H9. set_solver. }
      epose proof (teval_vtmap_total _ _) as [mv' ?].
      rewrite feval_msubst by exact H8. rewrite simpl_feval_fimpl. simp feval.
      intros [? []]. split...
    - specialize (H2 vs H0). apply seqsubst_msubst in H2...
      rewrite feval_msubst in H2 by exact H... rewrite simpl_feval_fimpl in H2 |- *.
      simp feval in H2 |- *. intros [[] ?]. apply H2. split...
    - rewrite simpl_feval_fimpl. simp feval. naive_solver.
    - rewrite simpl_feval_fimpl. simp feval. intros [[] []]. split_and!...
      unfold subst_initials. rewrite seqsubst_msubst...
      epose proof (teval_vtmap_total _ _) as [mv0 ?].
      rewrite feval_msubst by exact H7. rewrite simpl_feval_foralllist.
      intros vs' ?. rewrite seqsubst_msubst...
      2:{ apply NoDup_zip_pair_functional... }
      2:{ intros x ??. set_unfold in H10. destruct H10 as (?&?&?&->&?). set_solver. }
      epose proof (teval_vtmap_total _ _) as [mv' ?].
      rewrite feval_msubst by exact H9. rewrite simpl_feval_fimpl. simp feval.
      intros [? [? []]]. rewrite <- feval_msubst in H13 |- * by exact H9.
      unfold term_lt in H13 |- *. simp msubst in H13 |- *. simpl in H13 |- *.
      unfold var₀ in H13. eapply ATPred_proper_st in H13.
      2:{ reflexivity. }
      2:{ split.
          2:{ constructor; [reflexivity|constructor; [|reflexivity]].
              rewrite msubst_term_msubst_term_eq_cancel... reflexivity. }
          simpl... }
      rewrite <- feval_msubst in H13 |- * by exact H7. simp msubst in H13 |- *.
      simpl in H13 |- *. eapply ATPred_proper_st.
      1:{ reflexivity. }
      2:{ exact H13. }
      split... constructor; [reflexivity|]. constructor... simpl in H6.
      clear dependent H3 H4 H5 mv0 mv' H13 H2. destruct H6 as (vv&?&?).
      symmetry. etrans.
      + erewrite (msubst_term_trans var (↑ₓ w) (↑₀ w))...
        * rewrite msubst_term_diag... reflexivity.
        * set_solver.
        * intros x ??. set_unfold in H4. apply final_term_final in H5. naive_solver.
      + destruct (to_vtmap ↑ₓ w (TConst <$> vs')
                 !! to_initial_var (fresh_var String.EmptyString (as_var_set (list_to_set w)))
                 ) eqn:E.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E.
            2:{ typeclasses eauto. }
            apply elem_of_zip_pair in E as (i&?&?). apply list_lookup_fmap_Some in H4 as (x&?&?).
            destruct x. unfold as_var in H6. simpl in H6. apply (f_equal var_is_initial) in H6.
            simpl in H6. discriminate. }
        simpl. clear E.
        destruct (to_vtmap ↑₀ w ⇑ₓ w
                 !! to_initial_var (fresh_var String.EmptyString (as_var_set (list_to_set w))))
                   eqn:E.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E.
            2:{ typeclasses eauto. }
            apply elem_of_zip_pair in E as (i&?&?). apply list_lookup_fmap_Some in H4 as (x&?&?).
            rewrite initial_var_of_eq_to_initial_var in H6. apply to_initial_var_inj' in H6.
            - pose proof (fresh_var_fresh String.EmptyString (as_var_set (list_to_set w))).
              rewrite H6 in H7. apply elem_of_list_lookup_2 in H4. unfold as_var_set in H7.
              exfalso. apply H7. set_unfold. exists x. split...
            - apply fresh_var_final. unfold VarFinal, var_final. simpl...
            - apply var_final_as_var. }
        intros v. split; intros; apply teval_det with (v1:=vv) in H4; auto; subst...
  Qed.

End refinement.
