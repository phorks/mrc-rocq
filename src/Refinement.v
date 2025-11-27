From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
From Stdlib Require Import Strings.String.
From MRC Require Import Prelude.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

Open Scope stdpp_scope.
Open Scope refiney_scope.

(* TODO: move it *)
#[global] Hint Unfold universal_relation : core.

Section refinement.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation prog := (@prog M).
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.
  (* Implicit Types ts : list term. *)


  Lemma r_strengthen_post w pre post post' `{FormulaFinal _ pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A Hinit. simpl. f_simpl. rewrite <- Hent. reflexivity.
  Qed.

  Lemma r_weaken_pre w pre pre' post `{FormulaFinal _ pre} `{FormulaFinal _ pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A Hinit. simpl. f_simpl. assumption.
  Qed.

  (* TODO: move it *)
  Lemma teval_delete_bottom_state_var σ x t v :
    x ∉ dom σ →
    teval (<[x:=value_bottom M]> σ) t v ↔ teval σ t v.
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

  Lemma afeval_delete_bottom_state_var σ x af :
    x ∉ dom σ →
    afeval (<[x:=value_bottom M]> σ) af ↔ afeval σ af.
  Proof with auto.
    intros. destruct af...
    - simpl. setoid_rewrite teval_delete_bottom_state_var...
    - simpl. split; intros (vargs&?&?); exists vargs; split; auto; clear H1;
        generalize dependent vargs; induction args; intros; inversion H0; subst;
        try constructor...
      + rewrite <- (teval_delete_bottom_state_var _ x a v)...
      + rewrite (teval_delete_bottom_state_var _ x a v)...
  Qed.

  Lemma feval_delete_bottom_state_var σ x A :
    x ∉ dom σ →
    feval (<[x:=value_bottom M]> σ) A ↔ feval σ A.
  Proof with auto.
    intros. induction A; simp feval.
    2-5: naive_solver.
    apply afeval_delete_bottom_state_var...
  Qed.

  Lemma f_exists_introduce_binder x A :
    A ⇛ <! ∃ x, A !>.
  Proof with auto.
    intros σ H. simp feval. pose proof (teval_total σ x) as [v Hv].
    exists v. rewrite feval_subst with (v:=v)... inversion Hv.
    subst x0. subst v0. unfold state in *.
    rewrite lookup_total_alt in H1. destruct (σ !! x) eqn:E.
    + simpl in H1. subst. rewrite insert_id...
    + simpl in H1. rewrite <- H1. rewrite feval_delete_bottom_state_var...
      apply (not_elem_of_dom σ)...
  Qed.

  Lemma f_forall_drop_binder A x :
    <! ∀ x, A !> ⇛ A.
  Proof with auto.
    unfold FForall. apply f_ent_contrapositive. rewrite f_not_stable.
    apply f_exists_introduce_binder.
  Qed.

  Lemma initial_free_in_final_formula x A :
    formula_final A →
    initial_var_of x ∉ formula_fvars A.
  Proof.
    intros. intros contra. apply H in contra. cbv in contra. discriminate.
  Qed.

  Lemma r_contract_frame (x : final_variable) pre post `{FormulaFinal _ pre} :
    <{ x : [pre, post] }> ⊑ <{ : [pre, post[₀x\x] ] }>.
  Proof with auto.
    intros A Hfree. simpl. f_simpl. rewrite f_forall_drop_binder.
    unfold subst_initials. simpl. rewrite simpl_subst_impl.
    rewrite fequiv_subst_non_free with (A:=A).
    - reflexivity.
    - apply initial_free_in_final_formula...
  Qed.

Notation "' xs" := (TVar ∘ as_var <$> xs : list term)
                       (in custom term at level 0,
                           xs constr at level 0) : refiney_scope.
Notation "'₀ xs" := (TVar ∘ initial_var_of <$> xs : list term)
                       (in custom term at level 0,
                           xs constr at level 0) : refiney_scope.
  Lemma r_assignment w xs pre post ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
    <! ⌜'₀w =* 'w⌝ ∧ ⌜'₀xs =* 'xs⌝ ∧ pre !> ⇛ <! post[[ *$(as_var <$> xs) \ *$(as_term <$> ts) ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros proviso A Hfree. simpl. rewrite wp_asgn.
    assert (<! pre !> ≡ <! pre [_₀\w ++ xs] !>).
    { admit. }
    rewrite H1. clear H1. rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials.
    rewrite <- f_foralllist_one_point.
    2:{ unfold seqsubst_lists_unique. intros.
        rewrite elem_of_list_pair_indexed in H2, H3. destruct H2 as [].
        destruct H3.
        apply list_lookup_fmap_inv in H2 as (x1&?&?).
        apply list_lookup_fmap_inv in H3 as (x2&?&?).
        apply list_lookup_fmap_inv in H4 as (x3&?&?).
        apply list_lookup_fmap_inv in H5 as (x4&?&?).
        rewrite H6 in H8. inversion H8. subst x3. rewrite H7 in H9.
        inversion H9. subst x4. clear H8 H9. rewrite H2 in H3.
        rewrite H4. rewrite H5. f_equal. apply initial_var_of_inj in H3... }
    2: { set_unfold. intros x0. intros ((x&?&?)&?).
         apply elem_of_union_list in H3 as (fvars&?&?).
         apply elem_of_list_fmap in H3 as (x1&?&?).
         apply elem_of_list_fmap in H5 as (x2&?&?). subst x1. simpl in H3.
         subst fvars. apply elem_of_singleton in H4. subst x0.
         apply initial_var_of_ne in H4 as []. }
    assert (<! ⌜@*(initial_var_of <$> w ++ xs) =* $(fmap (TVar ∘ as_var) (w ++ xs))⌝
              ⇒ pre ∧ (∀* $(fmap as_var (w ++ xs)),  post ⇒ A) !> ⇛
            <! ⌜@*(initial_var_of <$> w ++ xs) =* $(fmap (TVar ∘ as_var) (w ++ xs))⌝
            ⇒ post[[ *$(as_var <$> xs) \ *$(as_term <$> ts)]]
              ∧ (∀* $(fmap as_var (w ++ xs)),  post ⇒ A) !> ).
    { admit. }
    rewrite H1. clear H1.



    assert
      (<! ⌜₀x = x⌝ ⇒ (pre ∧ (∀ x, post ⇒ A)) !> ⇛
                                <! ⌜₀x = x⌝ ⇒ (post [x \ t] ∧ (∀ x, post ⇒ A)) !>).
    { intros σ ?. rewrite simpl_feval_fimpl in H0. rewrite simpl_feval_fimpl. intros.
      simp feval in *. apply H0 in H1 as H2. destruct H2 as []. split... apply H.
      simp feval. split... }

    rewrite fmap_app.

         as_var_ne

        2: {
        injection H4.
        initial_var_of
        Unset Printing Notations.
        rewrite H3 in H4. inversion H4.
        rewrite H7 in H9. inversion H9.

        naive_solver.
        rewrite elem_of_list_pair_indexed in H3.
    remember ((<! pre ∧ $(FForallList (as_var <$> w ++ xs ++ []) <! post ⇒ A !>) !>)) as C.
    set ( initial_var_of <$> w ++ xs) as X.
    set ( (@TVar value) ∘ as_var <$> w ++ xs) as Y.
    (* pose proof (@f_foralllist_one_point _ X Y C). *)
    pose proof (@f_foralllist_one_point M).
    (* subst X. subst Y. *)
    Unset Printing Notations.
    Set Printing Implicit.

    rewrite <- f_foralllist_one_point with (xs:=X) (ts:=Y) (A:=C).
    rewrite <- f_foralllist_one_point.
    intros H A Hfree. simpl.
    assert (<! pre !> ≡ <! pre [_₀\list_to_set (w ++ xs)] !>).
    { unfold subst_initials. admit. }
    rewrite H1. simpl.
    simpl. f_simpl.
    (* intros pre post x t H A Hfree. simpl. *)
    (* assert (<! %pre !> ≡ pre [₀ x \ x]). *)
    (* { rewrite fequiv_subst_non_free... pose proof (final_formula_final pre). *)
    (*   destruct (decide (₀x ∈ formula_fvars pre))... apply H0 in e. simpl in e. discriminate. } *)
    rewrite H0. clear H0.
    rewrite <- simpl_subst_and.
    rewrite <- (f_forall_one_point).
    2:{ simpl. rewrite not_elem_of_singleton. apply initial_var_of_ne. }
    assert
      (<! ⌜₀x = x⌝ ⇒ (pre ∧ (∀ x, post ⇒ A)) !> ⇛
                                <! ⌜₀x = x⌝ ⇒ (post [x \ t] ∧ (∀ x, post ⇒ A)) !>).
    { intros σ ?. rewrite simpl_feval_fimpl in H0. rewrite simpl_feval_fimpl. intros.
      simp feval in *. apply H0 in H1 as H2. destruct H2 as []. split... apply H.
      simp feval. split... }
    rewrite H0. clear H0. rewrite (f_forall_elim t x). rewrite simpl_subst_impl.
    f_simpl. rewrite f_forall_one_point.
    2:{ simpl. rewrite not_elem_of_singleton. apply initial_var_of_ne. }
    rewrite fequiv_subst_non_free.
    2:{ destruct (decide (₀x ∈ formula_fvars <! A [x \ t] !>))... exfalso.
        apply fvars_subst_superset in e. apply elem_of_union in e. destruct e.
        - apply Hfree in H0. simpl in H0. discriminate.
        - pose proof (final_term_final t). apply H1 in H0. simpl in H0. discriminate. }
    reflexivity.
  Qed.

  Lemma r_alternation

  Lemma r_iteration w (I : formula) (v : variable) gcs :
    w : [inv, inv ∧ ¬ (gcomc_any_guard gcs)] ⊑ `PDo gcs`






Lemma assignment : forall pre post x E,
  pre ⇛ post[x \ E] ->
  <{ x : [pre, post] ⊑ x := E }>.
Proof.
  intros pre post w E H A Hfree. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

