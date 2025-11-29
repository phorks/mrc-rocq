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

  Lemma r_permute_frame w w' pre post `{FormulaFinal _ pre} :
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros. split; intros A Hfree.
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
  Lemma r_contract_frame w xs pre post `{FormulaFinal _ pre} :
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs] ] }>.
  Proof with auto.
    intros Hdisjoint A Hfree. simpl. f_simpl.
    rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist.
    2: { set_solver. }
    2: { intros x. intros. apply elem_of_union_list in H1 as (fvars&?&?).
         apply elem_of_list_to_set in H0. apply elem_of_list_fmap in H0 as (x'&?&?).
         apply elem_of_list_fmap in H1 as (t&?&?). apply elem_of_list_fmap in H4 as (y'&?&?).
         set_solver. }
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    f_simpl. rewrite f_subst_initials_final_formula... reflexivity.
  Qed.

  Lemma r_assignment w xs pre post ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ ⎡⇑₀ xs =* ⇑ₓ xs⎤ ∧ pre !> ⇛ <! post[[ ↑ₓ xs \ ⇑ₜ ts ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros Hlength Hnodup proviso A Hfinal. simpl. rewrite wp_asgn.
    assert (<! pre !> ≡ <! pre [_₀\w ++ xs] !>) as ->.
    { rewrite f_subst_initials_final_formula...  }
    rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials. rewrite <- f_foralllist_one_point...
    rewrite f_foralllist_app. rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite (f_foralllist_elim_as_ssubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    2:{ apply NoDup_fmap... apply as_var_inj. }
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite fmap_app. do 2 rewrite <- list_fmap_compose. reflexivity. }
    3: { rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_ssubst_impl.
    f_simpl. rewrite <- f_eqlist_app.
    erewrite eqlist_rewrite. Unshelve.
    4: { rewrite <- fmap_app. rewrite list_fmap_compose. reflexivity. }
    3: { rewrite <- fmap_app. reflexivity. }
    pose proof (@f_foralllist_one_point M
                  (initial_var_of <$> (w ++ xs)) ((TVar ∘ as_var <$> (w++xs)))) as ->...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula.
    2: { unfold formula_final. intros. apply fvars_ssubst_superset in H1.
         set_unfold. destruct H1.
         - apply Hfinal...
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
  intros pre post w E H A Hfree. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

