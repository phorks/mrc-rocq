From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset.
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
  Local Notation prog := (@prog M).
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).
  Local Notation final_term := (final_term (value M)).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.
  (* Implicit Types ts : list term. *)

  Lemma r_strengthen_post w pre post post' `{FormulaFinal _ pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof.
  Admitted.
    (* intros Hent A Hinit. simpl. f_simpl. *)
    (* f_equiv. *)
    (* induction w. *)
    (* - simpl. unfold as_var_set. rewrite fin_sets.set_map_empty. unfold set_to_list. *)
    (*   rewrite fin_sets.set_fold_empty. simpl.  *)
    (* f_simpl. apply f_forall_ent. intros. *)
    (* f_simpl. assumption. *)
  (* Qed. *)

  Lemma r_weaken_pre w pre pre' post `{FormulaFinal _ pre} `{FormulaFinal _ pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A Hinit. simpl. f_simpl. assumption.
  Qed.

  (* Lemma r_assignment w pre post xs t `{FormulaFinal _ pre} `{TermListFinal _ ts} : *)
  (*     (* <! ⌜₀xs = x⌝ ∧ pre !> ⇛ <! post[x \ t] !> -> *) *)
  (*     <{ *w, *xs : [pre, post] }> ⊑ abort. *)
  Lemma r_assignment w pre post xs ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
      (* <! ⌜₀xs = x⌝ ∧ pre !> ⇛ <! post[x \ t] !> -> *)
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *ts }>.
  Proof with auto.
    intros A Hfree. simpl.
    assert (<! pre !> ≡ <! pre [_₀\list_to_set (w ++ xs)] !>).
    { unfold subst_initials. admit. }
    rewrite H1. simpl.
    simpl. f_simpl.
    intros pre post x t H A Hfree. simpl.
    assert (<! %pre !> ≡ pre [₀ x \ x]).
    { rewrite fequiv_subst_non_free... pose proof (final_formula_final pre).
      destruct (decide (₀x ∈ formula_fvars pre))... apply H0 in e. simpl in e. discriminate. }
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

