From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

Section refinement.
  Context {M : model}.
  Local Notation prog := (@prog M).
  Local Notation formula := (formula (value M)).
  Local Notation ni_formula := (@ni_formula M).

  Implicit Types A B C : formula.
  Implicit Types pre : ni_formula.
  (* Implicit Types w : list variable. *)

  Definition refines (p1 p2 : prog) :=
    ∀ A : ni_formula,
      (∀ x, x ∈ formula_fvars A → var_is_initial x = false) ->
      wp p1 A ⇛ (wp p2 A).

  Notation "x '⊑' y" := (refines x y)
                          (in custom prog at level 60,
                              x custom prog,
                              y custom prog at level 95).

  Lemma r_strengthen_post pre post post' w :
    post' ⇛ post ->
    <{ w : [pre, post] ⊑ w : [pre, post'] }>.
  Proof.
    intros Hent A Hinit. simpl. f_simpl. apply f_forall_ent. intros.
    f_simpl. assumption.
  Qed.

  Lemma r_weaken_pre pre pre' post w :
    pre ⇛ pre' ->
    <{ w : [pre, post] ⊑ w : [pre', post] }>.
  Proof.
    intros Hent A Hinit. simpl. f_simpl. assumption.
  Qed.

  Lemma r_assignment : forall pre post (x : ni_variable) t,
      <! `ni_var_i x` = x ∧ pre !> ⇛ post[x \ t] ->
      <{ x : [pre, post] ⊑ x := t }>.
  Proof with auto.
    intros pre post x t H A Hfree. simpl.
    assert ((ni_formula_formula pre) ≡ pre [x ₀ \ x]).
    { rewrite fequiv_subst_non_free... pose proof (ni_formula_no_initials pre).
      destruct (decide (x ₀ ∈ formula_fvars pre))... apply H0 in e. simpl in e. discriminate. }
    rewrite H0. clear H0.
    rewrite <- simpl_subst_and.
    rewrite <- (f_forall_one_point).
    2:{ simpl. rewrite not_elem_of_singleton. apply ni_var_i_ne_ni_var. }
    assert
      (<! `ni_var_i x` = x => (pre ∧ (∀ x ● post => A)) !> ⇛
                                <! `ni_var_i x` = x => (post [x \ t] ∧ (∀ x ● post => A)) !>).
    { intros σ ?. rewrite simpl_feval_fimpl in H0. rewrite simpl_feval_fimpl. intros.
      simp feval in *. apply H0 in H1 as H2. destruct H2 as []. split... apply H.
      simp feval. split... }
    rewrite H0. clear H0. rewrite (f_forall_elim t x). rewrite simpl_subst_impl.
    f_simpl. rewrite f_forall_one_point.
    2:{ simpl. rewrite not_elem_of_singleton. apply ni_var_i_ne_ni_var. }
    rewrite fequiv_subst_non_free.
    2:{ destruct (decide (x ₀ ∈ formula_fvars <! A [x \ t] !>))... exfalso.
        apply fvars_subst_superset in e. apply elem_of_union in e. destruct e.
        - apply Hfree in H0. simpl in H0. discriminate.
        - admit. }
    reflexivity.
  Admitted.

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

