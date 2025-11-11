From Stdlib Require Import Lists.List. Import ListNotations.
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
    ∀ A,
      (∀ x, x ∈ formula_fvars A → var_is_initial x = false) ->
      wp p1 A ⇛ (wp p2 A).

  Notation "x '⊑' y" := (refines x y)
                          (in custom prog at level 60,
                              x custom prog,
                              y custom prog at level 95)
      : mrc_scope.

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

  Lemma assignment : forall pre post x E,
      pre ⇛ post[x \ E] ->
      <{ x : [pre, post] ⊑ x := E }>.
  Proof.
    intros pre post w E H A Hfree. simpl.
    assert ((ni_formula_formula pre) ≡ pre [w \ (var_non_initial w)]) by admit.
    rewrite H0.
    rewrite <- simpl_subst_and.
    rewrite <- (f_forall_one_point).
    2:{ admit. }
    2: {  }
    -
      simpl.
  Qed.





Lemma assignment : forall pre post x E,
  pre ⇛ post[x \ E] ->
  <{ x : [pre, post] ⊑ x := E }>.
Proof.
  intros pre post w E H A Hfree. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

