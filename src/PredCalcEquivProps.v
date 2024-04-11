From Coq Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.
From MRC Require Import PredCalcEquiv.
From MRC Require Import PredCalcProps.
From MRC Require Import Tactics.

Open Scope general_fassertion_scope.

Lemma fequiv_when_eq : forall A B,
  A = B ->
  <[ A ]> === <[ B ]>.
Proof.
  intros A B Heq. subst. reflexivity.
Qed.

Theorem subst_id_when_not_free : forall x A a,
  is_free_in x A = false ->
  <[ A[x\a] ]> === A.
Proof with auto.
  intros x A a H. induction A...
  - apply fequiv_when_eq.
    rewrite simpl_subst_simple_formula.
    destruct sf... simpl. symmetry. f_equal. 
    replace (map (fun arg : term => subst_term arg x a) args) 
      with args... induction args... simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2]. simpl.
    f_equal... symmetry. apply subst_term_id_when_not_in_term...
  - rewrite simpl_subst_not. simpl in H.
    forward IHA... rewrite IHA.
   rewrite IHA...
  - apply fequiv_when_eq.
    rewrite simpl_subst_and. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - apply fequiv_when_eq.
    rewrite simpl_subst_or. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - apply fequiv_when_eq.
    rewrite simpl_subst_implication. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - apply fequiv_when_eq.
    rewrite simpl_subst_iff. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - simpl in H. destruct (String.eqb_spec x0 x).
    + rewrite simpl_subst_exists_same...
    + rewrite simpl_subst_exists_neq...

     
     
  - simpl. destruct (String.eqb_spec x0 x)... rewrite e in H.
    simpl in H. rewrite String.eqb_refl in H. discriminate H.
  - simpl. f_equal. induction args... simpl in H. 
    apply Bool.orb_false_iff in H as [H1 H2].
    simpl. f_equal.
    + apply H0... simpl...
    + apply IHargs.
      * intros arg HIn Hap. apply H0... simpl...
      * simpl. apply H2.
Qed.


(* Theorem subst_id_when_not_free : forall x A a,
  is_free_in x A = false ->
  <[ A[x\a] ]> = A.
Proof with auto. 
  intros x A a H. induction A...
  - rewrite simpl_subst_simple_formula.
    destruct sf... simpl. symmetry. f_equal. 
    replace (map (fun arg : term => subst_term arg x a) args) 
      with args... induction args... simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2]. simpl.
    f_equal... symmetry. apply subst_term_id_when_not_in_term...
  - rewrite simpl_subst_not. simpl in H. rewrite IHA...
  - rewrite simpl_subst_and. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - rewrite simpl_subst_or. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - rewrite simpl_subst_implication. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - rewrite simpl_subst_iff. simpl in H.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite IHA1... rewrite IHA2...
  - simpl in H. destruct (String.eqb_spec x0 x).
    + rewrite simpl_subst_exists_same...
    + rewrite simpl_subst_exists_neq...

     
     
  - simpl. destruct (String.eqb_spec x0 x)... rewrite e in H.
    simpl in H. rewrite String.eqb_refl in H. discriminate H.
  - simpl. f_equal. induction args... simpl in H. 
    apply Bool.orb_false_iff in H as [H1 H2].
    simpl. f_equal.
    + apply H0... simpl...
    + apply IHargs.
      * intros arg HIn Hap. apply H0... simpl...
      * simpl. apply H2.
Qed. *)