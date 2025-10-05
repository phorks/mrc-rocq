From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
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

Theorem subst_term_same : forall t x,
  subst_term t x x = t.
Proof with auto.
  assert (Lemma: forall args x,
    (forall arg : term, In arg args -> subst_term arg x x = arg) ->
    map (fun arg => subst_term arg x x) args = args).
  { intros. induction args; simpl...
    f_equal.
    - apply H. simpl...
    - apply IHargs. intros arg HIn. apply H. simpl. right... }
  intros t x. induction t; simpl...
  - destruct (String.eqb_spec x0 x)... f_equal...
  - destruct args.
    + simpl...
    + simpl. f_equal. f_equal.
      * apply H. simpl...
      * apply Lemma. intros arg HIn. apply H. simpl...
Qed.

Axiom exists_fequiv : forall (x y : string) A B,
  <[ A ]> === <[ B[y\x] ]> ->
  <[ exists x, A ]> === <[ exists y, B ]>.

Theorem subst_same : forall A x,
  <[ A[x\x] ]> === A.
Proof with auto.
  intros A x. induction A.
  - apply fequiv_when_eq. unfold formula_subst. simpl. destruct sf;
      simpl... 
    replace ((map (fun arg : term => subst_term arg x x) args)) 
      with args...
    induction args... simpl. f_equal.
    + symmetry. apply subst_term_same.
    + apply IHargs.
  - rewrite simpl_subst_not. rewrite IHA. reflexivity.
  - rewrite simpl_subst_and. rewrite IHA1. rewrite IHA2. 
    reflexivity.
  - rewrite simpl_subst_or. rewrite IHA1. rewrite IHA2. 
    reflexivity.
  - rewrite simpl_subst_implication. rewrite IHA1. rewrite IHA2. 
    reflexivity.
  - rewrite simpl_subst_iff. rewrite IHA1. rewrite IHA2. 
    reflexivity.
  - destruct (String.eqb_spec x0 x).
    + subst x0. rewrite simpl_subst_exists_same... reflexivity.
    + rewrite simpl_subst_exists_neq... 

(* Theorem subst_id_when_not_free : forall x A a, *)
(*   is_free_in x A = false -> *)
(*   <[ A[x\a] ]> === A. *)
(* Proof with auto. *)
(*   intros x A a H. induction A... *)
(*   - apply fequiv_when_eq. *)
(*     rewrite simpl_subst_simple_formula. *)
(*     destruct sf... simpl. symmetry. f_equal.  *)
(*     replace (map (fun arg : term => subst_term arg x a) args)  *)
(*       with args... induction args... simpl in H. *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. simpl. *)
(*     f_equal... symmetry. apply subst_term_id_when_not_in_term... *)
(*   - rewrite simpl_subst_not. simpl in H. *)
(*     rewrite IHA... reflexivity. *)
(*   - rewrite simpl_subst_and. simpl in H. *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. *)
(*     rewrite IHA1... rewrite IHA2... reflexivity. *)
(*   - rewrite simpl_subst_or. simpl in H. *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. *)
(*     rewrite IHA1... rewrite IHA2... reflexivity. *)
(*   - rewrite simpl_subst_implication. simpl in H. *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. *)
(*     rewrite IHA1... rewrite IHA2... reflexivity. *)
(*   - rewrite simpl_subst_iff. simpl in H. *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. *)
(*     rewrite IHA1... rewrite IHA2... reflexivity. *)
(*   - inversion H. destruct (String.eqb_spec x0 x). *)
(*     + rewrite e. rewrite simpl_subst_exists_same... reflexivity. *)
(*     + rewrite simpl_subst_exists_neq... *)
(*       assert (Hfresh:=(fresh_quantifier_spec x0 A a)). *)
(*       destruct Hfresh as [[Hfr1 Hfr2] | Hfresh]. *)
(*       * rewrite <- Hfr2.   *)
(*       rewrite H0. *)
(*   - simpl. f_equal. induction args... simpl in H.  *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. *)
(*     simpl. f_equal. *)
(*     + apply H0... simpl... *)
(*     + apply IHargs. *)
(*       * intros arg HIn Hap. apply H0... simpl... *)
(*       * simpl. apply H2. *)
(* Qed. *)


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
