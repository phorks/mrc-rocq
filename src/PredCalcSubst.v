From Stdlib Require Import Strings.String.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import gmap fin_maps.
From MRC Require Import Options.
From MRC Require Import Model.
From MRC Require Import Tactics.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From MRC Require Import PredCalcEquiv.

Section subst.
  Context {M : model}.

  Implicit Types t : @term (value M).
  Implicit Types sf : @simple_formula (value M).
  Implicit Types A B C : @formula (value M).
  Implicit Types v : value M.

  Lemma higher_qrank__subst_eq A : ∀ x a r',
    quantifier_rank A <= r' →
    subst_formula_aux (quantifier_rank A) A x a =
      subst_formula_aux r' A x a.
  Proof with auto.
    induction A using formula_rank_ind.
    destruct A; intros x0 a r' Hrank; subst.
    - destruct r'...
    - simpl. destruct (quantifier_rank A) eqn:HrA; destruct r' eqn:Hr';
        simpl in *; subst...
      + fold_qrank_subst 0 A x0 a. fold_qrank_subst (S n) A x0 a.
        f_equal. rewrite <- HrA. apply H with (rank A); lia...
      + lia.
      + fold_qrank_subst (S n) A x0 a.
        fold_qrank_subst (S n0) A x0 a.
        f_equal. rewrite <- HrA. apply H with (rank A); lia.
    - simpl.
      assert (HMax :=
                (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
      + destruct (quantifier_rank A2) eqn:HrA; destruct r' eqn:Hr';
          simpl in *...
        * lia.
        * fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a.
          fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
          f_equal.
          -- assert (quantifier_rank A1 = 0) by lia. rewrite <- H0.
             symmetry. apply H with (rank A1); lia.
          -- rewrite <- HrA. apply H with (rank A2); lia.
        * fold_qrank_subst (S n0) A2 x0 a.
          fold_qrank_subst (S n0) A1 x0 a.
          fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a. f_equal.
          -- assert (Heq1: subst_formula_aux (quantifier_rank A1) A1 x0 a =
                             subst_formula_aux (S n) A1 x0 a).
             { apply H with (rank A1); lia. }
             assert (Heq2: subst_formula_aux (quantifier_rank A1) A1 x0 a =
                             subst_formula_aux (S n0) A1 x0 a).
             { apply H with (rank A1); lia. }
             rewrite <- Heq1...
          -- rewrite <- HrA. apply H with (rank A2); lia.
      + destruct (quantifier_rank A1) eqn:HrA; destruct r' eqn:Hr';
          simpl in *...
        * fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a.
          fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
          f_equal.
          -- rewrite <- HrA. apply H with (rank A1); lia.
          -- rewrite <- H2. apply H with (rank A2); lia.
        * lia.
        * fold_qrank_subst (S n0) A2 x0 a.
          fold_qrank_subst (S n0) A1 x0 a.
          fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a. f_equal.
          -- rewrite <- HrA. apply H with (rank A1); lia.
          -- assert (Heq1: subst_formula_aux (quantifier_rank A2) A2 x0 a =
                             subst_formula_aux (S n) A2 x0 a).
             { apply H with (rank A2); lia. }
             assert (Heq2: subst_formula_aux (quantifier_rank A2) A2 x0 a =
                             subst_formula_aux (S n0) A2 x0 a).
             { apply H with (rank A2); lia. }
             rewrite <- Heq1...
    - simpl.
      assert (HMax :=
                (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]]; try lia; rewrite H2 in *.
      + destruct (quantifier_rank A2) eqn:HrA; destruct r' eqn:Hr';
          simpl in *...
        * lia.
        * fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a.
          fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
          f_equal.
          -- assert (quantifier_rank A1 = 0) by lia. rewrite <- H0.
             symmetry. apply H with (rank A1); lia.
          -- rewrite <- HrA. apply H with (rank A2); lia.
        * fold_qrank_subst (S n0) A2 x0 a.
          fold_qrank_subst (S n0) A1 x0 a.
          fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a. f_equal.
          -- assert (Heq1: subst_formula_aux (quantifier_rank A1) A1 x0 a =
                             subst_formula_aux (S n) A1 x0 a).
             { apply H with (rank A1); lia. }
             assert (Heq2: subst_formula_aux (quantifier_rank A1) A1 x0 a =
                             subst_formula_aux (S n0) A1 x0 a).
             { apply H with (rank A1); lia. }
             rewrite <- Heq1...
          -- rewrite <- HrA. apply H with (rank A2); lia.
      + destruct (quantifier_rank A1) eqn:HrA; destruct r' eqn:Hr';
          simpl in *...
        * fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a.
          fold_qrank_subst 0 A2 x0 a. fold_qrank_subst 0 A1 x0 a.
          f_equal.
          -- rewrite <- HrA. apply H with (rank A1); lia.
          -- rewrite <- H2. apply H with (rank A2); lia.
        * lia.
        * fold_qrank_subst (S n0) A2 x0 a.
          fold_qrank_subst (S n0) A1 x0 a.
          fold_qrank_subst (S n) A2 x0 a.
          fold_qrank_subst (S n) A1 x0 a. f_equal.
          -- rewrite <- HrA. apply H with (rank A1); lia.
          -- assert (Heq1: subst_formula_aux (quantifier_rank A2) A2 x0 a =
                             subst_formula_aux (S n) A2 x0 a).
             { apply H with (rank A2); lia. }
             assert (Heq2: subst_formula_aux (quantifier_rank A2) A2 x0 a =
                             subst_formula_aux (S n0) A2 x0 a).
             { apply H with (rank A2); lia. }
             rewrite <- Heq1...
    - destruct r'; simpl in *.
      + lia.
      + fold_qrank_subst_fresh (S r') A x x0 a.
        fold_qrank_subst_fresh (S (quantifier_rank A)) A x x0 a.
        f_equal.
        destruct (quant_subst_skip_cond x A x0); try lia...
        f_equal.
        assert (subst_formula_aux (S (quantifier_rank A)) A x (fresh_var x (quant_subst_fvars x A x0 a))
                = subst_formula_aux (quantifier_rank A) A x (fresh_var x (quant_subst_fvars x A x0 a))).
        {
          symmetry. apply H with (m:=rank A); try lia...
        } rewrite H0. clear H0.
        assert (subst_formula_aux (S r') A x (fresh_var x (quant_subst_fvars x A x0 a))
                = subst_formula_aux (quantifier_rank A) A x (fresh_var x (quant_subst_fvars x A x0 a))).
        {
          symmetry. apply H with (m:=rank A); try lia...
        } rewrite H0. clear H0.
        remember (subst_formula_aux (quantifier_rank A) A x (fresh_var x (quant_subst_fvars x A x0 a)))
          as inner.
        pose proof (HsameInnerA := subst_preserves_shape_aux A x (fresh_var x (quant_subst_fvars x A x0 a)) (quantifier_rank A)).
        deduce_rank_eq HsameInnerA.
        replace (quantifier_rank A) with (quantifier_rank inner).
        * apply H with (m:=rank A); try rewrite Heqinner; lia...
        * rewrite Heqinner...
  Qed.

  Lemma simpl_subst_sf sf x a :
    subst_formula (FSimple sf) x a =
      FSimple (subst_sf sf x a).
  Proof with auto. unfold subst_formula. simpl. reflexivity. Qed.

  Lemma simpl_subst_not A x a :
    <! (~ A)[x \ a] !> = <! ~ (A[x \ a]) !>.
  Proof with auto.
    unfold subst_formula.
    replace (quantifier_rank <! ~A !>) with (quantifier_rank A) by reflexivity.
    destruct (quantifier_rank A); reflexivity.
  Qed.

  Lemma simpl_subst_and A B x a :
    <! (A ∧ B)[x \ a] !> = <! (A[x \ a]) ∧ (B[x \ a])!>.
  Proof with auto.
    unfold subst_formula.
    destruct (Nat.max_spec (quantifier_rank A) (quantifier_rank B)) as [[H1 H2] | [H1 H2]].
    - replace (quantifier_rank <! A ∧ B !>) with (quantifier_rank B) by (simpl; lia).
      destruct (quantifier_rank B) eqn:E; try lia... simpl. fold_qrank_subst (S n) B x a.
      fold_qrank_subst (S n) A x a. f_equal. symmetry. apply higher_qrank__subst_eq. lia.
    - replace (quantifier_rank <! A ∧ B !>) with (quantifier_rank A) by (simpl; lia).
      destruct (quantifier_rank A) eqn:E.
      + inversion H1. rewrite H0. simpl...
      + simpl. fold_qrank_subst (S n) B x a. fold_qrank_subst (S n) A x a. f_equal.
        symmetry. apply higher_qrank__subst_eq. lia.
  Qed.

  Lemma simpl_subst_or  A B x a :
    <! (A ∨ B)[x \ a] !> = <! (A[x \ a]) ∨ (B[x \ a])!>.
  Proof with auto.
    unfold subst_formula.
    destruct (Nat.max_spec (quantifier_rank A) (quantifier_rank B)) as [[H1 H2] | [H1 H2]].
    - replace (quantifier_rank <! A ∨ B !>) with (quantifier_rank B) by (simpl; lia).
      destruct (quantifier_rank B) eqn:E; try lia... simpl. fold_qrank_subst (S n) B x a.
      fold_qrank_subst (S n) A x a. f_equal.
      symmetry. apply higher_qrank__subst_eq. lia.
    - replace (quantifier_rank <! A ∨ B !>) with (quantifier_rank A) by (simpl; lia).
      destruct (quantifier_rank A) eqn:E.
      + inversion H1. rewrite H0. simpl...
      + simpl. fold_qrank_subst (S n) B x a. fold_qrank_subst (S n) A x a. f_equal.
        symmetry. apply higher_qrank__subst_eq. lia.
  Qed.

  Lemma simpl_subst_impl A B x a :
    <! (A => B)[x \ a] !> = <! (A[x \ a]) => (B[x \ a])!>.
  Proof with auto.
    unfold FImpl. rewrite simpl_subst_or. rewrite simpl_subst_not...
  Qed.

  Lemma simpl_subst_iff A B x a :
    <! (A <=> B)[x \ a] !> = <! (A[x \ a]) <=> (B[x \ a])!>.
  Proof with auto.
    intros. unfold FIff. rewrite simpl_subst_and. do 2 rewrite simpl_subst_impl...
  Qed.

  Lemma simpl_subst_exists_skip x y A a :
    x = y ∨ x ∉ formula_fvars A →
    <! (exists y, A)[x\a] !> = <! exists y, A !>.
  Proof with auto.
    intros Heq. unfold subst_formula. simpl. destruct (quant_subst_skip_cond y A x)...
    destruct Heq; contradiction.
  Qed.

  Lemma simpl_subst_exists_propagate x y A a :
    x ≠ y →
    x ∈ formula_fvars A →
    let y' := fresh_var y (quant_subst_fvars y A x a) in
    <! (exists y, A)[x\a] !> = <! (exists y', A[y\y'][x\a]) !>.
  Proof.
    intros Hneq Hfree. simpl. unfold subst_formula. simpl.
    destruct (quant_subst_skip_cond y A x)...
    1: { destruct H; contradiction. } f_equal.
    fold_qrank_subst_fresh (S (quantifier_rank A)) A y x a.
    f_equal.
    - assert (H:=subst_preserves_shape_aux A y
                   (fresh_var y (quant_subst_fvars y A x a)) (quantifier_rank A)).
      deduce_rank_eq H. lia.
    - symmetry. apply higher_qrank__subst_eq. lia.
  Qed.

  Lemma simpl_subst_forall_skip x y A a :
    x = y ∨ x ∉ formula_fvars A →
    <! (forall y, A)[x\a] !> = <! forall y, A !>.
  Proof with auto.
    intros Heq. unfold FForall. rewrite simpl_subst_not. rewrite simpl_subst_exists_skip...
  Qed.

  Lemma simpl_subst_forall_propagate x y A a :
    x ≠ y →
    x ∈ formula_fvars A →
    let y' := fresh_var y (quant_subst_fvars y A x a) in
    <! (forall y, A)[x\a] !> = <! (forall y', A[y\y'][x\a]) !>.
  Proof with auto.
    intros Hneq Hfree. unfold FForall. rewrite simpl_subst_not.
    rewrite simpl_subst_exists_propagate... do 2 rewrite simpl_subst_not...
  Qed.

  Lemma subst_formula_ind {x t} : ∀ P,
      (∀ sf, P (FSimple $ subst_sf sf x t) (FSimple sf)) →
      (∀ A, P <! A[x \ t] !> A → P <! ~ (A[x \ t]) !> <! ~ A !>) →
      (∀ A1 A2, P <! A1[x \ t] !> A1 → P <! A2[x \ t] !> A2 → P <! A1[x \ t] ∧ A2[x \ t] !> <! A1 ∧ A2 !>) →
      (∀ A1 A2, P <! A1[x \ t] !> A1 → P <! A2[x \ t] !> A2 → P <! A1[x \ t] ∨ A2[x \ t] !> <! A1 ∨ A2 !>) →
      (∀ y A, (∀ B, shape_eq B A = true → P <! B[x \ t] !> B) →
              (x = y ∨ x ∉ formula_fvars A → P <! exists y, A !> <! exists y, A !>)) →
      (∀ y A, (∀ B, shape_eq B A = true → P <! B[x \ t] !> B) →
              (x ≠ y → x ∈ formula_fvars A →
               let y' := fresh_var y (quant_subst_fvars y A x t) in
               P <! exists y', A[y \ y'][x \ t] !> <! exists y, A !>)) →
      ∀ A, P <! A[x \ t] !> A.
  Proof with auto.
    simpl.
    intros P Hsf Hnot Hand Hor Hexists1 Hexists2 A. induction A using formula_ind.
    - apply Hsf.
    - rewrite simpl_subst_not. apply Hnot...
    - rewrite simpl_subst_and. apply Hand...
    - rewrite simpl_subst_or. apply Hor...
    - rename x0 into y. destruct (quant_subst_skip_cond y A x).
      + rewrite simpl_subst_exists_skip...
      + rewrite simpl_subst_exists_propagate; try contradiction...
  Qed.

  Lemma subst_term_diag : forall t x,
      subst_term t x x = t.
  Proof with auto.
    intros t x. induction t using term_ind; simpl...
    - destruct (decide (x0 = x))... inversion e...
    - f_equal. induction args; simpl... f_equal.
      * apply H. simpl. left...
      * apply IHargs. intros. apply H. simpl. right...
  Qed.

  Lemma subst_sf_diag : forall sf x,
      subst_sf sf x x = sf.
  Proof with auto.
    intros sf x. destruct sf...
    - simpl... f_equal; apply subst_term_diag.
    - simpl. f_equal. induction args... rewrite map_cons. f_equal; auto; apply subst_term_diag.
  Qed.

(* Hint Resolve simpl_subst_sf : core. *)
(* Hint Resolve simpl_subst_not : core. *)
(* Hint Rewrite simpl_subst_and : core. *)
(* Hint Rewrite simpl_subst_or : core. *)
(* Hint Rewrite simpl_subst_impl : core. *)
(* Hint Rewrite simpl_subst_iff : core. *)
(* Hint Rewrite subst_term_diag : core. *)
(* Hint Rewrite subst_sf_diag : core. *)

  Lemma subst_term_non_free_eq t x t' :
    x ∉ term_fvars t →
    subst_term t x t' = t.
  Proof with auto.
    intros. induction t using term_ind; simpl...
    - simpl in H. destruct (decide (x0 = x))... apply not_elem_of_singleton in H. symmetry in e.
      contradiction.
    - simpl in H. f_equal. induction args... rewrite map_cons. simpl in H.
      apply not_elem_of_union in H as [H1 H2]. f_equal.
      * apply H0... simpl. left...
      * apply IHargs... intros. apply H0... simpl. right...
  Qed.

  Lemma subst_sf_non_free_eq sf x t :
    x ∉ sf_fvars sf →
    subst_sf sf x t = sf.
  Proof with auto.
    intros. destruct sf; simpl; try reflexivity.
    - simpl in H. apply not_elem_of_union in H as [? ?]. f_equal; apply subst_term_non_free_eq...
    - f_equal. simpl in H. induction args... simpl in *. apply not_elem_of_union in H as [? ?].
      f_equal.
      + simpl in H. apply subst_term_non_free_eq...
      + apply IHargs...
  Qed.

(* Lemma feval_exists_empty M σ1 σ2 x y τ A B b : *)
(*   value_ty_is_empty τ → *)
(*   feval M σ1 <! exists x : τ, A !> b ↔ feval M σ2 <! exists y : τ, B !> b. *)
(* Proof. *)
(*   intros. split; inversion 1; subst. *)
(*   - destruct H5 as [v [Hv _]]. apply H in Hv as []. *)
(*   - constructor. intros. apply H in H1 as []. *)
(*   - destruct H5 as [v [Hv _]]. apply H in Hv as []. *)
(*   - constructor. intros. apply H in H1 as []. *)
(* Qed. *)

(* Lemma fequiv_exists_empty_subst y τ A x t : *)
(*   value_ty_is_empty τ → *)
(*   <! (exists y : τ, A) [x \ t] !> ≡ <! exists y : τ, A !>. *)
(* Proof with auto. *)
(*   intros H M σ b. split; intros. *)
(*   - destruct (quant_subst_skip_cond y A x). *)
(*     + rewrite simpl_subst_exists_skip in H0... *)
(*     + rewrite simpl_subst_exists_propagate in H0... rewrite feval_exists_empty... *)
(*       apply H0. *)
(*   - destruct (quant_subst_skip_cond y A x). *)
(*     + rewrite simpl_subst_exists_skip... *)
(*     + rewrite simpl_subst_exists_propagate... rewrite feval_exists_empty... *)
(*       apply H0. *)
(* Qed. *)


  Lemma fequiv_subst_non_free A x t :
    x ∉ formula_fvars A →
    A[x \ t] ≡ A.
  Proof with auto.
    apply subst_formula_ind with (P:=λ A B, x ∉ formula_fvars B → A ≡ B); intros.
    - rewrite subst_sf_non_free_eq...
    - f_equiv...
    - simpl in H1. apply not_elem_of_union in H1 as [? ?].
      f_equiv; [apply H|apply H0]...
    - simpl in H1. apply not_elem_of_union in H1 as [? ?].
      f_equiv; [apply H|apply H0]...
    - reflexivity.
    - simpl in H2. apply not_elem_of_difference in H2. rewrite elem_of_singleton in H2.
      destruct H2; subst; contradiction.
  Qed.

  Lemma free_var_subst_fvars_subseteq t x t' :
    x ∈ term_fvars t →
    term_fvars t' ⊆ term_fvars (subst_term t x t').
  Proof with auto.
    intros. induction t; simpl in *.
    - apply elem_of_empty in H as [].
    - apply elem_of_singleton in H. subst.  destruct (decide (x0 = x0)); try contradiction.
      reflexivity.
    - intros a H3. apply elem_of_union_list in H as (x_arg_fvars&H1&H2).
      apply elem_of_list_fmap in H1 as (x_arg&->&H1). apply elem_of_list_In in H1 as H1'.
      forward (H0 x_arg)... forward H0... forward (H0 a)...
      apply elem_of_union_list. exists (term_fvars (subst_term x_arg x t')). split...
      clear H0 H3 a. apply elem_of_list_fmap. eexists. split; [reflexivity|].
      apply elem_of_list_fmap. eexists. split; [reflexivity|]...
  Qed.

  Lemma subst_term_free_fvars t x t' :
    x ∈ term_fvars t →
    term_fvars (subst_term t x t') = (term_fvars t ∖ {[x]}) ∪ term_fvars t'.
  Proof with auto.
    intros. apply leibniz_equiv. induction t.
    - simpl in H. apply elem_of_empty in H as [].
    - simpl in *. apply elem_of_singleton in H. subst.
      destruct (decide (x0 = x0)); try contradiction. rewrite difference_diag.
      rewrite union_empty_l_L. reflexivity.
    - simpl in *.
      apply elem_of_union_list in H as (x_arg_fvars&H1&H2).
      apply elem_of_list_fmap in H1 as (x_arg&->&H1). intros a. split; intros H.
      + apply elem_of_union_list in H as (a_arg_fvars&H3&H4).
        apply elem_of_list_fmap in H3 as (a_fvars&->&H3).
        apply elem_of_list_fmap in H3 as (a_arg&->&H3).
        destruct (decide (x ∈ term_fvars a_arg)).
        * forward (H0 a_arg) by ((apply elem_of_list_In in H3); auto)...
          forward H0... apply elem_of_union.
          rewrite H0 in H4. apply elem_of_union in H4 as [?|?]... left.
          apply elem_of_difference in H as [? ?]. apply elem_of_difference. split...
          apply elem_of_union_list. exists (term_fvars a_arg). split...
          apply elem_of_list_fmap. exists a_arg. split...
        * clear H0. rewrite subst_term_non_free_eq in H4... apply elem_of_union.
          destruct (decide (a = x)); [subst; contradiction |].
          left. apply elem_of_difference. split.
          -- apply elem_of_union_list. exists (term_fvars a_arg).
             split... apply elem_of_list_fmap. exists a_arg. split...
          -- apply not_elem_of_singleton...
      + apply elem_of_union in H. destruct H.
        * apply elem_of_difference in H as [H3 H4]. apply not_elem_of_singleton in H4.
          apply elem_of_union_list in H3 as (a_arg_fvars&?&?).
          apply elem_of_list_fmap in H as (a_arg&->&?).
          apply elem_of_union_list. apply elem_of_list_In in H as H'.
          forward (H0 a_arg) by ((apply elem_of_list_In in H1); auto).
          exists (term_fvars (subst_term a_arg x t')). rewrite elem_of_list_fmap.
          destruct (decide (x ∈ term_fvars a_arg)).
          -- forward H0... rewrite H0. split.
             ++ eexists. split; [reflexivity|]. apply elem_of_list_fmap.
                eexists. split; [reflexivity|]...
             ++ apply elem_of_union. left. apply elem_of_difference.
                rewrite not_elem_of_singleton. split...
          -- rewrite subst_term_non_free_eq... split... eexists. split; [reflexivity|].
             apply elem_of_list_fmap. exists a_arg. rewrite subst_term_non_free_eq...
        * apply elem_of_union_list. exists (term_fvars (subst_term x_arg x t')).
          split...
          -- apply elem_of_list_fmap. eexists. split; [reflexivity|]. apply elem_of_list_fmap.
             eexists. split; [reflexivity|]...
          -- apply free_var_subst_fvars_subseteq...
  Qed.

  Lemma subst_sf_free_fvars sf x t' :
    x ∈ sf_fvars sf →
    sf_fvars (subst_sf sf x t') = (sf_fvars sf ∖ {[x]}) ∪ term_fvars t'.
    intros. destruct sf.
    Proof with auto.
      - simpl in H. apply elem_of_empty in H as [].
      - simpl in H. apply elem_of_empty in H as [].
      - simpl in *. apply elem_of_union in H. destruct H.
        + rewrite subst_term_free_fvars... destruct (decide (x ∈ term_fvars t2)).
          * rewrite subst_term_free_fvars... set_solver.
          * rewrite subst_term_non_free_eq... set_solver.
        + rewrite (subst_term_free_fvars t2)... destruct (decide (x ∈ term_fvars t1)).
          * rewrite subst_term_free_fvars... set_solver.
          * rewrite subst_term_non_free_eq... set_solver.
      - simpl in *. apply leibniz_equiv. intros a.
        apply elem_of_union_list in H as (x_arg_fvars&H1&H2).
        apply elem_of_list_fmap in H1 as (x_arg&->&H1). split; intros H.
        + apply elem_of_union_list in H as (a_arg_fvars&H3&H4).
          apply elem_of_list_fmap in H3 as (a_fvars&->&H3).
          apply elem_of_list_fmap in H3 as (a_arg&->&H3).
          destruct (decide (x ∈ term_fvars a_arg)).
          * apply elem_of_union.
            rewrite subst_term_free_fvars in H4... apply elem_of_union in H4 as [?|?]... left.
            apply elem_of_difference in H as [? ?]. apply elem_of_difference. split...
            apply elem_of_union_list. exists (term_fvars a_arg). split...
            apply elem_of_list_fmap. exists a_arg. split...
          * rewrite subst_term_non_free_eq in H4... apply elem_of_union.
            destruct (decide (a = x)); [subst; contradiction|].
            left. apply elem_of_difference. split.
            -- apply elem_of_union_list. exists (term_fvars a_arg).
               split... apply elem_of_list_fmap. exists a_arg. split...
            -- apply not_elem_of_singleton...
        + apply elem_of_union in H. destruct H.
          * apply elem_of_difference in H as [H3 H4]. apply not_elem_of_singleton in H4.
            apply elem_of_union_list in H3 as (a_arg_fvars&?&?).
            apply elem_of_list_fmap in H as (a_arg&->&?).
            apply elem_of_union_list. apply elem_of_list_In in H as H'.
            exists (term_fvars (subst_term a_arg x t')). rewrite elem_of_list_fmap.
            destruct (decide (x ∈ term_fvars a_arg)).
            -- split.
               ++ eexists. split; [reflexivity|]. apply elem_of_list_fmap.
                  eexists. split; [reflexivity|]...
               ++ rewrite subst_term_free_fvars... apply elem_of_union. left. apply elem_of_difference.
                  rewrite not_elem_of_singleton. split...
            -- rewrite subst_term_non_free_eq... split... eexists. split; [reflexivity|].
               apply elem_of_list_fmap. exists a_arg. rewrite subst_term_non_free_eq...
          * apply elem_of_union_list. exists (term_fvars (subst_term x_arg x t')).
            split...
            -- apply elem_of_list_fmap. eexists. split; [reflexivity|]. apply elem_of_list_fmap.
               eexists. split; [reflexivity|]...
            -- apply free_var_subst_fvars_subseteq...
    Qed.

    Lemma fvars_subst_non_free A x t :
      x ∉ formula_fvars A →
      formula_fvars (A[x \ t]) = formula_fvars A.
    Proof with auto.
      apply subst_formula_ind with
        (P:=λ A B, x ∉ formula_fvars B → formula_fvars A = formula_fvars B); intros; simpl.
      - rewrite subst_sf_non_free_eq...
      - simpl...
      - simpl in H. simpl in H1. apply not_elem_of_union in H1 as [? ?]. simpl. set_solver.
      - simpl in H. simpl in H1. apply not_elem_of_union in H1 as [? ?]. simpl. set_solver.
      - reflexivity.
      - simpl in H2. apply not_elem_of_difference in H2. rewrite elem_of_singleton in H2.
        destruct H2; subst; contradiction.
    Qed.

    Lemma fvars_subst_free : ∀ A x t,
        x ∈ formula_fvars A →
        formula_fvars (A[x \ t]) = (formula_fvars A ∖ {[x]}) ∪ term_fvars t.
    Proof with auto.
      intros.
      generalize dependent t. generalize dependent x.
      induction A; simpl; intros.
      - rewrite subst_sf_free_fvars...
      - rewrite simpl_subst_not. simpl. rewrite IHA...
      - rewrite simpl_subst_and. simpl. apply elem_of_union in H as [|].
        + rewrite IHA1... destruct (decide (x ∈ formula_fvars A2)).
          * rewrite IHA2... set_solver.
          * rewrite fvars_subst_non_free... set_solver.
        + rewrite IHA2... destruct (decide (x ∈ formula_fvars A1)).
          * rewrite IHA1... set_solver.
          * rewrite fvars_subst_non_free... set_solver.
      - rewrite simpl_subst_or. simpl. apply elem_of_union in H as [|].
        + rewrite IHA1... destruct (decide (x ∈ formula_fvars A2)).
          * rewrite IHA2... set_solver.
          * rewrite fvars_subst_non_free... set_solver.
        + rewrite IHA2... destruct (decide (x ∈ formula_fvars A1)).
          * rewrite IHA1... set_solver.
          * rewrite fvars_subst_non_free... set_solver.
      - apply elem_of_difference in H0 as [? ?]. apply not_elem_of_singleton in H1.
        destruct (quant_subst_skip_cond x A x0).
        + destruct H2 as [|]; subst; contradiction.
        + rewrite simpl_subst_exists_propagate... simpl. rewrite H...
          * generalize_fresh_var x A x0 t as x'. destruct (decide (x ∈ formula_fvars A)).
            -- rewrite H... set_solver.
            -- rewrite fvars_subst_non_free... set_solver.
          * destruct (decide (x ∈ formula_fvars A)).
            -- rewrite H... apply elem_of_union. left. apply elem_of_difference. split...
               apply not_elem_of_singleton...
            -- rewrite fvars_subst_non_free...
    Qed.

    Lemma fvars_subst_diag A x :
      formula_fvars (A[x \ x]) = formula_fvars A.
    Proof with auto.
      destruct (decide (x ∈ formula_fvars A)) eqn:H.
      - rewrite fvars_subst_free... rewrite union_comm_L. simpl.
        rewrite <- union_difference_singleton_L...
      - apply fvars_subst_non_free...
    Qed.

    Lemma fvars_subst_superset A x t : formula_fvars (A[x \ t]) ⊆ formula_fvars A ∪ term_fvars t.
    Proof with auto.
      destruct (decide (x ∈ formula_fvars A)).
      - rewrite fvars_subst_free... apply union_mono_r. apply subseteq_difference_l...
      - rewrite fvars_subst_non_free... apply union_subseteq_l.
    Qed.

    Lemma subst_term_commute t x1 t1 x2 t2 :
      x1 ≠ x2 →
      x1 ∉ term_fvars t2 →
      x2 ∉ term_fvars t1 →
      subst_term (subst_term t x1 t1) x2 t2 = subst_term (subst_term t x2 t2) x1 t1.
    Proof with auto.
      intros Hneq H1 H2. induction t using term_ind; simpl...
      - destruct (decide (x = x1)); destruct (decide (x = x2)); subst.
        + contradiction.
        + simpl. destruct (decide (x1 = x1)); try contradiction. apply subst_term_non_free_eq...
        + simpl. destruct (decide (x2 = x2)); try contradiction. symmetry. apply subst_term_non_free_eq...
        + simpl. destruct (decide (x = x2)); destruct (decide (x = x1)); try contradiction...
      - f_equal. induction args; simpl... f_equal.
        + apply H. left...
        + apply IHargs. intros. apply H. right...
    Qed.

    Lemma subst_sf_commute sf x1 t1 x2 t2 :
      x1 ≠ x2 →
      x1 ∉ term_fvars t2 →
      x2 ∉ term_fvars t1 →
      subst_sf (subst_sf sf x1 t1) x2 t2 =
        subst_sf (subst_sf sf x2 t2) x1 t1.
    Proof with auto.
      intros. destruct sf; simpl...
      - f_equal; auto using subst_term_commute.
      - f_equal. induction args... repeat rewrite map_cons. f_equal... apply subst_term_commute...
    Qed.

    Lemma teval_delete_state_var x {σ t v} :
      x ∉ term_fvars t →
      teval σ t v ↔ teval (delete x σ) t v.
    Proof with auto.
      intros Hfree. split.
      - intros H. revert Hfree. assert (H':=H). revert H H'.
        generalize dependent v. generalize dependent t.
        apply (teval_ind_mut _
                 (λ t v _, teval σ t v → x ∉ term_fvars t → teval (delete x σ) t v)
                 (λ args vargs _, forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
                                  teval_args σ args vargs → teval_args (delete x σ) args vargs)).
        + intros. constructor.
        + intros x' v H H' Hfree. constructor. simpl in Hfree.
          destruct (decide (x' = x)); subst; simpl.
          * apply not_elem_of_singleton in Hfree. contradiction.
          * pose proof (@lookup_total_delete_ne _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ)...
        + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_App with vargs...
          apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
          apply not_elem_of_union in Hfree as [H1 H2].
          simpl. apply andb_prop_intro. split...
        + constructor.
        + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
          apply andb_prop_elim in Hfree as [Hfree Hfrees]. apply bool_decide_unpack in Hfree.
          constructor.
          * apply IH...
          * apply IHargs...
      - intros H. revert Hfree. assert (H':=H). revert H H'.
        generalize dependent v. generalize dependent t.
        apply (teval_ind_mut _
                 (λ t v _, teval (delete x σ) t v → x ∉ term_fvars t → teval σ t v)
                 (λ args vargs _, forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
                                  teval_args (delete x σ) args vargs → teval_args σ args vargs)).
        + intros. constructor.
        + intros x' v H H' Hfree. constructor. simpl in Hfree.
          destruct (decide (x' = x)); subst; simpl.
          * apply not_elem_of_singleton in Hfree. contradiction.
          * pose proof (@lookup_total_delete_ne _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ).
            rewrite H...
        + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_App with vargs...
          apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
          apply not_elem_of_union in Hfree as [? ?].
          simpl. apply andb_prop_intro. split...
        + constructor.
        + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
          apply andb_prop_elim in Hfree as [Hfree Hfrees]. apply bool_decide_unpack in Hfree.
          constructor.
          * apply IH...
          * apply IHargs...
    Qed.

    Lemma teval_args_delete_state_var {σ args vargs} x :
      forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
      teval_args σ args vargs ↔
        @teval_args M (delete x σ) args vargs.
    Proof with auto.
      intros Hfree. split.
      - induction 1.
        + constructor.
        + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
          constructor.
          * apply teval_delete_state_var...
          * apply IHteval_args...
      - induction 1.
        + constructor.
        + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
          constructor.
          * apply teval_delete_state_var in H...
          * apply IHteval_args...
    Qed.

    Lemma sfeval_delete_state_var {σ sf} x :
      x ∉ sf_fvars sf → sfeval σ sf ↔ sfeval (delete x σ) sf.
    Proof with auto.
      intros Hfree. destruct sf; simpl.
      - split; inversion 1; subst; constructor.
      - split; inversion 1; subst; constructor.
      - simpl in Hfree. apply not_elem_of_union in Hfree as [? ?].
        split; intros (v&?&?); exists v.
        + split; apply teval_delete_state_var...
        + apply teval_delete_state_var in H1, H2...
      - simpl in Hfree. split; intros (vargs&?&?); exists vargs.
        + split... apply teval_args_delete_state_var...
          clear H0 H vargs H symbol. induction args... simpl in *.
          apply not_elem_of_union in Hfree as [? ?].
          apply andb_prop_intro. split...
        + split... apply teval_args_delete_state_var in H...
          clear H0 H1 vargs H symbol. induction args... simpl in *.
          apply not_elem_of_union in Hfree as [? ?].
          apply andb_prop_intro. split...
    Qed.

    Lemma feval_delete_state_var {σ A} x :
      x ∉ formula_fvars A →
      feval σ A ↔ feval (delete x σ) A.
    Proof with auto.
      generalize dependent x. generalize dependent σ.
      induction A; simpl; intros σ x0 Hfree;
        try (apply not_elem_of_union in Hfree as [H1 H2]); simp feval.
      - split; subst; intros.
        + apply sfeval_delete_state_var...
        + apply sfeval_delete_state_var in H...
      - rewrite IHA with (x:=x0)...
      - rewrite IHA1 with (x:=x0)... rewrite IHA2 with (x:=x0)...
      - rewrite IHA1 with (x:=x0)... rewrite IHA2 with (x:=x0)...
      - apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
        setoid_rewrite <- H... destruct (decide (x0 = x)).
        + subst. destruct (decide (x ∈ formula_fvars A)).
          * rewrite fvars_subst_free... simpl. set_solver.
          * rewrite fvars_subst_non_free...
        + destruct Hfree; [| contradiction]. destruct (decide (x ∈ formula_fvars A)).
          * rewrite fvars_subst_free... simpl. set_solver.
          * rewrite fvars_subst_non_free...
    Qed.

    Lemma teval_delete_state_var_head {σ t vt} x v :
      x ∉ term_fvars t → teval (<[x:=v]> σ) t vt ↔ teval σ t vt.
    Proof with auto.
      intros. etrans.
      - apply teval_delete_state_var. exact H.
      - rewrite (delete_insert_delete σ). rewrite <- teval_delete_state_var...
    Qed.

    Lemma teval_args_delete_state_var_head x σ v args vargs :
      forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
      teval_args (<[x:=v]>σ) args vargs ↔ teval_args σ args vargs.
    Proof with auto.
      intros. etrans.
      - apply teval_args_delete_state_var. exact H.
      - rewrite (delete_insert_delete σ). rewrite <- teval_args_delete_state_var...
    Qed.

    Lemma sfeval_delete_state_var_head {σ sf v} x :
      x ∉ sf_fvars sf → sfeval (<[x:=v]> σ) sf ↔ sfeval σ sf.
    Proof with auto.
      intros. etrans.
      - apply sfeval_delete_state_var. exact H.
      - rewrite (delete_insert_delete σ). rewrite <- sfeval_delete_state_var...
    Qed.

    Lemma feval_delete_state_var_head {σ A v} x :
      x ∉ formula_fvars A →
      feval (<[x:=v]> σ) A ↔ feval σ A.
    Proof with auto.
      intros. etrans.
      - apply feval_delete_state_var. exact H.
      - rewrite (delete_insert_delete σ). rewrite <- feval_delete_state_var...
    Qed.

  Lemma teval_subst {σ t t' x v' v} (H : teval σ t' v') :
    teval (<[x:=v']> σ) t v ↔ teval σ (subst_term t x t') v.
  Proof with auto.
    split.
    - intros H'. generalize dependent t'. generalize dependent v.
      assert (Hind:=teval_ind_mut (<[x:=v']>σ)
        (λ t v _, ∀ t', teval σ t' v' → teval σ (subst_term t x t') v)
        (λ args vargs _, ∀ t', teval σ t' v' → teval_args σ (map (λ arg, subst_term arg x t') args) vargs)).
      simpl in Hind. apply Hind; clear Hind.
      + constructor.
      + rename x into x'. intros x v H t' Heval. destruct (decide (x = x')).
        * subst.
          pose proof (@lookup_total_insert _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ).
          rewrite H...
        * subst.
          pose proof (@lookup_total_insert_ne _ _ _ _ _ _ _ _ _ _ _ _ (@model_value_Inhabited M) σ).
          rewrite H...
      + intros. apply TEval_App with vargs...
      + constructor.
      + constructor; [apply H | apply H0]...
    - remember (subst_term t x t') as tpre. intros H'.
      assert (Hind:=teval_ind_mut σ
        (λ t v _, ∀ t', teval σ t' v' → ∀ tpre, t = subst_term tpre x t' → teval (<[x:=v']>σ) tpre v)
        (λ args vargs _, ∀ t', teval σ t' v' → ∀ args',
              args = (map (λ arg, subst_term arg x t') args') →
              teval_args (<[x:=v']>σ) args' vargs)).
      generalize dependent Heqtpre. generalize dependent t. generalize dependent H.
      generalize dependent t'. generalize dependent H'. generalize dependent v.
      generalize dependent tpre. simpl in Hind. apply Hind; clear Hind.
      + intros. destruct tpre; simpl in H0.
        * inversion H0. subst. constructor.
        * destruct (decide (x0 = x)); try discriminate. subst. inversion H; subst.
          constructor. rewrite (lookup_total_insert σ)...
        * discriminate.
      + intros. destruct tpre; simpl in H0; try discriminate.
        simpl in H0. destruct (decide (x1 = x)); subst.
        * apply TEval_Var. rewrite (lookup_total_insert σ). inversion H; subst...
        * inversion H0. subst. apply TEval_Var. rewrite (lookup_total_insert_ne σ)...
      + intros. destruct tpre; simpl in H1; try discriminate.
        * destruct (decide (x0 = x)); try discriminate. inversion H1; subst.
          inversion H0; subst. inversion H6; subst.
          2: { inversion f0; subst.
               - rewrite H1 in H3. discriminate.
               - constructor. rewrite (lookup_total_insert σ)... }
          inversion f0; subst; rewrite H1 in H5; [| discriminate].
          inversion H5; subst fdef0. clear H5.
          pose proof (Heq := teval_args_det _ _ _ H4 t). subst.
          pose proof (Heq := fdef_det _ H3 H7). subst.
          constructor. rewrite (lookup_total_insert σ)...
        * inversion H1. subst. apply TEval_App with vargs... apply H with t'...
      + intros. symmetry in H0. apply map_eq_nil in H0. subst. constructor...
      + intros. symmetry in H2. apply map_eq_cons in H2. destruct H2 as (y&ys&H3&H4&H5).
        subst. constructor.
        * apply H with t'...
        * apply H0 with t'...
  Qed.

  Lemma teval_args_subst {σ x t v args vargs} :
    teval σ t v →
    teval_args (<[x:=v]>σ) args vargs ↔
      teval_args σ (map (λ arg : term, subst_term arg x t) args) vargs.
  Proof with auto.
    intros Ht. split.
    - induction 1.
      + constructor.
      + constructor; [(apply (teval_subst Ht); assumption)|]. assumption.
    - remember (map (λ arg, subst_term arg x (TConst v)) args) as args'.
      generalize dependent vargs.
      generalize dependent args'.
      induction args; intros args' Heq vargs H.
      + subst. inversion H; subst. constructor.
      + subst. inversion H; subst. constructor; [(apply (teval_subst Ht); assumption)|].
        eapply IHargs.
        * reflexivity.
        * assumption.
  Qed.

  Lemma sfeval_subst {σ sf x t v} :
    teval σ t v →
    sfeval (<[x:=v]>σ) sf ↔ sfeval σ (subst_sf sf x t).
  Proof with auto.
    intros Ht. split.
    - destruct sf; simpl; inversion 1; subst...
      + destruct H0 as []. apply (teval_subst Ht) in H0, H1. eauto.
      + destruct H0 as []. apply (teval_args_subst Ht) in H0. eauto.
    - destruct sf; simpl; inversion 1; subst...
      + destruct H0 as []. apply (teval_subst Ht) in H0, H1. eauto.
      + destruct H0 as []. apply (teval_args_subst Ht) in H0. eauto.
  Qed.

  (* Lemma term_ty_subst {M Γ t x t' τ'} : *)
  (*   term_has_type M Γ t' τ' → *)
  (*   term_ty M Γ (subst_term t x t') = term_ty M (<[x:=τ']> Γ) t. *)
  (* Proof with auto. *)
  (*   intros. induction t; simpl... *)
  (*   - destruct (decide (x0 = x)). *)
  (*     + subst. rewrite (lookup_insert Γ)... *)
  (*     + rewrite (lookup_insert_ne Γ)... *)
  (*   - destruct (model_fdefs M !! f)... remember ((fdef_sig f0).1) as sig; clear Heqsig. *)
  (*     enough ( *)
  (*         args_wf_aux (term_ty M Γ <$> map (λ arg : term, subst_term arg x t') args) sig *)
  (*         = args_wf_aux (term_ty M (<[x:=τ']> Γ) <$> args) sig). *)
  (*     { rewrite H1... } *)
  (*     generalize dependent sig. *)
  (*     induction args... forward IHargs. { intros. apply H0. right... } *)
  (*     simpl. destruct sig... { destruct (term_ty M Γ (subst_term a x t')); *)
  (*         destruct (term_ty M (<[x:=τ']> Γ) a)... } *)
  (*     rewrite H0. 2:{ left... } *)
  (*               destruct (term_ty M (<[x:=τ']> Γ) a)... *)
  (*     destruct (v0 =? v)... *)
  (* Qed. *)

  (* Lemma term_wf_subst {M Γ t x t' τ'} : *)
  (*   term_has_type M Γ t' τ' → *)
  (*   term_wf_aux M Γ (subst_term t x t') = term_wf_aux M (<[x:=τ']> Γ) t. *)
  (* Proof with auto. *)
  (*   intros. unfold term_wf_aux. rewrite (term_ty_subst H)... *)
  (* Qed. *)

  (* Lemma sf_wf_subst {M Γ sf x t τ} : *)
  (*   term_has_type M Γ t τ → *)
  (*   sf_wf_aux M Γ (subst_sf sf x t) = sf_wf_aux M (<[x:=τ]> Γ) sf. *)
  (* Proof with auto. *)
  (*   intros. destruct sf... *)
  (*   - simpl. do 2 rewrite (term_wf_subst H)... *)
  (*   - simpl. destruct (model_pdefs M !! symbol)... remember (pdef_sig p) as sig; clear Heqsig. *)
  (*     generalize dependent sig. induction args... intros. simpl. destruct sig... *)
  (*     + intros. unfold term_args_match_sig. rewrite fmap_cons. simpl. *)
  (*       destruct (term_ty M Γ (subst_term a x t)); *)
  (*         destruct (term_ty M (<[x:=τ]> Γ))... *)
  (*     + unfold term_args_match_sig. simpl. rewrite (term_ty_subst H). *)
  (*       destruct (term_ty M (<[x:=τ]> Γ))... *)
  (*       destruct (v0 =? v)... apply IHargs. *)
  (* Qed. *)

  (* Lemma formula_wf_subst {M Γ} A x t τ : *)
  (*   term_has_type M Γ t τ → *)
  (*   formula_wf_aux M Γ (A[x \ t]) = formula_wf_aux M (<[x:=τ]> Γ) A. *)
  (* Proof with auto. *)
  (*   intros. *)
  (*   generalize dependent τ. generalize dependent t. generalize dependent x. *)
  (*   generalize dependent Γ. induction A; intros. *)
  (*   - simpl. rewrite (sf_wf_subst H)... *)
  (*   - rewrite simpl_subst_not. simpl... *)
  (*   - rewrite simpl_subst_and. simpl. rewrite (IHA1 _ _ _ _ H). rewrite (IHA2 _ _ _ _ H)... *)
  (*   - rewrite simpl_subst_or. simpl. rewrite (IHA1 _ _ _ _ H). rewrite (IHA2 _ _ _ _ H)... *)
  (*   - destruct (decide (x = x0)); [| destruct (decide (x0 ∈ formula_fvars A))]. *)
  (*     + subst. rewrite simpl_subst_exists_skip... simpl. *)
  (*       rewrite (insert_insert Γ)... *)
  (*     + rewrite simpl_subst_exists_propagate... generalize_fresh_var x A x0 t as x'. *)
  (*       simpl. assert (IH:=H). forward (H (A [x \ x']))... *)
  (*       assert (term_has_type M (<[x':=τ]> Γ) t τ0). *)
  (*       { unfold term_has_type. rewrite (term_ty_delete_state_var _ x')... *)
  (*         rewrite (delete_insert_delete Γ). rewrite <- (term_ty_delete_state_var)... } *)
  (*       apply (H _ x0) in H1. rewrite H1. clear H1 H. forward (IH A)... *)
  (*       assert (term_has_type M (<[x0:=τ0]> (<[x':=τ]> Γ)) x' τ). *)
  (*       { unfold term_has_type. simpl. rewrite (lookup_insert_ne (<[x':=τ]> Γ))... *)
  (*         apply lookup_insert_Some... } *)
  (*       apply (IH _ x) in H. rewrite H. clear IH H. rewrite (insert_commute Γ)... *)
  (*       destruct ((decide (x = x'))). *)
  (*       * subst. rewrite (insert_insert (<[x0:=τ0]> Γ))... *)
  (*       * destruct H3 as [H3 | H3]; [contradiction |]. *)
  (*         rewrite (formula_wf_delete_state_var _ x')... *)
  (*         rewrite (formula_wf_delete_state_var _ x' (<[x:=τ]> (<[x0:=τ0]> Γ)))... *)
  (*         f_equal. rewrite (insert_commute (<[x0:=τ0]> Γ))... *)
  (*         rewrite (delete_insert_delete (<[x:=τ]> (<[x0:=τ0]> Γ)))... *)
  (*     + rewrite simpl_subst_exists_skip... *)
  (*       simpl. destruct (value_ty_choice τ)... *)
  (*       rewrite (insert_commute Γ)... rewrite (formula_wf_delete_state_var_head _ x0)... *)
  (* Qed. *)

  (* Lemma term_wf_subst_term_wf M Γ t0 x t : *)
  (*   x ∈ term_fvars t0 → *)
  (*   term_wf_aux M Γ (subst_term t0 x t) → term_wf_aux M Γ t. *)
  (* Proof with auto. *)
  (*   generalize dependent t. generalize dependent x. induction t0; intros; simpl in *. *)
  (*   - apply elem_of_empty in H as []. *)
  (*   - apply elem_of_singleton in H. subst. destruct (decide (x = x)); [| contradiction]... *)
  (*   - apply elem_of_union_list in H0 as (arg_fvars&H2&H3). *)
  (*     apply elem_of_list_fmap in H2 as (arg&Heq&Hin). subst. apply elem_of_list_In in Hin. *)
  (*     apply H with (t:=t) in H3... clear H H3. unfold term_wf_aux in H1. *)
  (*     destruct (term_ty M Γ (TApp f (map (λ arg : term, subst_term arg x t) args))) eqn:E; *)
  (*       [| contradiction]. *)
  (*     simpl in E. destruct (model_fdefs M !! f); [| discriminate]. *)
  (*     remember ((fdef_sig f0).1) as sig. clear Heqsig. *)
  (*     destruct (args_wf_aux (term_ty M Γ <$> map (λ arg : term, subst_term arg x t) args) sig) eqn:E'; *)
  (*       [| discriminate]. *)
  (*     clear H1 E f0 v. rename E' into H. generalize dependent sig. generalize dependent arg. *)
  (*     induction args; simpl; intros; [contradiction|]. *)
  (*     destruct (term_ty M Γ (subst_term a x t)) eqn:E; [| discriminate]. *)
  (*     destruct sig eqn:E1; [discriminate|]. rename v0 into τ. subst. rename l into sig. *)
  (*     destruct (v =? τ) eqn:E1; [| discriminate]. apply Is_true_true in E1. apply eq_dec_eq in E1. *)
  (*     subst v. destruct Hin. *)
  (*     + subst. unfold term_wf_aux. rewrite E... *)
  (*     + apply (IHargs arg) in H... *)
  (* Qed. *)

  (* Lemma sf_wf_subst_term_wf M Γ sf x t : *)
  (*   x ∈ sf_fvars sf → *)
  (*   sf_wf_aux M Γ (subst_sf sf x t) → term_wf_aux M Γ t. *)
  (* Proof with auto. *)
  (*   intros. destruct sf; simpl in *; try (apply elem_of_empty in H as []). *)
  (*   - apply elem_of_union in H. apply Is_true_andb in H0 as []. destruct H. *)
  (*     + apply term_wf_subst_term_wf in H0... *)
  (*     + apply term_wf_subst_term_wf in H1... *)
  (*   - apply elem_of_union_list in H as (arg_fvars&H2&H3). *)
  (*     apply elem_of_list_fmap in H2 as (arg&Heq&Hin). subst. apply elem_of_list_In in Hin. *)
  (*     apply term_wf_subst_term_wf with (t:=t) (M:=M) (Γ:=Γ) in H3... *)
  (*     clear H3. destruct (model_pdefs M !! symbol); [| contradiction]. *)
  (*     remember (pdef_sig p) as sig. clear Heqsig. *)
  (*     unfold term_args_match_sig in H0. clear p symbol. rename H0 into H. *)
  (*     generalize dependent sig. generalize dependent arg. *)
  (*     induction args; simpl; intros; [contradiction|]. *)
  (*     destruct (term_ty M Γ (subst_term a x t)) eqn:E; [| contradiction]. *)
  (*     destruct sig eqn:E1; [contradiction|]. rename v0 into τ. subst. rename l into sig. *)
  (*     destruct (v =? τ) eqn:E1; [| contradiction]. apply Is_true_true in E1. apply eq_dec_eq in E1. *)
  (*     subst v. destruct Hin. *)
  (*     + subst. unfold term_wf_aux. rewrite E... *)
  (*     + apply (IHargs arg) in H... *)
  (* Qed. *)

  (* Lemma formula_wf_subst_non_free {M Γ} A x t : *)
  (*   x ∉ formula_fvars A → *)
  (*   formula_wf_aux M Γ (A[x \ t]) ↔ formula_wf_aux M Γ A. *)
  (* Proof with auto. *)
  (*   generalize dependent t. generalize dependent x. generalize dependent Γ. *)
  (*   induction A; intros. *)
  (*   - simpl. rewrite subst_sf_non_free_eq... *)
  (*   - rewrite simpl_subst_not. simpl. apply IHA... *)
  (*   - rewrite simpl_subst_and. simpl. do 2 rewrite Is_true_andb. simpl in H. *)
  (*     apply not_elem_of_union in H as []. f_equiv; [apply IHA1 | apply IHA2]... *)
  (*   - rewrite simpl_subst_or. simpl. do 2 rewrite Is_true_andb. simpl in H. *)
  (*     apply not_elem_of_union in H as []. f_equiv; [apply IHA1 | apply IHA2]... *)
  (*   - simpl in *. destruct (quant_subst_skip_cond x A x0). *)
  (*     + rewrite simpl_subst_exists_skip... *)
  (*     + rewrite simpl_subst_exists_propagate... simpl. destruct (value_ty_choice τ)... *)
  (*       generalize_fresh_var x A x0 t as x'. destruct H5. *)
  (*       * subst. apply not_elem_of_difference in H0. rewrite elem_of_singleton in H0. *)
  (*         destruct H0; contradiction. *)
  (*       * apply not_elem_of_difference in H0. rewrite elem_of_singleton in H0. *)
  (*         destruct H0; contradiction. *)
  (* Qed. *)



  (* Lemma formula_wf_subst_term_wf M Γ A x t : *)
  (*   x ∈ formula_fvars A → *)
  (*   formula_wf_aux M Γ (A[x \ t]) → term_wf_aux M Γ t. *)
  (* Proof with auto. *)
  (*   generalize dependent t. generalize dependent x. generalize dependent Γ. *)
  (*   induction A; intros; simpl in *. *)
  (*   - apply sf_wf_subst_term_wf in H0... *)
  (*   - rewrite simpl_subst_not in H0. simpl in H0. apply IHA in H0... *)
  (*   - rewrite simpl_subst_and in H0. simpl in H0. *)
  (*     apply Is_true_andb in H0 as []. apply elem_of_union in H as []. *)
  (*     + apply IHA1 in H0... *)
  (*     + apply IHA2 in H1... *)
  (*   - rewrite simpl_subst_or in H0. simpl in H0. *)
  (*     apply Is_true_andb in H0 as []. apply elem_of_union in H as []. *)
  (*     + apply IHA1 in H0... *)
  (*     + apply IHA2 in H1... *)
  (*   - destruct (value_ty_choice τ). *)
  (*     2:{ apply elem_of_empty in H0 as []. } *)
  (*     destruct (decide (x0 = x)). *)
  (*     + subst. set_solver. *)
  (*     + destruct (decide (x0 ∈ formula_fvars A)). *)
  (*       * rewrite simpl_subst_exists_propagate in H1... *)
  (*         generalize_fresh_var x A x0 t as x'. simpl in *. *)
  (*         destruct (value_ty_choice τ). *)
  (*         2:{ destruct s as [v Hv]. apply n0 in Hv as []. } *)
  (*         clear s0. destruct (decide (x ∈ formula_fvars A)). *)
  (*         -- apply H in H1... *)
  (*            2: { rewrite fvars_subst_free... set_solver. } *)
  (*            rewrite (term_wf_delete_state_var M x') in H1... *)
  (*            rewrite (delete_insert_delete Γ) in H1. *)
  (*            rewrite (term_wf_delete_state_var M x')... *)
  (*         -- apply H in H1... *)
  (*            2: { rewrite fvars_subst_non_free... } *)
  (*            rewrite term_wf_delete_state_var_head in H1... *)
  (*       * apply elem_of_difference in H0 as [? _]. contradiction. *)
  (* Qed. *)

  (* Lemma term_ty_subst_diag M Γ t x : *)
  (*   term_ty M Γ (subst_term t x x) = term_ty M Γ t. *)
  (* Proof with auto. *)
  (*   induction t... *)
  (*   - simpl. destruct (decide (x0 = x)); subst... *)
  (*   - simpl in *. unfold term_wf_aux. simpl. destruct (model_fdefs M !! f) eqn:E... *)
  (*     remember ((fdef_sig f0).1) as sig; clear Heqsig. *)
  (*     enough (args_wf_aux (term_ty M Γ <$> map (λ arg : term, subst_term arg x x) args) sig = *)
  (*               args_wf_aux (term_ty M Γ <$> args) sig). *)
  (*     { rewrite H0... } *)
  (*     generalize dependent sig. clear E. induction args... simpl. pose proof (IH:=H). *)
  (*     forward (H a) by left... rewrite H. destruct (term_ty M Γ a) eqn:E... *)
  (*     destruct sig eqn:E1... destruct (bool_decide (v = v0)) eqn:E2... *)
  (*     apply bool_decide_eq_true in E2. subst. rename v0 into τ. rename l into sig. *)
  (*     apply IHargs. intros. apply IH. right... *)
  (* Qed. *)

  (* Lemma term_wf_subst_diag M Γ t x : *)
  (*   term_wf_aux M Γ (subst_term t x x) = term_wf_aux M Γ t. *)
  (* Proof with auto. *)
  (*   destruct t... *)
  (*   - simpl. destruct (decide (x0 = x)); subst... *)
  (*   - unfold term_wf_aux. rewrite term_ty_subst_diag... *)
  (* Qed. *)

  (* Lemma sf_wf_subst_diag M Γ sf x : *)
  (*   sf_wf_aux M Γ (subst_sf sf x x) = sf_wf_aux M Γ sf. *)
  (* Proof with auto. *)
  (*   destruct sf; simpl... *)
  (*   - f_equal; apply term_wf_subst_diag. *)
  (*   - simpl in *. unfold term_wf_aux. simpl. destruct (model_pdefs M !! symbol) eqn:E... *)
  (*     remember (pdef_sig p) as sig; clear Heqsig. *)
  (*     unfold term_args_match_sig. *)
  (*     generalize dependent sig. clear E. induction args... simpl. intros sig. *)
  (*     rewrite term_ty_subst_diag. destruct (term_ty M Γ a) eqn:E... *)
  (*     destruct sig eqn:E1... destruct (bool_decide (v = v0)) eqn:E2... *)
  (* Qed. *)

  (* Lemma formula_wf_subst_diag M Γ A x : *)
  (*   formula_wf_aux M Γ (A[x \ x]) = formula_wf_aux M Γ A. *)
  (* Proof with auto. *)
  (*   generalize dependent x. generalize dependent Γ. induction A; intros. *)
  (*   - simpl. apply sf_wf_subst_diag. *)
  (*   - rewrite simpl_subst_not. apply IHA. *)
  (*   - rewrite simpl_subst_and. simpl. f_equal; [apply IHA1 | apply IHA2]. *)
  (*   - rewrite simpl_subst_or. simpl. f_equal; [apply IHA1 | apply IHA2]. *)
  (*   - destruct (decide (x = x0)). *)
  (*     + rewrite simpl_subst_exists_skip... *)
  (*     + destruct (decide (x0 ∈ formula_fvars A)). *)
  (*       * rewrite simpl_subst_exists_propagate... generalize_fresh_var x A x0 x0 as x'. *)
  (*         simpl. rewrite H... rewrite formula_wf_subst with (τ:=τ). *)
  (*         2:{ unfold term_has_type. simpl. apply lookup_insert_Some. left... } *)
  (*         destruct (decide (x = x')). *)
  (*         -- subst. rewrite (insert_insert Γ)... *)
  (*         -- destruct H2; [contradiction|]. rewrite (insert_commute Γ)... *)
  (*            rewrite formula_wf_delete_state_var_head... *)
  (*       * rewrite simpl_subst_exists_skip... *)
  (* Qed. *)
End subst.
