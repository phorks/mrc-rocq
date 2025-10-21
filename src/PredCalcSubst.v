From Stdlib Require Import Strings.String.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From stdpp Require Import gmap fin_maps.
From MRC Require Import Options.
From MRC Require Import Model.
From MRC Require Import Tactics.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.

Lemma higher_qrank__subst_eq : ∀ A x a r',
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
      assert (subst_formula_aux (S (quantifier_rank A)) A x (fresh_var x (quant_subst_fvars A x0 a))
            = subst_formula_aux (quantifier_rank A) A x (fresh_var x (quant_subst_fvars A x0 a))).
      {
        symmetry. apply H with (m:=rank A); try lia...
      } rewrite H0. clear H0.
      assert (subst_formula_aux (S r') A x (fresh_var x (quant_subst_fvars A x0 a))
            = subst_formula_aux (quantifier_rank A) A x (fresh_var x (quant_subst_fvars A x0 a))).
      {
        symmetry. apply H with (m:=rank A); try lia...
      } rewrite H0. clear H0.
      remember (subst_formula_aux (quantifier_rank A) A x (fresh_var x (quant_subst_fvars A x0 a)))
        as inner.
      pose proof (HsameInnerA := subst_preserves_shape_aux A x (fresh_var x (quant_subst_fvars A x0 a)) (quantifier_rank A)).
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

Lemma simpl_subst_exists_skip x y τ A a :
  y = x ∨ x ∉ formula_fvars A →
  <! (exists y : τ, A)[x\a] !> = <! exists y : τ, A !>.
Proof with auto.
  intros Heq. unfold subst_formula. simpl. destruct (quant_subst_skip_cond y A x)...
  destruct Heq; contradiction.
Qed.

Lemma simpl_subst_exists_propagate x y τ A a :
  y ≠ x →
  x ∈ formula_fvars A →
  let y' := fresh_var y (quant_subst_fvars A x a) in
  <! (exists y : τ, A)[x\a] !> = <! (exists y' : τ, A[y\y'][x\a]) !>.
Proof.
  intros Hneq Hfree. simpl. unfold subst_formula. simpl.
  destruct (quant_subst_skip_cond y A x)...
  1: { destruct H; contradiction. } f_equal.
  fold_qrank_subst_fresh (S (quantifier_rank A)) A y x a.
  f_equal.
  - assert (H:=subst_preserves_shape_aux A y
      (fresh_var y (quant_subst_fvars A x a)) (quantifier_rank A)).
    deduce_rank_eq H. lia.
  - symmetry. apply higher_qrank__subst_eq. lia.
Qed.

Lemma simpl_subst_forall_skip x y τ A a :
  y = x ∨ x ∉ formula_fvars A →
  <! (forall y : τ, A)[x\a] !> = <! forall y : τ, A !>.
Proof with auto.
  intros Heq. unfold FForall. rewrite simpl_subst_not. rewrite simpl_subst_exists_skip...
Qed.

Lemma simpl_subst_forall_propagate x y τ A a :
  y ≠ x →
  x ∈ formula_fvars A →
  let y' := fresh_var y (quant_subst_fvars A x a) in
  <! (forall y : τ, A)[x\a] !> = <! (forall y' : τ, A[y\y'][x\a]) !>.
Proof with auto.
  intros Hneq Hfree. unfold FForall. rewrite simpl_subst_not.
  rewrite simpl_subst_exists_propagate... do 2 rewrite simpl_subst_not...
Qed.

Lemma subst_formula_ind {x t} : ∀ P,
  (forall sf, P (FSimple $ subst_sf sf x t) (FSimple sf)) →
  (forall A, P <! A[x \ t] !> A → P <! ~ (A[x \ t]) !> <! ~ A !>) →
  (forall A1 A2, P <! A1[x \ t] !> A1 → P <! A2[x \ t] !> A2 → P <! A1[x \ t] ∧ A2[x \ t] !> <! A1 ∧ A2 !>) →
  (forall A1 A2, P <! A1[x \ t] !> A1 → P <! A2[x \ t] !> A2 → P <! A1[x \ t] ∨ A2[x \ t] !> <! A1 ∨ A2 !>) →
  (forall y τ A, (forall B, shape_eq B A = true → P <! B[x \ t] !> B) →
          (y = x ∨ x ∉ formula_fvars A →
           P <! exists y : τ, A !> <! exists y : τ, A !>)) →
  (forall y τ A, (forall B, shape_eq B A = true → P <! B[x \ t] !> B) →
          (y <> x → x ∈ formula_fvars A →
           let y' := fresh_var y (quant_subst_fvars A x t) in
           P <! exists y' : τ, A[y \ y'][x \ t] !> <! exists y : τ, A !>)) →
  forall A, P <! A[x \ t] !> A.
Proof with auto.
  simpl.
  intros P Hsf Hnot Hand Hor Hexists1 Hexists2 A.
  induction A using formula_ind.
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

Hint Resolve simpl_subst_sf : core.
Hint Resolve simpl_subst_not : core.
Hint Rewrite simpl_subst_and : core.
Hint Rewrite simpl_subst_or : core.
Hint Rewrite simpl_subst_impl : core.
Hint Rewrite simpl_subst_iff : core.
Hint Rewrite subst_term_diag : core.
Hint Rewrite subst_sf_diag : core.

Lemma subst_term_non_free t x t' :
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

Lemma subst_sf_non_free sf x t :
    x ∉ sf_fvars sf →
    subst_sf sf x t = sf.
Proof with auto.
  intros. destruct sf; simpl; try reflexivity.
  - simpl in H. apply not_elem_of_union in H as [? ?]. f_equal; apply subst_term_non_free...
  - f_equal. simpl in H. induction args... simpl in *. apply not_elem_of_union in H as [? ?].
    f_equal.
    + simpl in H. apply subst_term_non_free...
    + apply IHargs...
Qed.

Lemma subst_non_free A x t :
    x ∉ formula_fvars A →
    A[x \ t] = A.
Proof with auto.
  induction A using subst_formula_ind; intros.
  - simpl. rewrite simpl_subst_sf. f_equal. apply subst_sf_non_free...
  - simpl. rewrite simpl_subst_not. f_equal...
  - simpl. rewrite simpl_subst_and. apply not_elem_of_union in H as [? ?].
    f_equal; [apply IHA1|apply IHA2]...
  - simpl. rewrite simpl_subst_or. apply not_elem_of_union in H as [? ?].
    f_equal; [apply IHA1|apply IHA2]...
  - simpl in H1. unfold subst_formula. simpl. destruct (quant_subst_skip_cond y A x)...
    destruct H0; contradiction.
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
      * clear H0. rewrite subst_term_non_free in H4... apply elem_of_union.
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
        -- rewrite subst_term_non_free... split... eexists. split; [reflexivity|].
           apply elem_of_list_fmap. exists a_arg. rewrite subst_term_non_free...
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
      * rewrite subst_term_non_free... set_solver.
    + rewrite (subst_term_free_fvars t2)... destruct (decide (x ∈ term_fvars t1)).
      * rewrite subst_term_free_fvars... set_solver.
      * rewrite subst_term_non_free... set_solver.
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
      * rewrite subst_term_non_free in H4... apply elem_of_union.
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
        -- rewrite subst_term_non_free... split... eexists. split; [reflexivity|].
           apply elem_of_list_fmap. exists a_arg. rewrite subst_term_non_free...
      * apply elem_of_union_list. exists (term_fvars (subst_term x_arg x t')).
        split...
        -- apply elem_of_list_fmap. eexists. split; [reflexivity|]. apply elem_of_list_fmap.
           eexists. split; [reflexivity|]...
        -- apply free_var_subst_fvars_subseteq...
Qed.

Lemma subst_non_free_fvars A x t :
  x ∉ formula_fvars A →
  formula_fvars (A[x \ t]) = formula_fvars A.
Proof with auto. intros. rewrite subst_non_free... Qed.

Lemma subst_free_fvars : ∀ A x t,
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
      * rewrite subst_non_free... set_solver.
    + rewrite IHA2... destruct (decide (x ∈ formula_fvars A1)).
      * rewrite IHA1... set_solver.
      * rewrite subst_non_free... set_solver.
  - rewrite simpl_subst_or. simpl. apply elem_of_union in H as [|].
    + rewrite IHA1... destruct (decide (x ∈ formula_fvars A2)).
      * rewrite IHA2... set_solver.
      * rewrite subst_non_free... set_solver.
    + rewrite IHA2... destruct (decide (x ∈ formula_fvars A1)).
      * rewrite IHA1... set_solver.
      * rewrite subst_non_free... set_solver.
  - apply elem_of_difference in H0 as [? ?]. apply not_elem_of_singleton in H1.
    destruct (quant_subst_skip_cond x A x0).
    + destruct H2 as [|]; subst; contradiction.
    + rewrite simpl_subst_exists_propagate... simpl.
      rewrite H...
      * pose proof (fresh_var_fresh x (quant_subst_fvars A x0 t)) as Hfresh.
        apply quant_subst_fvars_inv in Hfresh as (Hfresh1&Hfresh2&Hfresh3).
        destruct (decide (x ∈ formula_fvars A)).
        -- rewrite H... set_solver.
        -- rewrite subst_non_free... set_solver.
      * destruct (decide (x ∈ formula_fvars A)).
        -- rewrite H... apply elem_of_union. left. apply elem_of_difference. split...
           apply not_elem_of_singleton...
        -- rewrite subst_non_free...
Qed.

(* Lemma term_wf_subst_free : *)
(*   x ∈ term_fvars t → *)
(*   term_wf  *)


Hint Rewrite subst_free_fvars : core.

Lemma subst_term_commute t x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    subst_term (subst_term t x1 t1) x2 t2 = subst_term (subst_term t x2 t2) x1 t1.
Proof with auto.
  intros Hneq H1 H2. induction t using term_ind; simpl...
  - destruct (decide (x = x1)); destruct (decide (x = x2)); subst.
    + contradiction.
    + simpl. destruct (decide (x1 = x1)); try contradiction. apply subst_term_non_free...
    + simpl. destruct (decide (x2 = x2)); try contradiction. symmetry. apply subst_term_non_free...
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

Lemma teval_delete_state_var x {M σ t v} :
    x ∉ term_fvars t →
    teval M σ t v ↔ teval M (delete x σ) t v.
Proof with auto.
  intros Hfree. split.
  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M σ t v → x ∉ term_fvars t → teval M (delete x σ) t v)
         (λ args vargs _, forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
                              teval_args M σ args vargs → teval_args M (delete x σ) args vargs)).
    + intros. constructor.
    + intros x' v H H' Hfree. constructor. simpl in Hfree.
      destruct (decide (x' = x)); subst; simpl.
      * apply not_elem_of_singleton in Hfree. contradiction.
      * apply lookup_delete_Some. split...
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
    apply (teval_ind_mut _ _
         (λ t v _, teval M (delete x σ) t v → x ∉ term_fvars t → teval M σ t v)
         (λ args vargs _, forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
                              teval_args M (delete x σ) args vargs → teval_args M σ args vargs)).
    + intros. constructor.
    + intros x' v H H' Hfree. constructor. simpl in Hfree.
      destruct (decide (x' = x)); subst; simpl.
      * apply not_elem_of_singleton in Hfree. contradiction.
      * apply lookup_delete_Some in H as [? ?]...
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

Lemma teval_args_delete_state_var : forall x {M σ args vargs},
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
    teval_args M σ args vargs ↔
    teval_args M (delete x σ) args vargs.
Proof with auto.
  intros x M σ args vargs Hfree. split.
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

Lemma sfeval_delete_state_var x {M σ sf b} :
    x ∉ sf_fvars sf → sfeval M σ sf b ↔ sfeval M (delete x σ) sf b.
Proof with auto.
  intros Hfree. destruct sf; simpl.
  - split; inversion 1; subst; constructor.
  - split; inversion 1; subst; constructor.
  - simpl in Hfree. apply not_elem_of_union in Hfree as [? ?].
    split; inversion 1; subst.
    + apply SFEval_Eq_True with v; apply teval_delete_state_var...
    + apply SFEval_Eq_False with (v1:=v1) (v2:=v2); try apply teval_delete_state_var...
    + apply teval_delete_state_var in H4, H6... apply SFEval_Eq_True with v...
    + apply teval_delete_state_var in H4, H5... apply SFEval_Eq_False with (v1:=v1) (v2:=v2)...
  - simpl in Hfree. split; inversion 1; subst.
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_state_var...
      clear H2 H4 vargs H symbol. induction args... simpl in *.
      apply not_elem_of_union in Hfree as [? ?].
      apply andb_prop_intro. split...
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_state_var in H2...
      clear H2 H4 H2 vargs H symbol. induction args... simpl in *.
      apply not_elem_of_union in Hfree as [? ?].
      apply andb_prop_intro. split...
Qed.

Lemma feval_delete_state_var x {M σ A b} :
    x ∉ formula_fvars A →
    feval M σ A b ↔ feval M (delete x σ) A b.
Proof with auto.
  generalize dependent b. generalize dependent x. generalize dependent σ.
  induction A using formula_ind; simpl; intros σ x0 b Hfree;
    try (apply not_elem_of_union in Hfree as [H1 H2]).
  - split; inversion 1; subst; constructor.
    + apply sfeval_delete_state_var...
    + apply sfeval_delete_state_var in H1...
  - split; inversion 1; subst; constructor.
    + apply IHA...
    + rewrite IHA with (x:=x0)...
  - split; inversion 1; subst.
    + constructor; [apply IHA1 | apply IHA2]...
    + constructor; [rewrite IHA1 with (x:=x0) | rewrite IHA2 with (x:=x0)]...
  - split; inversion 1; subst.
    + constructor; [apply IHA1 | apply IHA2]...
    + constructor; [rewrite IHA1 with (x:=x0) | rewrite IHA2 with (x:=x0)]...
  - apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
    destruct (decide (x0 = x)); subst; simpl.
    + apply feval_exists_equiv.
      * intros. rewrite (insert_delete_insert σ)...
      * unfold state_types. setoid_rewrite fmap_delete.
        rewrite (insert_delete_insert (value_typeof <$> σ))...
    + destruct Hfree; [| contradiction]. apply feval_exists_equiv; intros.
      * rewrite <- (delete_insert_ne σ)...
      * unfold state_types. setoid_rewrite fmap_delete.
        rewrite <- (delete_insert_ne (value_typeof <$> σ))...
        rewrite <- formula_wf_delete_state_var...
Qed.

Lemma teval_delete_state_var_head x M σ t v0 v :
  x ∉ term_fvars t → teval M (<[x:=v0]> σ) t v ↔ teval M σ t v.
Proof with auto.
  intros. etrans.
  - apply teval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- teval_delete_state_var...
Qed.

Lemma teval_args_delete_state_var_head x M σ (v : value) args vargs :
  forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args →
  teval_args M (<[x:=v]>σ) args vargs ↔ teval_args M σ args vargs.
Proof with auto.
  intros. etrans.
  - apply teval_args_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- teval_args_delete_state_var...
Qed.

Lemma sfeval_delete_state_var_head x M σ sf v b :
  x ∉ sf_fvars sf → sfeval M (<[x:=v]> σ) sf b ↔ sfeval M σ sf b.
Proof with auto.
  intros. etrans.
  - apply sfeval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- sfeval_delete_state_var...
Qed.

Lemma feval_delete_state_var_head x M σ A v b :
  x ∉ formula_fvars A →
  feval M (<[x:=v]> σ) A b ↔ feval M σ A b.
Proof with auto.
  intros. etrans.
  - apply feval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- feval_delete_state_var...
Qed.

Lemma teval_subst {M σ t t' x} {v' v : value} (H : teval M σ t' v') :
  teval M (<[x:=v']> σ) t v ↔ teval M σ (subst_term t x t') v.
Proof with auto.
  split.
  - intros H'. generalize dependent t'. generalize dependent v.
    assert (Hind:=teval_ind_mut M (<[x:=v']>σ)
      (λ t v _, ∀ t', teval M σ t' v' → teval M σ (subst_term t x t') v)
      (λ args vargs _, ∀ t', teval M σ t' v' → teval_args M σ (map (λ arg, subst_term arg x t') args) vargs)).
    simpl in Hind. apply Hind; clear Hind.
    + constructor.
    + rename x into x'. intros x v H t' Heval. destruct (decide (x = x')).
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H1 H2]].
        -- assumption.
        -- exfalso. apply H1...
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H1 H2]].
        -- contradiction.
        -- constructor...
    + intros. apply TEval_App with vargs...
    + constructor.
    + constructor; [apply H | apply H0]...
  - remember (subst_term t x t') as tpre. intros H'.
    assert (Hind:=teval_ind_mut M σ
      (λ t v _, ∀ t', teval M σ t' v' → ∀ tpre, t = subst_term tpre x t' → teval M (<[x:=v']>σ) tpre v)
      (λ args vargs _, ∀ t', teval M σ t' v' → ∀ args',
            args = (map (λ arg, subst_term arg x t') args') →
            teval_args M (<[x:=v']>σ) args' vargs)).
    generalize dependent Heqtpre. generalize dependent t. generalize dependent H.
    generalize dependent t'. generalize dependent H'. generalize dependent v.
    generalize dependent tpre. simpl in Hind. apply Hind; clear Hind.
    + intros. destruct tpre; simpl in H0.
      * inversion H0. subst. constructor.
      * destruct (decide (x0 = x)); try discriminate. subst. inversion H; subst.
        constructor. apply lookup_insert_Some...
      * discriminate.
    + intros. destruct tpre; simpl in H0; try discriminate.
      simpl in H0. destruct (decide (x1 = x)); subst.
      * apply TEval_Var. inversion H; subst. rewrite e in H1. inversion H1. apply lookup_insert_Some...
      * inversion H0. subst. apply TEval_Var.  apply lookup_insert_Some...
    + intros. destruct tpre; simpl in H1; try discriminate.
      * destruct (decide (x0 = x)); try discriminate. inversion H1; subst.
        inversion H0; subst. inversion H6; subst. inversion f0; subst.
        rewrite H1 in H5. inversion H5; subst fdef0. clear H5.
        pose proof (Heq := teval_args_det M H4 t). subst.
        pose proof (Heq := fdef_det _ H3 H7). subst.
        constructor. apply lookup_insert_Some...
      * inversion H1. subst. apply TEval_App with vargs... apply H with t'...
    + intros. symmetry in H0. apply map_eq_nil in H0. subst. constructor...
    + intros. symmetry in H2. apply map_eq_cons in H2. destruct H2 as (y&ys&H3&H4&H5).
      subst. constructor.
      * apply H with t'...
      * apply H0 with t'...
Qed.

Lemma teval_args_subst {M σ x t v args vargs} :
  teval M σ t v →
  teval_args M (<[x:=v]>σ) args vargs ↔
    teval_args M σ (map (λ arg : term, subst_term arg x t) args) vargs.
Proof with auto.
  intros Ht. split.
  - induction 1.
    + constructor.
    + constructor; [(apply (teval_subst Ht); assumption)|]. assumption.
  - remember (map (λ arg, subst_term arg x v) args) as args'.
    generalize dependent vargs.
    generalize dependent args'.
    induction args; intros args' Heq vargs H.
    + subst. inversion H; subst. constructor.
    + subst. inversion H; subst. constructor; [(apply (teval_subst Ht); assumption)|].
      eapply IHargs.
      * reflexivity.
      * assumption.
Qed.

Lemma sfeval_subst {M σ sf x t v b} :
  teval M σ t v →
  sfeval M (<[x:=v]>σ) sf b ↔ sfeval M σ (subst_sf sf x t) b.
Proof with auto.
  intros Ht. split.
  - destruct sf; simpl; inversion 1; subst...
    + apply (teval_subst Ht) in H2, H4. eauto.
    + apply (teval_subst Ht) in H2, H3. eauto.
    + apply (teval_args_subst Ht) in H2. eauto.
  - destruct sf; simpl; inversion 1; subst...
    + apply (teval_subst Ht) in H2, H4. eauto.
    + apply (teval_subst Ht) in H2, H3. eauto.
    + apply (teval_args_subst Ht) in H2. eauto.
Qed.

Lemma teval_term_has_type {M σ t v} :
  teval M σ t v →
  term_has_type M (state_types σ) t (value_typeof v).
Proof with auto.
  intros. apply teval_ty with (τ:=value_typeof v) in H. apply H.
  apply value_elem_of_iff_typeof_eq...
Qed.

Lemma term_ty_subst {M Γ t x t' τ'} :
  term_has_type M Γ t' τ' →
  term_ty M Γ (subst_term t x t') = term_ty M (<[x:=τ']> Γ) t.
Proof with auto.
  intros. induction t; simpl...
  - destruct (decide (x0 = x)).
    + subst. rewrite (lookup_insert Γ)...
    + rewrite (lookup_insert_ne Γ)...
  - destruct (model_fdefs M !! f)... remember ((fdef_sig f0).1) as sig; clear Heqsig.
    enough (
      args_wf_aux (term_ty M Γ <$> map (λ arg : term, subst_term arg x t') args) sig
      = args_wf_aux (term_ty M (<[x:=τ']> Γ) <$> args) sig).
    { rewrite H1... }
    generalize dependent sig.
    induction args... forward IHargs. { intros. apply H0. right... }
    simpl. destruct sig... { destruct (term_ty M Γ (subst_term a x t'));
        destruct (term_ty M (<[x:=τ']> Γ) a)... }
    rewrite H0. 2:{ left... }
    destruct (term_ty M (<[x:=τ']> Γ) a)...
    destruct (v0 =? v)...
Qed.

Lemma term_wf_subst {M Γ t x t' τ'} :
  term_has_type M Γ t' τ' →
  term_wf_aux M Γ (subst_term t x t') = term_wf_aux M (<[x:=τ']> Γ) t.
Proof with auto.
  intros. unfold term_wf_aux. rewrite (term_ty_subst H)...
Qed.

Lemma sf_wf_subst {M Γ sf x t τ} :
  term_has_type M Γ t τ →
  sf_wf_aux M Γ (subst_sf sf x t) = sf_wf_aux M (<[x:=τ]> Γ) sf.
Proof with auto.
  intros. destruct sf...
  - simpl. do 2 rewrite (term_wf_subst H)...
  - simpl. destruct (model_pdefs M !! symbol)... remember (pdef_sig p) as sig; clear Heqsig.
    generalize dependent sig. induction args... intros. simpl. destruct sig...
    + intros. unfold term_args_match_sig. rewrite fmap_cons. simpl.
      destruct (term_ty M Γ (subst_term a x t));
       destruct (term_ty M (<[x:=τ]> Γ))...
    + unfold term_args_match_sig. simpl. rewrite (term_ty_subst H).
      destruct (term_ty M (<[x:=τ]> Γ))...
      destruct (v0 =? v)... apply IHargs.
Qed.

Tactic Notation "generalize_fresh_var" ident(y) ident(A) ident(x) ident(t) "as" ident(y') :=
  let Hfres := fresh in
  let Heq := fresh in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in
  pose proof (Hfresh := fresh_var_fresh y (quant_subst_fvars A x t));
  apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3);
  remember (fresh_var y (quant_subst_fvars A x t)) as y' eqn:Heq;
  clear Heq.

Lemma formula_wf_subst {M Γ} A x t τ :
  term_has_type M Γ t τ →
  formula_wf_aux M Γ (A[x \ t]) = formula_wf_aux M (<[x:=τ]> Γ) A.
Proof with auto.
  intros.
  generalize dependent τ. generalize dependent t. generalize dependent x.
  generalize dependent Γ. induction A; intros.
  - simpl. rewrite (sf_wf_subst H)...
  - rewrite simpl_subst_not. simpl...
  - rewrite simpl_subst_and. simpl. rewrite (IHA1 _ _ _ _ H). rewrite (IHA2 _ _ _ _ H)...
  - rewrite simpl_subst_or. simpl. rewrite (IHA1 _ _ _ _ H). rewrite (IHA2 _ _ _ _ H)...
  - destruct (decide (x = x0)); [| destruct (decide (x0 ∈ formula_fvars A))].
    + subst. rewrite simpl_subst_exists_skip... simpl.
      rewrite (insert_insert Γ)...
    + rewrite simpl_subst_exists_propagate... generalize_fresh_var x A x0 t as x'.
      simpl. assert (IH:=H). forward (H (A [x \ x']))...
      assert (term_has_type M (<[x':=τ]> Γ) t τ0).
      { unfold term_has_type. rewrite (term_ty_delete_state_var _ x')...
        rewrite (delete_insert_delete Γ). rewrite <- (term_ty_delete_state_var)... }
      apply (H _ x0) in H1. rewrite H1. clear H1 H. forward (IH A)...
      assert (term_has_type M (<[x0:=τ0]> (<[x':=τ]> Γ)) x' τ).
      { unfold term_has_type. simpl. rewrite (lookup_insert_ne (<[x':=τ]> Γ))...
        apply lookup_insert_Some... }
      apply (IH _ x) in H. rewrite H. clear IH H. rewrite (insert_commute Γ)...
      destruct ((decide (x = x'))).
      * subst. rewrite (insert_insert (<[x0:=τ0]> Γ))...
      * rewrite (formula_wf_delete_state_var _ x')...
        rewrite (formula_wf_delete_state_var _ x' (<[x:=τ]> (<[x0:=τ0]> Γ)))...
        f_equal. rewrite (insert_commute (<[x0:=τ0]> Γ))...
        rewrite (delete_insert_delete (<[x:=τ]> (<[x0:=τ0]> Γ)))...
    + rewrite simpl_subst_exists_skip... rewrite (formula_wf_delete_state_var _ x0).
      2:{ simpl. set_solver. }
      symmetry. etrans.
      * rewrite (formula_wf_delete_state_var _ x0). 2: { simpl. set_solver. }
        rewrite (delete_insert_delete Γ). reflexivity.
      * reflexivity.
Qed.

Lemma state_types_insert {x v σ} :
  state_types (<[x:=v]> σ) = <[x:=value_typeof v]> (state_types σ).
Proof. unfold state_types. rewrite (fmap_insert _ σ). reflexivity. Qed.

Lemma feval_subst {v M σ A x t b} :
  teval M σ t v →
  feval M (<[x:=v]> σ) A b ↔ feval M σ (A[x \ t]) b.
Proof with auto.
  generalize dependent b. generalize dependent t. generalize dependent x.
  generalize dependent σ. generalize dependent v.
  induction A using formula_ind; intros v0 σ x0 t b Ht.
  - split; inversion 1; subst.
    + constructor. apply (sfeval_subst Ht)...
    + constructor. apply (sfeval_subst Ht)...
  - rewrite simpl_subst_not. split; inversion 1; subst.
    + constructor. apply IHA with (x:=x0) (b:=b0) in Ht. apply Ht...
    + constructor. apply IHA with (x:=x0) (b:=b0) in Ht. apply Ht...
  - rewrite simpl_subst_and. split; inversion 1; subst.
    + apply IHA1 with (x:=x0) (b:=b1) in Ht as ?.
      apply IHA2 with (x:=x0) (b:=b2) in Ht. constructor.
      * apply H0...
      * apply Ht...
    + apply IHA1 with (x:=x0) (b:=b1) in Ht as ?.
      apply IHA2 with (x:=x0) (b:=b2) in Ht. constructor.
      * apply H0...
      * apply Ht...
  - rewrite simpl_subst_or. split; inversion 1; subst.
    + apply IHA1 with (x:=x0) (b:=b1) in Ht as ?.
      apply IHA2 with (x:=x0) (b:=b2) in Ht. constructor.
      * apply H0...
      * apply Ht...
    + apply IHA1 with (x:=x0) (b:=b1) in Ht as ?.
      apply IHA2 with (x:=x0) (b:=b2) in Ht. constructor.
      * apply H0...
      * apply Ht...
  - destruct (decide (x = x0)).
    + subst. rewrite simpl_subst_exists_skip... apply feval_exists_equiv.
      * intros. rewrite (insert_insert σ)...
      * intros. unfold state_types. setoid_rewrite fmap_insert.
        setoid_rewrite (insert_insert (value_typeof <$> σ))...
    + destruct (decide (x0 ∈ formula_fvars A)).
      2: { rewrite simpl_subst_exists_skip... rewrite feval_delete_state_var_head... simpl.
      apply not_elem_of_difference... }
      rewrite simpl_subst_exists_propagate... generalize_fresh_var x A x0 t as x'.
      apply feval_exists_equiv.
      * intros. rewrite (feval_delete_state_var x')... rewrite <- H...
        2: { apply teval_delete_state_var_head... apply Ht. }
        rewrite (insert_commute σ x0 x')... rewrite <- H...
        2:{ apply TEval_Var. apply lookup_insert. }
        rewrite (@feval_delete_state_var x' _ (<[x:=v]> (<[x':=v]> (<[x0:=v0]> σ))))...
        apply eq_iff. clear H Ht. f_equal.
        destruct (decide (x = x')).
        -- subst. rewrite (insert_insert (<[x0:=v0]> σ))...
        -- rewrite (insert_commute (<[x0:=v0]> σ))...
           rewrite (delete_insert_delete (<[x:=v]> (<[x0:=v0]> σ)))...
      * intros.
        apply teval_term_has_type in Ht.
        assert (term_has_type M (<[x':=τ]> (state_types σ)) t (value_typeof v0)).
        {
          unfold term_has_type. rewrite (term_ty_delete_state_var M x')...
          rewrite (delete_insert_delete (state_types σ)).
          rewrite <- (term_ty_delete_state_var)...
        }
        apply formula_wf_subst with (A:=A[x \ x']) (x:=x0) in H1.
        rewrite H1. clear H1 Ht.
        assert (term_has_type M (<[x0:=value_typeof v0]> (<[x':=τ]> (state_types σ))) x' τ).
        {
          unfold term_has_type. simpl. rewrite (lookup_insert_ne (<[x':=τ]> (state_types σ)))...
          apply lookup_insert_Some...
        }
        apply formula_wf_subst with (A:=A) (x:=x) in H1.
        setoid_rewrite H1. clear H1. rewrite state_types_insert.
        rewrite (formula_wf_delete_state_var _ x')...
        symmetry. etrans. { rewrite (formula_wf_delete_state_var _ x')... }
        f_equal.
        destruct (decide (x = x')).
        -- subst.
           rewrite (delete_insert_delete (<[x0:=value_typeof v0]> (<[x':=τ]> (state_types σ)))).
           rewrite (delete_insert_delete (<[x0:=value_typeof v0]> (state_types σ))).
           rewrite (insert_commute (state_types σ))...
           rewrite (delete_insert_delete (<[x0:=value_typeof v0]> (state_types σ)))...
        --
           rewrite (delete_insert_ne (<[x0:=value_typeof v0]> (<[x':=τ]> (state_types σ))))...
           rewrite (delete_insert_ne (<[x0:=value_typeof v0]> (state_types σ)))...
           f_equal.
           rewrite (insert_commute (state_types σ))...
           rewrite (delete_insert_delete (<[x0:=value_typeof v0]> (state_types σ)))...
Qed.

Lemma teval_args_in : ∀ M σ arg args vargs,
  In arg args →
  teval_args M σ args vargs →
  exists v, teval M σ arg v.
Proof with auto.
  intros. induction H0.
  - simpl in H. contradiction.
  - simpl in H. destruct H.
    + subst. eauto.
    + apply IHteval_args...
Qed.

Lemma teval_subst_value : ∀ M σ t x t' v,
    x ∈ term_fvars t →
    teval M σ (subst_term t x t') v →
    exists v', teval M σ t' v'.
Proof with auto.
  induction t.
  - intros. simpl in H. apply elem_of_empty in H as [].
  - intros. simpl in H. apply elem_of_singleton in H as →. simpl in H0.
    destruct (decide (x = x)); try contradiction. eauto.
  - intros. simpl in H0.
    apply elem_of_union_list in H0 as (arg_fvars&H2&H3).
    apply elem_of_list_fmap in H2 as (arg&→&Hin). apply elem_of_list_In in Hin.
    forward (H arg)... inversion H1; subst.
    apply in_map with (f := (λ arg, subst_term arg x t')) in Hin.
    apply (teval_args_in M σ _ _ vargs) in Hin... destruct Hin as [v' Hv']. eauto.
Qed.

Lemma sfeval_subst_value : ∀ M σ sf x t,
    x ∈ sf_fvars sf →
    sfeval M σ (subst_sf sf x t) →
    ∃ v, teval M σ t v.
Proof with auto.
  intros. destruct sf.
  - simpl in H. apply elem_of_empty in H as [].
  - simpl in H. apply elem_of_empty in H as [].
  - simpl in H. apply elem_of_union in H. simpl in H0. inversion H0. subst.
    destruct H.
    + apply teval_subst_value in H3...
    + apply teval_subst_value in H4...
  - simpl in H.
    apply elem_of_union_list in H as (arg_fvars&H2&H3).
    apply elem_of_list_fmap in H2 as (arg&→&Hin). apply elem_of_list_In in Hin.
    inversion H0; subst.
    apply in_map with (f := (λ arg, subst_term arg x t)) in Hin.
    apply (teval_args_in M σ _ _ vargs) in Hin... destruct Hin as [v Hv].
    apply teval_subst_value in Hv...
Qed.

(* Lemma something : forall M σ t, *)
(*     term_fvars t ⊆ dom σ → *)
(*     ∃ v, teval M σ t v. *)
(* Proof with auto. *)
(*   induction t; simpl; intros. *)
(*   - exists v. constructor. *)
(*   - apply singleton_subseteq_l in H. apply elem_of_dom in H as [v Hv]. *)
(*     exists v. constructor... *)
(*   - unfold union_list in H0.  *)
(*     lookup_ *)
(*     Search (is_Some ?p → exists _, ?b). *)

(*     eauto. *)
(*   intros. *)
(* I don't think teval_subst_value holds in general because of LEM and the semantics
    of NOT *)

Lemma feval_subst_value : ∀ M σ A x t,
    x ∈ formula_fvars A →
    feval M σ (A[x \ t]) →
    ∃ v, teval M σ t v.
Proof with auto.
  intros. induction A; simpl in *.
  - eapply sfeval_subst_value. apply H. apply H0.
  - clear IHA. rewrite simpl_subst_not in H0. simpl in H0.
    unfold state_covers in H0. rewrite subst_free_fvars in H0...
    destruct H0 as []
  - simpl in H. apply elem_of_empty in H as [].
  - simpl in H. apply elem_of_empty in H as [].
  - simpl in H. apply elem_of_union in H. simpl in H0. inversion H0. subst.
    destruct H.
    + apply teval_subst_value in H3...
    + apply teval_subst_value in H4...
  - simpl in H.
    apply elem_of_union_list in H as (arg_fvars&H2&H3).
    apply elem_of_list_fmap in H2 as (arg&→&Hin). apply elem_of_list_In in Hin.
    inversion H0; subst.
    apply in_map with (f := (λ arg, subst_term arg x t)) in Hin.
    apply (teval_args_in M σ _ _ vargs) in Hin... destruct Hin as [v Hv].
    apply teval_subst_value in Hv...
Qed.
