From stdpp Require Import fin_maps.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.Basic.

Section syntactic.
  Context {value : Type}.
  Context {value_ty : Type}.
  Local Notation term := (term value).

  Implicit Types t : term.
  Implicit Types af : atomic_formula value value_ty.
  Implicit Types A B C : formula value value_ty.
  Implicit Types v : value.

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

  Lemma simpl_subst_af af x a :
    subst_formula (FAtom af) x a =
      FAtom (subst_af af x a).
  Proof with auto. unfold subst_formula. simpl. reflexivity. Qed.

  Lemma simpl_subst_not A x a :
    <! (¬ A)[x \ a] !> = <! ¬ (A[x \ a]) !>.
  Proof with auto.
    unfold subst_formula.
    replace (quantifier_rank <! ¬A !>) with (quantifier_rank A) by reflexivity.
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
    <! (A ⇒ B)[x \ a] !> = <! (A[x \ a]) ⇒ (B[x \ a])!>.
  Proof with auto.
    unfold FImpl. rewrite simpl_subst_or. rewrite simpl_subst_not...
  Qed.

  Lemma simpl_subst_iff A B x a :
    <! (A ⇔ B)[x \ a] !> = <! (A[x \ a]) ⇔ (B[x \ a])!>.
  Proof with auto.
    intros. unfold FIff. rewrite simpl_subst_and. do 2 rewrite simpl_subst_impl...
  Qed.

  Lemma simpl_subst_exists_skip x y A a :
    x = y ∨ x ∉ formula_fvars A →
    <! (∃ y, A)[x\a] !> = <! ∃ y, A !>.
  Proof with auto.
    intros Heq. unfold subst_formula. simpl. destruct (quant_subst_skip_cond y A x)...
    destruct Heq; contradiction.
  Qed.

  Lemma simpl_subst_exists_propagate x y A a :
    x ≠ y →
    x ∈ formula_fvars A →
    let y' := fresh_var y (quant_subst_fvars y A x a) in
    <! (∃ y, A)[x\a] !> = <! (∃ y', A[y\y'][x\a]) !>.
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
    <! (∀ y, A)[x\a] !> = <! ∀ y, A !>.
  Proof with auto.
    intros Heq. unfold FForall. rewrite simpl_subst_not. rewrite simpl_subst_exists_skip...
  Qed.

  Lemma simpl_subst_forall_propagate x y A a :
    x ≠ y →
    x ∈ formula_fvars A →
    let y' := fresh_var y (quant_subst_fvars y A x a) in
    <! (∀ y, A)[x\a] !> = <! (∀ y', A[y\y'][x\a]) !>.
  Proof with auto.
    intros Hneq Hfree. unfold FForall. rewrite simpl_subst_not.
    rewrite simpl_subst_exists_propagate... do 2 rewrite simpl_subst_not...
  Qed.

  Lemma subst_formula_ind {x t} : ∀ P,
      (∀ af, P (FAtom $ subst_af af x t) (FAtom af)) →
      (∀ A, P <! A[x \ t] !> A → P <! ¬ (A[x \ t]) !> <! ¬ A !>) →
      (∀ A1 A2, P <! A1[x \ t] !> A1 → P <! A2[x \ t] !> A2 → P <! A1[x \ t] ∧ A2[x \ t] !> <! A1 ∧ A2 !>) →
      (∀ A1 A2, P <! A1[x \ t] !> A1 → P <! A2[x \ t] !> A2 → P <! A1[x \ t] ∨ A2[x \ t] !> <! A1 ∨ A2 !>) →
      (∀ y A, (∀ B, shape_eq B A = true → P <! B[x \ t] !> B) →
              (x = y ∨ x ∉ formula_fvars A → P <! ∃ y, A !> <! ∃ y, A !>)) →
      (∀ y A, (∀ B, shape_eq B A = true → P <! B[x \ t] !> B) →
              (x ≠ y → x ∈ formula_fvars A →
               let y' := fresh_var y (quant_subst_fvars y A x t) in
               P <! ∃ y', A[y \ y'][x \ t] !> <! ∃ y, A !>)) →
      ∀ A, P <! A[x \ t] !> A.
  Proof with auto.
    simpl.
    intros P Haf Hnot Hand Hor Hexists1 Hexists2 A. induction A using formula_ind.
    - apply Haf.
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

  Lemma subst_af_diag : forall af x,
      subst_af af x x = af.
  Proof with auto.
    intros af x. destruct af...
    1-2: simpl; f_equal; apply subst_term_diag.
    simpl. f_equal. induction args... rewrite map_cons. f_equal; auto; apply subst_term_diag.
  Qed.

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

  Lemma subst_af_non_free af x t :
    x ∉ af_fvars af →
    subst_af af x t = af.
  Proof with auto.
    intros. destruct af; simpl; try reflexivity.
    - simpl in H. apply not_elem_of_union in H as [? ?]. f_equal; apply subst_term_non_free...
    - simpl in H. f_equal. apply subst_term_non_free...
    - f_equal. simpl in H. induction args... simpl in *. apply not_elem_of_union in H as [? ?].
      f_equal.
      + simpl in H. apply subst_term_non_free...
      + apply IHargs...
  Qed.

  Local Lemma free_var_subst_fvars_subseteq t x t' :
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

  Lemma fvars_subst_term_free t x t' :
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

  Lemma fvars_subst_af_free af x t' :
    x ∈ af_fvars af →
    af_fvars (subst_af af x t') = (af_fvars af ∖ {[x]}) ∪ term_fvars t'.
  Proof with auto.
    intros. destruct af.
    - simpl in H. apply elem_of_empty in H as [].
    - simpl in H. apply elem_of_empty in H as [].
    - simpl in *. apply elem_of_union in H. destruct H.
      + rewrite fvars_subst_term_free... destruct (decide (x ∈ term_fvars t2)).
        * rewrite fvars_subst_term_free... set_solver.
        * rewrite subst_term_non_free... set_solver.
      + rewrite (fvars_subst_term_free t2)... destruct (decide (x ∈ term_fvars t1)).
        * rewrite fvars_subst_term_free... set_solver.
        * rewrite subst_term_non_free... set_solver.
    - simpl in *. rewrite fvars_subst_term_free...
    - simpl in *. apply leibniz_equiv. intros a.
      apply elem_of_union_list in H as (x_arg_fvars&H1&H2).
      apply elem_of_list_fmap in H1 as (x_arg&->&H1). split; intros H.
      + apply elem_of_union_list in H as (a_arg_fvars&H3&H4).
        apply elem_of_list_fmap in H3 as (a_fvars&->&H3).
        apply elem_of_list_fmap in H3 as (a_arg&->&H3).
        destruct (decide (x ∈ term_fvars a_arg)).
        * apply elem_of_union.
          rewrite fvars_subst_term_free in H4... apply elem_of_union in H4 as [?|?]... left.
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
              ++ rewrite fvars_subst_term_free... apply elem_of_union. left. apply elem_of_difference.
                rewrite not_elem_of_singleton. split...
          -- rewrite subst_term_non_free... split... eexists. split; [reflexivity|].
              apply elem_of_list_fmap. exists a_arg. rewrite subst_term_non_free...
        * apply elem_of_union_list. exists (term_fvars (subst_term x_arg x t')).
          split...
          -- apply elem_of_list_fmap. eexists. split; [reflexivity|]. apply elem_of_list_fmap.
              eexists. split; [reflexivity|]...
          -- apply free_var_subst_fvars_subseteq...
  Qed.

  Lemma fvars_subst_non_free A x t :
    x ∉ formula_fvars A →
    formula_fvars (<! A[x \ t] !>) = formula_fvars A.
  Proof with auto.
    apply subst_formula_ind with
      (P:=λ A B, x ∉ formula_fvars B → formula_fvars A = formula_fvars B); intros; simpl.
    - rewrite subst_af_non_free...
    - simpl...
    - simpl in H. simpl in H1. apply not_elem_of_union in H1 as [? ?]. simpl. set_solver.
    - simpl in H. simpl in H1. apply not_elem_of_union in H1 as [? ?]. simpl. set_solver.
    - reflexivity.
    - simpl in H2. apply not_elem_of_difference in H2. rewrite elem_of_singleton in H2.
      destruct H2; subst; contradiction.
  Qed.

  Lemma fvars_subst_free : ∀ A x t,
      x ∈ formula_fvars A →
      formula_fvars (<! A[x \ t] !>) = (formula_fvars A ∖ {[x]}) ∪ term_fvars t.
  Proof with auto.
    intros.
    generalize dependent t. generalize dependent x.
    induction A; simpl; intros.
    - rewrite fvars_subst_af_free...
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
    formula_fvars (<! A[x \ x] !>) = formula_fvars A.
  Proof with auto.
    destruct (decide (x ∈ formula_fvars A)) eqn:H.
    - rewrite fvars_subst_free... rewrite union_comm_L. simpl.
      rewrite <- union_difference_singleton_L...
    - apply fvars_subst_non_free...
  Qed.

  Lemma fvars_subst_superset A x t :
    formula_fvars (<! A[x \ t] !>) ⊆ formula_fvars A ∪ term_fvars t.
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
      + simpl. destruct (decide (x1 = x1)); try contradiction. apply subst_term_non_free...
      + simpl. destruct (decide (x2 = x2)); try contradiction. symmetry.
        apply subst_term_non_free...
      + simpl. destruct (decide (x = x2)); destruct (decide (x = x1)); try contradiction...
    - f_equal. induction args; simpl... f_equal.
      + apply H. left...
      + apply IHargs. intros. apply H. right...
  Qed.

  Lemma subst_af_commute af x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    subst_af (subst_af af x1 t1) x2 t2 =
      subst_af (subst_af af x2 t2) x1 t1.
  Proof with auto.
    intros. destruct af; simpl...
    1-2: f_equal; auto using subst_term_commute.
    f_equal. induction args... repeat rewrite map_cons. f_equal... apply subst_term_commute...
  Qed.

End syntactic.
