From Equations Require Import Equations.
From Stdlib Require Import Lists.List. Import ListNotations.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import SeqNotation.
From MRC Require Import Model.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.SyntacticFacts.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.Variables.

Open Scope refiney_scope.

Section syntax.
  Context {value : Type}.
  Local Notation term := (term value).
  Local Notation final_term := (final_term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A : formula.
  Implicit Types m : gmap variable term.
  Implicit Types mv : gmap variable value.

  Fixpoint msubst_term t m :=
    match t with
    | TConst v => TConst v
    | TVar x =>
        match m !! x with
        | Some t' => t'
        | None => TVar x
        end
    | TApp sym args => TApp sym (map (λ arg, msubst_term arg m) args)
    end.

  Definition msubst_af af m :=
    match af with
    | AT_Eq t₁ t₂ => AT_Eq (msubst_term t₁ m) (msubst_term t₂ m)
    | AT_Pred sym args => AT_Pred sym (map (fun arg => msubst_term arg m) args)
    | _ => af
    end.

  Definition var_term_map_fvars m : gset variable :=
    ⋃ (term_fvars ∘ snd <$> map_to_list m).

  Lemma elem_of_var_term_map_fvars x m :
    x ∈ var_term_map_fvars m → ∃ y t, m !! y = Some t ∧ x ∈ term_fvars t.
  Proof with auto.
    intros. unfold var_term_map_fvars in H. apply elem_of_union_list in H as [fvars []].
    induction m using map_ind.
    - rewrite map_to_list_empty in H. simpl in H. apply elem_of_nil in H as [].
    - rewrite map_to_list_insert in H... simpl in H.
      destruct (decide (x ∈ term_fvars x0)).
      + exists i, x0. subst. split... apply (lookup_insert m).
      + apply elem_of_cons in H as [|]; [subst; contradiction|]. apply IHm in H as [y [t []]].
        exists y, t. split... rewrite lookup_insert_ne... intros ->. rewrite H in H1.
        discriminate.
  Qed.

  Lemma not_elem_of_var_term_map_fvars x m :
    x ∉ var_term_map_fvars m → (∀ y t, m !! y = Some t → x ∉ term_fvars t).
  Proof with auto.
    intros. unfold var_term_map_fvars in H. unfold not in H. intros contra.
    apply H. clear H. apply elem_of_union_list. exists (term_fvars t). split...
    induction m using map_ind.
    - apply lookup_empty_Some in H0 as [].
    - rewrite map_to_list_insert... simpl. apply elem_of_cons. destruct (decide (i = y)).
      + subst. rewrite lookup_insert in H0. inversion H0...
      + right. rewrite lookup_insert_ne in H0...
  Qed.

  Definition quant_msubst_fvars y A m :=
    (formula_fvars A ∖ {[y]}) ∪ var_term_map_fvars m ∪ dom m.

  Lemma quant_msubst_fvars_inv y' y A m :
    y' ∉ quant_msubst_fvars y A m →
    (y = y' ∨ y' ∉ formula_fvars A) ∧ (y' ∉ dom m) ∧ (∀ x t, m !! x = Some t → y' ∉ term_fvars t).
  Proof with auto.
    intros. unfold quant_msubst_fvars in H. do 2 rewrite not_elem_of_union in H.
    destruct_and! H. split_and!...
    - apply not_elem_of_difference in H. set_solver.
    - apply not_elem_of_var_term_map_fvars...
  Qed.

  Equations? msubst A m : formula by wf (rank A) lt :=
    msubst (FAtom af) m => FAtom (msubst_af af m);
    msubst (FNot A) m => FNot (msubst A m);
    msubst (FAnd A₁ A₂) m => FAnd
                        (msubst A₁ m)
                        (msubst A₂ m);
    msubst (FOr A₁ A₂) m => FOr
                       (msubst A₁ m)
                       (msubst A₂ m);
    msubst (FExists y A) m =>
        let y' := fresh_var y (quant_msubst_fvars y A m) in
        FExists y' (msubst (<! A[y \ y'] !>) m).
  Proof.
    all: try (simpl; lia).
    unfold rank. simpl. fold Nat.add. pose proof (subst_preserves_shape A y (y')).
    deduce_rank_eq H. rewrite Hfr. rewrite Hqr. lia.
  Qed.

  Definition to_var_term_map (xs : list variable) (ts : list term)
    `{OfSameLength variable term xs ts}: gmap variable term := list_to_map (zip xs ts).

  Local Notation "t [ [ₜ xs \ ts ] ]" := (msubst_term t (to_var_term_map xs ts))
                                           (in custom formula at level 74, left associativity,
                                               xs custom var_seq,
                                               ts custom term_seq) : refiney_scope.

  Local Notation "A [ [ xs \ ts ] ]" := (msubst A (to_var_term_map xs ts))
                                          (in custom formula at level 74, left associativity,
                                              xs custom var_seq,
                                              ts custom term_seq) : refiney_scope.


  Local Tactic Notation "generalize_fresh_var_for_msubst"
    ident(y) constr(A) constr(m) "as" ident(y') :=
    let Hfresh := fresh in
    let Heq := fresh in
    let H1 := fresh in let H2 := fresh in let H3 := fresh in
    pose proof (Hfresh := fresh_var_fresh y (quant_msubst_fvars y A m));
    apply quant_msubst_fvars_inv in Hfresh as (H1&H2&H3);
    remember (fresh_var y (quant_msubst_fvars y A m)) as y' eqn:Heq;
    clear Heq.


  Lemma msubst_term_id t m :
    dom m ## term_fvars t →
    msubst_term t m = t.
  Proof with auto.
    intros H. induction t; simpl...
    - simpl in H. replace (m !! x) with (@None term)... symmetry.
      rewrite <- not_elem_of_dom. set_solver.
    - f_equal. induction args... simpl. f_equal.
      + apply H0; [left; auto | set_solver].
      + apply IHargs; [naive_solver | set_solver].
  Qed.

  Lemma msubst_af_id af m :
    dom m ## af_fvars af →
    msubst_af af m = af.
  Proof with auto.
    intros H.
    destruct af...
    - simpl. simpl in H. do 2 rewrite msubst_term_id by set_solver...
    - simpl. f_equal. induction args... simpl in H. simpl in *. f_equal.
      + rewrite msubst_term_id... set_solver.
      + apply IHargs. set_solver.
  Qed.

  Lemma msubst_term_empty t :
    msubst_term t ∅ = t.
  Proof. apply msubst_term_id. set_solver. Qed.

  Lemma msubst_af_empty af :
    msubst_af af ∅ = af.
  Proof. apply msubst_af_id. set_solver. Qed.

  Lemma msubst_term_delete_non_free t x m :
    x ∉ term_fvars t →
    msubst_term t m = msubst_term t (delete x m).
  Proof with auto.
    intros. induction t; simpl...
    - simpl in H. apply not_elem_of_singleton in H. rewrite lookup_delete_ne...
    - f_equal. induction args... simpl. f_equal.
      + apply H0; [naive_solver | set_solver].
      + apply IHargs.
        * intros. apply H0... right...
        * set_solver.
  Qed.

  Lemma msubst_af_delete_non_free af x m :
    x ∉ af_fvars af →
    msubst_af af m = msubst_af af (delete x m).
  Proof with auto.
    intros. destruct af; simpl...
    - rewrite <- msubst_term_delete_non_free by set_solver.
      rewrite <- msubst_term_delete_non_free by set_solver...
    - f_equal. induction args... simpl. f_equal.
      + rewrite <- msubst_term_delete_non_free... set_solver.
      + apply IHargs. set_solver.
  Qed.

  (* TODO: can I replace all teval equiv lemmas with simple equality? Or at least tequiv? *)
  Lemma msubst_term_non_free t xs ts `{OfSameLength _ _ xs ts} :
    list_to_set xs ## term_fvars t →
    msubst_term t (to_var_term_map xs ts) = t.
  Proof with auto.
    intros. induction t; simpl...
    - destruct (to_var_term_map xs ts !! x) eqn:E.
      + apply elem_of_dom_2 in E. unfold to_var_term_map in E.
        rewrite dom_list_to_map_zip_L in E... set_solver.
      + apply not_elem_of_dom_2 in E. unfold to_var_term_map in E.
        rewrite dom_list_to_map_zip_L in E...
    - f_equal. induction args... simpl. f_equal.
      + simpl in H0. apply H1...
        * left...
        * set_solver.
      + apply IHargs.
        * intros. apply H1... right...
        * set_solver.
  Qed.

  Lemma msubst_af_non_free af xs ts `{OfSameLength _ _ xs ts} :
    list_to_set xs ## af_fvars af →
    msubst_af af (to_var_term_map xs ts) = af.
  Proof with auto.
    intros. destruct af; simpl in *...
    - rewrite msubst_term_non_free by set_solver. rewrite msubst_term_non_free by set_solver...
    - induction args; simpl... f_equal. f_equal.
      + rewrite msubst_term_non_free by set_solver...
      + forward IHargs by set_solver. inversion IHargs... rewrite H2...
  Qed.

  Lemma fvars_msubst_term_superset t xs ts `{OfSameLength _ _ xs ts} :
    term_fvars (msubst_term t (to_var_term_map xs ts)) ⊆ term_fvars t ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    induction t; simpl; [set_solver| | ].
    - destruct (to_var_term_map xs ts !! x) eqn:E.
      + unfold to_var_term_map in E. apply lookup_list_to_map_zip_Some in E as (i&?&?&_)...
        apply elem_of_list_lookup_2 in H1. set_unfold. intros x0 ?. right.
        apply elem_of_union_list. exists (term_fvars t). set_solver.
      + simpl. set_solver.
    - induction args.
      + simpl. set_solver.
      + simpl. assert (H1:=H0 a). forward H1 by (left; auto).
        forward IHargs.
        1: { intros. apply H0. right... }
        set_solver.
  Qed.

  Lemma fvars_msubst_term_superset_vars_not_free_in_terms t xs ts `{!OfSameLength xs ts} :
    NoDup xs →
    (list_to_set xs) ## ⋃ (term_fvars <$> ts) →
    term_fvars (<! t [[ₜ *xs \ *ts ]] !>) ⊆
      (term_fvars t ∖ list_to_set xs) ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    intros Hnodup ?. induction t; simpl; [set_solver | |].
    - destruct (decide (x ∈ xs)).
      + apply elem_of_list_lookup in e as (i&?). destruct (lookup_of_same_length_l ts H0) as (t&?).
        * replace (to_var_term_map xs ts !! x) with (Some t).
          -- intros x' ?. set_unfold. right. apply elem_of_union_list. exists (term_fvars t).
             split... apply elem_of_list_fmap. exists t. split...
             apply elem_of_list_lookup_2 in H1...
          -- symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some...
             exists i. split_and!... intros. apply NoDup_lookup with (i:=i) in H2...
             lia.
      + replace (to_var_term_map xs ts !! x) with (@None term); [set_solver|].
        symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None...
    - induction args; simpl; [set_solver|]. set_solver.
  Qed.

  Lemma fvars_msubst_af_superset af xs ts `{OfSameLength _ _ xs ts} :
    af_fvars (msubst_af af (to_var_term_map xs ts)) ⊆ af_fvars af ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    destruct af; simpl; [set_solver|set_solver | | ].
    - pose proof (fvars_msubst_term_superset t1 xs ts).
      pose proof (fvars_msubst_term_superset t2 xs ts). set_solver.
    - induction args.
      + simpl. set_solver.
      + simpl. pose proof (fvars_msubst_term_superset a xs ts). set_solver.
  Qed.

  Lemma fvars_msubst_superset A xs ts `{OfSameLength _ _ xs ts} :
    formula_fvars (<! A [[*xs \ *ts]] !>) ⊆ formula_fvars A ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    induction A; simp msubst; simpl.
    2-4: set_solver.
    - apply fvars_msubst_af_superset.
    - generalize_fresh_var_for_msubst x A (to_var_term_map xs ts) as x'.
      forward (H0 <! A [x \ x'] !>)...  clear H3 H4 H5.
      destruct (decide (x ∈ formula_fvars A)).
      + rewrite fvars_subst_free in H0... set_solver.
      + rewrite fvars_subst_non_free in H0... set_solver.
  Qed.

  Lemma simpl_msubst_not A (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (¬ A) [[*xs \ *ts]] !> = <! ¬ (A [[*xs \ *ts]]) !>.
  Proof. simp msubst. reflexivity. Qed.
  Lemma simpl_msubst_and A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ∧ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ∧ B [[*xs \ *ts]] !>.
  Proof. simp msubst. reflexivity. Qed.
  Lemma simpl_msubst_or A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ∨ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ∨ B [[*xs \ *ts]] !>.
  Proof. simp msubst. reflexivity. Qed.
  Lemma simpl_msubst_impl A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ⇒ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ⇒ B [[*xs \ *ts]] !>.
  Proof. unfold FImpl. simp msubst. reflexivity. Qed.
  Lemma simpl_msubst_iff A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ⇔ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ⇔ B [[*xs \ *ts]] !>.
  Proof. unfold FIff, FImpl. simp msubst. reflexivity. Qed.

  Global Instance msubst_formula_final {A xs} {ts : list final_term}
      `{FormulaFinal _ A} `{OfSameLength _ _ xs ts} :
    FormulaFinal <! A[[*xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    intros x ?. apply fvars_msubst_superset in H1. set_unfold. destruct H1 as [|].
    - apply H in H1...
    - apply elem_of_union_list in H1 as (fvars&?&?). set_unfold. destruct H1 as (?&->&t&->&?).
      apply (final_term_final t) in H2...
  Qed.

  Lemma msubst_term_trans t xs1 xs2 ts `{!OfSameLength xs1 xs2} `{!OfSameLength xs2 ts}
      `{!OfSameLength xs1 ts} :
    xs1 ## xs2 →
    NoDup xs1 →
    NoDup xs2 →
    list_to_set xs2 ## term_fvars t →
    <! t [[ₜ *xs1 \ ⇑ₓ₊ xs2]] [[ₜ *xs2 \ *ts]] !> = <! t [[ₜ *xs1 \ *ts]] !>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 Hfree. induction t...
    - simpl. destruct (decide (x ∈ xs1 ∨ x ∈ xs2)).
      2:{ apply Decidable.not_or in n as [].
          simpl. replace (to_var_term_map xs1 (@TVar value <$> xs2) !! x) with (@None term).
          2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None...
              typeclasses eauto. }
          replace (to_var_term_map xs1 ts !! x) with (@None term).
          2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
          simpl. replace (to_var_term_map xs2 ts !! x) with (@None term)...
          symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
      destruct o.
      + pose proof (Hdisjoint x H).
        apply elem_of_list_lookup in H as [i ?].
        destruct (lookup_of_same_length_l ts H) as [t ?].
        destruct (lookup_of_same_length_l xs2 H) as [x' ?].
        replace (to_var_term_map xs1 (@TVar value <$> xs2) !! x) with (Some (@TVar value x')).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists i. split_and!...
            - apply list_lookup_fmap_Some. exists x'. split...
            - intros. apply NoDup_lookup with (i:=i) in H3... lia. }
        simpl. replace (to_var_term_map xs2 ts !! x') with (Some t).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists i. split_and!...
            intros. apply NoDup_lookup with (i:=i) in H3... lia. }
        replace (to_var_term_map xs1 ts !! x) with (Some t)...
        symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
          [typeclasses eauto|]. exists i. split_and!...
        intros. apply NoDup_lookup with (i:=i) in H3... lia.
      + assert (x ∉ xs1) by (intros contra; apply (Hdisjoint x); auto).
        simpl in Hfree. set_unfold in Hfree. simpl in Hfree. apply Hfree in H as []...
    - simpl. f_equal. apply list_eq. rewrite <- list_fmap_compose. intros i.
      f_equal. induction args... simpl. rewrite H; [| left; auto | set_solver].
      f_equal. apply IHargs; [intros; apply H; auto; right; auto | set_solver].
  Qed.

  Lemma msubst_term_app t xs1 ts1 xs2 ts2 `{!OfSameLength xs1 ts1} `{!OfSameLength xs2 ts2} :
    xs1 ## xs2 →
    NoDup xs1 →
    NoDup xs2 →
    list_to_set xs1 ## ⋃ (term_fvars <$> ts2) →
    list_to_set xs2 ## ⋃ (term_fvars <$> ts1) →
    <! t[[ₜ *xs1, *xs2 \ *ts1, *ts2 ]] !> = <! t[[ₜ *xs1 \ *ts1 ]][[ₜ *xs2 \ *ts2]] !>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 Hfree1 Hfree2. induction t...
    - simpl. destruct (decide (x ∈ xs1 ∨ x ∈ xs2)).
      2:{ apply Decidable.not_or in n as [].
          simpl. replace (to_var_term_map (xs1 ++ xs2) (ts1 ++ ts2) !! x) with (@None term).
          2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None...
              - typeclasses eauto.
              - set_solver. }
          replace (to_var_term_map xs1 ts1 !! x) with (@None term).
          2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
          simpl. replace (to_var_term_map xs2 ts2 !! x) with (@None term)...
          symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
      destruct o.
      + pose proof (Hdisjoint x H).
        apply elem_of_list_lookup in H as [i ?].
        destruct (lookup_of_same_length_l ts1 H) as [t ?].
        replace (to_var_term_map (xs1 ++ xs2) (ts1 ++ ts2) !! x) with (Some t).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists i. split_and!...
            - rewrite lookup_app. rewrite H...
            - rewrite lookup_app. rewrite H1...
            - intros. apply lookup_app_l_Some_disjoint' in H2...
              apply NoDup_lookup with (i:=i) in H2... lia. }
        simpl. replace (to_var_term_map xs1 ts1 !! x) with (Some t).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists i. split_and!...
            intros. apply NoDup_lookup with (i:=i) in H2... lia. }
        rewrite msubst_term_id... unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        clear dependent x. intros x ??. apply (Hfree2 _ H). apply elem_of_union_list.
        exists (term_fvars t). split... apply elem_of_list_fmap. apply elem_of_list_lookup_2 in H1.
        exists t...
      + assert (x ∉ xs1) by (intros contra; apply (Hdisjoint x); auto).
        apply elem_of_list_lookup in H as [i ?].
        destruct (lookup_of_same_length_l ts2 H) as [t ?].
        replace (to_var_term_map (xs1 ++ xs2) (ts1 ++ ts2) !! x) with (Some t).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists (i + length xs1).
            opose proof (@of_same_length _ _ xs1 ts1 _)... split_and!...
            - rewrite lookup_app. replace (xs1 !! (i + length xs1)) with (@None variable).
              2:{ symmetry. apply list_lookup_None. lia. }
              rewrite Nat.add_sub. rewrite H...
            - rewrite H2. rewrite lookup_app.
              replace (ts1 !! (i + length ts1)) with (@None term).
              2:{ symmetry. apply list_lookup_None. lia. }
              rewrite Nat.add_sub. rewrite H1...
            - intros. apply lookup_app_r_Some_disjoint' in H3 as []...
              apply NoDup_lookup with (i:=i) in H4... subst. lia. }
        replace (to_var_term_map xs1 ts1 !! x) with (@None term).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None;
            [typeclasses eauto|]... }
        simpl. replace (to_var_term_map xs2 ts2 !! x) with (Some t)...
        symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some; [typeclasses eauto|].
        exists i. split_and!... intros. apply NoDup_lookup with (i:=i) in H2... lia.
    - simpl. f_equal. apply list_eq. rewrite <- list_fmap_compose. intros i.
      f_equal. induction args... simpl. rewrite H; [| left; auto].
      f_equal. apply IHargs. intros. apply H... right...
  Qed.

  Lemma msubst_term_comm t xs1 ts1 xs2 ts2 `{!OfSameLength xs1 ts1} `{!OfSameLength xs2 ts2} :
    xs1 ## xs2 →
    NoDup xs1 →
    NoDup xs2 →
    list_to_set xs1 ## ⋃ (term_fvars <$> ts2) →
    list_to_set xs2 ## ⋃ (term_fvars <$> ts1) →
    <! t[[ₜ *xs1 \ *ts1 ]][[ₜ *xs2 \ *ts2]] !> = <! t[[ₜ *xs2 \ *ts2 ]][[ₜ *xs1 \ *ts1]] !>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 Hfree1 Hfree2. induction t...
    - simpl. destruct (decide (x ∈ xs1 ∨ x ∈ xs2)).
      2:{ apply Decidable.not_or in n as [].
          simpl. assert (to_var_term_map xs1 ts1 !! x = @None term).
          { unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
          assert (to_var_term_map xs2 ts2 !! x = @None term).
          { unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
          rewrite H1. rewrite H2. simpl. rewrite H1. rewrite H2... }
      destruct o.
      + pose proof (Hdisjoint x H).
        apply elem_of_list_lookup in H as [i ?].
        destruct (lookup_of_same_length_l ts1 H) as [t ?].
        assert (to_var_term_map xs1 ts1 !! x = Some t).
        { unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists i. split_and!... intros.
            apply NoDup_lookup with (i:=i) in H2... lia. }
        rewrite H2. rewrite msubst_term_id.
        2:{ unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
            clear dependent x. intros x ??. apply (Hfree2 _ H). apply elem_of_union_list.
            exists (term_fvars t). split... apply elem_of_list_fmap.
            apply elem_of_list_lookup_2 in H1. exists t... }
        replace (to_var_term_map xs2 ts2 !! x) with (@None term).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
        simpl. rewrite H2...
      + assert (x ∉ xs1) by (intros contra; apply (Hdisjoint x); auto).
        replace (to_var_term_map xs1 ts1 !! x) with (@None term).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_None... }
        apply elem_of_list_lookup in H as [i ?].
        destruct (lookup_of_same_length_l ts2 H) as [t ?].
        simpl. replace (to_var_term_map xs2 ts2 !! x) with (Some t).
        2:{ symmetry. unfold to_var_term_map. apply lookup_list_to_map_zip_Some;
            [typeclasses eauto|]. exists i. split_and!... intros.
            apply NoDup_lookup with (i:=i) in H2... lia. }
        rewrite msubst_term_id... unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        clear dependent x. intros x ??. apply (Hfree1 _ H). apply elem_of_union_list.
        exists (term_fvars t). split... apply elem_of_list_fmap.
        apply elem_of_list_lookup_2 in H1. exists t...
    - simpl. f_equal. apply list_eq. rewrite <- list_fmap_compose. intros i.
      f_equal. induction args... simpl. rewrite H; [| left; auto].
      f_equal. apply IHargs. intros. apply H... right...
  Qed.

  Lemma msubst_term_app_comm t xs1 ts1 xs2 ts2 `{!OfSameLength xs1 ts1} `{!OfSameLength xs2 ts2} :
    xs1 ## xs2 →
    NoDup xs1 →
    NoDup xs2 →
    list_to_set xs1 ## ⋃ (term_fvars <$> ts2) →
    list_to_set xs2 ## ⋃ (term_fvars <$> ts1) →
    <! t[[ₜ *xs1, *xs2 \ *ts1, *ts2 ]] !> = <! t[[ₜ *xs2, *xs1 \ *ts2, *ts1 ]] !>.
  Proof with auto.
    intros. rewrite msubst_term_app... rewrite msubst_term_comm... rewrite <- msubst_term_app...
    set_solver.
  Qed.

  Lemma msubst_term_diag t xs :
    NoDup xs →
    msubst_term t (list_to_map (zip xs (TVar <$> xs))) = t.
  Proof with auto.
    intros Hnodup. induction t...
    - simpl. destruct (decide (x ∈ xs)).
      + apply elem_of_list_lookup in e as (i&?).
        replace (list_to_map (zip xs (@TVar value <$> xs)) !! x) with (Some (@TVar value x))...
        symmetry. apply lookup_list_to_map_zip_Some; [typeclasses eauto|].
        exists i. split_and!...
        * rewrite list_lookup_fmap. rewrite H...
        * intros. apply NoDup_lookup with (i:=i) in H0... lia.
      + replace (list_to_map (zip xs (@TVar value <$> xs)) !! x) with (@None term)...
        symmetry. apply lookup_list_to_map_zip_None... typeclasses eauto.
    - simpl. f_equal. apply list_eq. intros i. f_equal. clear i. induction args...
      simpl. rewrite H; [| left]... f_equal. apply IHargs. intros. apply H. right...
  Qed.

End syntax.

Notation "t [ [ₜ xs \ ts ] ]" := (msubst_term t (to_var_term_map xs ts))
                            (in custom formula at level 74, left associativity,
                              xs custom var_seq,
                              ts custom term_seq) : refiney_scope.
Notation "A [ [ xs \ ts ] ]" := (msubst A (to_var_term_map xs ts))
                            (in custom formula at level 74, left associativity,
                              xs custom var_seq,
                              ts custom term_seq) : refiney_scope.

Tactic Notation "generalize_fresh_var_for_msubst"
    ident(y) constr(A) constr(m) "as" ident(y') :=
  let Hfresh := fresh in
  let Heq := fresh in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in
  pose proof (Hfresh := fresh_var_fresh y (quant_msubst_fvars y A m));
  apply quant_msubst_fvars_inv in Hfresh as (H1&H2&H3);
  remember (fresh_var y (quant_msubst_fvars y A m)) as y' eqn:Heq;
  clear Heq.

Section semantics.
  Context {M : model}.

  Local Notation value := (value M).
  Local Notation term := (term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A : formula.
  Implicit Types m : gmap variable term.
  Implicit Types mv : gmap variable value.

  Definition teval_var_term_map σ m mv :=
      dom mv = dom m ∧ ∀ x t v, m !! x = Some t → mv !! x = Some v → teval σ t v.

  Lemma teval_var_term_map_total σ m :
    ∃ mv : gmap variable value, teval_var_term_map σ m mv.
  Proof with auto.
    unfold teval_var_term_map. induction m using map_ind.
    - exists ∅. split... intros. apply lookup_empty_Some in H. contradiction.
    - rename x into t. rename i into x. destruct (teval_total σ t) as [v Hv].
      destruct IHm as (mv&?&?). exists (<[x:=v]> mv). split.
      + set_solver.
      + intros x' t' v' ? ?. destruct (decide (x = x')).
        * subst. rewrite lookup_insert in H2. rewrite lookup_insert in H3.
          inversion H2... inversion H3. subst...
        * rewrite lookup_insert_ne in H2... rewrite lookup_insert_ne in H3...
          apply (H1 x' t' v' H2 H3).
  Qed.

  Lemma teval_var_term_map_insert {σ m mv} x t v :
    teval σ t v →
    teval_var_term_map σ m mv → teval_var_term_map σ (<[x:=t]> m) (<[x:=v]> mv).
  Proof with auto.
    intros ? []. unfold teval_var_term_map. split.
    - apply set_eq. intros. do 2 rewrite dom_insert. rewrite H0...
    - intros. destruct (decide (x = x0)).
      + subst. rewrite (lookup_insert mv) in H3. rewrite (lookup_insert m) in H2.
        inversion H3; inversion H2; subst. assumption.
      + rewrite (lookup_insert_ne mv) in H3... rewrite (lookup_insert_ne m) in H2...
        apply (H1 _ _ _ H2 H3).
  Qed.

  Lemma teval_var_term_map_delete {σ m mv} x :
    teval_var_term_map σ m mv → teval_var_term_map σ (delete x m) (delete x mv).
  Proof with auto.
    intros []. unfold teval_var_term_map. split.
    - apply set_eq. intros. do 2 rewrite dom_delete. do 2 rewrite elem_of_difference.
      rewrite H...
    - intros. destruct (decide (x = x0)).
      + subst. rewrite (lookup_delete mv) in H2. rewrite (lookup_delete m) in H1.
        inversion H2; inversion H1; subst.
      + rewrite (lookup_delete_ne mv) in H2... rewrite (lookup_delete_ne m) in H1...
        apply (H0 _ _ _ H1 H2).
  Qed.

  Lemma teval_var_term_map_det {σ} m mv mv' :
    teval_var_term_map σ m mv →
    teval_var_term_map σ m mv' →
    mv = mv'.
  Proof with auto.
    intros. generalize dependent m. generalize dependent mv'.
    induction mv as [| x v mv Hx IH] using map_ind; intros.
    - destruct H as []. destruct H0 as []. rewrite <- H in H0. rewrite dom_empty_L in H0.
      apply dom_empty_inv_L in H0. subst...
    - assert (Hmv:=H). assert (Hmv':=H0). destruct H as []. destruct H0 as [].
      rewrite dom_insert_L in H. symmetry in H. rewrite H in H0.
      apply dom_union_inv_L in H as (m1&m2&?&?&?&?).
      2: { apply disjoint_singleton_l. apply not_elem_of_dom... }
      apply dom_singleton_inv_L in H4 as [t Ht]. subst m1.
      rewrite <- insert_union_singleton_l in H. subst m. rename m2 into m.
      apply dom_union_inv_L in H0 as (m1&m2&?&?&?&?).
      2: { apply disjoint_singleton_l. apply not_elem_of_dom... }
      apply dom_singleton_inv_L in H4 as [v' Hv']. subst m1.
      rewrite <- insert_union_singleton_l in H. subst mv'. rename m2 into mv'.
      assert (teval σ t v).
      { apply H1 with (x:=x); apply lookup_insert... }
      assert (teval σ t v').
      { apply H2 with (x:=x); apply lookup_insert... }
      clear H1 H2. pose proof (teval_det _ _ _ H H4) as ->. clear H H4.
      apply (teval_var_term_map_delete x) in Hmv, Hmv'.
      apply map_disjoint_singleton_l in H3, H0. rewrite (delete_insert) in Hmv, Hmv'...
      rewrite (delete_insert) in Hmv, Hmv'... rewrite (IH mv' m)...
  Qed.

  Lemma teval_var_term_map_zip_cons_inv σ x xs t ts mv `{OfSameLength _ _ xs ts} :
    NoDup (x :: xs) →
    teval_var_term_map σ (to_var_term_map (x :: xs) (t :: ts)) mv →
    ∃ v mv', teval σ t v ∧ mv = {[x := v]} ∪ mv' ∧ x ∉ dom mv'
             ∧ teval_var_term_map σ (to_var_term_map xs ts) mv'.
  Proof with auto.
    intros. generalize dependent mv. generalize dependent t.
    generalize dependent x. induction_same_length xs ts as x' t'.
    - unfold to_var_term_map in H1. simpl in H1.
      destruct H1 as []. rewrite insert_empty in H1. rewrite dom_singleton_L in H1.
      apply dom_singleton_inv_L in H1 as [v ->]. exists v, ∅. split_and!.
      + eapply H2; [apply lookup_insert|apply lookup_singleton].
      + rewrite map_union_empty...
      + apply not_elem_of_empty.
      + hnf. cbn. split... intros. apply lookup_empty_Some in H1 as [].
    - intros. apply NoDup_cons in H0 as []. assert (Hl:=H').
      apply of_same_length_rest in Hl. ospecialize (IH Hl x' _ t')...
      destruct H1 as []. unfold to_var_term_map in H1. rewrite dom_list_to_map_zip_L in H1.
      2:{ typeclasses eauto. } rewrite list_to_set_cons in H1.
      apply dom_union_inv_L in H1 as (m1&m2&?&?&?&?).
      2: { set_solver. }
      apply dom_singleton_inv_L in H4 as [v Hv]. subst m1.
      rewrite <- insert_union_singleton_l in H1. subst mv. rename m2 into mv.
      assert (teval_var_term_map σ (to_var_term_map (x' :: xs) (t' :: ts)) mv).
      { split.
        - unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        - intros. assert (x0 ≠ x).
          { intros contra. subst. apply elem_of_dom_2 in H4. rewrite H5 in H4.
            apply elem_of_list_to_set in H4. contradiction. }
          apply (H2 x0)...
          ++ unfold to_var_term_map. simpl. rewrite lookup_insert_ne...
          ++ rewrite lookup_insert_ne...
      }
      destruct (IH mv) as (v'&mv'&?&?&?&?)...
      exists v, mv. split_and!...
      + apply (H2 x).
          * unfold to_var_term_map. simpl. rewrite lookup_insert...
          * rewrite lookup_insert...
        + rewrite insert_union_singleton_l...
        + set_solver.
  Qed.

  Lemma msubst_id A m :
    dom m ## formula_fvars A →
    msubst A m ≡ A.
  Proof with auto.
    induction A; simp msubst; intros.
    - rewrite msubst_af_id...
    - rewrite IHA...
    - rewrite IHA1 by set_solver. rewrite IHA2 by set_solver...
    - rewrite IHA1 by set_solver. rewrite IHA2 by set_solver...
    - simpl. generalize_fresh_var_for_msubst x A m as y'.
      intros σ. apply feval_exists_equiv_if. intros v. rewrite H...
      + destruct H3.
        * subst. rewrite fequiv_subst_diag...
        * rewrite (fequiv_subst_trans A x y' (TConst v))...
      + destruct H3.
        * subst. rewrite fvars_subst_diag. set_solver.
        * destruct (decide (x ∈ formula_fvars A)).
          -- rewrite fvars_subst_free... set_solver.
          -- rewrite fvars_subst_non_free... set_solver.
  Qed.

  Lemma teval_msubst σ t0 m v0 mv :
    teval_var_term_map σ m mv →
    teval σ (msubst_term t0 m) v0 ↔ teval (mv ∪ σ) t0 v0.
  Proof with auto.
    intros. generalize dependent v0. induction t0; intros.
    - split; inversion 1; subst; constructor.
    - simpl. destruct H as [? ?]. destruct (m !! x) eqn:E.
      + assert (x ∈ dom mv).
        { rewrite H. rewrite elem_of_dom. unfold is_Some. exists t... }
        apply elem_of_dom in H1 as [v Hv]. specialize (H0 x t v E Hv).
        pose proof (teval_det t v v0 H0). split; intros.
        * apply H1 in H2. subst v0. constructor. apply (lookup_total_union_l' mv)...
        * inversion H2. rewrite (lookup_total_union_l' mv) with (x:=v) in H4...
          subst...
      + assert (x ∉ dom mv).
        { rewrite H. rewrite not_elem_of_dom... }
        apply not_elem_of_dom in H1. split; inversion 1; subst.
        * constructor. rewrite (lookup_total_union_r mv)...
        * constructor. rewrite (lookup_total_union_r mv)...
    - split; inversion 1; subst.
      + apply TEval_App with (vargs := vargs)... clear H1 H6.
        generalize dependent vargs. induction args; simpl in *; intros.
        * inversion H4. constructor.
        * inversion H4; subst. clear H4. apply IHargs in H6; [| intros; apply H0; auto].
          constructor... apply H0...
      + apply TEval_App with (vargs := vargs)... clear H1 H6.
        generalize dependent vargs. induction args; simpl in *; intros.
        * inversion H4. constructor.
        * inversion H4; subst. clear H4. apply IHargs in H6; [| intros; apply H0; auto].
          constructor... apply H0...
  Qed.

  Lemma afeval_msubst σ af m mv :
    teval_var_term_map σ m mv →
    afeval σ (msubst_af af m) ↔ afeval (mv ∪ σ) af.
  Proof with auto.
    intros. destruct af...
    - split; inversion 1; destruct H1 as [].
      + rewrite teval_msubst with (mv:=mv) in H1, H2...
        econstructor. split; [exact H1 | exact H2].
      + rewrite <- teval_msubst with (m:=m) in H1, H2...
        econstructor. split; [exact H1 | exact H2].
    - split; inversion 1; destruct H1 as [].
      + rename x into vargs. exists vargs. split... clear H0 H2. generalize dependent vargs.
        induction args; intros.
        * inversion H1. subst. constructor.
        * inversion H1; subst. constructor... rewrite <- teval_msubst with (m:=m)...
      + rename x into vargs. exists vargs. split... clear H0 H2. generalize dependent vargs.
        induction args; intros.
        * inversion H1. subst. constructor.
        * inversion H1; subst. constructor... rewrite teval_msubst with (mv:=mv)...
  Qed.

  Lemma feval_msubst σ A m mv :
    teval_var_term_map σ m mv →
    feval σ (msubst A m) ↔ feval (mv ∪ σ) A.
  Proof with auto.
    intros. generalize dependent σ. induction A; intros σ Hteval; simp msubst; simp feval.
    - apply afeval_msubst...
    - rewrite IHA...
    - rewrite IHA1... rewrite IHA2...
    - rewrite IHA1... rewrite IHA2...
    - apply exists_iff_exists_weaken. intros v. destruct Hteval as [H1 H2]. rename H into IH.
      generalize_fresh_var_for_msubst x A m as x'. rewrite feval_subst with (v:=v)...
      rewrite IH...
      2: { split... intros. apply (H2 x0 t v0 H) in H0. apply H5 in H.
          rewrite teval_delete_state_var_head... }
      destruct (teval_total σ x') as [vx' Hvx'].
      assert (H6:=H4). rewrite <- H1 in H6. apply not_elem_of_dom in H6.
      rewrite feval_subst with (v:=v).
      2:{ constructor. rewrite (lookup_total_union_r mv)... apply (lookup_total_insert σ). }
      rewrite <- (insert_union_r mv)... destruct (decide (x = x')).
      + subst. rewrite (insert_insert (mv ∪ σ)). rewrite <- feval_subst with (t:=TConst v)...
      + rewrite (insert_commute (mv ∪ σ))... destruct H3; [contradiction|].
        rewrite feval_delete_state_var_head... rewrite feval_subst with (v:=v)...
  Qed.

  Global Instance msubst_proper : Proper((≡@{formula}) ==> (=) ==> (≡)) msubst.
  Proof with auto.
    intros A B H m ? <- σ. destruct (teval_var_term_map_total σ m) as [mv ?].
    split; repeat rewrite feval_msubst with (mv:=mv); auto; intros; apply H...
  Qed.

  Global Instance msubst_proper_fent : Proper((⇛ₗ@{M}) ==> (=) ==> (⇛)) msubst.
  Proof with auto.
    intros A B H m ? <- σ. destruct (teval_var_term_map_total σ m) as [mv ?].
    repeat rewrite feval_msubst with (mv:=mv); auto; intros; apply H...
  Qed.

  Lemma simpl_msubst_exists y A (xs : list variable) ts `{!OfSameLength xs ts} :
    y ∉ (quant_msubst_fvars y A (to_var_term_map xs ts)) →
    <! (∃ y, A)[[*xs \ *ts]] !> ≡ <! (∃ y, A [[*xs \ *ts]]) !>.
  Proof with auto.
    intros.
    assert (fresh_var y (quant_msubst_fvars y A (to_var_term_map xs ts)) = y).
    { apply fresh_var_id... }
    simp msubst. simpl. rewrite H0. rewrite fequiv_subst_diag...
  Qed.

  Lemma simpl_msubst_forall y A (xs : list variable) ts `{!OfSameLength xs ts} :
    y ∉ (quant_msubst_fvars y A (to_var_term_map xs ts)) →
    <! (∀ y, A)[[*xs \ *ts]] !> ≡ <! (∀ y, A [[*xs \ *ts]]) !>.
  Proof with auto.
    intros. unfold FForall. rewrite simpl_msubst_not. f_equiv.
    rewrite simpl_msubst_exists... rewrite simpl_msubst_not...
  Qed.

  Local Lemma teval_var_term_map_total_inv σ mv :
    ∃ m, teval_var_term_map σ m mv.
  Proof with auto.
    exists (TConst <$> mv). split.
    - rewrite dom_fmap_L...
    - intros. rewrite lookup_fmap in H. rewrite H0 in H. simpl in H. inversion H. subst.
      constructor.
  Qed.

  Lemma teval_delete_state_var_term_map_head σ t mv v :
    dom mv ## term_fvars t →
    teval (mv ∪ σ) t v ↔ teval σ t v.
  Proof with auto.
    destruct (teval_var_term_map_total_inv σ mv) as [m Hm].
    intros. rewrite <- teval_msubst with (m:=m)...
    rewrite msubst_term_id... rewrite <- (proj1 Hm)...
  Qed.

  Lemma afeval_delete_state_var_term_map_head σ af mv :
    dom mv ## af_fvars af →
    afeval (mv ∪ σ) af ↔ afeval σ af.
  Proof with auto.
    destruct (teval_var_term_map_total_inv σ mv) as [m Hm].
    intros. rewrite <- afeval_msubst with (m:=m)...
    rewrite msubst_af_id... rewrite <- (proj1 Hm)...
  Qed.

  Lemma feval_delete_state_var_term_map_head σ A mv :
    dom mv ## formula_fvars A →
    feval (mv ∪ σ) A ↔ feval σ A.
  Proof with auto.
    destruct (teval_var_term_map_total_inv σ mv) as [m Hm].
    intros. rewrite <- feval_msubst with (m:=m)...
    rewrite msubst_id... rewrite <- (proj1 Hm)...
  Qed.

  Lemma msubst_empty' A :
    msubst A ∅ ≡ A.
  Proof. apply msubst_id. set_solver. Qed.

  Lemma msubst_delete_non_free A x m :
    x ∉ formula_fvars A →
    msubst A m ≡ msubst A (delete x m).
  Proof with auto.
    intros H σ. destruct (m !! x) eqn:E.
    2:{ rewrite delete_notin... }
    rewrite <- (insert_delete m x t) at 1...
    pose proof (teval_var_term_map_total σ m) as [mv Hmv].
    apply teval_var_term_map_delete with (x:=x) in Hmv as H1.
    pose proof (teval_total σ t) as [v Hv].
    apply (teval_var_term_map_insert x t v Hv) in H1 as H2.
    rewrite feval_msubst with (mv:=(<[x:=v]> (delete x mv)))...
    rewrite feval_msubst with (mv:=(delete x mv))...
    rewrite <- (insert_union_l _ σ). rewrite feval_delete_state_var_head...
  Qed.

  Lemma msubst_term_extract t0 x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    (x ∉ var_term_map_fvars (delete x m)) →
    msubst_term t0 m = msubst_term (subst_term t0 x t) (delete x m).
  Proof with auto.
    induction t0; simpl; intros...
    - destruct (decide (x0 = x)).
      + subst. rewrite H. rewrite msubst_term_id...
      + simpl. rewrite lookup_delete_ne...
    - f_equal. induction args... simpl. f_equal.
      + apply H... left...
      + apply IHargs. intros. apply H... right...
  Qed.

  Lemma msubst_af_extract af x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    (x ∉ var_term_map_fvars (delete x m)) →
    msubst_af af m = msubst_af (subst_af af x t) (delete x m).
  Proof with auto.
    destruct af; simpl; intros...
    - simpl. f_equal; apply msubst_term_extract...
    - simpl. f_equal. induction args... simpl. f_equal...
      apply msubst_term_extract...
  Qed.

  Lemma msubst_extract_l' A x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    msubst A m ≡ msubst (<! A[x \ t] !>) (delete x m).
  Proof with auto.
    intros. intros σ. rewrite <- (insert_delete m x t) at 1...
    pose proof (teval_total σ t) as [v Hv].
    pose proof (teval_var_term_map_total σ (m)) as [mv Hmv].
    apply teval_var_term_map_delete with (x:=x) in Hmv as H2.
    apply (teval_var_term_map_insert x _ _ Hv) in H2 as H3.
    rewrite feval_msubst with (mv:=<[x:=v]> (delete x mv))...
    rewrite feval_msubst with (mv:=delete x mv)...
    assert (Hv':=Hv).
    rewrite <- teval_delete_state_var_term_map_head with (mv:=delete x mv) in Hv'...
    2: { rewrite (proj1 H2)... }
    rewrite feval_subst with (v:=v)... rewrite (insert_union_l (delete x mv))...
  Qed.

  Lemma msubst_extract_r' A x t m :
    m !! x = Some t →
    (x ∉ var_term_map_fvars (delete x m)) →
    msubst A m ≡ <! $(msubst A (delete x m)) [x \ t] !>.
  Proof with auto.
    intros. intros σ. rewrite <- (insert_delete m x t) at 1...
    pose proof (teval_total σ t) as [v Hv].
    rewrite feval_subst with (v:=v)...
    pose proof (teval_var_term_map_total σ (m)) as [mv Hmv].
    apply teval_var_term_map_delete with (x:=x) in Hmv as H2.
    apply (teval_var_term_map_insert x _ _ Hv) in H2 as H3.
    rewrite feval_msubst with (mv:=<[x:=v]> (delete x mv))...
    rewrite feval_msubst with (mv:=delete x mv)...
    2:{ destruct H2 as []. split... intros. pose proof (H2 x0 t0 v0 H4 H5).
        pose proof (not_elem_of_var_term_map_fvars _ _ H0). apply H7 in H4.
        apply teval_delete_state_var_head... }
    rewrite <- (insert_union_r (delete x mv))...
    - rewrite <- (insert_union_l (delete x mv))...
    - apply lookup_delete.
  Qed.

  Lemma msubst_subst_comm A x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    (x ∉ var_term_map_fvars (delete x m)) →
    msubst (<! A[x \ t] !>) (delete x m) ≡ <! $(msubst A (delete x m)) [x \ t] !>.
  Proof with auto.
    intros. rewrite <- msubst_extract_l'... rewrite <- msubst_extract_r'...
  Qed.

  Lemma msubst_empty A :
    <! A[[∅ \ ∅]] !> ≡ A.
  Proof. unfold to_var_term_map. simpl. rewrite msubst_empty'. reflexivity. Qed.

  Lemma msubst_single A x t :
    <! A[[x \ t]] !> ≡ <! A[x \ t] !>.
  Proof with auto.
    unfold to_var_term_map. simpl. rewrite (msubst_extract_l' A x t _).
    - rewrite delete_insert... rewrite msubst_empty...
    - rewrite lookup_insert...
    - rewrite delete_insert... set_solver.
  Qed.

  Lemma msubst_extract_l A x t xs ts `{OfSameLength _ _ xs ts} :
    x ∉ xs →
    list_to_set xs ## term_fvars t →
    <! A[[x, *xs \ t, *ts]] !> ≡ <! A[x \ t][[*xs \ *ts]] !>.
  Proof with auto.
    intros. unfold to_var_term_map. simpl. rewrite (msubst_extract_l' A x t).
    - rewrite delete_insert... apply lookup_list_to_map_zip_None...
    - rewrite lookup_insert...
    - rewrite dom_delete_L. rewrite dom_insert_L.
      rewrite difference_union_distr_l_L. rewrite difference_diag_L.
      rewrite union_empty_l_L. rewrite dom_list_to_map_zip_L...
      replace (list_to_set xs ∖ {[x]}) with (list_to_set xs : gset variable)...
      apply set_eq. intros y. rewrite elem_of_difference. rewrite elem_of_list_to_set.
      rewrite not_elem_of_singleton. naive_solver.
  Qed.

  Lemma msubst_extract_r A x t xs ts `{OfSameLength _ _ xs ts} :
    x ∉ xs →
    (x ∉ ⋃ (term_fvars <$> ts)) →
    <! A[[x, *xs \ t, *ts]] !> ≡ <! A[[*xs \ *ts]][x \ t] !>.
  Proof with auto.
    intros. unfold to_var_term_map. repeat rewrite app_nil_r.
    simpl. rewrite (msubst_extract_r' A x t).
    - rewrite delete_insert... apply lookup_list_to_map_zip_None...
    - rewrite lookup_insert...
    - intros contra. apply elem_of_var_term_map_fvars in contra as (y&t0&?&?).
      apply H1. apply elem_of_union_list. exists (term_fvars t0). split...
      rewrite delete_insert in H2...
      2:{ apply lookup_list_to_map_zip_None... }
      apply elem_of_list_fmap. apply lookup_list_to_map_zip_Some in H2 as (i&?&?&_)...
      exists t0. split... apply elem_of_list_lookup. exists i...
  Qed.

  Lemma msubst_extract_2 A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x2 ∉ term_fvars t1 →
    <! A[[x1, x2 \ t1, t2]] !> ≡ <! A[x1 \ t1][x2 \ t2] !>.
  Proof with auto.
    intros. rewrite msubst_extract_l with (x:=x1) (xs:=[x2]) (t:=t1) (ts:=[t2]).
    - rewrite msubst_single with (A:=<! A[x1\t1] !>) (x:=x2) (t:=t2)...
    - apply not_elem_of_cons. split... set_solver.
    - rewrite list_to_set_cons. rewrite list_to_set_nil. set_solver.
  Qed.

  Lemma msubst_extract_2' A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    <! A[[x1, x2 \ t1, t2]] !> ≡ <! A[x2 \ t2][x1 \ t1] !>.
  Proof with auto.
    intros. rewrite msubst_extract_r with (x:=x1) (xs:=[x2]) (t:=t1) (ts:=[t2]).
    - rewrite msubst_single with (A:=A) (x:=x2) (t:=t2)...
    - apply not_elem_of_cons. split... set_solver.
    - simpl. set_solver.
  Qed.

  Lemma msubst_dup_keep_l A xs0 ts0 x t xs1 ts1 xs2 ts2
      `{OfSameLength _ _ xs0 ts0} `{OfSameLength _ _ xs1 ts1} `{OfSameLength _ _ xs2 ts2} :
    x ∉ xs1 →
    <! A[[*xs0, x, *xs1, x, *xs2 \ *ts0, t, *ts1, t, *ts2]] !> ≡
      <! A[[*xs0, x, *xs1, *xs2 \ *ts0, t, *ts1, *ts2]] !>.
  Proof with auto.
    intros. unfold to_var_term_map. repeat rewrite app_nil_r. f_equiv.
    repeat rewrite zip_with_app... repeat rewrite list_to_map_app.
    simpl.
    rewrite (map_union_assoc (list_to_map (zip xs1 ts1))).
    rewrite (map_union_comm (list_to_map (zip xs1 ts1))).
    - rewrite (map_union_assoc (<[x:=t]> ∅)). rewrite (map_union_assoc (<[x:=t]> ∅)).
      rewrite map_union_idemp. rewrite <- (map_union_assoc (<[x:=t]> ∅))...
    - rewrite insert_empty. rewrite map_disjoint_singleton_r. apply lookup_list_to_map_zip_None...
  Qed.

  Lemma msubst_dup_keep_r A xs0 ts0 x t xs1 ts1 xs2 ts2
      `{OfSameLength _ _ xs0 ts0} `{OfSameLength _ _ xs1 ts1} `{OfSameLength _ _ xs2 ts2} :
    x ∉ xs1 →
    <! A[[*xs0, x, *xs1, x, *xs2 \ *ts0, t, *ts1, t, *ts2]] !> ≡
      <! A[[*xs0, *xs1, x, *xs2 \ *ts0, *ts1, t, *ts2]] !>.
  Proof with auto.
    intros. unfold to_var_term_map. repeat rewrite app_nil_r. f_equiv.
    repeat rewrite zip_with_app... repeat rewrite list_to_map_app.
    simpl.
    rewrite (map_union_assoc (list_to_map (zip xs1 ts1))).
    rewrite (map_union_comm (list_to_map (zip xs1 ts1))).
    - rewrite (map_union_assoc (<[x:=t]> ∅)). rewrite (map_union_assoc (<[x:=t]> ∅)).
      rewrite map_union_idemp. rewrite <- (map_union_assoc (<[x:=t]> ∅))...
    - rewrite insert_empty. rewrite map_disjoint_singleton_r. apply lookup_list_to_map_zip_None...
  Qed.

  Lemma msubst_comm A xs0 ts0 x1 t1 xs1 ts1 x2 t2 xs2 ts2
      `{OfSameLength _ _ xs0 ts0} `{OfSameLength _ _ xs1 ts1} `{OfSameLength _ _ xs2 ts2} :
    x1 ≠ x2 →
    x1 ∉ xs1 →
    x2 ∉ xs1 →
    <! A[[*xs0, x1, *xs1, x2, *xs2 \ *ts0, t1, *ts1, t2, *ts2]] !> ≡
      <! A[[*xs0, x2, *xs1, x1, *xs2 \ *ts0, t2, *ts1, t1, *ts2]] !>.
  Proof with auto.
    intros. unfold to_var_term_map. repeat rewrite app_nil_r. f_equiv.
    repeat rewrite zip_with_app... repeat rewrite list_to_map_app.
    simpl.
    rewrite (map_union_assoc (list_to_map (zip xs1 ts1))).
    rewrite (map_union_comm (list_to_map (zip xs1 ts1))).
    2:{ rewrite insert_empty. rewrite map_disjoint_singleton_r.
        apply lookup_list_to_map_zip_None... }
    rewrite (map_union_assoc (<[x1:=t1]> ∅)).
    rewrite (map_union_assoc (<[x1:=t1]> ∅)).
    rewrite (map_union_comm (<[x1:=t1]> ∅)).
    2: { rewrite insert_empty. rewrite map_disjoint_singleton_l. rewrite insert_empty.
         apply lookup_singleton_ne... }
    rewrite <- (map_union_assoc (<[x2:=t2]> ∅)).
    rewrite <- (map_union_assoc (<[x2:=t2]> ∅)).
    rewrite (map_union_comm (<[x1:=t1]> ∅)).
    2:{ rewrite insert_empty. rewrite map_disjoint_singleton_l.
        apply lookup_list_to_map_zip_None... }
    rewrite <- (map_union_assoc (list_to_map (zip xs1 ts1)))...
  Qed.

  Lemma msubst_comm_consecutive A xs0 ts0 x1 t1 x2 t2 xs1 ts1
      `{OfSameLength _ _ xs0 ts0} `{OfSameLength _ _ xs1 ts1} :
    x1 ≠ x2 →
    <! A[[*xs0, x1, x2, *xs1 \ *ts0, t1, t2, *ts1]] !> ≡
      <! A[[*xs0, x2, x1, *xs1 \ *ts0, t2, t1, *ts1]] !>.
  Proof with auto.
    intros.
    rewrite msubst_comm with (xs0:=xs0) (ts0:=ts0) (xs1:=nil) (ts1:=nil) (xs2:=xs1) (ts2:=ts1)
                           (x1:=x1) (t1:=t1) (x2:=x2) (t2:=t2)...
    all: apply not_elem_of_nil.
    Unshelve.
    all: typeclasses eauto.
  Qed.

  Lemma msubst_non_free A xs ts `{OfSameLength _ _ xs ts} :
    list_to_set xs ## formula_fvars A →
    <! A[[*xs \ *ts]] !> ≡ A.
  Proof with auto.
    intros. induction A; simp msubst.
    - rewrite msubst_af_non_free...
    - rewrite IHA...
    - rewrite IHA1; [| set_solver]. rewrite IHA2; [| set_solver]...
    - rewrite IHA1; [| set_solver]. rewrite IHA2; [| set_solver]...
    - simpl. generalize_fresh_var_for_msubst x A (to_var_term_map xs ts) as x'.
      unfold to_var_term_map in H5. rewrite dom_list_to_map_zip_L in H5...
      destruct H4.
      + subst. f_equiv. rewrite H1...
        * rewrite fequiv_subst_diag...
        * rewrite fvars_subst_diag. simpl in H0. set_solver.
      + destruct (decide (x ∈ formula_fvars A)).
        * rewrite (fexists_alpha_equiv x x' A)... f_equiv.
          apply H1... rewrite fvars_subst_free... set_solver.
        * rewrite H1...
          2:{ rewrite fvars_subst_non_free... set_solver. }
          rewrite (fexists_alpha_equiv x x' A)...
  Qed.

  Lemma msubst_trans A xs1 xs2 ts `{!OfSameLength xs1 xs2} `{!OfSameLength xs2 ts} `{!OfSameLength xs1 ts} :
    xs1 ## xs2 →
    NoDup xs2 →
    list_to_set xs2 ## formula_fvars A →
    <! A [[*xs1 \ ⇑ₓ₊ xs2]] [[*xs2 \ *ts]] !> ≡ <! A[[*xs1 \ *ts]] !>.
  Proof with auto.
    intros ? Hnodup ?. intros σ.
    opose proof (teval_var_term_map_total σ (to_var_term_map xs1 ts)) as [mv ?].
    opose proof (teval_var_term_map_total σ _) as [mvx2t ?].
    rewrite feval_msubst with (mv:=mvx2t) by exact H2.
    rewrite feval_msubst with (mv:=mv).
    2:{ unfold to_var_term_map in *. destruct H1 as [], H2 as [].
        split.
        - rewrite dom_list_to_map_zip_L in *... typeclasses eauto.
        - intros x1 tx2 v ??. apply lookup_list_to_map_zip_Some in H5 as (i&?&?&?)...
          2:{ typeclasses eauto. }
          apply list_lookup_fmap_Some in H7 as (x2&?&?).
          rewrite H9. clear dependent tx2.
          destruct (lookup_of_same_length_l ts H5) as (t&?).
          ospecialize (H3 x1 t v _ H6).
          { apply lookup_list_to_map_zip_Some... exists i... }
          assert (x2 ∈ dom mvx2t).
          { rewrite H2. rewrite dom_list_to_map_zip_L... apply elem_of_list_to_set.
            apply elem_of_list_lookup_2 in H7... }
          apply elem_of_dom in H10 as [v' ?].
          ospecialize (H4 x2 t v' _ H10).
          { apply lookup_list_to_map_zip_Some... exists i. split_and!... intros. apply H8.
            enough (i = j) by (subst; assumption).
            eapply NoDup_lookup; [exact Hnodup | exact H7 | exact H11].
          }
          pose proof (teval_det _ _ _ H3 H4) as <-.
          constructor. apply (lookup_total_union_l' _ σ)... }
    rewrite map_union_assoc. rewrite (map_union_comm mv).
    2:{ destruct H1 as (?&?), H2 as (?&?). apply map_disjoint_dom. rewrite H1.
        rewrite H2. unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        rewrite dom_list_to_map_zip_L...
        set_solver. }
    rewrite <- map_union_assoc. rewrite feval_delete_state_var_term_map_head.
    2:{ unfold teval_var_term_map in H2. destruct H2 as [-> _]. unfold to_var_term_map.
        rewrite dom_list_to_map_zip_L... }
    rewrite feval_msubst with (mv:=mv)...
  Qed.

  Lemma msubst_msubst_eq A xs ts1 ts2 `{!OfSameLength xs ts1} `{!OfSameLength xs ts2} :
    NoDup xs →
    <! A [[*xs \ *ts1]][[*xs \ *ts2]] !> ≡ <! A [[*xs \ *$((λ t, <! t[[ₜ *xs \ *ts2]] !>) <$> ts1)]] !>.
  Proof with auto.
    intros Hnodup σ.
    opose proof (teval_var_term_map_total σ _) as [mv1 ?].
    rewrite feval_msubst with (mv:=mv1) by exact H.
    opose proof (teval_var_term_map_total _ _) as [mv2 ?].
    rewrite feval_msubst with (mv:=mv2) by exact H0.
    opose proof (teval_var_term_map_total _ _) as [mv3 ?].
    rewrite feval_msubst with (mv:=mv3) by exact H1.
    rewrite map_union_assoc. f_equiv. f_equiv. apply (map_eq _ mv3).
    intros x. destruct H as [], H0 as [], H1 as [].
    destruct (decide (x ∈ xs)).
    2:{ enough (x ∉ dom mv3 ∧ x ∉ dom (mv2 ∪ mv1)).
        - destruct H5. apply not_elem_of_dom in H5, H6. rewrite H5, H6...
        - rewrite dom_union. rewrite H, H0, H1. unfold to_var_term_map.
          rewrite dom_list_to_map_zip_L; [|apply of_same_length_fmap_r].
          rewrite dom_list_to_map_zip_L; [|auto]. rewrite dom_list_to_map_zip_L; [|auto].
          rewrite union_idemp_L. split; set_solver. }
    assert (is_Some (mv2 !! x)).
    { apply elem_of_dom. rewrite H0. unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
      set_solver. }
    rewrite lookup_union_l'... destruct H5 as [v2 ?].
    assert (is_Some (mv3 !! x)) as (v3&?).
    { apply elem_of_dom. rewrite H1. unfold to_var_term_map. rewrite dom_list_to_map_zip_L;
        [set_solver|]. apply of_same_length_fmap_r. }
    rewrite H5, H6. f_equal. apply elem_of_list_lookup in e as (i&?).
    destruct (lookup_of_same_length_l ts1 H7) as (t1&?).
    eapply (@teval_det _ (mv1 ∪ σ)) with (t:=t1).
    - apply H3 with (x:=x)... unfold to_var_term_map. apply lookup_list_to_map_zip_Some...
      exists i. split_and!... intros. eapply NoDup_lookup with (i:=i) in H9... lia.
    - specialize (H4 x <! t1 [[ₜ *xs \ *ts2]] !> v3).
      rewrite <- teval_msubst; [apply H4| split; auto]... unfold to_var_term_map.
      apply lookup_list_to_map_zip_Some.
      { apply of_same_length_fmap_r. }
      exists i. split_and!...
      + apply list_lookup_fmap_Some. exists t1. split...
      + intros. apply NoDup_lookup with (i:=i) in H9... lia.
  Qed.

  (* TODO: move it *)
  Lemma fsubst_fsubst_ne A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    <! A [x1 \ t1][x2 \ t2] !> ≡ <! A [x2 \ t2][x1 \ $(subst_term t1 x2 t2)] !>.
  Proof with auto.
    intros ? Hfree σ.
    opose proof (teval_total σ _) as [v1 ?].
    rewrite feval_subst with (v:=v1) by exact H0.
    opose proof (teval_total _ _) as [v2 ?].
    rewrite feval_subst with (v:=v2) by exact H1.
    opose proof (teval_total σ _) as [v3 ?].
    rewrite feval_subst with (v:=v3) by exact H2.
    opose proof (teval_total _ _) as [v4 ?].
    rewrite feval_subst with (v:=v4) by exact H3.
    f_equiv. unfold state. apply map_eq. intros x.
    destruct (decide (x = x1)); destruct (decide (x = x2)).
    1:{ subst. contradiction. }
    3:{ repeat rewrite lookup_insert_ne... }
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t1).
      + apply H1.
      + erewrite teval_subst; [exact H2|]...
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t2).
      + exact H0.
      + rewrite <- teval_delete_state_var_head; [exact H3|]...
  Qed.

  Lemma msubst_msubst_disj A xs1 ts1 xs2 ts2 `{!OfSameLength xs1 ts1} `{!OfSameLength xs2 ts2} :
    xs1 ## xs2 →
    NoDup xs1 →
    NoDup xs2 →
    list_to_set xs1 ## ⋃ (term_fvars <$> ts2) →
    <! A [[*xs1 \ *ts1]][[*xs2 \ *ts2]] !> ≡ <! A [[*xs2 \ *ts2]] [[*xs1 \ *$((λ t, <! t[[ₜ *xs2 \ *ts2]] !>) <$> ts1)]] !>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 Hfree σ.
    opose proof (teval_var_term_map_total σ _) as [mv1 ?].
    rewrite feval_msubst with (mv:=mv1) by exact H.
    opose proof (teval_var_term_map_total _ _) as [mv2 ?].
    rewrite feval_msubst with (mv:=mv2) by exact H0.
    opose proof (teval_var_term_map_total _ _) as [mv3 ?].
    rewrite feval_msubst with (mv:=mv3) by exact H1.
    opose proof (teval_var_term_map_total _ _) as [mv4 ?].
    rewrite feval_msubst with (mv:=mv4) by exact H2.
    rewrite map_union_assoc. rewrite map_union_assoc.
    f_equiv. f_equiv. apply (map_eq (mv2 ∪ mv1)).
    intros x. destruct H as [], H0 as [], H1 as [], H2 as [].
    destruct (decide (x ∈ xs1 ∨ x ∈ xs2)).
    2:{ apply Decidable.not_or in n as []. enough (x ∉ dom (mv2 ∪ mv1) ∧ x ∉ dom (mv4 ∪ mv3)).
        - destruct H9. apply not_elem_of_dom in H9, H10. rewrite H9, H10...
        - do 2 rewrite dom_union. rewrite H, H0, H1, H2. unfold to_var_term_map.
          rewrite dom_list_to_map_zip_L... rewrite dom_list_to_map_zip_L...
          rewrite dom_list_to_map_zip_L; [|apply of_same_length_fmap_r].
          clear dependent mv1 mv2 mv3 mv4. split; set_solver. }
    destruct o.
    - apply Hdisjoint in H7 as ?.
      assert (is_Some (mv2 !! x)).
      { apply elem_of_dom. rewrite H0. unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        clear dependent mv1 mv2 mv3 mv4. set_solver. }
      assert (is_Some (mv3 !! x)).
      { apply elem_of_dom. rewrite H1. unfold to_var_term_map. clear dependent mv1 mv2 mv3 mv4.
        rewrite dom_list_to_map_zip_L; [set_solver|]. typeclasses eauto. }
      assert (mv4 !! x = None).
      { apply not_elem_of_dom. rewrite H2. unfold to_var_term_map. clear dependent mv1 mv2 mv3 mv4.
        rewrite dom_list_to_map_zip_L; [set_solver|]... }
      rewrite lookup_union_l'... rewrite lookup_union_r... destruct H9 as [v2 ?].
      destruct H10 as [v3 ?]. apply elem_of_list_lookup in H7 as (i&?).
      destruct (lookup_of_same_length_l ts1 H7) as (t&?). rewrite H9, H10. f_equal.
      eapply (@teval_det _ (mv1 ∪ σ)) with (t:=t).
      + apply H4 with (x:=x)... unfold to_var_term_map. apply lookup_list_to_map_zip_Some...
        exists i. split_and!... intros. eapply NoDup_lookup with (i:=i) in H13... lia.
      + specialize (H5 x <! t [[ₜ *xs2 \ *ts2 ]] !> v3).
        rewrite <- teval_msubst; [apply H5| split; auto]... unfold to_var_term_map.
        apply lookup_list_to_map_zip_Some.
        { apply of_same_length_fmap_r. }
        exists i. split_and!...
        * apply list_lookup_fmap_Some. exists t. split...
        * intros. apply NoDup_lookup with (i:=i) in H13... lia.
    - assert (x ∉ xs1) by (intros contra; apply (Hdisjoint x); auto).
      assert (is_Some (mv1 !! x)).
      { apply elem_of_dom. rewrite H. unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        clear dependent mv1 mv2 mv3 mv4. set_solver. }
      assert (is_Some (mv4 !! x)).
      { apply elem_of_dom. rewrite H2. unfold to_var_term_map. clear dependent mv1 mv2 mv3 mv4.
        rewrite dom_list_to_map_zip_L; [set_solver|]. typeclasses eauto. }
      assert (mv2 !! x = None).
      { apply not_elem_of_dom. rewrite H0. unfold to_var_term_map. clear dependent mv1 mv2 mv3 mv4.
        rewrite dom_list_to_map_zip_L; [set_solver|]... }
      rewrite lookup_union_r... destruct H9 as [v1 ?].
      rewrite lookup_union_l'... destruct H10 as [v4 ?].
      apply elem_of_list_lookup in H7 as (i&?).
      destruct (lookup_of_same_length_l ts2 H7) as (t&?). rewrite H9, H10. f_equal.
      eapply (@teval_det _ σ) with (t:=t).
      + apply H3 with (x:=x)... unfold to_var_term_map. apply lookup_list_to_map_zip_Some...
        exists i. split_and!... intros. apply NoDup_lookup with (i:=i) in H13... lia.
      + ospecialize (H6 x t v4 _ _)...
        { unfold to_var_term_map. apply lookup_list_to_map_zip_Some... exists i. split_and!...
          intros. apply NoDup_lookup with (i:=i) in H13... lia. }
        rewrite <- teval_delete_state_var_term_map_head; [exact H6|].
        rewrite H1. unfold to_var_term_map. rewrite dom_list_to_map_zip_L.
        2:{ typeclasses eauto. }
        clear dependent mv1 mv2 mv3 mv4 x. intros x ??. apply Hfree in H.
        apply H. apply elem_of_union_list. apply elem_of_list_lookup_2 in H12.
        set_solver.
  Qed.

End semantics.
