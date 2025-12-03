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
From MRC Require Import PredCalc.FinalElements.

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

  Fixpoint simult_subst_term t m :=
    match t with
    | TConst v => TConst v
    | TVar x =>
        match m !! x with
        | Some t' => t'
        | None => TVar x
        end
    | TApp sym args => TApp sym (map (λ arg, simult_subst_term arg m) args)
    end.

  Definition simult_subst_af af m :=
    match af with
    | AT_Eq t₁ t₂ => AT_Eq (simult_subst_term t₁ m) (simult_subst_term t₂ m)
    | AT_Pred sym args => AT_Pred sym (map (fun arg => simult_subst_term arg m) args)
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

  Definition quant_simult_subst_fvars y A m :=
    (formula_fvars A ∖ {[y]}) ∪ var_term_map_fvars m ∪ dom m.

  Lemma quant_simult_subst_fvars_inv y' y A m :
    y' ∉ quant_simult_subst_fvars y A m →
    (y = y' ∨ y' ∉ formula_fvars A) ∧ (y' ∉ dom m) ∧ (∀ x t, m !! x = Some t → y' ∉ term_fvars t).
  Proof with auto.
    intros. unfold quant_simult_subst_fvars in H. do 2 rewrite not_elem_of_union in H.
    destruct_and! H. split_and!...
    - apply not_elem_of_difference in H. set_solver.
    - apply not_elem_of_var_term_map_fvars...
  Qed.

  Equations? simult_subst A m : formula by wf (rank A) lt :=
    simult_subst (FAtom af) m => FAtom (simult_subst_af af m);
    simult_subst (FNot A) m => FNot (simult_subst A m);
    simult_subst (FAnd A₁ A₂) m => FAnd
                        (simult_subst A₁ m)
                        (simult_subst A₂ m);
    simult_subst (FOr A₁ A₂) m => FOr
                       (simult_subst A₁ m)
                       (simult_subst A₂ m);
    simult_subst (FExists y A) m =>
        let y' := fresh_var y (quant_simult_subst_fvars y A m) in
        FExists y' (simult_subst (<! A[y \ y'] !>) m).
  Proof.
    all: try (simpl; lia).
    unfold rank. simpl. fold Nat.add. pose proof (subst_preserves_shape A y (y')).
    deduce_rank_eq H. rewrite Hfr. rewrite Hqr. lia.
  Qed.

  Definition to_var_term_map (xs : list variable) (ts : list term)
    `{OfSameLength variable term xs ts}: gmap variable term := list_to_map (zip xs ts).

  Local Notation "A [[ xs \ ts ]]" := (simult_subst A (to_var_term_map xs ts))
                                        (in custom formula at level 74, left associativity,
                                            xs custom var_seq,
                                            ts custom term_seq) : refiney_scope.

  Local Tactic Notation "generalize_fresh_var_for_simult_subst"
    ident(y) constr(A) constr(m) "as" ident(y') :=
    let Hfresh := fresh in
    let Heq := fresh in
    let H1 := fresh in let H2 := fresh in let H3 := fresh in
    pose proof (Hfresh := fresh_var_fresh y (quant_simult_subst_fvars y A m));
    apply quant_simult_subst_fvars_inv in Hfresh as (H1&H2&H3);
    remember (fresh_var y (quant_simult_subst_fvars y A m)) as y' eqn:Heq;
    clear Heq.


  Lemma simult_subst_term_id t m :
    dom m ## term_fvars t →
    simult_subst_term t m = t.
  Proof with auto.
    intros H. induction t; simpl...
    - simpl in H. replace (m !! x) with (@None term)... symmetry.
      rewrite <- not_elem_of_dom. set_solver.
    - f_equal. induction args... simpl. f_equal.
      + apply H0; [left; auto | set_solver].
      + apply IHargs; [naive_solver | set_solver].
  Qed.

  Lemma simult_subst_af_id af m :
    dom m ## af_fvars af →
    simult_subst_af af m = af.
  Proof with auto.
    intros H.
    destruct af...
    - simpl. simpl in H. do 2 rewrite simult_subst_term_id by set_solver...
    - simpl. f_equal. induction args... simpl in H. simpl in *. f_equal.
      + rewrite simult_subst_term_id... set_solver.
      + apply IHargs. set_solver.
  Qed.

  Lemma simult_subst_term_empty t :
    simult_subst_term t ∅ = t.
  Proof. apply simult_subst_term_id. set_solver. Qed.

  Lemma simult_subst_af_empty af :
    simult_subst_af af ∅ = af.
  Proof. apply simult_subst_af_id. set_solver. Qed.

  Lemma simult_subst_term_delete_non_free t x m :
    x ∉ term_fvars t →
    simult_subst_term t m = simult_subst_term t (delete x m).
  Proof with auto.
    intros. induction t; simpl...
    - simpl in H. apply not_elem_of_singleton in H. rewrite lookup_delete_ne...
    - f_equal. induction args... simpl. f_equal.
      + apply H0; [naive_solver | set_solver].
      + apply IHargs.
        * intros. apply H0... right...
        * set_solver.
  Qed.

  Lemma simult_subst_af_delete_non_free af x m :
    x ∉ af_fvars af →
    simult_subst_af af m = simult_subst_af af (delete x m).
  Proof with auto.
    intros. destruct af; simpl...
    - rewrite <- simult_subst_term_delete_non_free by set_solver.
      rewrite <- simult_subst_term_delete_non_free by set_solver...
    - f_equal. induction args... simpl. f_equal.
      + rewrite <- simult_subst_term_delete_non_free... set_solver.
      + apply IHargs. set_solver.
  Qed.

  (* TODO: can I replace all teval equiv lemmas with simple equality? Or at least tequiv? *)
  Lemma ssubst_term_non_free t xs ts `{OfSameLength _ _ xs ts} :
    list_to_set xs ## term_fvars t →
    simult_subst_term t (to_var_term_map xs ts) = t.
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

  Lemma ssubst_af_non_free af xs ts `{OfSameLength _ _ xs ts} :
    list_to_set xs ## af_fvars af →
    simult_subst_af af (to_var_term_map xs ts) = af.
  Proof with auto.
    intros. destruct af; simpl in *...
    - rewrite ssubst_term_non_free by set_solver. rewrite ssubst_term_non_free by set_solver...
    - induction args; simpl... f_equal. f_equal.
      + rewrite ssubst_term_non_free by set_solver...
      + forward IHargs by set_solver. inversion IHargs... rewrite H2...
  Qed.

  Lemma fvars_ssubst_term_superset t xs ts `{OfSameLength _ _ xs ts} :
    term_fvars (simult_subst_term t (to_var_term_map xs ts)) ⊆ term_fvars t ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    induction t; simpl; [set_solver| | ].
    - destruct (to_var_term_map xs ts !! x) eqn:E.
      + unfold to_var_term_map in E. apply lookup_list_to_map_zip_Some in E as (i&?&?)...
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

  Lemma fvars_ssubst_af_superset af xs ts `{OfSameLength _ _ xs ts} :
    af_fvars (simult_subst_af af (to_var_term_map xs ts)) ⊆ af_fvars af ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    destruct af; simpl; [set_solver|set_solver | | ].
    - pose proof (fvars_ssubst_term_superset t1 xs ts).
      pose proof (fvars_ssubst_term_superset t2 xs ts). set_solver.
    - induction args.
      + simpl. set_solver.
      + simpl. pose proof (fvars_ssubst_term_superset a xs ts). set_solver.
  Qed.

  Lemma fvars_ssubst_superset A xs ts `{OfSameLength _ _ xs ts} :
    formula_fvars (<! A [[*xs \ *ts]] !>) ⊆ formula_fvars A ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    induction A; simp simult_subst; simpl.
    2-4: set_solver.
    - apply fvars_ssubst_af_superset.
    - generalize_fresh_var_for_simult_subst x A (to_var_term_map xs ts) as x'.
      forward (H0 <! A [x \ x'] !>)...  clear H3 H4 H5.
      destruct (decide (x ∈ formula_fvars A)).
      + rewrite fvars_subst_free in H0... set_solver.
      + rewrite fvars_subst_non_free in H0... set_solver.
  Qed.

  Lemma simpl_ssubst_not A (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (¬ A) [[*xs \ *ts]] !> = <! ¬ (A [[*xs \ *ts]]) !>.
  Proof. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_and A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ∧ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ∧ B [[*xs \ *ts]] !>.
  Proof. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_or A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ∨ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ∨ B [[*xs \ *ts]] !>.
  Proof. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_impl A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ⇒ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ⇒ B [[*xs \ *ts]] !>.
  Proof. unfold FImpl. simp simult_subst. reflexivity. Qed.
  Lemma simpl_ssubst_iff A B (xs : list variable) ts `{OfSameLength _ _ xs ts} :
    <! (A ⇔ B) [[*xs \ *ts]] !> = <! A [[*xs \ *ts]] ⇔ B [[*xs \ *ts]] !>.
  Proof. unfold FIff, FImpl. simp simult_subst. reflexivity. Qed.

  Global Instance ssubst_formula_final {A xs} {ts : list final_term}
      `{FormulaFinal _ A} `{OfSameLength _ _ xs ts} :
    FormulaFinal <! A[[*xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    intros x ?. apply fvars_ssubst_superset in H1. set_unfold. destruct H1 as [|].
    - apply H in H1...
    - apply elem_of_union_list in H1 as (fvars&?&?). set_unfold. destruct H1 as (?&->&t&->&?).
      apply (final_term_final t) in H2...
  Qed.

End syntax.

Notation "A [[ xs \ ts ]]" := (simult_subst A (to_var_term_map xs ts))
                            (in custom formula at level 74, left associativity,
                              xs custom var_seq,
                              ts custom term_seq) : refiney_scope.

Tactic Notation "generalize_fresh_var_for_simult_subst"
    ident(y) constr(A) constr(m) "as" ident(y') :=
  let Hfresh := fresh in
  let Heq := fresh in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in
  pose proof (Hfresh := fresh_var_fresh y (quant_simult_subst_fvars y A m));
  apply quant_simult_subst_fvars_inv in Hfresh as (H1&H2&H3);
  remember (fresh_var y (quant_simult_subst_fvars y A m)) as y' eqn:Heq;
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
    intros. generalize dependent mv. generalize dependent ts. generalize dependent t.
    generalize dependent x. induction xs as [|x' xs' IH]; intros; assert (Hl:=H).
    - apply of_same_length_nil_inv_l in Hl as ->. unfold to_var_term_map in H1. simpl in H1.
      destruct H1 as []. rewrite insert_empty in H1. rewrite dom_singleton_L in H1.
      apply dom_singleton_inv_L in H1 as [v ->]. exists v, ∅. split_and!.
      + eapply H2; [apply lookup_insert|apply lookup_singleton].
      + rewrite map_union_empty...
      + apply not_elem_of_empty.
      + hnf. cbn. split... intros. apply lookup_empty_Some in H1 as [].
    - apply of_same_length_cons_inv_l in Hl as (t'&ts'&->&?).
      apply NoDup_cons in H0 as []. forward (IH x')...
      apply of_same_length_rest in H as Hl. specialize (IH t' ts' Hl).
      destruct H1 as []. unfold to_var_term_map in H1. rewrite dom_list_to_map_zip_L in H1.
      2:{ typeclasses eauto. } rewrite list_to_set_cons in H1.
      apply dom_union_inv_L in H1 as (m1&m2&?&?&?&?).
      2: { set_solver. }
      apply dom_singleton_inv_L in H6 as [v Hv]. subst m1.
      rewrite <- insert_union_singleton_l in H1. subst mv. rename m2 into mv.
      assert (teval_var_term_map σ (to_var_term_map (x' :: xs') (t' :: ts')) mv).
      { split.
        - unfold to_var_term_map. rewrite dom_list_to_map_zip_L...
        - intros. assert (x0 ≠ x).
          { intros contra. subst. apply elem_of_dom_2 in H6. rewrite H7 in H6.
            apply elem_of_list_to_set in H6. contradiction. }
          apply (H4 x0)...
          ++ unfold to_var_term_map. simpl. rewrite lookup_insert_ne...
          ++ rewrite lookup_insert_ne...
      }
      destruct (IH mv) as (v'&mv'&?&?&?&?)...
      exists v, mv. split_and!...
      + apply (H4 x).
          * unfold to_var_term_map. simpl. rewrite lookup_insert...
          * rewrite lookup_insert...
        + rewrite insert_union_singleton_l...
        + set_solver.
  Qed.

  Lemma simult_subst_id A m :
    dom m ## formula_fvars A →
    simult_subst A m ≡ A.
  Proof with auto.
    induction A; simp simult_subst; intros.
    - rewrite simult_subst_af_id...
    - rewrite IHA...
    - rewrite IHA1 by set_solver. rewrite IHA2 by set_solver...
    - rewrite IHA1 by set_solver. rewrite IHA2 by set_solver...
    - simpl. generalize_fresh_var_for_simult_subst x A m as y'.
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

  Lemma teval_simult_subst σ t0 m v0 mv :
    teval_var_term_map σ m mv →
    teval σ (simult_subst_term t0 m) v0 ↔ teval (mv ∪ σ) t0 v0.
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

  Lemma afeval_simult_subst σ af m mv :
    teval_var_term_map σ m mv →
    afeval σ (simult_subst_af af m) ↔ afeval (mv ∪ σ) af.
  Proof with auto.
    intros. destruct af...
    - split; inversion 1; destruct H1 as [].
      + rewrite teval_simult_subst with (mv:=mv) in H1, H2...
        econstructor. split; [exact H1 | exact H2].
      + rewrite <- teval_simult_subst with (m:=m) in H1, H2...
        econstructor. split; [exact H1 | exact H2].
    - split; inversion 1; destruct H1 as [].
      + rename x into vargs. exists vargs. split... clear H0 H2. generalize dependent vargs.
        induction args; intros.
        * inversion H1. subst. constructor.
        * inversion H1; subst. constructor... rewrite <- teval_simult_subst with (m:=m)...
      + rename x into vargs. exists vargs. split... clear H0 H2. generalize dependent vargs.
        induction args; intros.
        * inversion H1. subst. constructor.
        * inversion H1; subst. constructor... rewrite teval_simult_subst with (mv:=mv)...
  Qed.

  Lemma feval_simult_subst σ A m mv :
    teval_var_term_map σ m mv →
    feval σ (simult_subst A m) ↔ feval (mv ∪ σ) A.
  Proof with auto.
    intros. generalize dependent σ. induction A; intros σ Hteval; simp simult_subst; simp feval.
    - apply afeval_simult_subst...
    - rewrite IHA...
    - rewrite IHA1... rewrite IHA2...
    - rewrite IHA1... rewrite IHA2...
    - apply exists_iff_exists_weaken. intros v. destruct Hteval as [H1 H2]. rename H into IH.
      generalize_fresh_var_for_simult_subst x A m as x'. rewrite feval_subst with (v:=v)...
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

  Lemma teval_delete_state_var_term_map_head σ t m mv v :
    teval_var_term_map σ m mv →
    dom mv ## term_fvars t →
    teval σ t v ↔ teval (mv ∪ σ) t v.
  Proof with auto.
    intros. rewrite <- teval_simult_subst with (m:=m)...
    rewrite simult_subst_term_id... rewrite <- (proj1 H)...
  Qed.

  Lemma afeval_delete_state_var_term_map_head σ af m mv :
    teval_var_term_map σ m mv →
    dom mv ## af_fvars af →
    afeval σ af ↔ afeval (mv ∪ σ) af.
  Proof with auto.
    intros. rewrite <- afeval_simult_subst with (m:=m)...
    rewrite simult_subst_af_id... rewrite <- (proj1 H)...
  Qed.

  Lemma feval_delete_state_var_term_map_head σ A m mv :
    teval_var_term_map σ m mv →
    dom mv ## formula_fvars A →
    feval σ A ↔ feval (mv ∪ σ) A.
  Proof with auto.
    intros. rewrite <- feval_simult_subst with (m:=m)...
    rewrite simult_subst_id... rewrite <- (proj1 H)...
  Qed.

  Lemma simult_subst_empty A :
    simult_subst A ∅ ≡ A.
  Proof. apply simult_subst_id. set_solver. Qed.

  Lemma simult_subst_delete_non_free A x m :
    x ∉ formula_fvars A →
    simult_subst A m ≡ simult_subst A (delete x m).
  Proof with auto.
    intros H σ. destruct (m !! x) eqn:E.
    2:{ rewrite delete_notin... }
    rewrite <- (insert_delete m x t) at 1...
    pose proof (teval_var_term_map_total σ m) as [mv Hmv].
    apply teval_var_term_map_delete with (x:=x) in Hmv as H1.
    pose proof (teval_total σ t) as [v Hv].
    apply (teval_var_term_map_insert x t v Hv) in H1 as H2.
    rewrite feval_simult_subst with (mv:=(<[x:=v]> (delete x mv)))...
    rewrite feval_simult_subst with (mv:=(delete x mv))...
    rewrite <- (insert_union_l _ σ). rewrite feval_delete_state_var_head...
  Qed.

  Lemma simult_subst_term_extract t0 x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    (x ∉ var_term_map_fvars (delete x m)) →
    simult_subst_term t0 m = simult_subst_term (subst_term t0 x t) (delete x m).
  Proof with auto.
    induction t0; simpl; intros...
    - destruct (decide (x0 = x)).
      + subst. rewrite H. rewrite simult_subst_term_id...
      + simpl. rewrite lookup_delete_ne...
    - f_equal. induction args... simpl. f_equal.
      + apply H... left...
      + apply IHargs. intros. apply H... right...
  Qed.

  Lemma simult_subst_af_extract af x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    (x ∉ var_term_map_fvars (delete x m)) →
    simult_subst_af af m = simult_subst_af (subst_af af x t) (delete x m).
  Proof with auto.
    destruct af; simpl; intros...
    - simpl. f_equal; apply simult_subst_term_extract...
    - simpl. f_equal. induction args... simpl. f_equal...
      apply simult_subst_term_extract...
  Qed.

  Lemma simult_subst_extract_l A x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    simult_subst A m ≡ simult_subst (<! A[x \ t] !>) (delete x m).
  Proof with auto.
    intros. intros σ. rewrite <- (insert_delete m x t) at 1...
    pose proof (teval_total σ t) as [v Hv].
    pose proof (teval_var_term_map_total σ (m)) as [mv Hmv].
    apply teval_var_term_map_delete with (x:=x) in Hmv as H2.
    apply (teval_var_term_map_insert x _ _ Hv) in H2 as H3.
    rewrite feval_simult_subst with (mv:=<[x:=v]> (delete x mv))...
    rewrite feval_simult_subst with (mv:=delete x mv)...
    assert (Hv':=Hv).
    rewrite teval_delete_state_var_term_map_head with (m:=delete x m) (mv:=delete x mv) in Hv'...
    2: { rewrite (proj1 H2)... }
    rewrite feval_subst with (v:=v)... rewrite (insert_union_l (delete x mv))...
  Qed.

  Lemma simult_subst_extract_r A x t m :
    m !! x = Some t →
    (x ∉ var_term_map_fvars (delete x m)) →
    simult_subst A m ≡ <! $(simult_subst A (delete x m)) [x \ t] !>.
  Proof with auto.
    intros. intros σ. rewrite <- (insert_delete m x t) at 1...
    pose proof (teval_total σ t) as [v Hv].
    rewrite feval_subst with (v:=v)...
    pose proof (teval_var_term_map_total σ (m)) as [mv Hmv].
    apply teval_var_term_map_delete with (x:=x) in Hmv as H2.
    apply (teval_var_term_map_insert x _ _ Hv) in H2 as H3.
    rewrite feval_simult_subst with (mv:=<[x:=v]> (delete x mv))...
    rewrite feval_simult_subst with (mv:=delete x mv)...
    2:{ destruct H2 as []. split... intros. pose proof (H2 x0 t0 v0 H4 H5).
        pose proof (not_elem_of_var_term_map_fvars _ _ H0). apply H7 in H4.
        apply teval_delete_state_var_head... }
    rewrite <- (insert_union_r (delete x mv))...
    - rewrite <- (insert_union_l (delete x mv))...
    - apply lookup_delete.
  Qed.

  Lemma simult_subst_subst_comm A x t m :
    m !! x = Some t →
    dom (delete x m) ## term_fvars t →
    (x ∉ var_term_map_fvars (delete x m)) →
    simult_subst (<! A[x \ t] !>) (delete x m) ≡ <! $(simult_subst A (delete x m)) [x \ t] !>.
  Proof with auto.
    intros. rewrite <- simult_subst_extract_l... rewrite <- simult_subst_extract_r...
  Qed.

  Lemma ssubst_empty A :
    <! A[[∅ \ ∅]] !> ≡ A.
  Proof. unfold to_var_term_map. simpl. rewrite simult_subst_empty. reflexivity. Qed.

  Lemma ssubst_single A x t :
    <! A[[x \ t]] !> ≡ <! A[x \ t] !>.
  Proof with auto.
    unfold to_var_term_map. simpl. rewrite (simult_subst_extract_l A x t _).
    - rewrite delete_insert... rewrite simult_subst_empty...
    - rewrite lookup_insert...
    - rewrite delete_insert... set_solver.
  Qed.

  Lemma ssubst_extract_l A x t xs ts `{OfSameLength _ _ xs ts} :
    x ∉ xs →
    list_to_set xs ## term_fvars t →
    <! A[[x, *xs \ t, *ts]] !> ≡ <! A[x \ t][[*xs \ *ts]] !>.
  Proof with auto.
    intros. unfold to_var_term_map. simpl. rewrite (simult_subst_extract_l A x t).
    - rewrite delete_insert... apply lookup_list_to_map_zip_None...
    - rewrite lookup_insert...
    - rewrite dom_delete_L. rewrite dom_insert_L.
      rewrite difference_union_distr_l_L. rewrite difference_diag_L.
      rewrite union_empty_l_L. rewrite dom_list_to_map_zip_L...
      replace (list_to_set xs ∖ {[x]}) with (list_to_set xs : gset variable)...
      apply set_eq. intros y. rewrite elem_of_difference. rewrite elem_of_list_to_set.
      rewrite not_elem_of_singleton. naive_solver.
  Qed.

  Lemma ssubst_extract_r A x t xs ts `{OfSameLength _ _ xs ts} :
    x ∉ xs →
    (x ∉ ⋃ (term_fvars <$> ts)) →
    <! A[[x, *xs \ t, *ts]] !> ≡ <! A[[*xs \ *ts]][x \ t] !>.
  Proof with auto.
    intros. unfold to_var_term_map. repeat rewrite app_nil_r.
    simpl. rewrite (simult_subst_extract_r A x t).
    - rewrite delete_insert... apply lookup_list_to_map_zip_None...
    - rewrite lookup_insert...
    - intros contra. apply elem_of_var_term_map_fvars in contra as (y&t0&?&?).
      apply H1. apply elem_of_union_list. exists (term_fvars t0). split...
      rewrite delete_insert in H2...
      2:{ apply lookup_list_to_map_zip_None... }
      apply elem_of_list_fmap. apply lookup_list_to_map_zip_Some in H2 as (i&?&?)...
      exists t0. split... apply elem_of_list_lookup. exists i...
  Qed.

  Lemma ssubst_extract_2 A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x2 ∉ term_fvars t1 →
    <! A[[x1, x2 \ t1, t2]] !> ≡ <! A[x1 \ t1][x2 \ t2] !>.
  Proof with auto.
    intros. rewrite ssubst_extract_l with (x:=x1) (xs:=[x2]) (t:=t1) (ts:=[t2]).
    - rewrite ssubst_single with (A:=<! A[x1\t1] !>) (x:=x2) (t:=t2)...
    - apply not_elem_of_cons. split... set_solver.
    - rewrite list_to_set_cons. rewrite list_to_set_nil. set_solver.
  Qed.

  Lemma ssubst_extract_2' A x1 t1 x2 t2 :
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    <! A[[x1, x2 \ t1, t2]] !> ≡ <! A[x2 \ t2][x1 \ t1] !>.
  Proof with auto.
    intros. rewrite ssubst_extract_r with (x:=x1) (xs:=[x2]) (t:=t1) (ts:=[t2]).
    - rewrite ssubst_single with (A:=A) (x:=x2) (t:=t2)...
    - apply not_elem_of_cons. split... set_solver.
    - simpl. set_solver.
  Qed.

  Lemma ssubst_dup_keep_l A xs0 ts0 x t xs1 ts1 xs2 ts2
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

  Lemma ssubst_dup_keep_r A xs0 ts0 x t xs1 ts1 xs2 ts2
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

  Lemma ssubst_comm A xs0 ts0 x1 t1 xs1 ts1 x2 t2 xs2 ts2
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

  Lemma ssubst_comm_consecutive A xs0 ts0 x1 t1 x2 t2 xs1 ts1
      `{OfSameLength _ _ xs0 ts0} `{OfSameLength _ _ xs1 ts1} :
    x1 ≠ x2 →
    <! A[[*xs0, x1, x2, *xs1 \ *ts0, t1, t2, *ts1]] !> ≡
      <! A[[*xs0, x2, x1, *xs1 \ *ts0, t2, t1, *ts1]] !>.
  Proof with auto.
    intros.
    rewrite ssubst_comm with (xs0:=xs0) (ts0:=ts0) (xs1:=nil) (ts1:=nil) (xs2:=xs1) (ts2:=ts1)
                           (x1:=x1) (t1:=t1) (x2:=x2) (t2:=t2)...
    all: apply not_elem_of_nil.
    Unshelve.
    all: typeclasses eauto.
  Qed.

  Lemma ssubst_non_free A xs ts `{OfSameLength _ _ xs ts} :
    list_to_set xs ## formula_fvars A →
    <! A[[*xs \ *ts]] !> ≡ A.
  Proof with auto.
    intros. induction A; simp simult_subst.
    - rewrite ssubst_af_non_free...
    - rewrite IHA...
    - rewrite IHA1; [| set_solver]. rewrite IHA2; [| set_solver]...
    - rewrite IHA1; [| set_solver]. rewrite IHA2; [| set_solver]...
    - simpl. generalize_fresh_var_for_simult_subst x A (to_var_term_map xs ts) as x'.
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

End semantics.
