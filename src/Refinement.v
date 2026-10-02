From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
From MRC Require Import Prelude.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import ListBag.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section refinement.
  Context {M : model}.
  Context `{MNat : ModelWithNat M}.
  Local Notation value := (value M).
  Local Notation prog := (prog M).
  Local Notation state := (state M).
  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  Implicit Types gcs : list final_formula.
  Implicit Types g : final_formula.
  Implicit Types rhs : list (@asgn_rhs_term M).
  Implicit Types p : prog.
  (* Implicit Types ts : list term. *)

  Lemma seqsubst_extract_l (A : formula) x t (xs : list variable) ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[;x, *xs \ t, *ts;] !> ≡ <! A[x \ t][;*xs \ *ts;] !>.
  Proof with auto.
    intros. simpl.
    induction_same_length xs ts as y u...
    intros. simpl. unfold OfSameLength in H'. simpl in H'. inversion H'.
    apply not_elem_of_cons in H as []. rewrite <- IH...
    2-3: set_solver.
    rewrite fequiv_subst_comm...
    - f_equiv. f_equiv. f_equiv. apply eq_pi. solve_decision.
    - set_solver.
    - set_solver.
  Qed.
  Lemma seqsubst_extract_r (A : formula) x t (xs : list variable) ts `{!OfSameLength xs ts} :
    <! A[;x, *xs \ t, *ts;] !> ≡ <! A[;*xs \ *ts;][x \ t] !>.
  Proof with auto. intros. simpl. repeat f_equiv. apply eq_pi. solve_decision. Qed.
  Lemma seqsubst_subst_comm (A : formula) x t (xs : list variable) ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[;*xs \ *ts;][x \ t] !> ≡ <! A[x \ t][;*xs \ *ts;] !>.
  Proof with auto.
    intros. rewrite <- seqsubst_extract_l... rewrite seqsubst_extract_r. reflexivity.
  Qed.

  Global Instance seqsubst_formula_final {A} {xs : list variable} {ts}
      `{!FormulaFinal A} `{!OfSameLength xs (⇑ₜ ts)} :
    FormulaFinal <! A[;*xs \ ⇑ₜ ts;] !>.
  Proof with auto.
    intros x ?. apply fvars_seqsubst_superset in H. set_unfold. destruct H as [|].
    - apply formula_is_final in H...
    - destruct H as (?&?&?&->&?). apply final_term_final in H...
  Qed.

  Global Instance seqsubst_formula_final' {A} {xs : list variable} {ys}
      `{!FormulaFinal A} `{!OfSameLength xs (⇑ₓ ys)} :
    FormulaFinal <! A[;*xs \ ⇑ₓ ys;] !>.
  Proof with auto.
    intros x ?. apply fvars_seqsubst_superset in H. set_unfold. destruct H as [|].
    - apply formula_is_final in H...
    - destruct H...
  Qed.

  Lemma fequiv_st_lem σ A B :
    A ≡_{σ} B ∨ ¬ A ≡_{σ} B.
  Proof with auto.
    destruct (feval_lem σ A); destruct (feval_lem σ B).
    - left. done.
    - right. intros []...
    - right. intros []...
    - left. done.
  Qed.

  Lemma finalized_initial_fvars_final A `{!FormulaFinal A} :
    finalized_initial_fvars A = [].
  Proof with auto.
    enough (finalized_initial_fvars A ≡ₚ []).
    { by apply Permutation_nil_r in H. }
    unfold finalized_initial_fvars, initial_fvars.
    rename FormulaFinal0 into H. unfold FormulaFinal, formula_final in H.
    induction (formula_fvars A) using set_ind_L...
    rewrite filter_set_to_list_delete_union_singleton_l.
    - apply IHg. set_solver.
    - apply var_final_not_initial. set_solver.
  Qed.

  Lemma subst_all_initials_id {A} `{!FormulaFinal A} :
    <! A[_₀\*] !> ≡ A.
  Proof with auto.
    unfold subst_all_initials.
    enough (finalized_initial_fvars A = []) as -> by (by rewrite subst_initials_nil).
    apply finalized_initial_fvars_final...
  Qed.

  Lemma subst_initials_cons_dup A (x : final_variable) (xs : list final_variable) :
    x ∈ xs →
    <! A[_₀\ (x :: xs)] !> ≡ <! A[_₀\ xs] !>.
  Proof with auto.
    intros. rewrite subst_initials_cons. rewrite subst_non_free... set_solver.
  Qed.

  Hint Extern 0 (<! _[_₀\[]] !>) => rewrite subst_initials_nil : core.

  Definition initials_closed A w := ∀ x, x ∉ w → <! A [₀x\x] !> ≡ A.

  Lemma initials_closed_alt' A w :
    initials_closed A w ↔
    ∀ x, x ∉ w → ₀x ∈ formula_fvars A → <! A [₀x\x] !> ≡ A.
  Proof with auto.
    unfold initials_closed; split; intros... destruct (decide (₀x ∈ formula_fvars A)).
    - rewrite H...
    - rewrite subst_non_free...
  Qed.

  Lemma initials_closed_alt A w :
    (∀ x, var_initial x → x ∈ formula_fvars A → to_final_var x ∈ w) →
    initials_closed A w.
  Proof.
    rewrite initials_closed_alt'. intros H x??. ospecialize (H ₀x _ H1); [done|].
    by rewrite to_final_var_initial_var_of in H.
  Qed.

  Global Instance initials_closed_proper : Proper ((=) ==> (≡ₚ) ==> iff) initials_closed.
  Proof.
    intros A ? -> w1 w2 ?. unfold initials_closed. by setoid_rewrite H.
  Qed.

  Lemma initials_closed_final A `{!FormulaFinal A} :
    ∀ w, initials_closed A w.
  Proof.
    setoid_rewrite initials_closed_alt'. intros w x ??.
    apply formula_is_final in H0. by apply var_final_not_initial in H0.
  Qed.

  Hint Extern 5 (initials_closed _ _) => apply initials_closed_final : core.


  Lemma initials_closed_app_inv_r A w1 w2 :
    initials_closed A (w1 ++ w2) →
    initials_closed (<! A[_₀\w2] !>) w1.
  Proof with auto.
    do 2 rewrite initials_closed_alt'. intros.
    rewrite <- subst_initials_cons. rewrite subst_initials_cons_l.
    destruct (decide (₀x ∈ formula_fvars A)).
    - specialize (H x). rewrite H... set_solver.
    - rewrite subst_non_free...
  Qed.

  Lemma initials_closed_app_inr A w1 w2 :
    initials_closed A w2 →
    initials_closed A (w1 ++ w2).
  Proof with auto. unfold initials_closed in *. intros. apply H. set_solver. Qed.

  Lemma initials_closed_app_inl A w1 w2 :
    initials_closed A w1 →
    initials_closed A (w1 ++ w2).
  Proof with auto. unfold initials_closed in *. intros. apply H. set_solver. Qed.

  Hint Extern 1 =>
    match goal with
    | H : initials_closed ?A (?w1 ++ ?w2) |- initials_closed <! ?A[_₀\?w2] !> ?w1 =>
        apply initials_closed_app_inv_r in H; exact H
    end : core.

  Hint Extern 1 =>
    match goal with
    | H : initials_closed ?A ?w1 |- initials_closed ?A (?w1 ++ _) =>
        apply initials_closed_app_inl; exact H
    end : core.

  Hint Extern 1 =>
    match goal with
    | H : initials_closed ?A ?w2 |- initials_closed ?A (_ ++ ?wp2) =>
        apply initials_closed_app_inr; exact H
    end : core.

  Lemma Permutation_app_cons_r_comm {A : Type} {x : A} {X Y : list A} :
    X ++ x :: Y ≡ₚ x :: X ++ Y.
  Proof. rewrite Permutation_app_comm. simpl. by rewrite Permutation_app_comm. Qed.

  Lemma subseteq_cons_not_in {A : Type} {x : A} {X Y : list A} :
    x ∉ X →
    x ∉ Y →
    X ⊆ Y ↔ x :: X ⊆ x :: Y.
  Proof. intros. set_solver. Qed.

  Lemma subst_all_initials_weaken A w :
    finalized_initial_fvars A ⊆ w →
    <! A[_₀\*] !> ≡ <! A[_₀\w] !>.
  Proof with auto.
    intros. generalize dependent A. unfold subst_all_initials. induction w as [|x w]; intros.
    - apply list_nil_subseteq in H. rewrite H...
    - destruct (decide (x ∈ w)).
      { rewrite subst_initials_cons_dup... apply IHw. set_solver. }
      destruct (decide (x ∈ finalized_initial_fvars A)).
      + pose proof (finalized_initial_fvars_NoDup A).
        apply elem_of_list_In in e. apply in_split in e as (l1&l2&?).
        rewrite H1 in *. apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as [].
        rewrite Permutation_app_cons_r_comm in *. do 2 rewrite subst_initials_cons_l.
        enough (l1 ++ l2 ≡ₚ finalized_initial_fvars <! A [₀x \ x] !>).
        * rewrite H5. apply IHw. rewrite <- H5. set_solver.
        * rewrite finalized_initial_fvars_subst_perm.
          -- rewrite H1. rewrite Permutation_app_cons_r_comm. rewrite delete_cons.
             rewrite delete_eq by set_solver. apply subseteq_cons_not_in in H...
             set_solver.
          -- assert (x ∈ finalized_initial_fvars A) by (rewrite H1; set_solver).
             set_solver.
      + rewrite subst_initials_cons_l. rewrite subst_non_free; [apply IHw|]; set_solver.
  Qed.

  Lemma subst_all_initials_closed A w :
    initials_closed A w →
    <! A[_₀\*] !> ≡ <! A[_₀\w] !>.
  Proof with auto.
    unfold subst_all_initials. rewrite initials_closed_alt'.
    remember (finalized_initial_fvars A) as la eqn:E.
    assert (<! A[_₀\la] !> ≡ <! A [_₀\finalized_initial_fvars A] !>) by (by subst).
    clear E. revert H. revert la. generalize dependent A.
    induction w as [|x w]; intros.
    - induction la as [|x la]... rewrite subst_initials_cons_l in H |- *.
      destruct (decide (₀x ∈ formula_fvars A)).
      + rewrite H0 in H |- *...
        1,2: set_solver.
      + rewrite subst_non_free in H |- *...
    - destruct (decide (x ∈ w)).
      { rewrite subst_initials_cons_dup... apply IHw... set_solver. }
      destruct (decide (x ∈ finalized_initial_fvars A)).
      + assert (e':=e). set_unfold in e'. pose proof (finalized_initial_fvars_NoDup A).
        apply elem_of_list_In in e. apply in_split in e as (l1&l2&?).
        rewrite H2 in *. apply NoDup_app in H1 as (?&?&?). apply NoDup_cons in H4 as [].
        rewrite Permutation_app_cons_r_comm in *. rewrite H.
        do 2 rewrite subst_initials_cons_l.
        enough (l1 ++ l2 ≡ₚ finalized_initial_fvars <! A [₀x \ x] !>).
        * rewrite H6. apply IHw... intros. rewrite fvars_subst in H8...
          set_unfold in H8. destruct H8 as [[] |].
          -- rewrite fequiv_subst_comm by (auto; set_solver).
             rewrite H0... set_solver.
          -- apply initial_var_of_eq_final_variable in H8 as [].
        * rewrite finalized_initial_fvars_subst_perm.
          -- rewrite H2. rewrite Permutation_app_cons_r_comm. rewrite delete_cons.
             rewrite delete_eq by set_solver...
          -- assert (x ∈ finalized_initial_fvars A) by (rewrite H2; set_solver).
             set_solver.
      + rewrite subst_initials_cons_l. rewrite subst_non_free; [apply IHw|]; set_solver.
    Qed.

  Lemma subst_initials_closed_disjoint A w1 w2 :
    initials_closed A w1 →
    w1 ## w2 →
    <! A[_₀\w2] !> ≡ <! A !>.
  Proof with auto.
    induction w2 as [|x w2]... intros. assert (x ∉ w1) by set_solver.
    rewrite subst_initials_cons_l. rewrite (H x)... apply IHw2...
    set_solver.
  Qed.

  Lemma wp_spec w (pre : final_formula) post A `{!FormulaFinal A} :
    initials_closed post w →
    wp (PSpec w pre post) A ≡ <! pre ∧ (∀* ↑ₓ w, post ⇒ A) [_₀\ w] !>.
  Proof with auto.
    intros. simpl. f_equiv. apply subst_all_initials_closed. rewrite initials_closed_alt'.
    intros y??. set_unfold in H1. unfold initials_closed in H.
    destruct H1. destruct H1.
    2:{ apply formula_is_final in H1. apply var_final_initial_var_of in H1 as []. }
    rewrite simpl_subst_foralllist...
    - rewrite simpl_subst_impl. rewrite subst_non_free with (A:=A).
      + rewrite H...
      + intros contra. apply formula_is_final in contra.
        apply var_final_initial_var_of in contra as [].
    - set_unfold. intros (x&?&_). apply initial_var_of_eq_final_variable in H3 as [].
    - simpl. intros i??. set_unfold in H4. subst i. apply elem_of_set_to_list in H3.
      apply elem_of_set_to_list in H3. apply elem_of_list_to_set in H3.
      set_solver.
  Qed.

  Lemma wp_spec' w (pre : final_formula) post A `{!FormulaFinal A} :
    initials_closed post w →
    <! pre ∧ (∀* ↑ₓ w, post ⇒ A) [_₀\*] !> ≡ <! pre ∧ (∀* ↑ₓ w, post ⇒ A) [_₀\ w] !>.
  Proof using M MNat. intros. pose proof (wp_spec). simpl in H0. apply H0; auto. Qed.

  (* TODO: reorder laws *)
  (* 1.8 *)
  Lemma r_absorb_assumption pre' w pre post `{!FormulaFinal pre'} `{!FormulaFinal pre} :
    <{ {pre'}; *w : [pre, post] }> ≡ <{ *w : [pre' ∧ pre, post] }>.
  Proof with auto.
    intros A. simpl. rewrite subst_all_initials_id.
    fSimpl. rewrite f_and_assoc...
  Qed.

  (* Law 1.1 *)
  Lemma r_strengthen_post w pre post post' `{!FormulaFinal pre} :
    initials_closed post w →
    initials_closed post' w →
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros ?? Hent A. do 2 (rewrite wp_spec; auto). simpl. fSimpl. rewrite <- Hent...
  Qed.

  (* Law 5.1 *)
  Lemma r_strengthen_post_with_initials w pre post post' `{!FormulaFinal pre} :
    initials_closed post w →
    initials_closed post' w →
    <! pre[; ↑ₓ w \ ⇑₀ w ;] ∧ post' !> ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros ?? Hent A. do 2 (rewrite wp_spec; auto). simpl.
    rewrite <- Hent. rewrite <- f_impl_curry. rewrite -> f_foralllist_impl_unused_l.
    2: { intros x ? ?. apply (fvars_seqsubst_superset_vars_not_free_in_terms) in H2...
         set_solver. }
    rewrite simpl_subst_initials_impl. rewrite subst_initials_inverse_l by set_solver...
    rewrite <- (f_and_idemp pre) at 1. rewrite <- f_and_assoc. fSimpl...
  Qed.

  (* Law 1.2 *)
  Lemma r_weaken_pre w pre pre' post `{!FormulaFinal pre} `{!FormulaFinal pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A. simpl. fSimpl. assumption.
  Qed.

  (* Law 1.7 *)
  Lemma r_simple_spec x t `{!TermFinal t} :
    as_var x ∉ term_fvars t →
    <{ x := t }> ≡ <{ x : [⌜x = t⌝] }>.
  Proof with auto.
    intros Hfree A. rewrite wp_spec... simpl. fSimpl.
    unfold subst_all_initials, subst_initials. rewrite seqsubst_non_free.
    - rewrite f_forall_one_point... apply msubst_single.
    - simpl. set_unfold. intros. destruct H; [|done]. destruct H0.
      assert (¬ var_final x0).
      { unfold var_final. subst. simpl. done. }
      destruct_or! H0; try done.
      + rename TermFinal0 into H3. unfold TermFinal, term_final in H3. by apply H3 in H0.
      + pose proof (final_formula_final A). unfold formula_final in H3. by apply H3 in H0.
  Qed.

  Lemma r_permute_frame w w' pre post `{!FormulaFinal pre} :
    initials_closed post w →
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros ? H A. do 2 (rewrite wp_spec; auto).
    2: { rewrite <- H... }
    simpl. fSimpl.
    rewrite subst_initials_perm with (xs':=w')... f_equiv.
    rewrite f_foralllist_permute with (xs':=(fmap as_var w'))... apply Permutation_map...
  Qed.

  (* Law 5.4 *)
  Lemma r_contract_frame w xs pre post `{!FormulaFinal pre} :
    initials_closed post (w ++ xs) →
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs]] }>.
  Proof with auto.
    intros ? Hdisjoint A. do 2 (rewrite wp_spec; auto).
    simpl. fSimpl. rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist by set_solver.
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    fSimpl. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 8.3 *)
  Lemma r_expand_frame xs w pre post `{!FormulaFinal pre} :
    initials_closed post w →
    w ## xs →
    <{ *w : [pre, post] }> ⊑ <{ *w, *xs : [pre, post ∧ ⎡⇑ₓ xs =* ⇑₀ xs⎤] }>.
  Proof with auto.
    intros Hclosed Hdisjoint A.
    pose proof (subst_initials_closed_disjoint _ _ _ Hclosed Hdisjoint) as H.
    do 2 (rewrite wp_spec; auto)...
    2:{ intros y?. rewrite simpl_subst_and. rewrite (Hclosed y) by set_solver.
        rewrite subst_non_free... contradict H0. rewrite fvars_eqlist in H0.
        set_unfold in H0. rewrite to_final_var_initial_var_of in H0. set_solver. }
    simpl. fSimpl.
    unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite <- f_foralllist_one_point...
    setoid_rewrite <- (@eqlist_rewrite _ _ (⇑₀ (w ++ xs))).
    2-3: do 2 rewrite fmap_app; reflexivity.
    rewrite f_eqlist_app. rewrite fmap_app. rewrite foralllist_app.
    rewrite <- f_impl_curry. rewrite (f_foralllist_impl_unused_l (↑₀ xs)).
    2:{ intros ???. rewrite fvars_eqlist in H1. set_solver. }
    f_equiv. f_equiv.
    rewrite f_and_comm. rewrite <- f_impl_curry.
    rewrite fmap_app. rewrite foralllist_app.
    rewrite f_foralllist_comm.
    rewrite (f_foralllist_impl_unused_l (↑ₓ w) _ <! post ⇒ A !>).
    2:{ intros ???. rewrite fvars_eqlist in H1. set_solver. }
    setoid_rewrite (f_foralllist_one_point (↑ₓ xs))...
    rewrite f_foralllist_one_point... setoid_rewrite <- H at 2. rewrite fold_subst_initials.
    rewrite subst_initials_inverse_l...
    1: { rewrite H... }
    intros x ??. set_unfold. destruct H1. clear H2.
    destruct H1 as [[[] |] |]; [set_solver|set_solver|].
    apply formula_is_final in H1. naive_solver.
    Unshelve. all: typeclasses eauto.
  Qed.

  (* TODO: move me *)
  Global Instance set_unfold_initial_var_elem_of_final_formula {x} {A} `{!FormulaFinal A} :
    SetUnfoldElemOf ₀x (formula_fvars A) False.
  Proof with auto.
    constructor. split; intros; [|done]. apply formula_is_final in H.
    apply var_final_initial_var_of in H as [].
  Qed.

  (* Law 3.2 *)
  Lemma r_skip w pre post `{!FormulaFinal pre} :
    initials_closed post w →
    pre ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. rewrite wp_spec... simpl.
    fSimpl. rewrite subst_all_initials_weaken with (w:=[]) by set_solver.
    rewrite subst_initials_nil. rewrite <- (f_subst_initials_final_formula pre w)...
    unfold subst_initials. simpl. do 2 rewrite fold_subst_initials.
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite H0. rewrite f_impl_elim. rewrite f_foralllist_one_point...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 5.3 *)
  Lemma r_skip_with_initials w pre post `{!FormulaFinal pre} :
    initials_closed post w →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ pre !> ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. rewrite wp_spec... simpl. unfold subst_initials. simpl.
    rewrite fold_subst_initials.
    fSimpl. rewrite subst_all_initials_weaken with (w:=[]) by set_solver.
    rewrite subst_initials_nil. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite f_impl_dup_hyp. rewrite f_and_assoc. rewrite H0. rewrite f_impl_elim.
    rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 3.4 *)
  Lemma r_skip_seq_l p :
    <{ $skip; $p }> ≡ p.
  Proof with auto.
    intros A. simpl. rewrite subst_all_initials_weaken with (w:=[]) by set_solver. fSimpl...
  Qed.

  (* Law 3.4 *)
  Lemma r_skip_seq_r p :
    <{ $p; $skip }> ≡ p.
  Proof with auto.
    intros A. simpl. apply wp_congr...
    rewrite subst_all_initials_weaken with (w:=[]) by set_solver. fSimpl...
  Qed.

  (* Law 3.3 *)
  Lemma r_seq w pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} `{!FormulaFinal post} :
    initials_closed mid w →
    initials_closed post w →
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, mid]; *w : [mid, post] }>.
  Proof with auto.
    intros ?? A. simpl.
    pose proof wp_spec. simpl in H1.
    rewrite (H1 w <!! pre !!> post A)... simpl.
    rewrite (H1 w <!! mid !!> post A)... simpl.
    rewrite (H1 w <!! pre !!> mid _)... simpl.
    fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_foralllist_impl_unused_r _ mid) by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* Law B.2 *)
  Lemma r_seq_frame w xs pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} :
    initials_closed post (w ++ xs) →
    initials_closed mid xs →
    w ## xs →
    list_to_set (↑₀ xs) ## formula_fvars post →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs : [pre, mid]; *w, *xs : [mid, post] }>.
  Proof with auto.
    intros. intros A. simpl.
    pose proof wp_spec. simpl in H3.
    rewrite (H3 _ <!! pre !!> post A)... simpl.
    rewrite (H3 _ <!! pre !!> mid _)... simpl.
    rewrite (H3 _ <!! mid !!> post A)... simpl.
    fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (subst_initials_app _ w xs).
    assert (formula_fvars <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> ## list_to_set (↑₀ xs)).
    { intros x ??. set_unfold in H4. destruct H4 as ([|]&?); [set_solver|].
      set_unfold. destruct H5 as [? _]. apply elem_of_fvars_final_formula_inv in H4... }
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials _ xs) at 1 by set_solver...
    rewrite (f_foralllist_impl_unused_r (↑ₓ xs)) at 1 by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  Lemma f_forall_add_typing x ty A :
    <! ∀ x, A !> ⇛ <! ∀ x : ty, A !>.
  Proof with auto.
    intros σ H. unfold FForallT. simpl. intros. rewrite simpl_feval_fforall in H |- *.
    intros. specialize (H v). rewrite feval_subst with (v:=v) in H...
    rewrite feval_subst with (v:=v)... rewrite simpl_feval_fimpl...
  Qed.

  Lemma fold_fmap_as_var xs : list_fmap final_variable variable as_var xs  = ↑ₓ xs.
  Proof. reflexivity. Qed.

  Lemma simpl_subst_forall_skip' y A x t  :
    x ∉ term_fvars t →
    <! A[x\t] !> ≡ <! A !> →
    <! (∀ y, A)[x\t] !> ≡ <! ∀ y, A !>.
  Proof with auto.
    intros Hfree H. destruct (decide (x = y)).
    - rewrite simpl_subst_forall_skip...
    - rewrite <- H. rewrite simpl_subst_forall_skip...
      right. intros contra. apply fvars_subst_superset' in contra. set_solver.
  Qed.

  Lemma simpl_subst_forall_skip'' (x y : variable) A t :
    y ∉ term_fvars t →
    <! A[x\t] !> ≡ <! A !> →
    <! (∀ y, A)[x\t] !> ≡ <! ∀ y, A !>.
  Proof with auto.
    intros Hfree ?. destruct (decide (x = y)).
    - rewrite simpl_subst_forall_skip...
    - mk_fresh (formula_fvars A ∪ {[x; y]} ∪ term_fvars t) as z.
      rewrite simpl_subst_forall_rename with (y':=z).
      2:{ unfold quant_subst_fvars. set_solver. }
      rewrite fforall_alpha_equiv with (x:=y) (x':=z).
      2:{ unfold quant_subst_fvars. set_solver. }
      f_equiv. rewrite fsubst_fsubst_ne... simpl. destruct (decide _).
      + subst. set_unfold in H0. destruct_and! H0. done.
      + rewrite <- H at 2...
  Qed.

  (* Lemma temp A x t : *)
  (*   ∀ σ, feval σ <! A[x \ t] !> ↔ feval σ A → *)
  (*   ∀ σ, feval (delete x σ) A ↔ feval σ A. *)
  (* Proof. *)
  (*   intros.  *)

  (*   int *)
  (*   <! A[x\t] !> ≡ <! A !> → *)


  (* Lemma subst_id_inject_l A (x y z : variable) t : *)
  (*   x ∉ term_fvars t → *)
  (*   <! A[x\z] !> ≡ <! A !> → *)
  (*   <! A[y\t][x\z] !> ≡ <! A[y\t] !>. *)
  (* Proof with auto. *)
  (*   intros. *)
  (*   destruct (decide (y = x)). *)
  (*   - subst. destruct (decide (x ∈ formula_fvars A)). *)
  (*     + rewrite subst_non_free with (t:=z)... intros contra. rewrite fvars_subst in contra... *)
  (*       set_solver. *)
  (*     + repeat rewrite subst_non_free... *)
  (*   - intros σ. split; intros. *)
  (*     + opose proof (teval_total σ z) as (vz&?). *)
  (*       rewrite feval_subst in H1 by exact H2... *)
  (*       opose proof (teval_total (<[x:=vz]> σ) t) as (vt&?). *)
  (*       rewrite feval_subst in H1 by exact H3... *)
  (*       rewrite teval_delete_state_var_head in H3... *)
  (*       rewrite feval_subst by exact H3... *)
  (*       unfold state in *. rewrite insert_commute in H1... *)
  (*       rewrite <- teval_delete_state_var_head with (x:=y) (v:=vt) in H2. *)
  (*       2: {   } *)
  (*       apply H0 in H1. *)


  (*     mk_fresh (formula_fvars A ∪ {[x; y; z]} ∪ term_fvars t) as u. *)
  (*     destruct (decide (z = y)). *)
  (*     + subst. rewrite <- H0 at 1. rewrite fequiv_subst_trans. *)
  (*     rewrite subst_subst_l with (z:=u)... *)
  (*     2-6: set_solver. *)
  (*     simpl. destruct (decide (_)). *)
  (*     + subst. assert (z ≠) *)
  (*     2: set_solver. *)
  (*     rewrite H1 at 1... *)
  (* Qed. *)

  (* Law 6.1 *)
  Lemma r_var_intro {w x ty pre post} `{!FormulaFinal pre} :
    initials_closed post w →
    x ∉ w →
    as_var x ∉ formula_fvars pre →
    as_var x ∉ formula_fvars post →
    <{ *w : [pre, post] }> ⊑ <{ |[ var x : ty ⦁ x, *w : [pre, post] ]| }>.
  Proof with auto.
    intros Hclosed Hw Hpre Hpost A.
    rewrite wp_spec...
    mk_fresh ({[as_var x]} ∪ prog_fvars <{ *w : [pre, post] }>
                ∪ formula_fvars A ∪ list_to_set ↑ₓ w
                ∪ formula_fvars post)
      as y.
    rewrite wp_var with (y:=y)...
    2-4: set_solver.
    rewrite wp_spec... etrans.
    2:{ apply subst_proper_fent. 2,3: reflexivity. apply f_forall_add_typing. }
    rewrite f_forall_and_unused_l... rewrite simpl_subst_and.
    rewrite subst_non_free; [|set_solver]. f_equiv.
    simpl. rewrite (fold_fmap_as_var w). rewrite subst_initials_cons_l.
    rewrite simpl_subst_forall_skip' with (x:=₀x).
    2: set_solver.
    2:{
      rewrite simpl_subst_foralllist.
      2: set_solver.
      2:{ intros ???. apply elem_of_list_to_set in H0. set_solver. }
      f_equiv. rewrite simpl_subst_impl. rewrite (Hclosed x)...
      rewrite subst_non_free...
      set_solver.
    }
    rewrite fforall_unused by set_solver. repeat rewrite subst_initials_msubst.
    rewrite msubst_subst_comm' by set_solver. repeat rewrite <- subst_initials_msubst.
    mk_fresh (formula_fvars <! ∀* ↑ₓ w, post ⇒ A [x \ y] !>
              ∪ {[as_var x; y]} ∪ list_to_set ↑ₓ w ∪ formula_fvars post ∪ formula_fvars A) as z.
    rewrite simpl_subst_forall_rename with (y':=z) by set_solver.
    rewrite simpl_subst_foralllist by set_solver.
    rewrite simpl_subst_foralllist.
    2:{ destruct_and! H. contradict H3. apply elem_of_list_to_set... }
    2:{ intros ???. apply elem_of_list_to_set in H1. set_solver. }
    do 2 rewrite simpl_subst_impl. rewrite subst_non_free.
    2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
    rewrite subst_non_free... rewrite subst_non_free with (x:=x) (t:=z).
    2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
    rewrite fequiv_subst_trans by set_solver. rewrite fequiv_subst_diag.
    rewrite f_forall_foralllist_comm. rewrite fforall_unused... set_solver.
  Qed.

  (* Lemma wp_constlist xs p A : *)
  (*   wp <{ |[ con* xs ⦁ $p ]| }> A ≡ <! ∃* ↑ₓ xs, $(wp p A) !>. *)
  (* Proof with auto. *)
  (*   induction xs as [|x xs IH]... simpl. rewrite f_exists_ty_top. rewrite IH. reflexivity. *)
  (* Qed. *)

  Lemma prog_fvars_varlist xs ty p :
    prog_fvars (PVarList xs ty p) = prog_fvars p ∖ list_to_set (↑ₓ xs).
  Proof. induction xs; set_solver. Qed.

  Lemma wp_varlist_cons x xs ty p A y `{!FormulaFinal A} `{VarFinal y} :
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PVarList (x :: xs) ty p) A ≡
      <! (∀ x : ty, $(wp (PVarList xs ty p) <! A [x \ y] !>)) [y \ x] !>.
  Proof with auto.
    intros. simpl. pose proof (wp_var). simpl in H3. rewrite H3 with (y:=y)...
    rewrite prog_fvars_varlist. set_solver.
  Qed.


  Hint Extern 1 =>
    match goal with
    | H : zip_pair_functional (_ :: ?a) (_ :: ?b) |- zip_pair_functional ?a ?b =>
        apply zip_pair_functional_cons_inv in H; exact H
    end : core.

  Fixpoint fresh_var_list (X : gset variable) (n : nat) : list final_variable :=
    match n with
    | 0 => []
    | S n =>
        let rest := (fresh_var_list X n) in
        let x := fresh_var String.EmptyString ((list_to_set (↑ₓ rest) ∪ X)) in
        as_final_var x :: rest
    end.

  Lemma fresh_var_list_spec X n :
    let l := fresh_var_list X n in
    NoDup l ∧ X ## list_to_set (↑ₓ l) ∧ length l = n.
  Proof with auto.
    simpl. generalize dependent X. induction n.
    - intros. simpl. split_and!...
      + constructor.
      + set_solver.
    - simpl. intros.
      pose proof (fresh_var_fresh String.EmptyString (list_to_set ↑ₓ (fresh_var_list X n) ∪ X)).
      split_and!...
      + constructor; [|set_solver].
        apply not_elem_of_union in H as [].  apply not_elem_of_list_to_set in H.
        contradict H. apply elem_of_list_fmap.
        exists (as_final_var
                  (fresh_var String.EmptyString (list_to_set ↑ₓ (fresh_var_list X n) ∪ X))).
        split... rewrite as_var_as_final_var...
      + intros x??. rewrite elem_of_union, elem_of_singleton in H1. destruct H1; [|set_solver].
        subst. rewrite as_var_as_final_var in H0. set_solver.
      + naive_solver.
  Qed.

  Lemma elem_of_set_to_list {A : Type} `{Countable A} x (xs : gset A) :
    x ∈ set_to_list xs ↔ x ∈ xs.
  Proof with auto.
    unfold elem_of at 1. split; intros.
    - induction xs using set_ind_L.
      + rewrite set_to_list_empty in H0. inversion H0.
      + rewrite set_to_list_union_singleton_l_perm in H0... set_solver.
    - induction xs using set_ind_L.
      + set_solver.
      + rewrite set_to_list_union_singleton_l_perm... set_solver.
  Qed.

  Global Instance set_unfold_elem_of_set_to_list {A : Type} `{Countable A} x (xs : gset A) P :
    (∀ x, SetUnfoldElemOf x xs (P x)) →
    SetUnfoldElemOf x
      (set_to_list xs)
      (P x).
  Proof. constructor. rewrite elem_of_set_to_list. apply H0. Qed.

  Definition dedup {A : Type} (xs : list A) `{Countable A} : list A :=
    set_to_list ∘ list_to_set $ xs.

  Lemma dedup_equiv {A : Type} (xs : list A) `{Countable A} : xs ≡ dedup xs.
  Proof. intros x. unfold dedup. simpl. set_solver. Qed.

  Global Instance set_unfold_elem_of_dedup {A : Type} `{Countable A} x (xs : list A) P :
    (∀ x, SetUnfoldElemOf x xs (P x)) →
    SetUnfoldElemOf x
      (dedup xs)
      (P x).
  Proof. constructor. rewrite <- dedup_equiv. apply H0. Qed.

  Global Instance set_to_list_proper {A : Type} `{Countable A} :
    Proper ((≡) ==> (≡)) (@set_to_list A _ _).
  Proof. intros X. induction X using set_ind_L; intros; set_solver. Qed.

  Global Instance set_to_list_proper_perm {A : Type} `{Countable A} :
    Proper ((≡) ==> (≡ₚ)) (@set_to_list A _ _).
  Proof. intros X. induction X using set_ind_L; intros; set_solver. Qed.

  Local Definition fresh_vars_for_varlist' xs p A `{!FormulaFinal A} :=
    fresh_var_list (prog_fvars p ∪ list_to_set (↑ₓ xs) ∪ formula_fvars A) (length xs).

  Local Lemma fresh_vars_for_varlist'_spec xs p A `{!FormulaFinal A} :
    let zs := fresh_vars_for_varlist' xs p A in
      NoDup zs ∧
      zs ## xs ∧
      list_to_set (↑ₓ zs) ## prog_fvars p ∧
      list_to_set (↑ₓ zs) ## formula_fvars A ∧
      length zs = length xs.
  Proof with auto.
    unfold fresh_vars_for_varlist'.
    pose proof (fresh_var_list_spec (prog_fvars p ∪ list_to_set (↑ₓ xs) ∪
                                        formula_fvars A) (length xs))
      as (?&?&?).
    repeat rewrite disjoint_union_l in H0. destruct_and! H0.
    split_and!...
    intros x??. apply (H4 x); apply elem_of_list_to_set; set_solver.
  Qed.

  Definition first_index_of {A : Type} (x : A) (xs : list A) `{EqDecision A} : option nat :=
    let fix go (xs : list A) i :=
      match xs with
      | [] => None
      | x' :: xs => if decide (x' = x) then Some i else go xs (S i)
      end in
    go xs 0.


  Global Instance variable_inhabited : Inhabited variable :=
    populate (mkVar String.EmptyString 0 false).

  Global Instance final_variable_inhabited : Inhabited final_variable :=
    populate (mkFinalVar String.EmptyString 0).

  Definition fresh_vars_for_varlist xs p A `{!FormulaFinal A} : list final_variable :=
    let xs' := dedup xs in
    let zs' := fresh_vars_for_varlist' xs' p A in
    let fix go (ys : list final_variable) : list final_variable :=
      match ys with
      | [] => []
      | y :: ys =>
          match first_index_of y xs' with
          | None => []
          | Some i => zs' !!! i :: go ys
          end
      end in
    go xs.

  Lemma set_to_list_union_singleton_l_dup {A : Type} `{Countable A} (x : A) (xs : gset A) :
    x ∈ xs →
    set_to_list ({[x]} ∪ xs) ≡ set_to_list xs.
  Proof. intros ? y. set_solver. Qed.

  Lemma set_to_list_union_singleton_l_dup_perm {A : Type} `{Countable A} (x : A) (xs : gset A) :
    x ∈ xs →
    set_to_list ({[x]} ∪ xs) ≡ₚ set_to_list xs.
  Proof with auto.
    intros. induction xs using set_ind_L; [set_solver|].
    set_unfold in H0. destruct H0.
    - subst x0. f_equiv. set_solver.
    - rewrite union_comm_L with (y:=X). rewrite union_assoc_L.
      repeat rewrite union_comm_L with (y:={[x0]}).
      rewrite set_to_list_union_singleton_l_perm by set_solver.
      rewrite set_to_list_union_singleton_l_perm with (x:=x0) by set_solver.
      f_equiv. apply IHxs...
  Qed.

  Lemma list_equiv_nil {A : Type} (xs : list A) :
    xs ≡ [] ↔ xs = nil.
  Proof with auto.
    split; intros; [| subst]... induction xs... set_solver.
  Qed.

  Lemma list_equiv_cons_inl {A : Type} (xs : list A) x ys :
    x ∈ xs →
    xs ≡ ys →
    xs ≡ x :: ys.
  Proof. set_solver. Qed.

  Lemma set_to_list_list_to_set_nil_iff {A : Type} `{Countable A} (xs : list A) :
    set_to_list (list_to_set xs) ≡ [] ↔ xs = [].
  Proof. induction xs; set_solver. Qed.

  Lemma set_to_list_NoDup {A : Type} `{Countable A} (xs : gset A) :
    NoDup (set_to_list xs).
  Proof with auto.
    induction xs using set_ind_L.
    - rewrite set_to_list_empty. constructor.
    - rewrite set_to_list_union_singleton_l_perm... constructor... set_solver.
  Qed.

  Lemma set_to_list_list_to_set_cons_inv {A : Type} `{Countable A} (xs : list A) y ys :
    set_to_list (list_to_set xs) = y :: ys → y ∈ xs ∧ y ∉ ys.
  Proof with auto.
    intros. assert (set_to_list (list_to_set xs) ≡ₚ y :: ys) by (by rewrite H0).
    assert (∃ k, set_to_list (list_to_set xs) ≡ₚ y :: k) by eauto.
    rewrite <- elem_of_Permutation in H2. split; [set_solver|].
    pose proof (set_to_list_NoDup (list_to_set xs)).
    rewrite H0 in H3. inversion H3. set_solver.
  Qed.

  Lemma dedup_nil {A : Type} `{Countable A} :
    dedup [] = @nil A.
  Proof.
    unfold dedup. simpl. rewrite <- list_equiv_nil. by rewrite set_to_list_empty.
  Qed.

  Lemma dedup_nil_iff {A : Type} `{Countable A} (xs : list A) :
    dedup xs = [] ↔ xs = [].
  Proof.
    unfold dedup. simpl. rewrite <- list_equiv_nil. by rewrite set_to_list_list_to_set_nil_iff.
  Qed.

  Lemma dedup_cons_inv {A : Type} `{Countable A} (xs : list A) y ys :
    dedup xs = y :: ys → y ∈ xs ∧ y ∉ ys.
  Proof.
    unfold dedup. simpl. intros. by apply set_to_list_list_to_set_cons_inv in H0.
  Qed.

  Lemma dedup_NoDup {A : Type} (xs : list A) `{Countable A} :
    NoDup (dedup xs).
  Proof. apply set_to_list_NoDup. Qed.

  Lemma elem_of_dedup {A : Type} `{Countable A} x (xs : list A) :
    x ∈ xs ↔ x ∈ dedup xs.
  Proof. intros. set_solver. Qed.

  Lemma first_index_of_nil {A : Type} (x : A)  `{EqDecision A} :
    first_index_of x nil = None.
  Proof. reflexivity. Qed.

  Lemma first_index_of_cons {A : Type} (x : A) (xs : list A) `{EqDecision A} :
    first_index_of x (x :: xs) = Some 0.
  Proof. unfold first_index_of. destruct (decide _); done. Qed.

  Lemma first_index_of_cons_ne {A : Type} (x : A) (xs : list A) y `{EqDecision A} :
    x ≠ y →
    first_index_of x (y :: xs) = S <$> (first_index_of x xs).
  Proof with auto.
    intros. unfold first_index_of. destruct (decide _); [done|].
    enough (∀ n,
      (fix go (xs0 : list A) (i : nat) {struct xs0} : option nat :=
        match xs0 with
        | [] => None
        | x' :: xs1 => if decide (x' = x) then Some i else go xs1 (S i)
        end)
        xs (S n) =
      S <$>
      (fix go (xs0 : list A) (i : nat) {struct xs0} : option nat :=
        match xs0 with
        | [] => None
        | x' :: xs1 => if decide (x' = x) then Some i else go xs1 (S i)
        end)
        xs n)...
    induction xs... intros. destruct (decide _)...
  Qed.

  Lemma first_index_of_cons_ne_Some_inv {A : Type} (x : A) (xs : list A) y `{EqDecision A} i :
    x ≠ y →
    first_index_of x (y :: xs) = Some i → ∃ j, i = S j ∧ first_index_of x xs = Some j.
  Proof with auto.
    intros. rewrite first_index_of_cons_ne in H0...
    destruct (first_index_of x xs) as [j|] eqn:E.
    - simpl in H0. inversion H0. exists j...
    - discriminate.
  Qed.

  Lemma first_index_of_None_inv {A : Type} (y : A) (xs : list A) `{EqDecision A} :
    first_index_of y xs = None → y ∉ xs.
  Proof with auto.
    intros. induction xs as [|x xs]; [set_solver|].
    destruct (decide (x = y)).
    - subst. rewrite first_index_of_cons in H. inversion H.
    - rewrite first_index_of_cons_ne in H... destruct (first_index_of y xs) as [j|] eqn:E.
      + simpl in H. discriminate.
      + set_solver.
  Qed.

  Lemma first_index_of_Some_inv {A : Type} (y : A) (xs : list A) i `{EqDecision A} :
    first_index_of y xs = Some i → xs !! i = Some y ∧ ∀ j z, j < i → xs !! j = Some z → y ≠ z.
  Proof with auto.
    intros. generalize dependent i. induction xs as [|x xs]; [discriminate|]; intros.
    destruct (decide (x = y)).
    - subst. rewrite first_index_of_cons in H. inversion H. subst. split; [set_solver|lia].
    - apply first_index_of_cons_ne_Some_inv in H as (j&?&?)...
      apply IHxs in H0 as []. subst i. simpl. split... intros.
      destruct (j0).
      + simpl in H2. inversion H2. subst...
      + assert (n0 < j) by lia. apply H1 with n0...
  Qed.

  Lemma first_index_of_Some_elem_of {A : Type} (y : A) (xs : list A) `{EqDecision A} :
    y ∈ xs →
    ∃ i, first_index_of y xs = Some i.
  Proof with auto.
    intros. induction xs as [|x xs]; [set_solver|]. set_unfold in H.
    destruct (decide (y = x)).
    - subst. exists 0. rewrite first_index_of_cons...
    - destruct H; [done|]. destruct (IHxs H) as (i&?). exists (S i).
      rewrite first_index_of_cons_ne... rewrite H0. reflexivity.
  Qed.
  (* Lemma temp xs p A `{!FormulaFinal A} x i : *)
  (*   xs !! i = Some x → *)
  (*   ∃ (j : nat) (z : final_variable), *)
  (*     dedup xs !! j = Some x ∧ *)
  (*     fresh_vars_for_varlist' (dedup xs) p A !! j = Some z ∧ *)
  (*     fresh_vars_for_varlist xs p A !! i = Some z. *)
  (* Proof with auto. *)
  (*   intros. assert (x ∈ xs). *)
  (*   { apply elem_of_list_lookup. eauto. } *)
  (*   apply elem_of_dedup in H0. apply elem_of_list_lookup_1 in H0 as (j&?). *)
  (*   exists j. *)
  (*   pose proof (fresh_vars_for_varlist'_spec (dedup xs) p A) as (_&_&_&_&?). *)
  (*   symmetry in H1. *)
  (*   pose proof (zip_pair_lookup_l' H1 H0) as (z&?). *)
  (*   exists z. split_and!... unfold fresh_vars_for_varlist. *)
  (*   remember (fresh_vars_for_varlist' (dedup xs) p A) as dxs. *)
  (*   clear Heqdxs. *)
  (*   Search (∃ _, ?l !! _ = _). *)
  (*   apply dedup_in *)
  (*   apply set_elem_of_dedup *)

  Local Lemma fresh_vars_for_varlist_subset xs p A `{!FormulaFinal A} :
    fresh_vars_for_varlist xs p A ⊆ fresh_vars_for_varlist' (dedup xs) p A.
  Proof with auto.
    unfold fresh_vars_for_varlist.
    pose proof (fresh_vars_for_varlist'_spec (dedup xs) p A) as (_&_&_&_&?).
    assert (xs ⊆ dedup xs) by set_solver.
    remember (dedup xs) as dxs. clear Heqdxs.
    remember (fresh_vars_for_varlist' dxs p A) as dzs. clear Heqdzs.
    induction xs as [|x xs]; intros.
    - set_solver.
    - destruct (first_index_of x dxs) as [i|] eqn:E.
      + apply first_index_of_Some_inv in E as [E' _].
        symmetry in H. destruct (zip_pair_lookup_l' H E') as [z ?].
        apply list_lookup_total_correct in H1 as H2. rewrite H2.
        apply elem_of_list_lookup_2 in H1.
        apply list_subseteq_cons_iff. split... apply IHxs.
        set_solver.
      + apply first_index_of_None_inv in E. set_solver.
  Qed.

  Fixpoint fresh_vars_for_varlist_aux (dxs : list final_variable) (dzs : list final_variable) (xs : list final_variable) :=
      match xs with
      | [] => []
      | x :: xs =>
          match first_index_of x dxs with
          | None => []
          | Some i => dzs !!! i :: fresh_vars_for_varlist_aux dxs dzs xs
          end
      end.

  Fixpoint zip_pair_image {A B : Type} `{EqDecision A} (xs' xs : list A) (ys : list B) :=
    match xs, ys with
    | x :: xs, y :: ys =>
        if decide (x ∈ xs') then
          y :: zip_pair_image xs' xs ys
        else
          zip_pair_image xs' xs ys
    | _, _ => []
    end.


  Global Instance zip_pair_image_proper {A B : Type} `{EqDecision A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=)) (@zip_pair_image A B _).
  Proof with auto.
    intros xs'1 xs'2 H xs ? <- ys ? <-. generalize dependent ys. induction xs as [|x xs]...
    intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _)...
    - f_equal. apply IHxs.
    - apply H in e. contradiction.
    - apply H in e. contradiction.
  Qed.

  Global Instance set_unfold_elem_of_list_delete_elem {A : Type} `{EqDecision A} (y x : A) (xs : list A) P :
    SetUnfoldElemOf y xs P →
    SetUnfoldElemOf y
      (delete x xs)
      (y ≠ x ∧ P).
  Proof with auto.
    intros. constructor. destruct H. rewrite <- set_unfold_elem_of. clear set_unfold_elem_of.
    unfold delete, list_delete_elem. induction xs; [set_solver|].
    simpl. destruct (decide_rel _); set_solver.
  Qed.

  Lemma zip_pair_image_cons_pair {A B : Type} `{EqDecision A} (xs' : list A) x (xs : list A) y (ys : list B) :
    x ∈ xs' →
    zip_pair_image xs' (x :: xs) (y :: ys) = y :: zip_pair_image xs' xs ys.
  Proof. intros. simpl. by destruct (decide _). Qed.

  Lemma zip_pair_image_cons_pair_notin {A B : Type} `{EqDecision A} (xs' : list A) x (xs : list A) y (ys : list B) :
    x ∉ xs' →
    zip_pair_image xs' (x :: xs) (y :: ys) = zip_pair_image xs' xs ys.
  Proof. intros. simpl. by destruct (decide _). Qed.

  Lemma zip_pair_image_nil_1 {A B : Type} `{EqDecision A} (xs : list A) (ys : list B) :
    zip_pair_image [] xs ys = [].
  Proof with auto.
    generalize dependent ys. induction xs as [|x xs]... destruct ys as [|y ys]... simpl...
  Qed.
  Lemma zip_pair_image_nil_2 {A B : Type} `{EqDecision A} (xs' : list A) (ys : list B) :
    zip_pair_image xs' [] ys = [].
  Proof with auto. induction ys... Qed.
  Lemma zip_pair_image_nil_3 {A B : Type} `{EqDecision A} (xs' xs : list A) :
    zip_pair_image xs' xs (@nil B) = [].
  Proof with auto. induction xs... Qed.

  Lemma zip_pair_image_delete_1 {A B : Type} `{EqDecision A} (x : A) (xs' xs : list A) (ys : list B) :
    x ∉ xs →
    zip_pair_image xs' xs ys = zip_pair_image (delete x xs') xs ys.
  Proof with auto.
    intros. generalize dependent ys. induction xs as [|x' xs]...
    intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _).
    2-4: set_solver.
    f_equal. apply IHxs. set_solver.
  Qed.

  Lemma zip_pair_image_delete_1_head {A B : Type} `{EqDecision A} (x : A) (xs' xs : list A) (ys : list B) :
    x ∉ xs →
    zip_pair_image (x :: xs') xs ys = zip_pair_image xs' xs ys.
  Proof with auto.
    intros. generalize dependent ys. induction xs as [|x' xs]...
    intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _).
    2-4: set_solver.
    f_equal. apply IHxs. set_solver.
  Qed.

  Lemma zip_pair_image_diag_1 {A B : Type} `{EqDecision A} (xs : list A) (ys : list B) :
    zip_pair_image xs xs ys = take (length xs) ys.
  Proof with auto.
    generalize dependent xs. induction ys as [|y ys].
    - intros. rewrite take_nil. rewrite zip_pair_image_nil_3...
    - destruct xs as [|x xs]... simpl. destruct (decide _); [|set_solver].
      destruct (decide (x ∈ xs)).
      + assert (xs ≡ x :: xs) by set_solver. f_equiv. rewrite <- IHys.
        apply zip_pair_image_proper...
      + rewrite zip_pair_image_delete_1_head... f_equal. apply IHys.
  Qed.

  Lemma zip_pair_image_sub_1 {A B : Type} `{EqDecision A} (xs' xs : list A) (ys : list B) :
    xs ⊆ xs' →
    zip_pair_image xs' xs ys = zip_pair_image xs xs ys.
  Proof with auto.
    intros. generalize dependent ys. generalize dependent xs'. induction xs as [|x xs]...
    intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _).
    2-4: set_solver.
    - f_equal. rewrite IHxs; [|set_solver].
      destruct (decide (x ∈ xs)).
      + apply zip_pair_image_proper... set_solver.
      + rewrite <- zip_pair_image_delete_1_head with (x:=x)...
  Qed.

  Global Instance cons_proper_eq' {A : Type} : Proper ((=) ==> (≡) ==> (≡)) (@cons A).
  Proof. intros x ? -> xs ys ?. intros z. set_solver. Qed.

  Global Instance cons_proper_subseteq {A : Type} : Proper ((=) ==> (⊆) ==> (⊆)) (@cons A).
  Proof. intros x ? -> xs ys ?. intros z. set_solver. Qed.

  Lemma cons_cons {A : Type} (x y : A) (xs : list A) :
    x :: y :: xs ≡ y :: x :: xs.
  Proof. set_solver. Qed.

  Lemma zip_pair_image_cons_1 {A B : Type} `{EqDecision A} (x : A) (y : B)
      (xs' xs : list A) (ys : list B) :
    length xs = length ys →
    zip_pair_functional xs ys →
    x ∉ xs' →
    (x, y) ∈ (xs, ys) →
    zip_pair_image (x :: xs') xs ys ≡ y :: zip_pair_image xs' xs ys.
  Proof with auto.
    intros Hlen. intros. generalize dependent ys. induction xs as [|x1 xs1]; intros.
    { apply elem_of_zip_pair in H1 as (i&?&?). discriminate. }
    destruct ys as [|y1 ys1].
    { apply elem_of_zip_pair in H1 as (i&?&?). discriminate. }
    destruct (decide (x = x1)).
    - subst. simpl in *. destruct (decide _); [|set_solver]. destruct (decide _); [set_solver|].
      apply zip_pair_functional_cons_inv in H as ?. inversion Hlen. clear Hlen. rename H4 into Hlen.
      specialize (IHxs1 ys1 Hlen H2). assert (y = y1).
      {
        apply elem_of_zip_pair in H1 as (i&?&?). destruct (decide (i = 0)).
        - subst. simpl in *. inversion H3...
        - rewrite lookup_cons_ne_0 in H1... rewrite lookup_cons_ne_0 in H3...
          symmetry.
          eapply (H 0 i); apply elem_of_zip_pair_indexed...
          split; rewrite lookup_cons_ne_0...
      }
      subst. destruct (decide (x1 ∈ xs1)).
      + apply elem_of_list_lookup in e0 as (i&?).
        pose proof (zip_pair_lookup_l' Hlen H3) as (y1'&?).
        assert (y1 = y1').
        {
          apply elem_of_zip_pair in H1 as (j&?&?).
          eapply H.
          - apply elem_of_zip_pair_indexed. split...
            + exact H1.
            + exact H5.
          - Unshelve. 2: exact (S i). apply elem_of_zip_pair_indexed. split...
        }
        subst y1'. forward IHxs1 by (apply elem_of_zip_pair; eauto).
        set_solver.
      + rewrite zip_pair_image_delete_1_head...
    - simpl. destruct decide.
      + destruct decide; [| set_solver]. clear e. rewrite cons_cons.
        rewrite IHxs1... apply elem_of_zip_pair_hd_ne in H1...
      + destruct decide; [set_solver|]. apply IHxs1...
        apply elem_of_zip_pair_hd_ne in H1...
  Qed.

  Lemma take_all {A : Type} (xs : list A) :
    take (length xs) xs = xs.
  Proof. apply firstn_all. Qed.

  (* Lemma zip_pair_image_cons_pair : *)

  Local Lemma fresh_vars_for_varlist_superset xs p A `{!FormulaFinal A} :
    fresh_vars_for_varlist' (dedup xs) p A ⊆ fresh_vars_for_varlist xs p A.
  Proof with auto.
    enough (zip_pair_image xs (dedup xs) (fresh_vars_for_varlist' (dedup xs) p A)
              ⊆ fresh_vars_for_varlist xs p A).
    {
      rewrite zip_pair_image_sub_1 in H by set_solver...
      rewrite zip_pair_image_diag_1 in H.
      pose proof (fresh_vars_for_varlist'_spec (dedup xs) p A) as (_&_&_&_&?).
      rewrite <- H0 in H. rewrite take_all in H...
    }
    unfold fresh_vars_for_varlist.
    pose proof (fresh_vars_for_varlist'_spec (dedup xs) p A) as (_&_&_&_&?).
    assert (xs ⊆ dedup xs) by set_solver.
    assert (NoDup (dedup xs)) by apply dedup_NoDup.
    remember (dedup xs) as dxs. clear Heqdxs.
    remember (fresh_vars_for_varlist' dxs p A) as dzs. clear Heqdzs.
    induction xs as [|x xs]; intros.
    - rewrite zip_pair_image_nil_1...
    - destruct (first_index_of x dxs) as [i|] eqn:E.
      + apply list_subseteq_cons_iff in H0 as [? ?]. destruct (decide (x ∈ xs)).
        * assert (x :: xs ≡ xs) by set_solver. rewrite H3. apply list_subseteq_cons...
        * symmetry in H. apply first_index_of_Some_inv in E as [? _].
          pose proof (zip_pair_lookup_l' H H3) as [dy ?].
          eapply subseteq_proper.
          -- apply zip_pair_image_cons_1...
            ++ apply NoDup_zip_pair_functional...
            ++ apply elem_of_zip_pair. eauto.
          -- reflexivity.
          -- apply list_lookup_total_correct in H4. rewrite H4. apply cons_proper_subseteq...
      + apply first_index_of_None_inv in E. set_solver.
  Qed.

  Lemma fresh_vars_for_varlist_equiv  xs p A `{!FormulaFinal A} :
    fresh_vars_for_varlist xs p A ≡ fresh_vars_for_varlist' (dedup xs) p A.
  Proof.
    split.
    - apply fresh_vars_for_varlist_subset.
    - apply fresh_vars_for_varlist_superset.
  Qed.

  Lemma fresh_vars_for_varlist_length xs p A `{!FormulaFinal A} :
    length (fresh_vars_for_varlist xs p A) = length xs.
  Proof with auto.
    unfold fresh_vars_for_varlist.
    assert (xs ⊆ dedup xs) by set_solver.
    remember (dedup xs) as dxs. clear Heqdxs.
    remember (fresh_vars_for_varlist' dxs p A) as dzs. clear Heqdzs.
    induction xs as [|x xs]; intros...
    destruct (first_index_of x dxs) as [i|] eqn:E.
    + simpl. f_equal. apply IHxs. set_solver.
    + apply first_index_of_None_inv in E. set_solver.
  Qed.

  Lemma zip_pair_functional_nil {A B : Type}  :
    zip_pair_functional (@nil A) (@nil B).
  Proof.
    intros i j x y1 y2 ??. apply elem_of_zip_pair_indexed_inv in H0.
    apply elem_of_zip_pair_nil in H0 as [].
  Qed.

  (* Global Instance elem_of_list_indexed {A : Type} : ElemOf (nat * A) (list A) := *)
  (*   λ ix (xs : list A), xs !! ix.1 = Some ix.2. *)

  (* Lemma elem_of_list_indexed_lookup {A : Type} i (x : A) (xs : list A) : *)
  (*   (i, x) ∈ xs ↔ xs !! i = Some x. *)
  (* Proof. reflexivity. Qed. *)

  Lemma elem_of_zip_pair_indexed_hd {A B : Type} x x' y y' (xs : list A) (ys : list B) :
    (0, (x, y)) ∈ (x' :: xs, y' :: ys) ↔ x = x' ∧ y = y'.
  Proof. unfold elem_of, zip_pair_elem_of_with_index. naive_solver. Qed.

  Lemma elem_of_zip_pair_indexed_tl {A B : Type} x x' y y' (xs : list A) (ys : list B) i :
    (S i, (x, y)) ∈ (x' :: xs, y' :: ys) ↔ (i, (x, y)) ∈ (xs, ys).
  Proof. unfold elem_of, zip_pair_elem_of_with_index. naive_solver. Qed.

  Lemma zip_pair_functional_cons {A B : Type} x (xs : list A) y (ys : list B) :
    length xs = length ys →
    zip_pair_functional (x :: xs) (y :: ys) ↔
      (∀ i y', (i, (x, y')) ∈ (xs, ys) → y' = y) ∧ zip_pair_functional xs ys.
  Proof with auto.
    split; intros.
    - split; [|eapply zip_pair_functional_cons_inv; eauto]. intros.
      apply elem_of_zip_pair_indexed in H1 as []. simpl in *.
      ospecialize (H0 0 (S i) x y y' _ _)...
      1-2: apply elem_of_zip_pair_indexed; auto.
    - destruct H0. intros i j u y1 y2 ??. destruct i, j; try contradiction.
      + apply elem_of_zip_pair_indexed_hd in H2 as (->&->).
        apply elem_of_zip_pair_indexed_hd in H3 as (_&->)...
      + apply elem_of_zip_pair_indexed_hd in H2 as (->&->).
        apply elem_of_zip_pair_indexed_tl in H3. specialize (H0 j y2 H3)...
      + apply elem_of_zip_pair_indexed_hd in H3 as (->&->)...
        apply elem_of_zip_pair_indexed_tl in H2. specialize (H0 i y1 H2)...
      + apply elem_of_zip_pair_indexed_tl in H2.
        apply elem_of_zip_pair_indexed_tl in H3.
        specialize (H1 i j u y1 y2 H2 H3)...
  Qed.

  Hint Extern 0 (zip_pair_functional [] []) => apply zip_pair_functional_nil : core.

  Lemma fresh_vars_for_varlist_zip_pair_functional xs p A `{!FormulaFinal A} :
    zip_pair_functional xs (fresh_vars_for_varlist xs p A).
  Proof with auto.
    enough (∀ i x y, (i, (x, y)) ∈ (xs, fresh_vars_for_varlist xs p A) →
                     ∃ j, (j, (x, y)) ∈ (dedup xs, fresh_vars_for_varlist' (dedup xs) p A)).
    {
      intros i j x y1 y2 ??. apply H in H0 as (k&?&?). apply H in H1 as (k'&?&?).
      simpl in *. pose proof (dedup_NoDup xs).
      pose proof (NoDup_lookup _ _ _ _ H4 H0 H1) as ->. naive_solver.
    }
    unfold fresh_vars_for_varlist.
    pose proof (fresh_vars_for_varlist'_spec (dedup xs) p A) as (_&_&_&_&?).
    remember (dedup xs) as dxs. clear Heqdxs.
    remember (fresh_vars_for_varlist' dxs p A) as dzs. clear Heqdzs.
    induction xs as [|x xs]; intros.
    { rewrite elem_of_zip_pair_indexed in H0. naive_solver. }
    destruct (first_index_of x dxs) as [k|] eqn:E.
    + apply first_index_of_Some_inv in E as [? _].
      symmetry in H. pose proof (zip_pair_lookup_l' H H1) as (dz&?).
      destruct i.
      * apply elem_of_zip_pair_hd_indexed in H0 as (?&?). subst x0.
        apply list_lookup_total_correct in H2 as H4. rewrite H4 in H3. subst dz. clear H4.
        exists k. apply elem_of_zip_pair_indexed...
      * apply elem_of_zip_pair_tl_indexed in H0. apply IHxs in H0...
    + rewrite elem_of_zip_pair_indexed in H0. naive_solver.
  Qed.

  Lemma fresh_vars_for_varlist_spec xs p A `{!FormulaFinal A} :
    let zs := fresh_vars_for_varlist xs p A in
      zip_pair_functional xs zs ∧
      zs ## xs ∧
      list_to_set (↑ₓ zs) ## prog_fvars p ∧
      list_to_set (↑ₓ zs) ## formula_fvars A.
  Proof with auto.
    simpl.
    pose proof (fresh_vars_for_varlist_subset xs p A).
    pose proof (fresh_vars_for_varlist'_spec (dedup xs) p A) as (?&?&?&?&?).
    pose proof (fresh_vars_for_varlist_zip_pair_functional xs p A).
    split_and!... all: set_solver.
  Qed.

  Definition fresh_vars_for_varlist xs p A `{!FormulaFinal A} : list final_variable :=
    let xs' := dedup xs in
    let zs' := fresh_vars_for_varlist' xs' p A in
    let fix go (xs : list final_variable) : list final_variable :=
      match xs with
      | [] => []
      | x :: xs =>
          match find (λ x', x =? x') xs' with
          | None => []
          | Some i =>
            match zs' !! i with
            | None => []
            | Some z => []
            end
          end
      end in
    go xs.

  Lemma fresh_var_list_spec X n :
    let l := fresh_var_list X n in
    NoDup l ∧ X ## list_to_set (↑ₓ l) ∧ length l = n.
  Proof with auto.
    simpl. generalize dependent X. induction n.
    - intros. simpl. split_and!...
      + constructor.
      + set_solver.
    - simpl. intros.
      pose proof (fresh_var_fresh String.EmptyString (list_to_set ↑ₓ (fresh_var_list X n) ∪ X)).
      split_and!...
      + constructor; [|set_solver].
        apply not_elem_of_union in H as [].  apply not_elem_of_list_to_set in H.
        contradict H. apply elem_of_list_fmap.
        exists (as_final_var
                  (fresh_var String.EmptyString (list_to_set ↑ₓ (fresh_var_list X n) ∪ X))).
        split... rewrite as_var_as_final_var...
      + intros x??. rewrite elem_of_union, elem_of_singleton in H1. destruct H1; [|set_solver].
        subst. rewrite as_var_as_final_var in H0. set_solver.
      + naive_solver.
  Qed.

  Definition fresh_vars_for_varlist xs p A `{!FormulaFinal A} :=
    fresh_var_list (prog_fvars p ∪ list_to_set (↑ₓ xs) ∪ formula_fvars A) (length xs).


  Lemma wp_varlist' (xs : list final_variable) p (A : formula) `{!FormulaFinal A}
      (zs : list final_variable) `{!OfSameLength xs zs} `{!OfSameLength zs xs} :
    NoDup zs →
    zs ## xs →
    list_to_set (↑ₓ zs) ## prog_fvars p →
    list_to_set (↑ₓ zs) ## formula_fvars A →
    wp <{ |[ var* xs ⦁ $p ]| }> A ≡
      <! (∀* ↑ₓ xs, $(wp p <! A[; ↑ₓ xs \ ⇑ₓ zs ;] !>))[; ↑ₓ zs \ ⇑ₓ xs ;] !>.
  Proof with auto.
    generalize dependent A. induction_same_length xs zs as x z... intros.
    apply NoDup_cons in H. rewrite wp_varlist_cons with (y:=z)...
    2-5: set_solver.
    simpl fmap at 1. rewrite foralllist_cons. simpl. unshelve rewrite IH...
    2-4: set_solver.
    - f_equiv. rewrite f_forall_ty_top.
      (* + rewrite fforall_unused. *)
      (*   2:{ contradict e. apply fvars_seqsubst_superset in e. apply elem_of_union in e as [|]. *)
      (*       - destruct H3. contradict H4. rewrite to_final_var_as_var. split... *)
      (*       - rewrite to_final_var_as_var in H3. set_solver. *)
      (*   } *)
      (*   2:{ rewrite fvars_foralllist. contradict e. set_unfold in e. destruct e as [_ ?]. *)
      (*       contradict H3. split... rewrite to_final_var_as_var... } *)
      (*   rewrite f_fora *)
      (*   rewrite fforall_unused. *)
      (*   * *)
      (* + admit. *)
      + rewrite simpl_seqsubst_forall.
        2:{ intros contra. apply (H1 x); set_solver. }
        2:{ set_unfold. intros []. rewrite to_final_var_as_var in H4. set_solver. }
        rewrite f_forall_ty_top. f_equiv. unfold fmap at 6 7. apply seqsubst_proper...
        f_equiv. apply wp_congr... rewrite seqsubst_subst_comm.
        * f_equiv. apply eq_pi. solve_decision.
        * set_solver.
        * set_unfold. contradict H0. intros ?. apply (H3 $ to_final_var x).
          -- set_solver.
          -- rewrite to_final_var_as_var. set_solver.
        * set_unfold. intros. subst. rewrite to_final_var_as_var in H3. set_solver.
    - intros y??. apply elem_of_list_to_set in H3. apply fvars_subst_superset' in H4.
      apply (H2 y).
      + apply elem_of_list_to_set. set_solver.
      + set_unfold in H4. destruct H4 as [[] |]... subst. set_solver.
  Qed.
  Lemma wp_varlist' (xs : list final_variable) p (A : formula) `{!FormulaFinal A}
      (zs : list final_variable) `{!OfSameLength xs zs} `{!OfSameLength zs xs} :
    NoDup xs →
    NoDup zs →
    zs ## xs →
    list_to_set (↑ₓ zs) ## prog_fvars p →
    list_to_set (↑ₓ zs) ## formula_fvars A →
    wp <{ |[ var* xs ⦁ $p ]| }> A ≡
      <! (∀* ↑ₓ xs, $(wp p <! A[; ↑ₓ xs \ ⇑ₓ zs ;] !>))[; ↑ₓ zs \ ⇑ₓ xs ;] !>.
  Proof with auto.
    generalize dependent A. induction_same_length xs zs as x z... intros.
    apply NoDup_cons in H, H0. rewrite wp_varlist_cons with (y:=z)...
    2-5: set_solver.
    simpl fmap at 1. rewrite foralllist_cons. simpl. unshelve rewrite IH...
    2-5: set_solver.
    - f_equiv. rewrite simpl_seqsubst_forall.
      2:{ intros contra. apply (H1 x); set_solver. }
      2:{ set_unfold. intros []. rewrite to_final_var_as_var in H5. set_solver. }
      rewrite f_forall_ty_top. f_equiv. unfold fmap at 6 7. apply seqsubst_proper...
      f_equiv. apply wp_congr...
      rewrite seqsubst_subst_comm.
      + f_equiv. apply eq_pi. solve_decision.
      + set_solver.
      + set_unfold. contradict H1. intros ?. apply (H4 $ to_final_var x).
        * set_solver.
        * rewrite to_final_var_as_var. set_solver.
      + set_unfold. intros. subst. rewrite to_final_var_as_var in H4. set_solver.
    - intros y??. apply elem_of_list_to_set in H4. apply fvars_subst_superset' in H5.
      apply (H3 y).
      + apply elem_of_list_to_set. set_solver.
      + set_unfold in H5. destruct H5 as [[] |]... subst. set_solver.
  Qed.

  Lemma of_same_length_comm {A B : Type} (l1 : list A) (l2 : list B) :
    OfSameLength l1 l2 → OfSameLength l2 l1.
  Proof. naive_solver. Qed.

  Global Instance of_same_length_fresh_var_for_varlist {xs p A} `{!FormulaFinal A} :
    OfSameLength xs (fresh_vars_for_varlist xs p A).
  Proof.
    pose proof (fresh_var_list_spec (prog_fvars p ∪ list_to_set (↑ₓ xs) ∪
                                        formula_fvars A) (length xs))
      as (?&?&?).
    unfold OfSameLength, of_same_length. naive_solver.
  Qed.

  Global Instance of_same_length_fresh_var_for_varlist' {xs p A} `{!FormulaFinal A} :
    OfSameLength (fresh_vars_for_varlist xs p A) xs.
  Proof. apply of_same_length_comm. typeclasses eauto. Qed.

  Lemma wp_varlist (xs : list final_variable) p A `{!FormulaFinal A} :
    NoDup xs →
    let zs := fresh_vars_for_varlist xs p A in
      wp <{ |[ var* xs ⦁ $p ]| }> A ≡
        <! (∀* ↑ₓ xs, $(wp p <! A[; ↑ₓ xs \ ⇑ₓ zs ;] !>))[; ↑ₓ zs \ ⇑ₓ xs ;] !>.
  Proof with auto.
    intros. pose proof (fresh_vars_for_varlist_spec xs p A). destruct_and! H0.
    apply wp_varlist'...
  Qed.

  Lemma r_varlist_app xs1 xs2 p :
    <{ |[ var* $(xs1 ++ xs2) ⦁ $p ]| }> ≡ <{ |[ var* $(xs2 ++ xs1) ⦁ $p ]| }>.
  Proof with auto.

    intros A. generalize dependent xs2. generalize dependent A.
    induction xs1 as [|x xs1]; intros.
    - simpl. rewrite app_nil_r...
    - simpl app.
      mk_fresh (prog_fvars p ∪ {[as_var x]} ∪ formula_fvars A) as z.
      rewrite wp_varlist_cons with (y:=z) by set_solver...
      specialize (IHxs1 (as_final_formula <! A [x \ z] !>) xs2).
      rewrite IHxs1. simpl.
    do 2 rewrite wp_varlist. do 2 rewrite fmap_app.
    do 2 rewrite foralllist_app. rewrite f_foralllist_comm...
  Qed.
  Lemma r_varlist_permute xs xs' p :
    xs ≡ₚ xs' →
    <{ |[ var* xs ⦁ $p ]| }> ≡ <{ |[ var* xs' ⦁ $p ]| }>.
  Proof with auto.
    intros Hperm A. generalize dependent xs'. generalize dependent A.
    induction xs as [|x xs]; intros.
    - destruct xs'... apply Permutation_cons_inv_r in Hperm as (?&?&?&?).
      symmetry in H. apply app_eq_nil in H as [].  discriminate.
    - apply Permutation_cons_inv_l in Hperm as (l1&l2&?&?). subst xs'.
      mk_fresh (prog_fvars p ∪ {[as_var x]} ∪ formula_fvars A) as z.
      rewrite wp_varlist_cons with (y:=z) by set_solver.
      apply app_nil_r in H.
    -
    simpl.
    do 2 rewrite wp_varlist. rewrite f_foralllist_permute; [reflexivity|].
    apply Permutation_map. assumption.
  Qed.

  Lemma r_varlist_app xs1 xs2 p :
    <{ |[ var* $(xs1 ++ xs2) ⦁ $p ]| }> ≡ <{ |[ var* $(xs2 ++ xs1) ⦁ $p ]| }>.
  Proof with auto.
    intros A. do 2 rewrite wp_varlist. do 2 rewrite fmap_app.
    do 2 rewrite foralllist_app. rewrite f_foralllist_comm...
  Qed.

  Lemma r_following_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!OfSameLength xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <{ *w, *xs : [pre, post] }> ⊑
    <{ *w, *xs : [pre, post[[↑ₓ xs \ ⇑ₜ ts]]]; *xs := *(FinalRhsTerm <$> ts) }>.
  Proof with auto.
    intros Hlength Hnodup A. simpl. rewrite wp_asgn. fSimpl. rewrite <- simpl_msubst_impl.
    f_equiv. rewrite fmap_app. do 2 rewrite foralllist_app. f_equiv.
    rewrite <- f_foralllist_idemp. rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !>)...
    - reflexivity.
    - rewrite length_fmap...
  Qed.

  Lemma r_leading_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!FormulaFinal <! pre[[↑ₓ xs \ ⇑ₜ ts]] !>} :
    w ## xs →
    NoDup w →
    NoDup xs →
    let ts₀ := (λ t : final_term, <! t[[ₜ ↑ₓ w, ↑ₓ xs \ ⇑₀ w, ⇑₀ xs]] !>) <$> ts in
    <{ *w, *xs : [pre[[↑ₓ xs \ ⇑ₜ ts]], post[[↑₀ xs \ *ts₀]]] }> ⊑
      <{ *xs := *(FinalRhsTerm <$> ts); *w, *xs : [pre, post] }>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 ? A. simpl. rewrite wp_asgn. rewrite simpl_msubst_and.
    fSimpl. unfold subst_initials at 1. rewrite subst_initials_app_comm.
    rewrite subst_initials_app. rewrite subst_initials_msubst.
    setoid_rewrite (msubst_trans _ (↑₀ xs) (↑ₓ xs) (⇑ₜ ts)); [| set_solver | |]...
    2:{ intros x ??. set_unfold. destruct H0 as [|]; [set_solver|].
        destruct H. destruct H0 as (x'&?&?&_&_). subst.
        rewrite to_final_var_as_var in H1. set_solver. }
    assert (zip_pair_functional ↑₀ xs ⇑ₜ ts).
    { apply NoDup_zip_pair_functional. apply NoDup_fmap... apply initial_var_of_inj. }
    assert (list_to_set ↑₀ xs ## ⋃ (term_fvars <$> ⇑ₜ ts)).
    { intros x ??. set_unfold in H0. set_unfold in H1. destruct H1 as (t&?&t'&?&?).
      subst. destruct H0 as []. apply final_term_final in H1. done. }
    assert (as_formula A ≡ <! A [[↑₀ xs \ *ts₀]] !>).
    { rewrite msubst_non_free... intros x ??. apply formula_is_final in H2. set_solver. }
    rewrite H1 at 1. clear H1. rewrite <- simpl_msubst_impl.
    assert (<! (∀* ↑ₓ (w ++ xs), (post ⇒ A) [ [↑₀ xs \ * ts₀] ]) !> ≡
              <! (∀* ↑ₓ (w ++ xs), (post ⇒ A)) [ [↑₀ xs \ * ts₀] ] !>).
    { rewrite simpl_msubst_foralllist; [auto|set_solver|]. intros x ??. set_unfold in H1.
      destruct H1 as []. set_unfold in H2. destruct H2 as (t&?&t'&?&?). subst.
      apply fvars_msubst_term_superset_vars_not_free_in_terms in H2...
      - set_unfold in H2. destruct H2 as [[] |].
        + apply Decidable.not_or in H4 as []. destruct H3.
          * apply H4. exists (to_final_var x). split... rewrite as_var_to_final_var.
            symmetry. apply var_with_is_initial_id. apply H1.
          * apply H6. exists (to_final_var x). split... rewrite as_var_to_final_var.
            symmetry. apply var_with_is_initial_id. apply H1.
        + destruct H2 as (t&?&?). destruct H4.
          * destruct H4 as (x'&->&?&?&?). simpl in H2. set_unfold in H2. subst x'.
            rewrite H4 in H1. unfold var_final in H1. simpl in H1. discriminate.
          * destruct H4 as (x'&->&?&?&?). simpl in H2. set_unfold in H2. subst x'.
            rewrite H4 in H1. unfold var_final in H1. simpl in H1. discriminate.
      - apply NoDup_app. do 2 rewrite NoDup_fmap by apply as_var_inj. set_solver.
      - apply disjoint_final_initial_vars; [set_solver|]. clear dependent x. intros x ??.
        rewrite <- fmap_app in H1. set_unfold in H1. destruct H1 as (t&?&x'&->&?).
        destruct H3; destruct H3 as (?&->&?); set_unfold in H1; subst x; done. }
    rewrite H1. clear H1.
    rewrite fold_subst_initials. rewrite subst_initials_app.
    rewrite (subst_initials_msubst xs). rewrite msubst_msubst_eq.
    2:{ apply NoDup_fmap... apply initial_var_of_inj. }
    rewrite subst_initials_msubst. rewrite msubst_msubst_disj.
    2:{ set_solver. }
    2-3: apply NoDup_fmap; auto; apply initial_var_of_inj.
    2:{ set_solver. }
    rewrite <- subst_initials_msubst. f_equiv. apply map_eq. intros x₀. unfold to_vtmap.
    destruct (decide (x₀ ∈ ↑₀ xs)).
    - apply elem_of_list_fmap in e as (x'&?&?). apply elem_of_list_lookup in H2 as (i&?).
      destruct (lookup_of_same_length_l ts H2) as (t&?). trans (Some (as_term t)).
      + rewrite lookup_list_to_map_zip_Some by typeclasses eauto. exists i. split_and!.
        * rewrite list_lookup_fmap. rewrite H2. simpl. rewrite H1...
        * unfold ts₀. repeat rewrite list_lookup_fmap. rewrite H3.
          simpl. f_equal.
          opose proof msubst_term_app. unfold to_vtmap in H4 at 2 3.
          assert (xs ## w) by set_solver.
          erewrite <- H4; clear H4... rewrite msubst_term_app_comm...
          opose proof (msubst_term_trans t (↑ₓ w ++ ↑ₓ xs) (↑₀ w ++ ↑₀ xs) (⇑ₓ w ++ ⇑ₓ xs)).
             trans (msubst_term t (to_vtmap (↑ₓ w ++ ↑ₓ xs) ((@TVar M <$> (as_var <$> w)) ++
                                                           (@TVar M <$> (as_var <$> xs))))).
             -- symmetry. etrans.
                ++ rewrite <- H4; clear dependent H4 H ts₀; [reflexivity| | | | ].
                   ** set_solver.
                   ** rewrite NoDup_app.
                      repeat rewrite NoDup_fmap; [| apply as_var_inj | apply as_var_inj].
                      set_solver.
                   ** rewrite <- fmap_app. apply NoDup_fmap; [apply initial_var_of_inj|].
                      apply NoDup_app...
                   ** clear dependent x₀ x'. intros x ??. set_unfold in H.
                      apply term_is_final in H1. destruct H as [[x' [? ?]] | [x' [? ?]]]; subst;
                        done.
                ++ f_equal. f_equal. unfold to_vtmap. f_equal. f_equal. rewrite fmap_app...
             -- unfold to_vtmap. repeat rewrite <- fmap_app. rewrite msubst_term_diag'...
                apply NoDup_fmap; [apply as_var_inj|]. apply NoDup_app...
        * intros. apply list_lookup_fmap_Some in H4 as (x''&?&?). rewrite H1 in H5.
          apply initial_var_of_inj in H5. subst x''. apply NoDup_lookup with (i:=i) in H4...
          lia.
      + symmetry. subst. apply lookup_list_to_map_zip_Some; [typeclasses eauto|]. exists i.
        split_and!...
        * rewrite list_lookup_fmap. rewrite H2. simpl...
        * rewrite list_lookup_fmap. rewrite H3. simpl...
        * intros. apply list_lookup_fmap_Some in H1 as (x''&?&?). apply initial_var_of_inj in H4.
          subst x''. apply NoDup_lookup with (i:=i) in H1... lia.
    - etrans.
      + apply lookup_list_to_map_zip_None... typeclasses eauto.
      + symmetry. apply lookup_list_to_map_zip_None... typeclasses eauto.
  Qed.


  (* Law 5.2 *)
  Lemma r_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ ⎡⇑₀ xs =* ⇑ₓ xs⎤ ∧ pre !> ⇛ <! post[[ ↑ₓ xs \ ⇑ₜ ts ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros Hlength Hnodup proviso A. simpl. rewrite wp_asgn.
    rewrite <- (f_subst_initials_final_formula pre (w ++ xs))...
    rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials. rewrite <- f_foralllist_one_point...
    rewrite f_foralllist_app. rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite fmap_app. reflexivity. }
    3: { do 2 rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_msubst_impl.
    fSimpl. rewrite <- f_eqlist_app.
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    3: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    setoid_rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
    apply msubst_formula_final.
    Unshelve. typeclasses eauto.
  Qed.

  Local Lemma r_asgn_equiv' xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    asgn_opens (split_asgn_list xs1 rhs1) ≡ₚ asgn_opens (split_asgn_list xs2 rhs2) →
    (asgn_xs (split_asgn_list xs1 rhs1), asgn_ts (split_asgn_list xs1 rhs1)) ≡ₚₚ
      (asgn_xs (split_asgn_list xs2 rhs2), asgn_ts (split_asgn_list xs2 rhs2)) →
    <{ * xs1 := * rhs1 }> ≡ <{ * xs2 := * rhs2 }>.
  Proof with auto.
    intros Hnodup1 Hnodup2 Hopens Hclosed A. unfold PAsgnWithOpens.
    destruct (split_asgn_list xs1 rhs1) eqn:E1. simpl in *.
    destruct (split_asgn_list xs2 rhs2) eqn:E2. simpl in *. apply wp_proper_pequiv.
    rewrite r_varlist_permute.
    2:{ apply Hopens. }
    f_equiv. clear A Hopens. intros A. simpl. apply msubst_zip_pair_Permutation.
    - apply NoDup_fmap.
      + apply as_var_inj.
      + eapply submseteq_NoDup; [exact Hnodup1|].
        replace asgn_xs with (Prog.asgn_xs (split_asgn_list xs1 rhs1)).
        * apply asgn_xs_submseteq.
        * rewrite E1. reflexivity.
    - apply NoDup_fmap.
      + apply as_var_inj.
      + eapply submseteq_NoDup; [exact Hnodup2|].
        replace asgn_xs0 with (Prog.asgn_xs (split_asgn_list xs2 rhs2)).
        * apply asgn_xs_submseteq.
        * rewrite E2. reflexivity.
    - apply zip_pair_Permutation_fmap; try typeclasses eauto...
  Qed.

  Lemma r_asgn_equiv xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    (xs1, rhs1) ≡ₚₚ (xs2, rhs2) →
    <{ * xs1 := * rhs1 }> ≡ <{ * xs2 := * rhs2 }>.
  Proof with auto.
    intros. apply r_asgn_equiv'...
    - apply asgn_opens_Permutation...
    - apply asgn_xs_ts_Permutation...
  Qed.

  Lemma wp_asgn_equiv (A : final_formula) xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    (xs1, rhs1) ≡ₚₚ (xs2, rhs2) →
    wp (PAsgnWithOpens xs1 rhs1) A ≡ wp (PAsgnWithOpens xs2 rhs2) A.
  Proof with auto. intros. apply r_asgn_equiv... Qed.

  Lemma r_open_assignment_l x t xs rhs
      `{!OfSameLength xs rhs}
      `{!OfSameLength ([x] ++ xs) ([OpenRhsTerm] ++ rhs)}
      `{!OfSameLength ([x] ++ xs) ([FinalRhsTerm t] ++ rhs)} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs, rhs) → as_var x ∉ term_fvars t') →
    <{ x, *xs := ?, *rhs }> ⊑ <{ x, *xs := t, *rhs }>.
  Proof with auto.
    intros. intros A. unfold PAsgnWithOpens. simpl.
    destruct (split_asgn_list (x :: xs) (OpenRhsTerm :: rhs)) eqn:E1.
    destruct (split_asgn_list (x :: xs) (FinalRhsTerm (as_final_term t) :: rhs)) eqn:E2.
    rewrite split_asgn_list_cons_open with (OfSameLength0:=OfSameLength0) in E1.
    rewrite split_asgn_list_cons_closed with (Hl1:=OfSameLength0) in E2.
    unfold asgn_args_with_open in E1. unfold asgn_args_with_closed in E2.
    simpl in E1, E2. destruct (split_asgn_list xs rhs) eqn:E3.
    inversion E1. inversion E2. subst.
    assert (asgn_opens0 = Prog.asgn_opens (split_asgn_list xs rhs)) as Heq1 by (rewrite E3; done).
    assert (asgn_xs = Prog.asgn_xs (split_asgn_list xs rhs)) as Heq2 by (rewrite E3; done).
    assert (asgn_ts = Prog.asgn_ts (split_asgn_list xs rhs)) as Heq3 by (rewrite E3; done).
    clear E1 E2 E3. simpl. repeat rewrite wp_varlist. simpl. rewrite f_forall_ty_top.
    rewrite f_forall_elim with (t:=t). rewrite simpl_subst_foralllist.
    2:{ intros contra. apply elem_of_list_fmap in contra. destruct contra as (x'&?&?).
        apply as_var_inj in H3. subst. eapply elem_of_submseteq in H4;
          [| apply asgn_opens_submseteq]... }
    2:{ intros y ??. set_unfold in H3. destruct H3 as []. apply H1 with (x':=(to_final_var y)).
        - subst. apply elem_of_asgn_opens in H5...
        - rewrite as_var_to_final_var_final... }
    rewrite <- msubst_extract_r.
    - simpl. reflexivity.
    - intros contra. apply elem_of_list_fmap in contra as (x'&?&?). apply as_var_inj in H3.
      subst. eapply elem_of_submseteq in H4; [| apply asgn_xs_submseteq]. done.
    - clear dependent t. set_unfold. intros (?&?&t&->&?). subst.
      apply elem_of_asgn_ts_inv in H3 as (xt&?).
      apply elem_of_asgn_xs_ts in H3... apply H2 in H3. contradiction.
  Qed.

  (* Law 3.1 *)
  Lemma r_open_assignment_r x t xs rhs
      `{!OfSameLength xs rhs}
      `{!OfSameLength (xs ++ [x]) (rhs ++ [OpenRhsTerm])}
      `{!OfSameLength (xs ++ [x]) (rhs ++ [FinalRhsTerm t])} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs, rhs) → as_var x ∉ term_fvars t') →
    <{ *xs, x := *rhs, ? }> ⊑ <{ *xs, x := *rhs, t }>.
  Proof with auto.
    intros. intros A.
    rewrite wp_asgn_equiv with (xs2:=[x] ++ xs) (rhs2:=[OpenRhsTerm] ++ rhs).
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        apply zip_pair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite wp_asgn_equiv with (xs1:=xs ++ [x]) (xs2:=[x] ++ xs) (rhs2:=[FinalRhsTerm t] ++ rhs)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        rewrite as_final_term_as_term. apply zip_pair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite (r_open_assignment_l x t xs rhs H H0 H1 H2 A). simpl.
    rewrite as_final_term_as_term. reflexivity.
  Qed.

  Lemma r_open_assignment_middle x t xs0 xs1 rhs0 rhs1
      `{!OfSameLength xs0 rhs0}
      `{!OfSameLength xs1 rhs1}
      `{!OfSameLength (xs0 ++ [x] ++ xs1) (rhs0 ++ [OpenRhsTerm] ++ rhs1)}
      `{!OfSameLength (xs0 ++ [x] ++ xs1) (rhs0 ++ [FinalRhsTerm t] ++ rhs1)} :
    (∀ x', (x', OpenRhsTerm) ∈ (xs0, rhs0) → as_var x' ∉ term_fvars t) →
    (∀ x', (x', OpenRhsTerm) ∈ (xs1, rhs1) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs0, rhs0) → as_var x ∉ term_fvars t') →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs1, rhs1) → as_var x ∉ term_fvars t') →
    x ∉ xs0 →
    x ∉ xs1 →
    NoDup xs0 →
    NoDup xs1 →
    xs0 ## xs1 →
    <{ *xs0, x, *xs1 := *rhs0, ?, *rhs1 }> ⊑ <{ *xs0, x, *xs1 := *rhs0, t, *rhs1 }>.
  Proof with auto.
    intros. intros A.
    rewrite wp_asgn_equiv with (xs2:=[x] ++ xs0 ++ xs1) (rhs2:=[OpenRhsTerm] ++ rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons. split... }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm...
        2: typeclasses eauto. simpl. apply zip_pair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zip_pair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    rewrite wp_asgn_equiv with (xs1:=xs0 ++ [x] ++ xs1) (xs2:=[x] ++ xs0 ++ xs1)
                                                    (rhs2:=[FinalRhsTerm t] ++ rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons.
        split... }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm...
        2: typeclasses eauto. simpl. rewrite as_final_term_as_term.
        apply zip_pair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zip_pair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    opose proof (r_open_assignment_l x t (xs0 ++ xs1) (rhs0 ++ rhs1) _ _ _ _ A).
    1:{ set_solver. }
    1:{ apply NoDup_app. split_and!... }
    1:{ intros. apply elem_of_zip_pair_app in H8... destruct H8... }
    1:{ intros. apply elem_of_zip_pair_app in H8... destruct H8...
        - eapply H1. apply H8.
        - eapply H2. apply H8. }
    rewrite H8. simpl. rewrite as_final_term_as_term. reflexivity.
  Qed.

  (* Law 4.1 *)
  Lemma r_alternation w pre post gs `{!FormulaFinal pre} :
    pre ⇛ <! ∨* ⤊ gs !> →
    <{ *w : [pre, post] }> ⊑ <{ if | g : gs → *w : [g ∧ pre, post] fi }>.
  Proof with auto.
    intros proviso A. simpl. rewrite fent_fent_st. intros σ.
    rewrite fent_fent_st in proviso. specialize (proviso σ).
    induction gs as [|g gs IH].
    - rewrite proviso. simpl. fSimpl...
    - simpl in *. fold (@fmap list _ final_formula formula) in *.
      fold (@fmap list _ (final_formula * prog)).
      fLem g.
      + fSimpl. fSplit... fLem pre.
        2:{ fSimpl... }
        fLem <! ∨* ⤊ gs !>.
        * forward IH... fSimpl. rewrite IH. intros ?. simp feval in H2. destruct H2 as [].
          assumption.
        * clear IH proviso H H0 g. induction gs as [|g gs IH]; simpl...
          simpl in *. apply f_or_equiv_st_false in H1 as []. rewrite H. fSimpl.
          rewrite IH...
      + fSimpl. forward IH...
  Qed.

  Lemma r_if_2 w pre post g1 g2 `{!FormulaFinal pre} :
    pre ⇛ <! g1 ∨ g2 !> →
    <{ *w : [pre, post] }> ⊑ <{ if g1 → *w : [g1 ∧ pre, post] | g2 → *w : [g2 ∧ pre, post] fi }>.
  Proof with auto.
    intros proviso.
    pose proof (r_alternation w pre post [g1; g2]). simpl in H. simpl.
    apply H. etrans.
    - apply proviso.
    - fSimpl. reflexivity.
  Qed.

  Lemma r_if_2_proper g1 g2 {p1 p1' p2 p2'} :
    p1 ⊑ p1' →
    p2 ⊑ p2' →
    <{ if g1 → $p1 | g2 → $p2 fi }> ⊑ <{ if g1 → $p1' | g2 → $p2' fi }>.
  Proof with auto.
    intros. intros A. simpl. fSimpl. rewrite (refines_total H).
    rewrite (refines_total H0). fSimpl. reflexivity.
  Qed.


  (* TODO: move these *)
  Definition nat_to_term (n : nat) : term :=
    TConst (nat_to_value n).

  Coercion nat_to_term : nat >-> term.

  (* Arguments raw_initial_var name : simpl never. *)

  Lemma initial_var_of_eq_to_initial_var (x : final_variable) :
    initial_var_of x = to_initial_var x.
  Proof. cbv. reflexivity. Qed.

  Lemma set_to_list_as_var_set_list_to_set w :
    NoDup w →
    set_to_list (as_var_set (list_to_set w)) ≡ₚ ↑ₓ w.
  Proof with auto.
    intros. unfold as_var_set. rewrite set_to_list_set_map_perm by exact as_var_inj.
    apply fmap_Permutation. apply set_to_list_list_to_set...
  Qed.

  Lemma r_iteration (w : list final_variable) (g : formula) (inv : final_formula) (var : final_term) `{!FormulaFinal g} :
    NoDup w →
    let var₀ := <! $(as_term var) [[ₜ ↑ₓ w \ ⇑₀ w ]] !> in
    <{ *w : [inv, inv ∧ ¬ g] }> ⊑
      <{ while g invariant inv variant var ⟶
         *w : [inv ∧ g, inv ∧ ⌜var ∈ₜ ℕ⌝ ∧ ⌜0 ≤ var⌝ ∧ ⌜var < var₀⌝] end }>.
  Proof with auto.
    intros Hnodup ? A. simpl. unfold modified_vars. simpl.
    rewrite (f_foralllist_permute (set_to_list (as_var_set (list_to_set w))) (↑ₓ w)).
    2:{ apply set_to_list_as_var_set_list_to_set... }
    rewrite f_subst_initials_no_initials.
    2:{ rewrite fvars_foralllist. simpl. intros x ??. set_unfold. destruct H as [].
        destruct H0 as [? _]. rename FormulaFinal0 into Final. unfold FormulaFinal in Final.
        unfold formula_final in Final. destruct_or! H0; try apply final_formula_final in H0... }
    intros σ. simp feval. simpl. repeat rewrite simpl_feval_foralllist. intros.
    destruct_and! H.
    assert (Haux1 : zip_pair_functional ↑ₓ w (@TConst M <$> vs)) by
      (apply NoDup_zip_pair_functional; auto).
    assert (Haux2 : list_to_set ↑ₓ w ## ⋃ (@term_fvars M <$> (TConst <$> vs))).
    { intros x ??. set_unfold in H3. destruct H3 as (t&?&vt&->&?). simpl in H3. set_solver. }
    rewrite seqsubst_msubst... epose proof (teval_vtmap_total σ _) as [mv ?].
    rewrite feval_msubst by exact H. simp feval. split_and!.
    - rewrite simpl_feval_fimpl. simp feval. intros. destruct_and! H3. split_and!...
      unfold subst_initials. rewrite seqsubst_msubst...
      epose proof (teval_vtmap_total _ _) as [mv0 ?].
      rewrite feval_msubst by exact H4. rewrite simpl_feval_foralllist. intros.
      rewrite seqsubst_msubst.
      2:{ apply NoDup_zip_pair_functional... }
      2:{ intros x ??. set_unfold in H9. destruct H9 as (?&?&?&->&?). simpl in H9. set_solver. }
      epose proof (teval_vtmap_total _ _) as [mv' ?].
      rewrite feval_msubst by exact H8. rewrite simpl_feval_fimpl. simp feval.
      intros [? []]. split...
    - specialize (H2 vs H0). apply seqsubst_msubst in H2...
      rewrite feval_msubst in H2 by exact H... rewrite simpl_feval_fimpl in H2 |- *.
      simp feval in H2 |- *. intros [[] ?]. apply H2. split...
    - rewrite simpl_feval_fimpl. simp feval. naive_solver.
    - rewrite simpl_feval_fimpl. simp feval. intros [[] []]. split_and!...
      unfold subst_initials. rewrite seqsubst_msubst...
      epose proof (teval_vtmap_total _ _) as [mv0 ?].
      rewrite feval_msubst by exact H7. rewrite simpl_feval_foralllist.
      intros vs' ?. rewrite seqsubst_msubst...
      2:{ apply NoDup_zip_pair_functional... }
      2:{ intros x ??. set_unfold in H10. destruct H10 as (?&?&?&->&?). set_solver. }
      epose proof (teval_vtmap_total _ _) as [mv' ?].
      rewrite feval_msubst by exact H9. rewrite simpl_feval_fimpl. simp feval.
      intros [? [? []]]. rewrite <- feval_msubst in H13 |- * by exact H9.
      unfold term_lt in H13 |- *. simp msubst in H13 |- *. simpl in H13 |- *.
      unfold var₀ in H13. eapply ATPred_proper_st in H13.
      2:{ reflexivity. }
      2:{ split.
          2:{ constructor; [reflexivity|constructor; [|reflexivity]].
              rewrite msubst_term_msubst_term_eq_cancel... reflexivity. }
          simpl... }
      rewrite <- feval_msubst in H13 |- * by exact H7. simp msubst in H13 |- *.
      simpl in H13 |- *. eapply ATPred_proper_st.
      1:{ reflexivity. }
      2:{ exact H13. }
      split... constructor; [reflexivity|]. constructor... simpl in H6.
      clear dependent H3 H4 H5 mv0 mv' H13 H2. destruct H6 as (vv&?&?).
      symmetry. etrans.
      + erewrite (msubst_term_trans var (↑ₓ w) (↑₀ w))...
        * rewrite msubst_term_diag... reflexivity.
        * set_solver.
        * intros x ??. set_unfold in H4. apply final_term_final in H5. naive_solver.
      + destruct (to_vtmap ↑ₓ w (TConst <$> vs')
                 !! to_initial_var (fresh_var String.EmptyString (as_var_set (list_to_set w)))
                 ) eqn:E.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E.
            2:{ typeclasses eauto. }
            apply elem_of_zip_pair in E as (i&?&?). apply list_lookup_fmap_Some in H4 as (x&?&?).
            destruct x. unfold as_var in H6. simpl in H6. apply (f_equal var_is_initial) in H6.
            simpl in H6. discriminate. }
        simpl. clear E.
        destruct (to_vtmap ↑₀ w ⇑ₓ w
                 !! to_initial_var (fresh_var String.EmptyString (as_var_set (list_to_set w))))
                   eqn:E.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E.
            2:{ typeclasses eauto. }
            apply elem_of_zip_pair in E as (i&?&?). apply list_lookup_fmap_Some in H4 as (x&?&?).
            rewrite initial_var_of_eq_to_initial_var in H6. apply to_initial_var_inj' in H6.
            - pose proof (fresh_var_fresh String.EmptyString (as_var_set (list_to_set w))).
              rewrite H6 in H7. apply elem_of_list_lookup_2 in H4. unfold as_var_set in H7.
              exfalso. apply H7. set_unfold. exists x. split...
            - apply fresh_var_final. unfold VarFinal, var_final. simpl...
            - apply var_final_as_var. }
        intros v. split; intros; apply teval_det with (v1:=vv) in H4; auto; subst...
  Qed.

  Lemma r_iteration'
    (w : list final_variable) (g : formula) (inv inv' post : final_formula) (var : final_term)
    `{!FormulaFinal g} :
    NoDup w →
    inv ≡ inv' →
    as_formula post ≡ <! inv ∧ ¬ g !> →
    let var₀ := <! $(as_term var) [[ₜ ↑ₓ w \ ⇑₀ w ]] !> in
    <{ *w : [inv, post] }> ⊑
      <{ while g invariant inv' variant var ⟶
         *w : [inv ∧ g, inv ∧ ⌜var ∈ₜ ℕ⌝ ∧ ⌜0 ≤ var⌝ ∧ ⌜var < var₀⌝] end }>.
  Proof with auto.
    intros. rewrite H1. etrans.
    - apply r_iteration...
    - apply pequiv_refines. f_equiv.
      2: reflexivity.
      + unfold equiv, ffequiv. simpl. fSimpl...
      + unfold var₀. done.
  Qed.

  Lemma feval_seqsubst_pi {xs : list variable} {ts H1 H2 σ A} :
    feval σ (@seqsubst M A xs ts H1) ↔ feval σ (@seqsubst M A xs ts H2).
  Proof. f_equiv. f_equiv. apply OfSameLength_pi. Qed.



  (* Lemma 7.1 *)
  Lemma r_remove_inv {w pre inv post} `{!FormulaFinal pre} `{!FormulaFinal inv} :
    list_to_set (↑ₓ w) ## formula_fvars inv →
    NoDup w →
    <{ *w : [pre ∧ inv, inv ∧ post] }> ⊑ <{ *w : [pre, post] }>.
  Proof with auto.
    intros Hdisj Hnodup. intros A. simpl. intros σ ?. simp feval in *. destruct_and! H.
    split...
    unfold subst_initials in *. rewrite seqsubst_msubst in *...
    epose proof (teval_vtmap_total σ _) as [mv ?].
    rewrite feval_msubst by exact H0.
    rewrite feval_msubst in H1 by exact H0.
    rewrite simpl_feval_foralllist in *. intros. specialize (H1 vs H3).
    rewrite seqsubst_msubst.
    2:{ apply NoDup_zip_pair_functional... }
    2:{ set_unfold. intros. destruct H5 as (?&?&?&?&?). subst. done. }
    epose proof (teval_vtmap_total _ _) as [mv' ?].
    rewrite feval_msubst by exact H4.
    rewrite seqsubst_msubst in H1.
    2:{ apply NoDup_zip_pair_functional... }
    2:{ set_unfold. intros. destruct H6 as (?&?&?&?&?). subst. done. }
    rewrite feval_msubst in H1 by exact H4. rewrite simpl_feval_fimpl in *.
    intros. apply H1. simp feval. split... rewrite <- feval_msubst by exact H4.
    rewrite msubst_non_free... rewrite <- feval_msubst by exact H0.
    rewrite msubst_non_free... set_solver.
  Qed.

End refinement.
