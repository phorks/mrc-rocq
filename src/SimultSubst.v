From Equations Require Import Equations.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import SeqNotation.
From MRC Require Import Model.
From MRC Require Import PredCalcBasic.
From MRC Require Import PredCalcEquiv.
From MRC Require Import PredCalcSubst.
From MRC Require Import PredCalcFacts.

Section simult_subst.
  Context {M : model}.

  Local Notation term := (term (value M)).
  Local Notation atomic_formula := (atomic_formula (value M)).
  Local Notation formula := (formula (value M)).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A : formula.
  Implicit Types m : gmap variable term.

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

  Definition simult_subst_map_fvars m : gset variable :=
    ⋃ (term_fvars ∘ snd <$> map_to_list m).

  Definition quant_simult_subst_fvars y A m :=
    (formula_fvars A ∖ {[y]}) ∪ simult_subst_map_fvars m ∪ dom m.

  Lemma quant_simult_subst_fvars_inv y' y A m :
    y' ∉ quant_simult_subst_fvars y A m →
    (y = y' ∨ y' ∉ formula_fvars A) ∧ (y' ∉ dom m) ∧ (∀ x t, m !! x = Some t → y' ∉ term_fvars t).
  Proof with auto.
    intros. unfold quant_simult_subst_fvars in H. do 2 rewrite not_elem_of_union in H.
    destruct_and! H. split_and!...
    - apply not_elem_of_difference in H. set_solver.
    - clear H H1. unfold simult_subst_map_fvars in H2. unfold not in H2.
      rewrite elem_of_union_list in H2. intros. destruct (decide (y' ∈ term_fvars t))...
      exfalso. apply H2. clear H2. exists (term_fvars t). split...
      assert (<[x:=t]> (delete x m) = m) as <- by (apply insert_delete; assumption).
      rewrite map_to_list_insert.
      2:{ rewrite lookup_delete... }
      simpl. apply elem_of_cons. left...
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
        FExists y' (simult_subst (A[y \ y']) m).
  Proof.
    all: try (simpl; lia).
    unfold rank. simpl. fold Nat.add. pose proof (subst_preserves_shape A y (y')).
    deduce_rank_eq H. rewrite Hfr. rewrite Hqr. lia.
  Qed.

  Definition to_simult_subst_map (xs : list variable) (ts : list term)
    `{LengthEqLists variable term xs ts}: gmap variable term := list_to_map (zip xs ts).


  Notation "A [[ xs \ ts ]]" := (simult_subst A (to_simult_subst_map xs ts))
                              (at level 10, left associativity,
                                xs custom seq_notation,
                                ts custom seq_notation) : refiney_scope.

  Notation "A [[ xs \ ts ]]" := (simult_subst A (to_simult_subst_map xs ts))
                              (in custom formula at level 74, left associativity,
                                xs custom seq_notation,
                                ts custom seq_notation) : refiney_scope.

  Lemma simult_subst_term_id t m :
    term_fvars t ∩ dom m = ∅ →
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
    af_fvars af ∩ dom m = ∅ →
    simult_subst_af af m = af.
  Proof with auto.
    intros H.
    destruct af...
    - simpl. simpl in H. do 2 rewrite simult_subst_term_id by set_solver...
    - simpl. f_equal. induction args... simpl in H. simpl in *. f_equal.
      + rewrite simult_subst_term_id... set_solver.
      + apply IHargs. set_solver.
  Qed.

  Tactic Notation "generalize_fresh_var_for_simult_subst"
      ident(y) constr(A) constr(m) "as" ident(y') :=
    let Hfresh := fresh in
    let Heq := fresh in
    let H1 := fresh in let H2 := fresh in let H3 := fresh in
    pose proof (Hfresh := fresh_var_fresh y (quant_simult_subst_fvars y A m));
    apply quant_simult_subst_fvars_inv in Hfresh as (H1&H2&H3);
    remember (fresh_var y (quant_simult_subst_fvars y A m)) as y' eqn:Heq;
    clear Heq.

  Lemma simult_subst_id A m :
    formula_fvars A ∩ dom m = ∅ →
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

  Lemma simult_subst_term_empty t :
    simult_subst_term t ∅ = t.
  Proof. apply simult_subst_term_id. set_solver. Qed.

  Lemma simult_subst_af_empty af :
    simult_subst_af af ∅ = af.
  Proof. apply simult_subst_af_id. set_solver. Qed.

  Lemma simult_subst_empty A :
    simult_subst A ∅ ≡ A.
  Proof. apply simult_subst_id. set_solver. Qed.

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

  Lemma simult_subst_delete_non_free A x m :
    x ∉ formula_fvars A →
    simult_subst A m ≡ simult_subst A (delete x m).
  Proof with auto.
    intros. induction A; simp simult_subst.
    - rewrite <- simult_subst_af_delete_non_free...
    - rewrite IHA...
    - rewrite IHA1 by set_solver. rewrite IHA2 by set_solver...
    - rewrite IHA1 by set_solver. rewrite IHA2 by set_solver...
    - simpl. rename x0 into y.
      generalize_fresh_var_for_simult_subst y A m as y1.
      generalize_fresh_var_for_simult_subst y A (delete x m) as y2.
      rewrite <- H0...
      2: { admit. }
      intros σ. apply feval_exists_equiv_if. intros v.
      f_equiv. simpl.



      (* rewrite <- H0... *)
      (* +  *)


  Lemma simult_subst_term_extract t0 x t m :
    m !! x = Some t →
    (term_fvars t ∩ dom (delete x m) = ∅) →
    (x ∉ simult_subst_map_fvars (delete x m)) →
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
    (term_fvars t ∩ dom (delete x m) = ∅) →
    (x ∉ simult_subst_map_fvars (delete x m)) →
    simult_subst_af af m = simult_subst_af (subst_af af x t) (delete x m).
  Proof with auto.
    destruct af; simpl; intros...
    - simpl. f_equal; apply simult_subst_term_extract...
    - simpl. f_equal. induction args... simpl. f_equal...
      apply simult_subst_term_extract...
  Qed.

  Lemma simult_subst_extract A x t m :
    m !! x = Some t →
    (term_fvars t ∩ dom (delete x m) = ∅) →
    (x ∉ simult_subst_map_fvars (delete x m)) →
    simult_subst A m ≡ simult_subst (A[x \ t]) (delete x m).
  Proof with auto.
    induction A; simp simult_subst; simpl; intros.
    - rewrite simpl_subst_af. rewrite (simult_subst_af_extract af x t m)...
    - rewrite simpl_subst_not. simp simult_subst. rewrite IHA...
    - rewrite simpl_subst_and. simpl. simp simult_subst. rewrite IHA1... rewrite IHA2...
    - rewrite simpl_subst_or. simpl. simp simult_subst. rewrite IHA1... rewrite IHA2...
    - rename x0 into y. destruct (decide (x = y)).
      + subst. rewrite simpl_subst_exists_skip... simp simult_subst.
        simpl.
        generalize_fresh_var_for_simult_subst y A m as y1.
        generalize_fresh_var_for_simult_subst y A (delete y m) as y2.
        admit.
      + rewrite simpl_subst_exists_propagate.
        2: { admit. }
        2: { admit. }
        generalize_fresh_var_for_simult_subst y A m as y1.
        generalize_fresh_var y A x t as y2.
        simp simult_subst.
        constr ident constr as ident
        generalize_fresh_var_for_simult_subst y A (delete y m) as y2.
        rewrite simult_subst_non_free.

      +
      destruct (decide ())



      generalize_fresh_var_for_simult_subst x A (∅ : gmap variable term) as y'.
      intros σ. apply feval_exists_equiv_if. intros v. rewrite H...
      destruct H2.
      + subst. rewrite fequiv_subst_diag...
      + rewrite (fequiv_subst_trans A x y' (TConst v))...
  Qed.
End simult_subst.
