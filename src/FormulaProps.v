From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc PredCalcEquiv PredCalcSubst PredCalcFacts.

Open Scope mrc_scope.
Section props.
  Context {M : model}.

  Implicit Types t : @term (value M).
  Implicit Types sf : @simple_formula (value M).
  Implicit Types A B C : @formula (value M).
  Implicit Types v : value M.

  Ltac prove_equiv := intros; intros σ; unfold FIff, FImpl; simp feval;
                      split; try (pose proof (@feval_lem M); naive_solver).

  Lemma f_and_commute A B :
    <! A ∧ B !> ≡ <! B ∧ A !>.
  Proof. prove_equiv. Qed.

  Lemma f_or_commute A B :
      <! A ∨ B !> ≡ <! B ∨ A !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_idemp A :
    <! A ∧ A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma f_or_idemp A :
    <! A ∨ A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_assoc A B C :
    <! A ∧ (B ∧ C) !> ≡ <! (A ∧ B) ∧ C !>.
  Proof. prove_equiv. Qed.

  Lemma f_or_assoc A B C :
      <! A ∨ (B ∨ C) !> ≡ <! (A ∨ B) ∨ C !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_absorption A B :
    <! A ∧ (A ∨ B) !> ≡ A.
  Proof. prove_equiv. Qed.

  Lemma f_or_absorption A B :
    <! A ∨ (A ∧ B) !> ≡ A.
  Proof. prove_equiv. Qed.

  Lemma f_and_or_distr A B C :
    <! A ∧ (B ∨ C) !> ≡ <! (A ∧ B) ∨ (A ∧ C) !>.
  Proof. prove_equiv. Qed.

  Lemma f_or_and_distr A B C :
    <! A ∨ (B ∧ C) !> ≡ <! (A ∨ B) ∧ (A ∨ C) !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_true A :
    <! A ∧ true !> ≡ A.
  Proof. prove_equiv. Qed.

  Lemma f_or_true A :
    <! A ∨ true !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_false A :
    <! A ∧ false !> ≡ <! false !>.
  Proof. prove_equiv. Qed.

  Lemma f_or_false A :
    <! A ∨ false !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma f_not_true : <! ¬ true !> ≡@{@formula (value M)} <! false !>.
  Proof. prove_equiv. Qed.

  Lemma f_not_false : <! ¬ false !> ≡@{@formula (value M)} <! true !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_not_self A :
    <! A ∧ ¬ A !> ≡ <! false !>.
  Proof. prove_equiv. Qed.

  Lemma f_excluded_middle A :
      <! A ∨ ¬ A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  Lemma f_not_stable A :
    <! ¬ ¬ A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma f_not_and A B :
    <! ¬ (A ∧ B) !> ≡ <! ¬ A ∨ ¬ B !>.
  Proof. prove_equiv. Qed.

  Lemma f_not_or A B :
      <! ¬ (A ∨ B) !> ≡ <! ¬ A ∧ ¬ B !>.
  Proof. prove_equiv. Qed.

  Lemma f_or_not_absorption A B :
      <! A ∨ (¬ A ∧ B) !> ≡ <! A ∨ B !>.
  Proof. prove_equiv. Qed.

  Lemma f_and_not_absorption A B :
    <! A ∧ (¬ A ∨ B) !> ≡ <! A ∧ B !>.
  Proof. prove_equiv. Qed.

  (* A.22 *)
  Lemma f_imp_equiv_or A B :
    <! A => B !> ≡ <! ¬ A ∨ B !>.
  Proof. prove_equiv. Qed.

  (* A.23 *)
  Lemma f_implies_self A :
    <! A => A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.24 *)
  Lemma f_impl_as_not_and A B :
    <! A => B !> ≡ <! ¬ (A ∧ ¬ B) !>.
  Proof. prove_equiv. Qed.

  (* A.25 *)
  Lemma f_not_impl_as_and A B :
      <! ¬ (A => B) !> ≡ <! A ∧ ¬ B !>.
  Proof. prove_equiv. Qed.

  (* A.26 *)
  Lemma f_contrapositive A B :
      <! A => B !> ≡ <! ¬ B => ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.27 *)
  Lemma f_implies_true A :
    <! A => true !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.28 *)
  Lemma f_true_implies A :
      <! true => A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  (* A.29 *)
  Lemma f_implies_false A :
    <! A => false !> ≡ <! ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.30 *)
  Lemma f_false_implies A :
      <! false => A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.31 *)
  Lemma f_implies_not_self A :
      <! A => ¬ A !> ≡ <! ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.32 *)
  Lemma f_not_implies_self A :
      <! ¬ A => A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  (* A.33 *)
  Lemma f_impl_distr1 A B C :
      <! C => (A ∧ B) !> ≡ <! (C => A) ∧ (C => B) !>.
  Proof. prove_equiv. Qed.

  (* A.34 *)
  Lemma f_impl_distr2 A B C :
    <! (A ∨ B) => C !> ≡ <! (A => C) ∧ (B => C) !>.
  Proof. prove_equiv. Qed.

  (* A.35 *)
  Lemma f_impl_distr3 A B C :
    <! C => (A ∨ B) !> ≡ <! (C => A) ∨ (C => B) !>.
  Proof. prove_equiv. Qed.

  (* A.36 *)
  Lemma f_impl_distr4 A B C :
    <! (A ∧ B) => C !> ≡ <! (A => C) ∨ (B => C) !>.
  Proof with auto.
    unfold FImpl. intros σ. simp feval. split; [| naive_solver].
    intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec.
  Qed.

  (* A.37 *)
  Lemma f_successive_hypotheses A B C :
    <! A => (B => C) !> ≡ <! (A ∧ B) => C !>.
  Proof with auto.
    unfold FImpl. intros σ. simp feval. split; [naive_solver |].
    intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec.
  Qed.

  (* A.37 *)
  Lemma f_successive_hypotheses' A B C :
    <! B => (A => C) !> ≡ <! (A ∧ B) => C !>.
  Proof with auto.
    unfold FImpl. intros σ. simp feval. split; [naive_solver |].
    intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec.
  Qed.

  (* A.38 *)
  Lemma f_def_by_cases A B C :
    <! (A => B) ∧ (¬A => C) !> ≡ <! (A ∧ B) ∨ (¬A ∧ C) !>.
  Proof. prove_equiv. Qed.

  (* A.39 *)
  Lemma f_iff_equiv1 A B C :
    <! A <=> B !> ≡ <! (A => B) ∧ (B => A) !>.
  Proof. prove_equiv. Qed.

  (* A.40 *)
  Lemma f_iff_equiv2 A B :
    <! A <=> B !> ≡ <! (A ∧ B) ∨ ¬(A ∨ B) !>.
  Proof. prove_equiv. Qed.

  (* A.41 *)
  Lemma f_iff_equiv3 A B :
    <! A <=> B !> ≡ <! ¬A <=> ¬B !>.
  Proof. prove_equiv. Qed.

  (* A.42 *)
  Lemma f_iff_self A :
    <! A <=> A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.43 *)
  Lemma f_iff_not_self A :
    <! A <=> ¬ A !> ≡ <! false !>.
  Proof. prove_equiv. Qed.

  (* A.44 *)
  Lemma f_iff_true A :
    <! A <=> true !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  (* A.45 *)
  Lemma f_iff_false A :
    <! A <=> false !> ≡ <! ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.46 *)
  Lemma f_impl_equiv_iff A B :
    <! A => B !> ≡ <! A <=> (A ∧ B) !>.
  Proof. prove_equiv. Qed.

  (* A.47 *)
  Lemma f_impl_equiv_iff2 A B :
    <! B => A !> ≡ <! A <=> (A ∨ B) !>.
  Proof with auto.
    intros σ. unfold FIff, FImpl. simp feval. split.
    - intros [|]; [|naive_solver]. split.
      + pose proof (feval_lem σ A). destruct H0 as [|]...
      + pose proof (feval_lem σ A) as [|]; naive_solver.
    - intros []. destruct_or! H; naive_solver.
  Qed.

  (* A.48 *)
  Lemma f_or_equiv_iff A B C :
    <! A ∨ (B <=> C) !> ≡ <! (A ∨ B) <=> (A ∨ C) !>.
  Proof with auto.
    intros σ. unfold FIff, FImpl. simp feval. split; [|naive_solver].
    intros [|[]]; [naive_solver|]. split; destruct (feval_lem σ A); naive_solver.
  Qed.

  (* A.49 *)
  Lemma f_equiv_comm A B :
    <! A <=> B !> ≡ <! B <=> A !>.
  Proof. prove_equiv. Qed.

  (* A.50 *)
  Lemma f_equiv_assoc A B C :
      <! A <=> (B <=> C) !> ≡ <! (A <=> B) <=> C !>.
  Proof.
    unfold FIff, FImpl. rewrite f_not_and.
    repeat rewrite f_not_and. repeat rewrite f_not_or. repeat rewrite f_not_stable.
    intros σ. simp feval. split; naive_solver.
  Qed.

  (* A.56 *)
  Lemma f_exists_one_point x t A :
      x ∉ term_fvars t →
      <! exists x, x = t ∧ A !> ≡ <! A[x \ t] !>.
  Proof with auto.
    intros Hfree σ. simp feval. setoid_rewrite simpl_subst_and.
    setoid_rewrite simpl_subst_sf. simpl. destruct (decide (x = x)); [|contradiction].
    clear e. split.
    - intros [v Hv]. simp feval in Hv. destruct Hv as [H1 H2]. inversion H1.
      destruct H as []. inversion H. subst v0 x0. clear H H1.
      (* TODO: teval_subst looks ugly match it with feval_subst *)
      rewrite <- (@teval_subst _ _ _ _ _ v _) in H0...
      apply teval_delete_state_var_head in H0... rewrite (feval_subst v)...
      rewrite <- (feval_subst _ (TConst v))...
    - intros. pose proof (teval_total σ t) as [v Hv]. exists v. simp feval. split.
      + simpl. exists v. split... rewrite <- (@teval_subst _ _ _ _ _ v _)...
        rewrite teval_delete_state_var_head...
      + rewrite (feval_subst v) in H... rewrite (feval_subst v)...
  Qed.

  (* A.56 *)
  Lemma f_forall_one_point x t A :
      x ∉ term_fvars t →
      <! forall x, x = t => A !> ≡ <! A[x \ t] !>.
  Proof with auto.
    intros Hfree. unfold FForall. rewrite f_not_impl_as_and.
    apply (f_exists_one_point x t(FNot A)) in Hfree. rewrite Hfree.
    rewrite simpl_subst_not. rewrite f_not_stable...
  Qed.

  (* A.60 *)
  Lemma f_exists_idemp x A :
    <! exists x x, A !> ≡ <! exists x, A !>.
  Proof with auto. rewrite fexists_unused... simpl. set_solver. Qed.

  (* A.59 *)
  Lemma f_forall_idemp x A :
    <! forall x x, A !> ≡ <! forall x, A !>.
  Proof with auto. unfold FForall. rewrite f_not_stable. rewrite f_exists_idemp... Qed.

  (* A.61 *)
  Lemma f_not_forall x A :
    <! ¬ forall x, A !> ≡ <! exists x, ¬ A !>.
  Proof. unfold FForall. rewrite f_not_stable. auto. Qed.

  (* A.62 *)
  Lemma f_not_exists x A :
    <! ¬ exists x, A !> ≡ <! forall x, ¬ A !>.
  Proof. unfold FForall. rewrite f_not_stable. auto. Qed.

  (* A.64 *)
  Lemma f_exists_comm x y A :
    <! exists x y, A !> ≡ <! exists y x, A !>.
  Proof with auto.
    intros σ. destruct (decide (x = y)). 1:{ subst... }
    destruct (decide (x ∈ formula_fvars A)).
    2:{ rewrite fexists_unused.
        - rewrite (fexists_unused x)...
        - simpl. set_solver. }
    destruct (decide (y ∈ formula_fvars A)).
    2:{ rewrite (fexists_unused y)...
        rewrite (fexists_unused y)... simpl. set_solver. }
    simp feval. split.
    - intros [vx H]. rewrite (feval_subst vx) in H... simp feval in H. destruct H as [vy H].
      rewrite (feval_subst vy) in H... exists vy. rewrite (feval_subst vy)...
      simp feval. exists vx. rewrite (feval_subst vx)... rewrite (insert_commute σ)...
    - intros [vy H]. rewrite (feval_subst vy) in H... simp feval in H. destruct H as [vx H].
      rewrite (feval_subst vx) in H... exists vx. rewrite (feval_subst vx)...
      simp feval. exists vy. rewrite (feval_subst vy)... rewrite (insert_commute σ)...
  Qed.

  (* A.63 *)
  Lemma f_forall_comm x y A :
    <! forall x y, A !> ≡ <! forall y x, A !>.
  Proof. unfold FForall. do 2 rewrite f_not_stable. rewrite f_exists_comm. reflexivity. Qed.

  (* A.66 *)
  Lemma f_exists_or x A B :
    <! exists x, A ∨ B !> ≡ <! (exists x, A) ∨ (exists x, B) !>.
  Proof with auto.
    intros σ. simp feval. setoid_rewrite simpl_subst_or. split.
    - intros [v H]. simp feval in H. destruct H as [|]; [left|right]; exists v...
    - intros [[v H] | [v H]]; exists v; simp feval...
  Qed.

  (* A.65 *)
  Lemma f_forall_and x A B :
    <! forall x, A ∧ B !> ≡ <! (forall x, A) ∧ (forall x, B) !>.
  Proof. unfold FForall. rewrite f_not_and. rewrite f_exists_or. rewrite f_not_or; auto. Qed.

  (* A.67 *)
  Lemma f_exists_impl x A B :
    <! exists x, A => B !> ≡ <! (forall x, A) => (exists x, B) !>.
  Proof with auto.
    intros σ. unfold FImpl. rewrite f_exists_or. unfold FForall. rewrite f_not_stable...
  Qed.

  (* A.68 *)
  Lemma f_forall_ent_exists x A :
    <! forall x, A !> ⇛ <! exists x, A !>.
  Proof.
    intros σ. rewrite simpl_feval_fforall. intros. simp feval.
    exists ⊥. apply H.
  Qed.

  (* A.69 *)
  Lemma f_or_forall x A B :
    <! (forall x, A) ∨ (forall x, B) !> ⇛ <! forall x, A ∨ B !>.
  Proof.
    intros σ. simp feval. do 3 rewrite simpl_feval_fforall.
    setoid_rewrite simpl_subst_or.
    intros [|]; intros; simp feval; naive_solver.
  Qed.

  (* A.70 *)
  Lemma f_forall_impl x A B :
    <! forall x, A => B !> ⇛ <! (forall x, A) => (forall x, B) !>.
  Proof.
    intros σ. rewrite simpl_feval_fimpl. do 3 rewrite simpl_feval_fforall.
    intros. specialize (H v). rewrite simpl_subst_impl in H. rewrite simpl_feval_fimpl in H.
    naive_solver.
  Qed.

  (* A.71 *)
  Lemma f_exists_and x A B :
    <! exists x, A ∧ B !> ⇛ <! (exists x, A) ∧ (exists x, B) !>.
  Proof with auto.
    intros σ. simp feval. intros [v H]. rewrite simpl_subst_and in H. simp feval in H.
    destruct H as []. split; exists v...
  Qed.

  (* A.72 *)
  Lemma fimpl_fexists x A B :
    <! (exists x, A) => (exists x, B) !> ⇛ <! exists x, A => B !>.
  Proof with auto.
    intros σ. rewrite simpl_feval_fimpl. intros. simp feval.
    setoid_rewrite simpl_subst_impl. setoid_rewrite simpl_feval_fimpl.
    destruct (feval_lem σ <! exists x, A !>).
    - apply H in H0. simp feval in H0. destruct H0 as [v Hv]. exists v. intros...
    - exists ⊥. intros. simp feval in H0. exfalso. apply H0. exists ⊥...
  Qed.

  (* A.73 *)
  Lemma fexists_fforall x y A :
    <! exists x, (forall y, A) !> ⇛ <! forall y, (exists x, A) !>.
  Proof with auto.
    intros σ. simp feval. rewrite simpl_feval_fforall. intros [vx H] vy.
    destruct (decide (x = y)).
    1:{ subst y. rewrite simpl_subst_forall_skip in H... rewrite simpl_subst_exists_skip...
        apply f_forall_ent_exists in H... }
    rewrite (feval_subst vx) in H... rewrite simpl_feval_fforall in H.
    specialize (H vy). rewrite (feval_subst vy) in H...
    rewrite (feval_subst vy)... simp feval. exists vx. rewrite (feval_subst vx)...
    rewrite (insert_commute σ)...
  Qed.

  (* A.74: fforall_unused *)
  (* A.75: fequiv_forall_non_free_binder *)

  (* A.76 *)
  Lemma f_forall_and_unused_l x A B :
    x ∉ formula_fvars A →
    <! forall x, A ∧ B !> ≡ <! A ∧ (forall x, B) !>.
  Proof with auto. intros. rewrite f_forall_and. rewrite fforall_unused... Qed.

  (* A.76' *)
  Lemma f_forall_and_unused_r x A B :
    x ∉ formula_fvars B →
    <! forall x, A ∧ B !> ≡ <! (forall x, A) ∧ B !>.
  Proof with auto. intros. rewrite f_forall_and. rewrite (fforall_unused x B)... Qed.

  (* A.77 *)
  Lemma f_forall_or_unused_l x A B :
    x ∉ formula_fvars A →
    <! forall x, A ∨ B !> ≡ <! A ∨ (forall x, B) !>.
  Proof with auto.
    intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_or.
    split; intros.
    - simp feval. destruct (feval_lem σ A)... right. rewrite simpl_feval_fforall.
      intros. specialize (H0 v). simp feval in H0. destruct H0...
      rewrite (feval_subst v) in H0... apply feval_delete_state_var_head in H0...
      contradiction.
    - simp feval in *. rewrite (feval_subst v)... rewrite feval_delete_state_var_head...
      destruct H0... right. rewrite simpl_feval_fforall in H0. apply H0.
  Qed.

  (* A.77' *)
  Lemma f_forall_or_unused_r x A B :
    x ∉ formula_fvars B →
    <! forall x, A ∨ B !> ≡ <! (forall x, A) ∨ B !>.
  Proof with auto.
    intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_or.
    split; intros.
    - simp feval. destruct (feval_lem σ B)... left. rewrite simpl_feval_fforall.
      intros. specialize (H0 v). simp feval in H0. destruct H0...
      rewrite (feval_subst v) in H0... apply feval_delete_state_var_head in H0...
      contradiction.
    - simp feval in *. destruct H0.
      + left. rewrite simpl_feval_fforall in H0. apply H0...
      + right. rewrite (feval_subst v)... rewrite feval_delete_state_var_head...
  Qed.

  (* A.78 *)
  Lemma f_forall_impl_unused_l x A B :
    x ∉ formula_fvars A →
    <! forall x, A => B !> ≡ <! A => (forall x, B) !>.
  Proof with auto.
    intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_impl.
    rewrite simpl_feval_fimpl.
    split; intros.
    - rewrite simpl_feval_fforall. intros. specialize (H0 v). rewrite simpl_feval_fimpl in H0.
      rewrite (feval_subst v) in H0... rewrite feval_delete_state_var_head in H0...
    - rewrite simpl_feval_fimpl. intros. rewrite (feval_subst v) in H1...
      rewrite feval_delete_state_var_head in H1... apply H0 in H1.
      rewrite simpl_feval_fforall in H1...
  Qed.

  (* A.79 *)
  Lemma f_forall_impl_unused_r x A B :
    x ∉ formula_fvars B →
    <! forall x, A => B !> ≡ <! (exists x, A) => B !>.
  Proof with auto.
    intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_impl.
    setoid_rewrite simpl_feval_fimpl. simp feval.
    split; intros.
    - destruct H1 as [v Hv]. apply H0 in Hv. apply (feval_subst v) in Hv...
      apply feval_delete_state_var_head in Hv...
    - forward H0 by (exists v)... apply (feval_subst v)... apply feval_delete_state_var_head...
  Qed.

  (* A.80 *)
  Lemma f_exists_and_unused_l x A B :
    x ∉ formula_fvars A →
    <! exists x, A ∧ B !> ≡ <! A ∧ (exists x, B) !>.
  Proof with auto.
    intros. rewrite <- (f_not_stable A). rewrite <- (f_not_stable B). rewrite <- (f_not_or).
    rewrite <- (f_not_forall). rewrite f_forall_or_unused_l by (simpl; auto).
    rewrite f_not_or. rewrite f_not_forall...
  Qed.

  (* A.80' *)
  Lemma fexists_fand_unused_r x A B :
    x ∉ formula_fvars B →
    <! exists x, A ∧ B !> ≡ <! (exists x, A) ∧ B !>.
  Proof with auto.
    intros. rewrite <- (f_not_stable A). rewrite <- (f_not_stable B). rewrite <- (f_not_or).
    rewrite <- (f_not_forall). rewrite f_forall_or_unused_r by (simpl; auto).
    rewrite f_not_or. rewrite f_not_forall...
  Qed.

  (* A.81 *)
  Lemma fexists_for_unused_l x A B :
    x ∉ formula_fvars A →
    <! exists x, A ∨ B !> ≡ <! A ∨ (exists x, B) !>.
  Proof with auto. intros. rewrite f_exists_or. rewrite fexists_unused... Qed.

  (* A.81' *)
  Lemma fexists_for_unused_r x A B :
    x ∉ formula_fvars B →
    <! exists x, A ∨ B !> ≡ <! (exists x, A) ∨ B !>.
  Proof with auto. intros. rewrite f_exists_or. rewrite (fexists_unused _ B)... Qed.

  (* A.82 *)
  Lemma fexists_fimpl_unused_l x A B :
    x ∉ formula_fvars A →
    <! exists x, A => B !> ≡ <! A => (exists x, B) !>.
  Proof with auto. intros. rewrite f_exists_impl. rewrite fforall_unused... Qed.

  (* A.83 *)
  Lemma fexists_fimpl_unused_r x A B :
    x ∉ formula_fvars B →
    <! exists x, A => B !> ≡ <! (forall x, A) => B !>.
  Proof with auto. intros. rewrite f_exists_impl. rewrite fexists_unused... Qed.

  (* A.84: fforall_alpha_equiv *)
  (* A.85: fexists_alpha_equiv *)

  (* A.86 *)
  Lemma f_forall_elim t x A :
    <! forall x, A !> ⇛ A[x \ t].
  Proof with auto.
    intros σ. rewrite simpl_feval_fforall. intros. pose proof (teval_total σ t) as [v Hv].
    specialize (H v). rewrite (feval_subst v) in H... rewrite (feval_subst v)...
  Qed.

  (* A.86 *)
  Lemma f_exists_intro t x A :
    A[x \ t] ⇛ <! exists x, A !>.
  Proof with auto.
    intros σ. simp feval. intros. pose proof (teval_total σ t) as [v Hv].
    exists v. rewrite (feval_subst v) in H... rewrite (feval_subst v)...
  Qed.

End props.
