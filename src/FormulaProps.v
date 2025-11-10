From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc PredCalcEquiv PredCalcSubst PredCalcFacts.

Open Scope mrc_scope.
(* Ltac prove_equiv_by_inversion := *)
(*   let HTT := fresh "HTT" in *)
(*   let HFF := fresh "HFF" in *)
(*   assert (HTT:=feval_true_true); *)
(*   assert (HFF:=feval_false_false); *)
(*   right; *)
(*   repeat match goal with *)
(*   | H : feval _ _ _ (F_Not _) true |- _ => *)
(*     apply feval_not_true_iff in H *)
(*   | H : feval _ _ _ (F_Not _) false |- _ => *)
(*     apply feval_not_false_iff in H *)
(*   | H : feval _ _ _ (F_And _ _) true |- _ => *)
(*     let H1 := fresh "H1" in *)
(*     let H2 := fresh "H2" in *)
(*     apply feval_and_true_iff in H as [H1 H2] *)
(*   | H : feval _ _ _ (F_And _ _) false |- _ => *)
(*     apply feval_and_false_iff in H as [H | H] *)
(*   | H : feval _ _ _ (F_Or _ _) true |- _ => *)
(*     apply feval_or_true_iff in H as [H | H] *)
(*   | H : feval _ _ _ (F_Or _ _) false |- _ => *)
(*     let H1 := fresh "H1" in *)
(*     let H2 := fresh "H2" in *)
(*     apply feval_or_false_iff in H as [H1 H2] *)
(*   | H : feval _ _ _ (F_Implies _ _) true |- _ => *)
(*     apply feval_implication_true_iff in H as [H | H] *)
(*   | H : feval _ _ _ (F_Implies _ _) false |- _ => *)
(*     let H1 := fresh "H1" in *)
(*     let H2 := fresh "H2" in *)
(*     apply feval_implication_false_iff in H as [H1 H2] *)
(*   | H : feval _ _ _ (F_Iff _ _) true |- _ => *)
(*     let H1 := fresh "H1" in *)
(*     let H2 := fresh "H2" in *)
(*     apply feval_iff_true_iff in H as [[H1 H2] | [H1 H2]] *)
(*   | H : feval _ _ _ (F_Iff _ _) false |- _ => *)
(*     let H1 := fresh "H1" in *)
(*     let H2 := fresh "H2" in *)
(*     apply feval_iff_false_iff in H as [[H1 H2] | [H1 H2]]  *)
(*   | H : feval _ _ _ (F_Exists _ _) true |- _ => *)
(*     apply feval_exists_true_iff in H *)
(*   | H : feval _ _ _ (F_Exists _ _) false |- _ => *)
(*     apply feval_exists_false_iff in H *)
(*   | H : feval _ _ _ (F_Forall _ _) true |- _ => *)
(*     apply feval_forall_true_iff in H *)
(*   | H : feval _ _ _ (F_Forall _ _) false |- _ => *)
(*     apply feval_forall_false_iff in H     *)
(*   | H : feval _ _ _ (F_Simple AT_False) true |- _ => *)
(*     apply feval_inversion_false_true in H; destruct H *)
(*   | H : feval _ _ _ (F_Simple AT_True) false |- _ => *)
(*     apply feval_inversion_true_false in H; destruct H *)
(*   | H1 : feval _ _ _ ?A true |- _ => *)
(*     match goal with  *)
(*     | H2 : feval _ _ _ A false |- _ => *)
(*       destruct (feval_functional _ _ _ _ H1 H2) *)
(*     end *)
(*   end; *)
(*   repeat match goal with *)
(*     | [|- context[feval _ _ _ (F_Not _) true]] => *)
(*       rewrite feval_not_true_iff *)
(*     | [|- context[feval _ _ _ (F_Not _) false]] => *)
(*       rewrite feval_not_false_iff *)
(*     | [|- context[feval _ _ _ (F_And _ _) true]] => *)
(*       rewrite feval_and_true_iff *)
(*     | [|- context[feval _ _ _ (F_And _ _) false]] => *)
(*       rewrite feval_and_false_iff *)
(*     | [|- context[feval _ _ _ (F_Or _ _) true]] => *)
(*       rewrite feval_or_true_iff *)
(*     | [|- context[feval _ _ _ (F_Or _ _) false]] => *)
(*       rewrite feval_or_false_iff          *)
(*     | [|- context[feval _ _ _ (F_Implies _ _) true]] => *)
(*       rewrite feval_implication_true_iff *)
(*     | [|- context[feval _ _ _ (F_Implies _ _) false]] => *)
(*       rewrite feval_implication_false_iff *)
(*     | [|- context[feval _ _ _ (F_Iff _ _) true]] => *)
(*       rewrite feval_iff_true_iff *)
(*     | [|- context[feval _ _ _ (F_Iff _ _) false]] => *)
(*       rewrite feval_iff_false_iff *)
(*   end; *)
(*   auto; *)
(*   clear HTT; *)
(*   clear HFF. *)


Section props.
  Context {M : model}.

  Implicit Types t : @term (value M).
  Implicit Types sf : @simple_formula (value M).
  Implicit Types A B C : @formula (value M).
  Implicit Types v : value M.

  Ltac prove_equiv := intros; intros σ; unfold FIff, FImpl; simp feval;
                      split; try (pose proof (@feval_lem M); naive_solver).
  Lemma and_commute A B :
    <! A ∧ B !> ≡ <! B ∧ A !>.
  Proof. prove_equiv. Qed.

  Lemma or_commute A B :
      <! A ∨ B !> ≡ <! B ∨ A !>.
  Proof. prove_equiv. Qed.

  Lemma and_idemp A :
    <! A ∧ A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma or_idemp A :
    <! A ∨ A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma and_assoc A B C :
    <! A ∧ (B ∧ C) !> ≡ <! (A ∧ B) ∧ C !>.
  Proof. prove_equiv. Qed.

  Lemma or_assoc A B C :
      <! A ∨ (B ∨ C) !> ≡ <! (A ∨ B) ∨ C !>.
  Proof. prove_equiv. Qed.

  Lemma and_absorption A B :
    <! A ∧ (A ∨ B) !> ≡ A.
  Proof. prove_equiv. Qed.

  Lemma or_absorption A B :
    <! A ∨ (A ∧ B) !> ≡ A.
  Proof. prove_equiv. Qed.

  Lemma and_or_distr A B C :
    <! A ∧ (B ∨ C) !> ≡ <! (A ∧ B) ∨ (A ∧ C) !>.
  Proof. prove_equiv. Qed.

  Lemma or_and_distr A B C :
    <! A ∨ (B ∧ C) !> ≡ <! (A ∨ B) ∧ (A ∨ C) !>.
  Proof. prove_equiv. Qed.

  Lemma and_true A :
    <! A ∧ true !> ≡ A.
  Proof. prove_equiv. Qed.

  Lemma or_true A :
    <! A ∨ true !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  Lemma and_false A :
    <! A ∧ false !> ≡ <! false !>.
  Proof. prove_equiv. Qed.

  Lemma or_false A :
    <! A ∨ false !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma not_true : <! ¬ true !> ≡@{@formula (value M)} <! false !>.
  Proof. prove_equiv. Qed.

  Lemma not_false : <! ¬ false !> ≡@{@formula (value M)} <! true !>.
  Proof. prove_equiv. Qed.

  Lemma A_and_not_A A :
    <! A ∧ ¬ A !> ≡ <! false !>.
  Proof. prove_equiv. Qed.

  Lemma excluded_middle A :
      <! A ∨ ¬ A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  Lemma not_stable A :
    <! ¬ ¬ A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  Lemma not_and A B :
    <! ¬ (A ∧ B) !> ≡ <! ¬ A ∨ ¬ B !>.
  Proof. prove_equiv. Qed.

  Lemma not_or A B :
      <! ¬ (A ∨ B) !> ≡ <! ¬ A ∧ ¬ B !>.
  Proof. prove_equiv. Qed.

  Lemma or_neg_absorption A B :
      <! A ∨ (¬ A ∧ B) !> ≡ <! A ∨ B !>.
  Proof. prove_equiv. Qed.

  Lemma and_neg_absorption A B :
    <! A ∧ (¬ A ∨ B) !> ≡ <! A ∧ B !>.
  Proof. prove_equiv. Qed.

  (* A.22 *)
  Lemma implication_equiv_or A B :
    <! A => B !> ≡ <! ¬ A ∨ B !>.
  Proof. prove_equiv. Qed.

  (* A.23 *)
  Lemma A_implies_A__true A :
    <! A => A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.24 *)
  Lemma implication_as_not_and A B :
    <! A => B !> ≡ <! ¬ (A ∧ ¬ B) !>.
  Proof. prove_equiv. Qed.

  (* A.25 *)
  Lemma not_implication_as_and A B :
      <! ¬ (A => B) !> ≡ <! A ∧ ¬ B !>.
  Proof. prove_equiv. Qed.

  (* A.26 *)
  Lemma contrapositive_law A B :
      <! A => B !> ≡ <! ¬ B => ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.27 *)
  Lemma everything_implies_true A :
    <! A => true !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.28 *)
  Lemma true_implies_A A :
      <! true => A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  (* A.29 *)
  Lemma A_implies_false A :
    <! A => false !> ≡ <! ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.30 *)
  Lemma false_implies_everything A :
      <! false => A !> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.31 *)
  Lemma A_implies_not_A A :
      <! A => ¬ A !> ≡ <! ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.32 *)
  Lemma not_A_implies_A A :
      <! ¬ A => A !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  (* A.33 *)
  Lemma implication_distr1 A B C :
      <! C => (A ∧ B) !> ≡ <! (C => A) ∧ (C => B) !>.
  Proof. prove_equiv. Qed.

  (* A.34 *)
  Lemma implication_distr2 A B C :
    <! (A ∨ B) => C !> ≡ <! (A => C) ∧ (B => C) !>.
  Proof. prove_equiv. Qed.

  (* A.35 *)
  Lemma implication_distr3 A B C :
    <! C => (A ∨ B) !> ≡ <! (C => A) ∨ (C => B) !>.
  Proof. prove_equiv. Qed.

  (* A.36 *)
  Lemma implication_distr4 A B C :
    <! (A ∧ B) => C !> ≡ <! (A => C) ∨ (B => C) !>.
  Proof with auto.
    unfold FImpl. intros σ. simp feval. split; [| naive_solver].
    intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec.
  Qed.

  (* A.37 *)
  Lemma successive_hypotheses A B C :
    <! A => (B => C) !> ≡ <! (A ∧ B) => C !>.
  Proof with auto.
    unfold FImpl. intros σ. simp feval. split; [naive_solver |].
    intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec.
  Qed.

  (* A.37 *)
  Lemma successive_hypotheses' A B C :
    <! B => (A => C) !> ≡ <! (A ∧ B) => C !>.
  Proof with auto.
    unfold FImpl. intros σ. simp feval. split; [naive_solver |].
    intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec.
  Qed.

  (* A.38 *)
  Lemma def_by_cases A B C :
    <! (A => B) ∧ (¬A => C) !> ≡ <! (A ∧ B) ∨ (¬A ∧ C) !>.
  Proof. prove_equiv. Qed.

  (* A.39 *)
  Lemma iff_equiv1 A B C :
    <! A <=> B !> ≡ <! (A => B) ∧ (B => A) !>.
  Proof. prove_equiv. Qed.

  (* A.40 *)
  Lemma iff_equiv2 A B :
    <! A <=> B !> ≡ <! (A ∧ B) ∨ ¬(A ∨ B) !>.
  Proof. prove_equiv. Qed.

  (* A.41 *)
  Lemma iff_equiv3 A B :
    <! A <=> B !> ≡ <! ¬A <=> ¬B !>.
  Proof. prove_equiv. Qed.

  (* A.42 *)
  Lemma A_iff_A A :
    <! A <=> A!> ≡ <! true !>.
  Proof. prove_equiv. Qed.

  (* A.43 *)
  Lemma A_iff_not_A A :
    <! A <=> ¬ A !> ≡ <! false !>.
  Proof. prove_equiv. Qed.

  (* A.44 *)
  Lemma iff_true_id A :
    <! A <=> true !> ≡ <! A !>.
  Proof. prove_equiv. Qed.

  (* A.45 *)
  Lemma iff_false_neg A :
    <! A <=> false !> ≡ <! ¬ A !>.
  Proof. prove_equiv. Qed.

  (* A.46 *)
  Lemma implication_equiv_iff1 A B :
    <! A => B !> ≡ <! A <=> (A ∧ B) !>.
  Proof. prove_equiv. Qed.

  (* A.47 *)
  Lemma implication_equiv_iff2 A B :
      <! B => A !> ≡ <! A <=> (A ∨ B) !>.
  Proof with auto.
    intros σ. unfold FIff, FImpl. simp feval. split.
    - intros [|]; [|naive_solver]. split.
      + pose proof (feval_lem σ A). destruct H0 as [|]...
      + pose proof (feval_lem σ A) as [|]; naive_solver.
    - intros []. destruct_or! H; naive_solver.
  Qed.

  (* A.48 *)
  Lemma or_equiv_iff A B C :
      <! A ∨ (B <=> C) !> ≡ <! (A ∨ B) <=> (A ∨ C) !>.
  Proof with auto.
    intros σ. unfold FIff, FImpl. simp feval. split; [|naive_solver].
    intros [|[]]; [naive_solver|]. split; destruct (feval_lem σ A); naive_solver.
  Qed.

  (* A.49 *)
  Lemma equiv_comm A B :
      <! A <=> B !> ≡ <! B <=> A !>.
  Proof. prove_equiv. Qed.

  (* A.50 *)
  Lemma equiv_assoc A B C :
      <! A <=> (B <=> C) !> ≡ <! (A <=> B) <=> C !>.
  Proof.
    unfold FIff, FImpl. rewrite not_and.
    repeat rewrite not_and. repeat rewrite not_or. repeat rewrite not_stable.
    intros σ. simp feval. split; naive_solver.
  Qed.

  (* A.56 *)
  Lemma existential_one_point x t A :
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
  Lemma universal_one_point x t A :
      x ∉ term_fvars t →
      <! forall x, x = t => A !> ≡ <! A[x \ t] !>.
  Proof with auto.
    intros Hfree. unfold FForall. rewrite not_implication_as_and.
    apply (existential_one_point x t(FNot A)) in Hfree. rewrite Hfree.
    rewrite simpl_subst_not. rewrite not_stable...
  Qed.

  (* A.60 *)
  Lemma fexists_idemp x A :
    <! exists x x, A !> ≡ <! exists x, A !>.
  Proof with auto. rewrite fexists_unused... simpl. set_solver. Qed.

  (* A.59 *)
  Lemma fforall_idemp x A :
    <! forall x x, A !> ≡ <! forall x, A !>.
  Proof with auto. unfold FForall. rewrite not_stable. rewrite fexists_idemp... Qed.

  (* A.61 *)
  Lemma fnot_fforall x A :
    <! ¬ forall x, A !> ≡ <! exists x, ¬ A !>.
  Proof. unfold FForall. rewrite not_stable. auto. Qed.

  (* A.62 *)
  Lemma fnot_fexists x A :
    <! ¬ exists x, A !> ≡ <! forall x, ¬ A !>.
  Proof. unfold FForall. rewrite not_stable. auto. Qed.

  (* A.64 *)
  Lemma fexists_comm x y A :
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
  Lemma fforall_comm x y A :
    <! forall x y, A !> ≡ <! forall y x, A !>.
  Proof. unfold FForall. do 2 rewrite not_stable. rewrite fexists_comm. reflexivity. Qed.

  (* A.66 *)
  Lemma fexists_for x A B :
    <! exists x, A ∨ B !> ≡ <! (exists x, A) ∨ (exists x, B) !>.
  Proof with auto.
    intros σ. simp feval. setoid_rewrite simpl_subst_or. split.
    - intros [v H]. simp feval in H. destruct H as [|]; [left|right]; exists v...
    - intros [[v H] | [v H]]; exists v; simp feval...
  Qed.

  (* A.65 *)
  Lemma fforall_fand x A B :
    <! forall x, A ∧ B !> ≡ <! (forall x, A) ∧ (forall x, B) !>.
  Proof. unfold FForall. rewrite not_and. rewrite fexists_for. rewrite not_or; auto. Qed.

  (* A.67 *)
  Lemma fexists_fimpl x A B :
    <! exists x, A => B !> ≡ <! (forall x, A) => (exists x, B) !>.
  Proof with auto.
    intros σ. unfold FImpl. rewrite fexists_for. unfold FForall. rewrite not_stable...
  Qed.

  (* A.68 *)
  Lemma fforall_fent_fexists x A :
    <! forall x, A !> ⇛ <! exists x, A !>.
  Proof.
    intros σ. rewrite simpl_feval_fforall. intros. simp feval.
    exists ⊥. apply H.
  Qed.

  (* A.69 *)
  Lemma for_fforall x A B :
    <! (forall x, A) ∨ (forall x, B) !> ⇛ <! forall x, A ∨ B !>.
  Proof.
    intros σ. simp feval. do 3 rewrite simpl_feval_fforall.
    setoid_rewrite simpl_subst_or.
    intros [|]; intros; simp feval; naive_solver.
  Qed.

  (* A.70 *)
  Lemma fforall_fimpl x A B :
    <! forall x, A => B !> ⇛ <! (forall x, A) => (forall x, B) !>.
  Proof.
    intros σ. rewrite simpl_feval_fimpl. do 3 rewrite simpl_feval_fforall.
    intros. specialize (H v). rewrite simpl_subst_impl in H. rewrite simpl_feval_fimpl in H.
    naive_solver.
  Qed.

  (* A.71 *)
  Lemma fexists_fand x A B :
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
        apply fforall_fent_fexists in H... }
    rewrite (feval_subst vx) in H... rewrite simpl_feval_fforall in H.
    specialize (H vy). rewrite (feval_subst vy) in H...
    rewrite (feval_subst vy)... simp feval. exists vx. rewrite (feval_subst vx)...
    rewrite (insert_commute σ)...
  Qed.

  (* A.74: fforall_unused *)
  (* A.75: fequiv_forall_non_free_binder *)

  (* A.76 *)
  Lemma fforall_fand_unused_l x A B:
    x ∉ formula_fvars A →
    <! forall x, A ∧ B !> ≡ <! A ∧ (forall x, B) !>.
  Proof with auto. intros. rewrite fforall_fand. rewrite fforall_unused... Qed.

  (* A.76' *)
  Lemma fforall_fand_unused_r x A B:
    x ∉ formula_fvars B →
    <! forall x, A ∧ B !> ≡ <! (forall x, A) ∧ B !>.
  Proof with auto. intros. rewrite fforall_fand. rewrite (fforall_unused x B)... Qed.

  (* A.77 *)
  Lemma fforall_for_unused_l x A B:
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
  Lemma fforall_for_unused_r x A B:
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
  Lemma fforall_fimpl_unused_l x A B:
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
  Lemma fforall_fimpl_unused_r x A B:
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
  Lemma fexists_fand_unused_l x A B:
    x ∉ formula_fvars A →
    <! exists x, A ∧ B !> ≡ <! A ∧ (exists x, B) !>.
  Proof with auto.
    intros. rewrite <- (not_stable A). rewrite <- (not_stable B). rewrite <- (not_or).
    rewrite <- (fnot_fforall). rewrite fforall_for_unused_l by (simpl; auto).
    rewrite not_or. rewrite fnot_fforall...
  Qed.

  (* A.80' *)
  Lemma fexists_fand_unused_r x A B:
    x ∉ formula_fvars B →
    <! exists x, A ∧ B !> ≡ <! (exists x, A) ∧ B !>.
  Proof with auto.
    intros. rewrite <- (not_stable A). rewrite <- (not_stable B). rewrite <- (not_or).
    rewrite <- (fnot_fforall). rewrite fforall_for_unused_r by (simpl; auto).
    rewrite not_or. rewrite fnot_fforall...
  Qed.

  (* A.81 *)
  Lemma fexists_for_unused_l x A B:
    x ∉ formula_fvars A →
    <! exists x, A ∨ B !> ≡ <! A ∨ (exists x, B) !>.
  Proof with auto. intros. rewrite fexists_for. rewrite fexists_unused... Qed.

  (* A.81' *)
  Lemma fexists_for_unused_r x A B:
    x ∉ formula_fvars B →
    <! exists x, A ∨ B !> ≡ <! (exists x, A) ∨ B !>.
  Proof with auto. intros. rewrite fexists_for. rewrite (fexists_unused _ B)... Qed.

  (* A.82 *)
  Lemma fexists_fimpl_unused_l x A B:
    x ∉ formula_fvars A →
    <! exists x, A => B !> ≡ <! A => (exists x, B) !>.
  Proof with auto. intros. rewrite fexists_fimpl. rewrite fforall_unused... Qed.

  (* A.83 *)
  Lemma fexists_fimpl_unused_r x A B:
    x ∉ formula_fvars B →
    <! exists x, A => B !> ≡ <! (forall x, A) => B !>.
  Proof with auto. intros. rewrite fexists_fimpl. rewrite fexists_unused... Qed.

End props.
