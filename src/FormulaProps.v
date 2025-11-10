From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc PredCalcEquiv PredCalcSubst PredCalcFacts.

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
