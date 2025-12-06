From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.SyntacticFacts.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.EquivLemmas.

Lemma f_lem_elim_Prop {M : model} (A : formula (value M)) (P : ∀ σ : state M, Prop) :
  (∀ σ, A ≡_{σ} <! true !> → P σ) →
  (∀ σ, A ≡_{σ} <! false !> → P σ) →
  ∀ σ, P σ.
Proof.
  intros. specialize (H σ). specialize (H0 σ).
  destruct (feval_lem σ A); [apply H | apply H0]; split; simp feval; naive_solver.
Qed.

Lemma fent_fent_st {M : model} (A B : formula (value M)) :
  A ⇛ B ↔ ∀ σ, A ⇛_{σ} B.
Proof. reflexivity. Qed.

Lemma fequiv_fequiv_st {M : model} (A B : formula (value M)) :
  A ≡ B ↔ ∀ σ, A ≡_{σ} B.
Proof. reflexivity. Qed.

Ltac fLem C :=
  (match goal with
  | |- _ ⇛ _ => rewrite fent_fent_st
  | |- _ ≡ _ => rewrite fequiv_fequiv_st
  end);
  (match goal with
  | |- ∀ σ, ?P => apply (f_lem_elim_Prop C (λ σ, P))
  end);
  let H := fresh in
  intros σ H; rewrite H in *.

Ltac fRewrite_goal E tac :=
  match goal with
  | |- _ ≡ _ => tac E
  | |- _ ⇛ _ => tac E
  | |- _ ≡_{?σ} _ =>
      let HE := fresh in
      opose proof E as HE;
      match type of HE with
      | _ ≡ _ => rewrite fequiv_fequiv_st in HE; specialize (HE σ)
      | _ ⇛ _ => rewrite fent_fent_st in HE; specialize (HE σ)
      end; tac HE; clear HE
  | |- _ ⇛_{?σ} _ =>
      let HE := fresh in
      opose proof E as HE;
      match type of HE with
      | _ ≡ _ => rewrite fequiv_fequiv_st in HE; specialize (HE σ)
      | _ ⇛ _ => rewrite fent_fent_st in HE; specialize (HE σ)
      end; tac HE; clear HE
  end.

Ltac fRewrite_hyp E H tac :=
  match goal with
  | H : _ ≡ _ |- _ => tac E
  | H : _ ⇛ _ |- _ => tac E
  | H : _ ≡_{?σ} _ |- _ =>
      let HE := fresh in
      opose proof E as HE;
      match type of HE with
      | _ ≡ _ => rewrite fequiv_fequiv_st in HE; specialize (HE σ)
      | _ ⇛ _ => rewrite fent_fent_st in HE; specialize (HE σ)
      end; tac HE; clear HE
  | |- _ ⇛_{?σ} _ =>
      let HE := fresh in
      opose proof E as HE;
      match type of HE with
      | _ ≡ _ => rewrite fequiv_fequiv_st in HE; specialize (HE σ)
      | _ ⇛ _ => rewrite fent_fent_st in HE; specialize (HE σ)
      end; tac HE; clear HE
  end.

Tactic Notation "fRewrite" uconstr(E) :=
  fRewrite_goal E ltac:(fun HE => rewrite HE).
Tactic Notation "fRewrite" uconstr(E) "at" integer(n) :=
  fRewrite_goal E ltac:(fun HE => rewrite HE at n).
Tactic Notation "fRewrite" "<-" uconstr(E) :=
  fRewrite_goal E ltac:(fun HE => rewrite <- HE).
Tactic Notation "fRewrite" "<-" uconstr(E) "at" integer(n) :=
  fRewrite_goal E ltac:(fun HE => rewrite <- HE at n).

Tactic Notation "fRewrite" uconstr(E) "in" hyp(H) :=
  fRewrite_goal E ltac:(fun HE => rewrite HE in H).
Tactic Notation "fRewrite" uconstr(E) "in" hyp(H) "at" integer(n) :=
  fRewrite_goal E ltac:(fun HE => rewrite HE in H at n).
Tactic Notation "fRewrite" "<-" uconstr(E) "in" hyp(H) :=
  fRewrite_goal E ltac:(fun HE => rewrite <- HE in H).
Tactic Notation "fRewrite" "<-" uconstr(E) "in" hyp(H) "at" integer(n) :=
  fRewrite_goal E ltac:(fun HE => rewrite <- HE in H at n).

Ltac f_simpl :=
  repeat match goal with
    | H : context[<! ?A ∧ ?A !>] |- _ =>
        fRewrite (f_and_idemp A) in H
    | |- context[<! ?A ∧ ?A !>] =>
        fRewrite (f_and_idemp A)

    | H : context[<! ?A ∨ ?A !>] |- _ =>
        fRewrite (f_or_idemp A) in H
    | |- context[<! ?A ∨ ?A !>] =>
        fRewrite (f_or_idemp A)

    (*  f_and_or_absorb *)
    | H : context[<! ?A ∧ (?A ∨ ?B) !>] |- _ =>
        fRewrite (f_and_or_absorb A B) in H
    | H : context[<! (?A ∨ ?B) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_and_or_absorb A B) in H; clear Heq
    | H : context[<! (?B ∨ ?A) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_and_or_absorb A B) in H; clear Heq
    | |- context[<! ?A ∧ (?A ∨ ?B) !>] =>
        fRewrite (f_and_or_absorb A B)
    | |- context[<! (?A ∨ ?B) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        fRewrite Heq; fRewrite (f_and_or_absorb A B); clear Heq
    | |- context[<! (?B ∨ ?A) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        fRewrite Heq; fRewrite (f_and_or_absorb A B); clear Heq

    (*  f_or_and_absorb *)
    | H : context[<! ?A ∨ (?A ∧ ?B) !>] |- _ =>
        fRewrite (f_or_and_absorb A B) in H
    | H : context[<! (?A ∧ ?B) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_or_and_absorb A B) in H; clear Heq
    | H : context[<! (?B ∧ ?A) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_or_and_absorb A B) in H; clear Heq
    | |- context[<! ?A ∨ (?A ∧ ?B) !>] =>
        fRewrite (f_and_or_absorb A B)
    | |- context[<! (?A ∧ ?B) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        fRewrite Heq; fRewrite (f_and_or_absorb A B); clear Heq
    | |- context[<! (?B ∧ ?A) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        fRewrite Heq; fRewrite (f_and_or_absorb A B); clear Heq

    (* f_and_true *)
    | H : context[<! ?A ∧ true !>] |- _ =>
        fRewrite (f_and_true A) in H
    | H : context[<! true ∧ ?A !>] |- _ =>
        fRewrite (f_and_comm <! true !> A) in H; fRewrite (f_and_true A) in H
    | |- context[<! ?A ∧ true !>] =>
        fRewrite (f_and_true A)
    | |- context[<! true ∧ ?A !>] =>
        fRewrite (f_and_comm <! true !> A); fRewrite (f_and_true A)

    (* f_and_false *)
    | H : context[<! ?A ∧ false !>] |- _ =>
        fRewrite (f_and_false A) in H
    | H : context[<! false ∧ ?A !>] |- _ =>
        fRewrite (f_and_comm <! false !> A) in H; fRewrite (f_and_false A) in H
    | |- context[<! ?A ∧ false !>] =>
        fRewrite (f_and_false A)
    | |- context[<! false ∧ ?A !>] =>
        fRewrite (f_and_comm <! false !> A); fRewrite (f_and_false A)

    (* f_or_true *)
    | H : context[<! ?A ∨ true !>] |- _ =>
        fRewrite (f_or_true A) in H
    | H : context[<! true ∨ ?A !>] |- _ =>
        fRewrite (f_or_comm <! true !> A) in H; fRewrite (f_or_true A) in H
    | |- context[<! ?A ∨ true !>] =>
        fRewrite (f_or_true A)
    | |- context[<! true ∨ ?A !>] =>
        fRewrite (f_or_comm <! true !> A); fRewrite (f_or_true A)

    (* f_or_false *)
    | H : context[<! ?A ∨ false !>] |- _ =>
        fRewrite (f_or_false A) in H
    | H : context[<! false ∨ ?A !>] |- _ =>
        fRewrite (f_or_comm <! false !> A) in H; fRewrite (f_or_false A) in H
    | |- context[<! ?A ∨ false !>] =>
        fRewrite (f_or_false A)
    | |- context[<! false ∨ ?A !>] =>
        fRewrite (f_or_comm <! false !> A); fRewrite (f_or_false A)

    (* f_not_true *)
    | H : context[<! ¬ true !>] |- _ =>
        fRewrite f_not_true in H
    | |- context[<! ¬ true !>] =>
        fRewrite f_not_true

    (* f_false_true *)
    | H : context[<! ¬ false !>] |- _ =>
        fRewrite f_not_false in H
    | |- context[<! ¬ false !>] =>
        fRewrite f_not_false

    (* f_and_not_self *)
    | H : context[<! ?A ∧ ¬ ?A !>] |- _ =>
        fRewrite (f_and_not_self A) in H
    | H : context[<! ¬ ?A ∧ ?A !>] |- _ =>
        fRewrite (f_and_comm (<! ¬ A !>) A) in H; fRewrite (f_and_not_self A) in H
    | |- context[<! ?A ∧ ¬ ?A !>] =>
        fRewrite (f_and_not_self A)
    | |- context[<! ¬ ?A ∧ ?A !>] =>
        fRewrite (f_and_comm (<! ¬ A !>) A); fRewrite (f_and_not_self A)

    (* f_lem *)
    | H : context[<! ?A ∨ ¬ ?A !>] |- _ =>
        fRewrite (f_lem A) in H
    | H : context[<! ¬ ?A ∨ ?A !>] |- _ =>
        fRewrite (f_or_comm (<! ¬ A !>) A) in H; fRewrite (f_lem A) in H
    | |- context[<! ?A ∨ ¬ ?A !>] =>
        fRewrite (f_lem A)
    | |- context[<! ¬ ?A ∨ ?A !>] =>
        fRewrite (f_or_comm (<! ¬ A !>) A); fRewrite (f_lem A)

    (* f_not_stable *)
    | H : context[<! ¬ ¬ ?A !>] |- _ =>
        fRewrite (f_not_stable A) in H
    | |- context[<! ¬ ¬ ?A !>] =>
        fRewrite (f_not_stable A)

    (* f_not_and *)
    | H : context[<! ¬ (?A ∧ ?B) !>] |- _ =>
        fRewrite (f_not_and A B) in H
    | |- context[<! ¬ (?A ∧ ?B) !>] =>
        fRewrite (f_not_and A B)

    (* f_not_or *)
    | H : context[<! ¬ (?A ∨ ?B) !>] |- _ =>
        fRewrite (f_not_or A B) in H
    | |- context[<! ¬ (?A ∨ ?B) !>] =>
        fRewrite (f_not_or A B)

    (* (* f_and_or_distr *) *)
    (* | H : context[<! ?A ∧ (?B ∨ ?C) !>] |- _ => *)
    (*     fRewrite f_and_or_distr in H *)
    (* | H : context[<! (?B ∨ ?C) ∧ ?A !>] |- _ => *)
    (*     fRewrite (f_and_comm (?B ∨ ?C) ?A) in H; fRewrite f_and_or_distr in H *)
    (* | |- context[<! ?A ∧ (?B ∨ ?C) !>] => *)
    (*     fRewrite f_and_or_distr *)
    (* | |- context[<! (?B ∨ ?C) ∧ ?A !>] => *)
    (*     fRewrite (f_and_comm (?B ∨ ?C) ?A); fRewrite f_and_or_distr *)

    (* (* f_or_and_distr *) *)
    (* | H : context[<! ?A ∨ (?B ∧ ?C) !>] |- _ => *)
    (*     fRewrite f_or_and_distr in H *)
    (* | H : context[<! (?B ∧ ?C) ∨ ?A !>] |- _ => *)
    (*     fRewrite (f_or_comm (?B ∧ ?C) ?A) in H; fRewrite f_or_and_distr in H *)
    (* | |- context[<! ?A ∨ (?B ∧ ?C) !>] => *)
    (*     fRewrite f_or_and_distr *)
    (* | |- context[<! (?B ∨ ?C) ∧ ?A !>] => *)
    (*     fRewrite (f_and_comm (?B ∨ ?C) ?A); fRewrite f_or_and_distr *)

    (*  f_and_or_absorb' *)
    | H : context[<! ?A ∧ (¬ ?A ∨ ?B) !>] |- _ =>
        fRewrite (f_and_or_absorb' A B) in H
    | H : context[<! (¬ ?A ∨ ?B) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∨ B) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_and_or_absorb' A B) in H; clear Heq
    | H : context[<! (?B ∨ ¬ ?A) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ ¬ A) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_and_or_absorb' A B) in H; clear Heq
    | |- context[<! ?A ∧ (¬ ?A ∨ ?B) !>] =>
        fRewrite (f_and_or_absorb' A B)
    | |- context[<! (¬ ?A ∨ ?B) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∨ B) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        fRewrite Heq; fRewrite (f_and_or_absorb' A B); clear Heq
    | |- context[<! (?B ∨ ¬ ?A) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ ¬ A) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        fRewrite Heq; fRewrite (f_and_or_absorb' A B); clear Heq

    (*  f_or_and_absorb' *)
    | H : context[<! ?A ∨ (¬ ?A ∧ ?B) !>] |- _ =>
        fRewrite (f_or_and_absorb' A B) in H
    | H : context[<! (¬ ?A ∧ ?B) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∧ B) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_or_and_absorb' A B) in H; clear Heq
    | H : context[<! (?B ∧ ¬ ?A) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ ¬ A) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_or_and_absorb' A B) in H; clear Heq
    | |- context[<! ?A ∨ (¬ ?A ∧ ?B) !>] =>
        fRewrite (f_or_and_absorb' A B)
    | |- context[<! (¬ ?A ∧ ?B) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∧ B) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        fRewrite Heq; fRewrite (f_or_and_absorb' A B); clear Heq
    | |- context[<! (?B ∧ ¬ ?A) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ ¬ A) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        fRewrite Heq; fRewrite (f_or_and_absorb' A B); clear Heq

    (* f_implies_self *)
    | H : context[<! ?A ⇒ ?A !>] |- _ =>
        fRewrite (f_implies_self A) in H
    | |- context[<! ?A ⇒ ?A !>] =>
        fRewrite (f_implies_self A)

    (* f_not_impl *)
    | H : context[<! ¬ (?A ⇒ ?B) !>] |- _ =>
        fRewrite (f_not_impl A B) in H
    | |- context[<! ¬ (?A ⇒ ?B) !>] =>
        fRewrite (f_not_impl A B)

    (* f_implies_true *)
    | H : context[<! ?A ⇒ true !>] |- _ =>
        fRewrite (f_implies_true A) in H
    | |- context[<! ?A ⇒ true !>] =>
        fRewrite (f_implies_true A)

    (* f_true_implies *)
    | H : context[<! true ⇒ ?A !>] |- _ =>
        fRewrite (f_true_implies A) in H
    | |- context[<! true ⇒ ?A !>] =>
        fRewrite (f_true_implies A)

    (* f_implies_false *)
    | H : context[<! ?A ⇒ false !>] |- _ =>
        fRewrite (f_implies_false A) in H
    | |- context[<! ?A ⇒ false !>] =>
        fRewrite (f_implies_false A)

    (* f_false_implies *)
    | H : context[<! false ⇒ ?A !>] |- _ =>
        fRewrite (f_false_implies A) in H
    | |- context[<! false ⇒ ?A !>] =>
        fRewrite (f_false_implies A)

    (* f_implies_not_self *)
    | H : context[<! ?A ⇒ ¬ ?A !>] |- _ =>
        fRewrite (f_implies_not_self A) in H
    | |- context[<! ?A ⇒ ¬ ?A !>] =>
        fRewrite (f_implies_not_self A)

    (* f_not_implies_self *)
    | H : context[<! ¬ ?A ⇒ ?A !>] |- _ =>
        fRewrite (f_not_implies_self A) in H
    | |- context[<! ¬ ?A ⇒ ?A !>] =>
        fRewrite (f_not_implies_self A)

    (* f_iff_equiv3 *)
    | H : context[<! ¬ ?A ⇔ ¬ ?B !>] |- _ =>
        fRewrite <- (f_iff_negate A B) in H
    | |- context[<! ¬ ?A ⇔ ¬ ?B !>] =>
        fRewrite <- (f_iff_negate A B)

    (* f_iff_self *)
    | H : context[<! ?A ⇔ ?A !>] |- _ =>
        fRewrite (f_iff_self A) in H
    | |- context[<! ?A ⇔ ?A !>] =>
        fRewrite (f_iff_self A)

    (* f_iff_not_self *)
    | H : context[<! ?A ⇔ ¬ ?A !>] |- _ =>
        fRewrite (f_iff_not_self A) in H
    | H : context[<! ¬ ?A ⇔ ?A !>] |- _ =>
        fRewrite (f_iff_comm (<! ¬ A !>) A) in H; fRewrite (f_iff_not_self A) in H
    | |- context[<! ?A ⇔ ?A !>] =>
        fRewrite (f_iff_self A)
    | |- context[<! ¬ ?A ⇔ ?A !>] =>
        fRewrite (f_iff_comm (<! ¬ A !>) A); fRewrite (f_iff_not_self A)

    (* f_iff_true *)
    | H : context[<! ?A ⇔ true !>] |- _ =>
        fRewrite (f_iff_true A) in H
    | H : context[<! true ⇔ ?A !>] |- _ =>
        fRewrite (f_iff_comm (<! true !>) A) in H; fRewrite (f_iff_true A) in H
    | |- context[<! ?A ⇔ true !>] =>
        fRewrite (f_iff_true A)
    | |- context[<! true ⇔ ?A !>] =>
        fRewrite (f_iff_comm (<! true !>) A); fRewrite (f_iff_true A)

    (* f_iff_false *)
    | H : context[<! ?A ⇔ false !>] |- _ =>
        fRewrite (f_iff_false A) in H
    | H : context[<! false ⇔ ?A !>] |- _ =>
        fRewrite (f_iff_comm (<! false !>) A) in H; fRewrite (f_iff_false A) in H
    | |- context[<! ?A ⇔ false !>] =>
        fRewrite (f_iff_false A)
    | |- context[<! false ⇔ ?A !>] =>
        fRewrite (f_iff_comm (<! false !>) A); fRewrite (f_iff_false A)

    (*  f_iff_and_absorb *)
    | H : context[<! ?A ⇔ (?A ∧ ?B) !>] |- _ =>
        fRewrite (f_iff_and_absorb A B) in H
    | H : context[<! (?A ∧ ?B) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_iff_and_absorb A B) in H; clear Heq
    | H : context[<! (?B ∧ ?A) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_iff_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_iff_and_absorb A B) in H; clear Heq
    | |- context[<! ?A ⇔ (?A ∧ ?B) !>] =>
        fRewrite (f_iff_and_absorb A B)
    | |- context[<! (?A ∧ ?B) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        fRewrite Heq; fRewrite (f_iff_and_absorb A B); clear Heq
    | |- context[<! (?B ∧ ?A) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_iff_comm; reflexivity);
        fRewrite Heq; fRewrite (f_iff_and_absorb A B); clear Heq

    (* f_not_forall *)
    | H : context[<! ¬ ∀ ?x, ?A !>] |- _ =>
        fRewrite (f_not_forall x A) in H
    | |- context[<! ¬ ∀ ?x, ?A !>] =>
        fRewrite (f_not_forall x A)

    (* f_not_exists *)
    | H : context[<! ¬ ∃ ?x, ?A !>] |- _ =>
        fRewrite (f_not_exists x A) in H
    | |- context[<! ¬ ∃ ?x, ?A !>] =>
        fRewrite (f_not_exists x A)

    (*  f_iff_or_absorb *)
    | H : context[<! ?A ⇔ (?A ∨ ?B) !>] |- _ =>
        fRewrite (f_iff_or_absorb A B) in H
    | H : context[<! (?A ∨ ?B) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_iff_or_absorb A B) in H; clear Heq
    | H : context[<! (?B ∨ ?A) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_iff_comm; reflexivity);
        fRewrite Heq in H; fRewrite (f_iff_or_absorb A B) in H; clear Heq
    | |- context[<! ?A ⇔ (?A ∨ ?B) !>] =>
        fRewrite (f_iff_or_absorb A B)
    | |- context[<! (?A ∨ ?B) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        fRewrite Heq; fRewrite (f_iff_or_absorb A B); clear Heq
    | |- context[<! (?B ∨ ?A) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_iff_comm; reflexivity);
        fRewrite Heq; fRewrite (f_iff_or_absorb A B); clear Heq

    (* f_impl_elim *)
    | H : context[<! ?A ∧ (?A ⇒ ?B) !>] |- _ =>
        rewrite (f_impl_elim A B) in H
    | H : context[<! (?A ⇒ ?B) ∧ ?A !>] |- _ =>
        rewrite (f_and_comm (<! ?A ⇒ ?B !>) ?A) in H; rewrite (f_impl_elim A B) in H
    | |- context[<! ?A ∧ (?A ⇒ ?B) !>] =>
        rewrite (f_impl_elim A B)
    | |- context[<! (?A ⇒ ?B) ∧ ?A !>] =>
        rewrite (f_and_comm (<! ?A ⇒ ?B !>) ?A); rewrite (f_impl_elim A B)

    (* automatically prove A ≡ A and discharge ¬ A ≡ A *)
    | H : ¬ (<! ?A !> ≡ <! ?A !>) |- _ =>
        specialize (H (reflexivity A)); destruct H
    | |- <! ?A !> ≡ <! ?A !> =>
        reflexivity

    (* f_and_cancel_l and f_and_cancel_r *)
    | |- <! ?A ∧ ?B !> ≡ <! ?A ∧ ?C !> =>
        apply f_and_cancel_l
    | |- <! ?B ∧ ?A !> ≡ <! ?A ∧ ?C !> =>
        rewrite (f_and_comm B A); apply f_and_cancel_l
    | |- <! ?A ∧ ?B !> ≡ <! ?C ∧ ?A !> =>
        rewrite (f_and_comm C A); apply f_and_cancel_l
    | |- <! ?B ∧ ?A !> ≡ <! ?C ∧ ?A !> =>
        apply f_and_cancel_r

    (* f_or_cancel_l and f_or_cancel_r *)
    | |- <! ?A ∨ ?B !> ≡ <! ?A ∨ ?C !> =>
        apply f_or_cancel_l
    | |- <! ?B ∨ ?A !> ≡ <! ?A ∨ ?C !> =>
        rewrite (f_or_comm B A); apply f_or_cancel_l
    | |- <! ?A ∨ ?B !> ≡ <! ?C ∨ ?A !> =>
        rewrite (f_or_comm C A); apply f_or_cancel_l
    | |- <! ?B ∨ ?A !> ≡ <! ?C ∨ ?A !> =>
        apply f_or_cancel_r

    (* f_impl_cancel_l and f_impl_cancel_r *)
    | |- <! ?A ⇒ ?B !> ≡ <! ?A ⇒ ?C !> =>
        apply f_impl_cancel_l
    | |- <! ?B ⇒ ?A !> ≡ <! ?C ⇒ ?A !> =>
        apply f_impl_cancel_r

    (* f_subst_cancel *)
    | |- <! ?A [ ?x \ ?t ]!> ≡ <! ?B [ ?x \ ?t ] !> =>
        apply f_subst_cancel
    | |- <! ?A [ ?x \ ?t1 ]!> ≡ <! ?A [ ?x \ ?t2 ] !> =>
        apply f_subst_cancel_term

    (* f_ent_and_cancel_l and f_ent_and_cancel_r *)
    | |- <! ?A ∧ ?B !> ⇛ <! ?A ∧ ?C !> =>
        apply f_ent_and_cancel_l
    | |- <! ?B ∧ ?A !> ⇛ <! ?A ∧ ?C !> =>
        rewrite (f_and_comm B A); apply f_ent_and_cancel_l
    | |- <! ?A ∧ ?B !> ⇛ <! ?C ∧ ?A !> =>
        rewrite (f_and_comm C A); apply f_ent_and_cancel_l
    | |- <! ?B ∧ ?A !> ⇛ <! ?C ∧ ?A !> =>
        apply f_ent_and_cancel_r

    (* f_ent_or_cancel_l and f_ent_or_cancel_r *)
    | |- <! ?A ∨ ?B !> ⇛ <! ?A ∨ ?C !> =>
        apply f_ent_or_cancel_l
    | |- <! ?B ∨ ?A !> ⇛ <! ?A ∨ ?C !> =>
        rewrite (f_or_comm B A); apply f_ent_or_cancel_l
    | |- <! ?A ∨ ?B !> ⇛ <! ?C ∨ ?A !> =>
        rewrite (f_or_comm C A); apply f_ent_or_cancel_l
    | |- <! ?B ∨ ?A !> ⇛ <! ?C ∨ ?A !> =>
        apply f_ent_or_cancel_r

    (* f_ent_impl_cancel_l and f_ent_impl_cancel_r *)
    | |- <! ?A ⇒ ?B !> ⇛ <! ?A ⇒ ?C !> =>
        apply f_ent_impl_cancel_l
    | |- <! ?B ⇒ ?A !> ⇛ <! ?C ⇒ ?A !> =>
        apply f_ent_impl_cancel_r

    (* f_ent_subst_cancel *)
    | |- <! ?A [ ?x \ ?t ]!> ⇛ <! ?B [ ?x \ ?t ] !> =>
        apply f_ent_subst_cancel

    | |- context[<! ⌜?t = ?t⌝ !>] =>
        rewrite f_eq_refl
    | |- context[<! ⌜?t ≠ ?t⌝ !>] =>
        rewrite f_neq_irrefl
  end.
