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

Ltac f_simpl :=
  repeat match goal with
    | H : context[<! ?A ∧ ?A !>] |- _ =>
        rewrite f_and_idemp in H
    | |- context[<! ?A ∧ ?A !>] =>
        rewrite f_and_idemp

    | H : context[<! ?A ∨ ?A !>] |- _ =>
        rewrite f_or_idemp in H
    | |- context[<! ?A ∨ ?A !>] =>
        rewrite f_or_idemp

    (*  f_and_or_absorb *)
    | H : context[<! ?A ∧ (?A ∨ ?B) !>] |- _ =>
        rewrite f_and_or_absorb in H
    | H : context[<! (?A ∨ ?B) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        rewrite Heq in H; rewrite f_and_or_absorb in H; clear Heq
    | H : context[<! (?B ∨ ?A) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        rewrite Heq in H; rewrite f_and_or_absorb in H; clear Heq
    | |- context[<! ?A ∧ (?A ∨ ?B) !>] =>
        rewrite f_and_or_absorb
    | |- context[<! (?A ∨ ?B) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        rewrite Heq; rewrite f_and_or_absorb; clear Heq
    | |- context[<! (?B ∨ ?A) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ∧ A !> ≡ <! (A ∧ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        rewrite Heq; rewrite f_and_or_absorb; clear Heq

    (*  f_or_and_absorb *)
    | H : context[<! ?A ∨ (?A ∧ ?B) !>] |- _ =>
        rewrite f_or_and_absorb in H
    | H : context[<! (?A ∧ ?B) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        rewrite Heq in H; rewrite f_or_and_absorb in H; clear Heq
    | H : context[<! (?B ∧ ?A) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        rewrite Heq in H; rewrite f_or_and_absorb in H; clear Heq
    | |- context[<! ?A ∨ (?A ∧ ?B) !>] =>
        rewrite f_or_and_absorb
    | |- context[<! (?A ∧ ?B) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        rewrite Heq; rewrite f_or_and_absorb; clear Heq
    | |- context[<! (?B ∧ ?A) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ∨ A !> ≡ <! (A ∨ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        rewrite Heq; rewrite f_or_and_absorb; clear Heq

    (* f_and_true *)
    | H : context[<! ?A ∧ true !>] |- _ =>
        rewrite f_and_true in H
    | H : context[<! true ∧ ?A !>] |- _ =>
        rewrite (f_and_comm <! true !> A) in H; rewrite f_and_true in H
    | |- context[<! ?A ∧ true !>] =>
        rewrite f_and_true
    | |- context[<! true ∧ ?A !>] =>
        rewrite (f_and_comm <! true !> A); rewrite f_and_true

    (* f_and_false *)
    | H : context[<! ?A ∧ false !>] |- _ =>
        rewrite f_and_false in H
    | H : context[<! false ∧ ?A !>] |- _ =>
        rewrite (f_and_comm <! false !> A) in H; rewrite f_and_false in H
    | |- context[<! ?A ∧ false !>] =>
        rewrite f_and_false
    | |- context[<! false ∧ ?A !>] =>
        rewrite (f_and_comm <! false !> A); rewrite f_and_false

    (* f_or_true *)
    | H : context[<! ?A ∨ true !>] |- _ =>
        rewrite f_or_true in H
    | H : context[<! true ∨ ?A !>] |- _ =>
        rewrite (f_or_comm <! true !> A) in H; rewrite f_or_true in H
    | |- context[<! ?A ∨ true !>] =>
        rewrite f_or_true
    | |- context[<! true ∨ ?A !>] =>
        rewrite (f_or_comm <! true !> A); rewrite f_or_true

    (* f_or_false *)
    | H : context[<! ?A ∨ false !>] |- _ =>
        rewrite f_or_false in H
    | H : context[<! false ∨ ?A !>] |- _ =>
        rewrite (f_or_comm <! false !> A) in H; rewrite f_or_false in H
    | |- context[<! ?A ∨ false !>] =>
        rewrite f_or_false
    | |- context[<! false ∨ ?A !>] =>
        rewrite (f_or_comm <! false !> A); rewrite f_or_false

    (* f_not_true *)
    | H : context[<! ¬ true !>] |- _ =>
        rewrite f_not_true in H
    | |- context[<! ¬ true !>] =>
        rewrite f_not_true

    (* f_false_true *)
    | H : context[<! ¬ false !>] |- _ =>
        rewrite f_not_false in H
    | |- context[<! ¬ false !>] =>
        rewrite f_not_false

    (* f_and_not_self *)
    | H : context[<! ?A ∧ ¬ ?A !>] |- _ =>
        rewrite f_and_not_self in H
    | H : context[<! ¬ ?A ∧ ?A !>] |- _ =>
        rewrite (f_and_comm (<! ¬ A !>) A) in H; rewrite f_and_not_self in H
    | |- context[<! ?A ∧ ¬ ?A !>] =>
        rewrite f_and_not_self
    | |- context[<! ¬ ?A ∧ ?A !>] =>
        rewrite (f_and_comm (<! ¬ A !>) A); rewrite f_and_not_self

    (* f_lem *)
    | H : context[<! ?A ∨ ¬ ?A !>] |- _ =>
        rewrite f_lem in H
    | H : context[<! ¬ ?A ∨ ?A !>] |- _ =>
        rewrite (f_or_comm (<! ¬ A !>) A) in H; rewrite f_lem in H
    | |- context[<! ?A ∨ ¬ ?A !>] =>
        rewrite f_lem
    | |- context[<! ¬ ?A ∨ ?A !>] =>
        rewrite (f_or_comm (<! ¬ A !>) A); rewrite f_lem

    (* f_not_stable *)
    | H : context[<! ¬ ¬ ?A !>] |- _ =>
        rewrite f_not_stable in H
    | |- context[<! ¬ ¬ ?A !>] =>
        rewrite f_not_stable

    (* f_not_and *)
    | H : context[<! ¬ (?A ∧ ?B) !>] |- _ =>
        rewrite f_not_and in H
    | |- context[<! ¬ (?A ∧ ?B) !>] =>
        rewrite f_not_and

    (* f_not_or *)
    | H : context[<! ¬ (?A ∨ ?B) !>] |- _ =>
        rewrite f_not_or in H
    | |- context[<! ¬ (?A ∨ ?B) !>] =>
        rewrite f_not_or

    (* (* f_and_or_distr *) *)
    (* | H : context[<! ?A ∧ (?B ∨ ?C) !>] |- _ => *)
    (*     rewrite f_and_or_distr in H *)
    (* | H : context[<! (?B ∨ ?C) ∧ ?A !>] |- _ => *)
    (*     rewrite (f_and_comm (?B ∨ ?C) ?A) in H; rewrite f_and_or_distr in H *)
    (* | |- context[<! ?A ∧ (?B ∨ ?C) !>] => *)
    (*     rewrite f_and_or_distr *)
    (* | |- context[<! (?B ∨ ?C) ∧ ?A !>] => *)
    (*     rewrite (f_and_comm (?B ∨ ?C) ?A); rewrite f_and_or_distr *)

    (* (* f_or_and_distr *) *)
    (* | H : context[<! ?A ∨ (?B ∧ ?C) !>] |- _ => *)
    (*     rewrite f_or_and_distr in H *)
    (* | H : context[<! (?B ∧ ?C) ∨ ?A !>] |- _ => *)
    (*     rewrite (f_or_comm (?B ∧ ?C) ?A) in H; rewrite f_or_and_distr in H *)
    (* | |- context[<! ?A ∨ (?B ∧ ?C) !>] => *)
    (*     rewrite f_or_and_distr *)
    (* | |- context[<! (?B ∨ ?C) ∧ ?A !>] => *)
    (*     rewrite (f_and_comm (?B ∨ ?C) ?A); rewrite f_or_and_distr *)

    (*  f_and_or_absorb' *)
    | H : context[<! ?A ∧ (¬ ?A ∨ ?B) !>] |- _ =>
        rewrite f_and_or_absorb' in H
    | H : context[<! (¬ ?A ∨ ?B) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∨ B) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        rewrite Heq in H; rewrite f_and_or_absorb' in H; clear Heq
    | H : context[<! (?B ∨ ¬ ?A) ∧ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ ¬ A) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        rewrite Heq in H; rewrite f_and_or_absorb' in H; clear Heq
    | |- context[<! ?A ∧ (¬ ?A ∨ ?B) !>] =>
        rewrite f_and_or_absorb'
    | |- context[<! (¬ ?A ∨ ?B) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∨ B) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_and_comm; reflexivity);
        rewrite Heq; rewrite f_and_or_absorb'; clear Heq
    | |- context[<! (?B ∨ ¬ ?A) ∧ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ ¬ A) ∧ A !> ≡ <! (A ∧ (¬ A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_and_comm; reflexivity);
        rewrite Heq; rewrite f_and_or_absorb'; clear Heq

    (*  f_or_and_absorb' *)
    | H : context[<! ?A ∨ (¬ ?A ∧ ?B) !>] |- _ =>
        rewrite f_or_and_absorb' in H
    | H : context[<! (¬ ?A ∧ ?B) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∧ B) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        rewrite Heq in H; rewrite f_or_and_absorb' in H; clear Heq
    | H : context[<! (?B ∧ ¬ ?A) ∨ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ ¬ A) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        rewrite Heq in H; rewrite f_or_and_absorb' in H; clear Heq
    | |- context[<! ?A ∨ (¬ ?A ∧ ?B) !>] =>
        rewrite f_or_and_absorb'
    | |- context[<! (¬ ?A ∧ ?B) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (¬ A ∧ B) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_or_comm; reflexivity);
        rewrite Heq; rewrite f_or_and_absorb'; clear Heq
    | |- context[<! (?B ∧ ¬ ?A) ∨ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ ¬ A) ∨ A !> ≡ <! (A ∨ (¬ A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_or_comm; reflexivity);
        rewrite Heq; rewrite f_or_and_absorb'; clear Heq

    (* f_implies_self *)
    | H : context[<! ?A ⇒ ?A !>] |- _ =>
        rewrite f_implies_self in H
    | |- context[<! ?A ⇒ ?A !>] =>
        rewrite f_implies_self

    (* f_not_impl *)
    | H : context[<! ¬ (?A ⇒ ?B) !>] |- _ =>
        rewrite f_not_impl in H
    | |- context[<! ¬ (?A ⇒ ?B) !>] =>
        rewrite f_not_impl

    (* f_implies_true *)
    | H : context[<! ?A ⇒ true !>] |- _ =>
        rewrite f_implies_true in H
    | |- context[<! ?A ⇒ true !>] =>
        rewrite f_implies_true

    (* f_true_implies *)
    | H : context[<! true ⇒ ?A !>] |- _ =>
        rewrite f_true_implies in H
    | |- context[<! true ⇒ ?A !>] =>
        rewrite f_true_implies

    (* f_implies_false *)
    | H : context[<! ?A ⇒ false !>] |- _ =>
        rewrite f_implies_false in H
    | |- context[<! ?A ⇒ false !>] =>
        rewrite f_implies_false

    (* f_false_implies *)
    | H : context[<! false ⇒ ?A !>] |- _ =>
        rewrite f_false_implies in H
    | |- context[<! false ⇒ ?A !>] =>
        rewrite f_false_implies

    (* f_implies_not_self *)
    | H : context[<! ?A ⇒ ¬ ?A !>] |- _ =>
        rewrite f_implies_not_self in H
    | |- context[<! ?A ⇒ ¬ ?A !>] =>
        rewrite f_implies_not_self

    (* f_not_implies_self *)
    | H : context[<! ¬ ?A ⇒ ?A !>] |- _ =>
        rewrite f_not_implies_self in H
    | |- context[<! ¬ ?A ⇒ ?A !>] =>
        rewrite f_not_implies_self

    (* f_iff_equiv3 *)
    | H : context[<! ¬ ?A ⇔ ¬ ?B !>] |- _ =>
        rewrite <- f_iff_negate in H
    | |- context[<! ¬ ?A ⇔ ¬ ?B !>] =>
        rewrite <- f_iff_negate

    (* f_iff_self *)
    | H : context[<! ?A ⇔ ?A !>] |- _ =>
        rewrite f_iff_self in H
    | |- context[<! ?A ⇔ ?A !>] =>
        rewrite f_iff_self

    (* f_iff_not_self *)
    | H : context[<! ?A ⇔ ¬ ?A !>] |- _ =>
        rewrite f_iff_not_self in H
    | H : context[<! ¬ ?A ⇔ ?A !>] |- _ =>
        rewrite (f_iff_comm (<! ¬ A !>) A) in H; rewrite f_iff_not_self in H
    | |- context[<! ?A ⇔ ?A !>] =>
        rewrite f_iff_self
    | |- context[<! ¬ ?A ⇔ ?A !>] =>
        rewrite (f_iff_comm (<! ¬ A !>) A); rewrite f_iff_not_self

    (* f_iff_true *)
    | H : context[<! ?A ⇔ true !>] |- _ =>
        rewrite f_iff_true in H
    | H : context[<! true ⇔ ?A !>] |- _ =>
        rewrite (f_iff_comm (<! true !>) A) in H; rewrite f_iff_true in H
    | |- context[<! ?A ⇔ true !>] =>
        rewrite f_iff_true
    | |- context[<! true ⇔ ?A !>] =>
        rewrite (f_iff_comm (<! true !>) A); rewrite f_iff_true

    (* f_iff_false *)
    | H : context[<! ?A ⇔ false !>] |- _ =>
        rewrite f_iff_false in H
    | H : context[<! false ⇔ ?A !>] |- _ =>
        rewrite (f_iff_comm (<! false !>) A) in H; rewrite f_iff_false in H
    | |- context[<! ?A ⇔ false !>] =>
        rewrite f_iff_false
    | |- context[<! false ⇔ ?A !>] =>
        rewrite (f_iff_comm (<! false !>) A); rewrite f_iff_false

    (*  f_iff_and_absorb *)
    | H : context[<! ?A ⇔ (?A ∧ ?B) !>] |- _ =>
        rewrite f_iff_and_absorb in H
    | H : context[<! (?A ∧ ?B) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        rewrite Heq in H; rewrite f_iff_and_absorb in H; clear Heq
    | H : context[<! (?B ∧ ?A) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_iff_comm; reflexivity);
        rewrite Heq in H; rewrite f_iff_and_absorb in H; clear Heq
    | |- context[<! ?A ⇔ (?A ∧ ?B) !>] =>
        rewrite f_iff_and_absorb
    | |- context[<! (?A ∧ ?B) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∧ B) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        rewrite Heq; rewrite f_iff_and_absorb; clear Heq
    | |- context[<! (?B ∧ ?A) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∧ A) ⇔ A !> ≡ <! (A ⇔ (A ∧ B)) !>) as Heq
          by (rewrite f_and_comm; rewrite f_iff_comm; reflexivity);
        rewrite Heq; rewrite f_iff_and_absorb; clear Heq

    (* f_not_forall *)
    | H : context[<! ¬ ∀ ?x, ?A !>] |- _ =>
        rewrite f_not_forall in H
    | |- context[<! ¬ ∀ ?x, ?A !>] =>
        rewrite f_not_forall

    (* f_not_exists *)
    | H : context[<! ¬ ∃ ?x, ?A !>] |- _ =>
        rewrite f_not_exists in H
    | |- context[<! ¬ ∃ ?x, ?A !>] =>
        rewrite f_not_exists

    (*  f_iff_or_absorb *)
    | H : context[<! ?A ⇔ (?A ∨ ?B) !>] |- _ =>
        rewrite f_iff_or_absorb in H
    | H : context[<! (?A ∨ ?B) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        rewrite Heq in H; rewrite f_iff_or_absorb in H; clear Heq
    | H : context[<! (?B ∨ ?A) ⇔ ?A !>] |- _ =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_iff_comm; reflexivity);
        rewrite Heq in H; rewrite f_iff_or_absorb in H; clear Heq
    | |- context[<! ?A ⇔ (?A ∨ ?B) !>] =>
        rewrite f_iff_or_absorb
    | |- context[<! (?A ∨ ?B) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (A ∨ B) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_iff_comm; reflexivity);
        rewrite Heq; rewrite f_iff_or_absorb; clear Heq
    | |- context[<! (?B ∨ ?A) ⇔ ?A !>] =>
        let Heq := fresh "Heq" in
        assert (<! (B ∨ A) ⇔ A !> ≡ <! (A ⇔ (A ∨ B)) !>) as Heq
          by (rewrite f_or_comm; rewrite f_iff_comm; reflexivity);
        rewrite Heq; rewrite f_iff_or_absorb; clear Heq

    (* f_impl_elim *)
    | H : context[<! ?A ∧ (?A ⇒ ?B) !>] |- _ =>
        rewrite f_impl_elim in H
    | H : context[<! (?A ⇒ ?B) ∧ ?A !>] |- _ =>
        rewrite (f_and_comm (<! ?A ⇒ ?B !>) ?A) in H; rewrite f_impl_elim in H
    | |- context[<! ?A ∧ (?A ⇒ ?B) !>] =>
        rewrite f_impl_elim
    | |- context[<! (?A ⇒ ?B) ∧ ?A !>] =>
        rewrite (f_and_comm (<! ?A ⇒ ?B !>) ?A); rewrite f_impl_elim

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
