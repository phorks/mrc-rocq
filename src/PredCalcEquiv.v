From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalcBasic.

Section equiv.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).

  Implicit Types A B C : formula.
  Implicit Types t : term.

  Global Instance tequiv : Equiv term := λ t1 t2, ∀ σ v, teval σ t1 v ↔ teval σ t2 v.

  Definition fent A B : Prop := ∀ σ, feval σ A → feval σ B .
  Global Instance fequiv : Equiv formula := λ A B, ∀ σ, feval σ A ↔ feval σ B.


  Global Instance fent_refl : Reflexive fent.
  Proof with auto. intros ? ? ?... Qed.

  Global Instance fent_trans : Transitive fent.
  Proof with auto. intros ? ? ? ? ? ? ?... Qed.

  Global Instance fequiv_refl : Reflexive (≡@{formula}).
  Proof with auto. intros ? ?... Qed.

  Global Instance fequiv_sym : Symmetric (≡@{formula}).
  Proof with auto.
    intros A B H σ. destruct (H σ) as [H1 H2]. split; [apply H2|apply H1]...
  Qed.

  Global Instance fequiv_trans : Transitive (≡@{formula}).
  Proof with auto.
    intros A B C H H' σ. destruct (H σ) as [H1 H2]. destruct (H' σ) as [H3 H4].
    clear H H'. split; intros H.
    - apply H3. apply H1...
    - apply H2. apply H4...
  Qed.

  Global Instance fequiv_equiv : Equivalence (≡@{formula}).
  Proof.
    split.
    - exact fequiv_refl.
    - exact fequiv_sym.
    - exact fequiv_trans.
  Qed.

  Global Instance fent_antisym : Antisymmetric formula (≡@{formula}) fent.
  Proof. intros A B H1 H2 σ. specialize (H1 σ). specialize (H2 σ). naive_solver. Qed.

  Global Instance fent_proper_l : Proper ((≡@{formula}) ==> (=) ==> iff) fent.
  Proof with auto.
    intros A B H C ? <-. split; intros Hent σ; specialize (Hent σ);
      specialize (H σ); naive_solver.
  Qed.

  Global Instance fent_proper_r : Proper ((=) ==> (≡@{formula}) ==> iff) fent.
  Proof with auto.
    intros A ? <- B C H. split; intros Hent σ; specialize (Hent σ);
      specialize (H σ); naive_solver.
  Qed.

  Global Instance feval_proper : Proper ((=) ==> (≡@{formula}) ==> iff) feval.
  Proof with auto.
    intros σ ? <- A B H. split; intros; apply H...
  Qed.

  Global Instance fnot_proper : Proper ((≡@{formula}) ==> (≡@{formula})) FNot.
  Proof with auto.
    intros A B Hequiv σ. simp feval. split; intros H contra; apply H; apply Hequiv...
  Qed.

  Global Instance fand_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FAnd.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. simp feval.
    split; intros [? ?]; (split; [apply Heq1 | apply Heq2])...
  Qed.

  Global Instance for_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FOr.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. simp feval.
    split; (intros [|]; [left; apply Heq1 | right; apply Heq2])...
  Qed.

  Global Instance fimpl_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FImpl.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. unfold FImpl. rewrite Heq1. rewrite Heq2...
  Qed.

  Global Instance fiff_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FIff.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. unfold FIff, FImpl. rewrite Heq1. rewrite Heq2...
  Qed.
End equiv.

Declare Scope mrc_scope.
Infix "⇛" := fent (at level 70, no associativity) : mrc_scope.
Notation "(⇛)" := fent (only parsing).
