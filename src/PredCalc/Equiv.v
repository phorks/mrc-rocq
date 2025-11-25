From Equations Require Import Equations.
From stdpp Require Import fin_maps.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.Basic.

Section equiv.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).

  Implicit Types A B C : formula.
  Implicit Types t : term.

  Global Instance tequiv : Equiv term := λ t1 t2, ∀ σ v, teval σ t1 v ↔ teval σ t2 v.

  Global Instance tequiv_refl : Reflexive tequiv.
  Proof with auto. intros ? ? ?... Qed.

  Global Instance tequiv_sym : Symmetric tequiv.
  Proof with auto. intros ? ? ? ? ?. symmetry... Qed.

  Global Instance tequiv_trans : Transitive tequiv.
  Proof with auto.
    intros ? ? ? ? ? ? ?... split; intros.
    - apply H0. apply H...
    - apply H. apply H0...
  Qed.

  Global Instance tequiv_equiv : Equivalence tequiv.
  Proof.
    split; [exact tequiv_refl | exact tequiv_sym | exact tequiv_trans].
  Qed.

  Definition fent A B : Prop := ∀ σ, feval σ A → feval σ B.
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

  Global Instance ATEq_proper : Proper ((≡@{term}) ==> (≡@{term}) ==> (≡@{formula})) AT_Eq.
  Proof with auto.
    intros t1 t1' H1 t2 t2' H2 σ. simp feval. simpl. split; intros (v&?&?); exists v;
      (split; [apply H1 | apply H2])...
  Qed.

  Global Instance FNot_proper : Proper ((≡@{formula}) ==> (≡@{formula})) FNot.
  Proof with auto.
    intros A B Hequiv σ. simp feval. split; intros H contra; apply H; apply Hequiv...
  Qed.

  Global Instance FAnd_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FAnd.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. simp feval.
    split; intros [? ?]; (split; [apply Heq1 | apply Heq2])...
  Qed.

  Global Instance FOr_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FOr.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. simp feval.
    split; (intros [|]; [left; apply Heq1 | right; apply Heq2])...
  Qed.

  Global Instance FImpl_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FImpl.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. unfold FImpl. rewrite Heq1. rewrite Heq2...
  Qed.

  Global Instance FIff_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FIff.
  Proof with auto.
    intros A1 A2 Heq1 B1 B2 Heq2 σ. unfold FIff, FImpl. rewrite Heq1. rewrite Heq2...
  Qed.

  Global Instance feval_proper_fent : Proper ((=) ==> (fent) ==> (→)) feval.
  Proof with auto.
    intros σ ? <- A B Hent H. apply Hent...
  Qed.

End equiv.

Infix "⇛" := fent (at level 70, no associativity).
Notation "(⇛)" := fent (only parsing).
Notation "(⇛@{ M } )" := (@fent M) (only parsing).
Infix "⇚" := (flip fent) (at level 70, no associativity).
Notation "(⇚)" := (flip fent) (only parsing).
Notation "(⇚@{ M } )" := (flip (@fent M)) (only parsing).

Section ent.
  Context {M : model}.
  Implicit Types A B C : formula (value M).

  Global Instance FNot_proper_fent : Proper ((⇛) ==> (flip (⇛@{M}))) FNot.
  Proof with auto.
    intros A B Hent σ. simp feval. intros H contra. apply H. apply Hent...
  Qed.

  Lemma f_ent_contrapositive A B :
    <! ¬ B !> ⇛ <! ¬ A !> ↔ <! A !> ⇛ <! B !>.
  Proof with auto.
    split; intros.
    - intros σ. specialize (H σ). simp feval in H. intros. pose proof (feval_lem σ B) as []...
      apply H in H1. contradiction.
    - rewrite H... reflexivity.
  Qed.

  Lemma f_ent_reverse_direction A B :
    <! A !> ⇚ <! B !> ↔ <! ¬ A !> ⇛ <! ¬ B !>.
  Proof with auto.
    unfold flip. rewrite f_ent_contrapositive...
  Qed.

  Global Instance FAnd_proper_fent : Proper ((⇛) ==> (⇛) ==> (⇛@{M})) FAnd.
  Proof with auto.
    intros A1 A2 Hent1 B1 B2 Hent2 σ. simp feval.
    intros [? ?]; split; [apply Hent1 | apply Hent2]...
  Qed.

  Global Instance FOr_proper_fent : Proper ((⇛) ==> (⇛) ==> (⇛@{M})) FOr.
  Proof with auto.
    intros A1 A2 Hent1 B1 B2 Hent2 σ. simp feval.
    intros [|]; [left; apply Hent1 | right; apply Hent2]...
  Qed.

  Global Instance FImpl_proper_fent : Proper ((⇚) ==> (⇛@{M}) ==> (⇛)) FImpl.
  Proof with auto.
    intros A1 A2 Hent1 B1 B2 Hent2. unfold FImpl. rewrite f_ent_reverse_direction in Hent1.
    rewrite Hent1. rewrite Hent2. reflexivity.
  Qed.

End ent.
