From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import PredCalc.
From MRC Require Import PredCalcSubst.
From Stdlib Require Import Setoid Morphisms.
From stdpp Require Import base gmap.

Definition fimplies (A B : formula) : Prop := ∀ M σ b, feval M σ A b → feval M σ B b.
Instance fequiv : Equiv formula := λ A B, forall M σ b, feval M σ A b ↔ feval M σ B b.

Declare Scope mrc_scope.
Infix "⇛" := fimplies (at level 70, no associativity) : mrc_scope.

Open Scope stdpp_scope.

Implicit Types A B C : formula.

Instance fequiv_refl : Reflexive (≡@{formula}).
Proof with auto. intros ? ? ?. reflexivity. Qed.

Instance fequiv_sym : Symmetric (≡@{formula}).
Proof with auto.
  intros A B H M σ b. destruct (H M σ b) as [H1 H2]. split; [apply H2|apply H1]...
Qed.

Instance fequiv_trans : Transitive (≡@{formula}).
Proof with auto.
  intros A B C H H' M σ b. destruct (H M σ b) as [H1 H2]. destruct (H' M σ b) as [H3 H4].
  clear H H'. split; intros H.
  - apply H3. apply H1...
  - apply H2. apply H4...
Qed.

Instance fequiv_equiv : Equivalence (≡@{formula}).
Proof.
  split.
  - exact fequiv_refl.
  - exact fequiv_sym.
  - exact fequiv_trans.
Qed.

Instance feval_proper : Proper ((=) ==> (=) ==> (≡@{formula}) ==> (=) ==> iff) feval.
Proof with auto.
  intros M ? <- σ ? <- A B H b ? <-. split; intros; apply H...
Qed.

Instance fnot_proper : Proper ((≡@{formula}) ==> (≡@{formula})) FNot.
Proof with auto.
  intros A B Hequiv M σ b. simpl. split; inversion 1; subst; constructor; apply Hequiv...
Qed.

Instance fand_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FAnd.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ b. simpl.
  split; (inversion 1; subst; constructor; [apply Heq1 | apply Heq2])...
Qed.

Instance for_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FOr.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ b. simpl.
  split; (inversion 1; subst; constructor; [apply Heq1 | apply Heq2])...
Qed.

Instance fimpl_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula})) FImpl.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ b. unfold FImpl.
  assert (FNot A1 ≡ FNot A2) by (apply fnot_proper; assumption).
  apply (for_proper _ _ H _ _ Heq2).
Qed.

(* Instance fexists_proper : Proper ((=) ==> (=) ==> (≡@{formula}) ==> (≡@{formula})) FExists. *)
(* Proof with auto. *)
(*   intros x ? <- τ ? <- A B H M σ b. apply feval_exists_equiv. *)
(*   - intros. rewrite H... *)
(*   - intros. *)
