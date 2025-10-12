From MRC Require Import PredCalc.
From Stdlib Require Import Setoid Morphisms.
From stdpp Require Import base.

Definition fimplies (A B : formula) : Prop := forall M σ, feval M σ A -> feval M σ B.
Instance fequiv : Equiv formula := λ A B, forall M σ, feval M σ A <-> feval M σ B.

Declare Scope mrc_scope.
Infix "⇛" := fimplies (at level 70, no associativity) : mrc_scope.

Open Scope mrc_scope.
Open Scope stdpp_scope.

Implicit Types A B C : formula.

Instance fequiv_refl : Reflexive (≡@{formula}).
Proof with auto. intros ? ? ?. reflexivity. Qed.

Instance fequiv_sym : Symmetric (≡@{formula}).
Proof with auto.
  intros A B H M σ. destruct (H M σ) as [H1 H2]. split; [apply H2|apply H1]...
Qed.

Instance fequiv_trans : Transitive (≡@{formula}).
Proof with auto.
  intros A B C H H' M σ. destruct (H M σ) as [H1 H2]. destruct (H' M σ) as [H3 H4].
  clear H H'. split; intros H.
  - apply H3. apply H1...
  - apply H2. apply H4...
Qed.

Add Relation (formula) (fequiv)
  reflexivity proved by (fequiv_refl)
  symmetry proved by (fequiv_sym)
  transitivity proved by (fequiv_trans)
  as fequiv_rel.

Add Morphism F_Not
  with signature (≡@{formula}) ==> (≡@{formula}) as fnot_mor.
Proof with auto.
  intros A B Hequiv M σ. simpl. split; intros H contra; apply H; apply Hequiv...
Qed.

Add Morphism F_And
  with signature (≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula}) as fand_mor.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ. simpl. split; intros [H1 H2]; split.
  - apply Heq1...
  - apply Heq2...
  - apply Heq1...
  - apply Heq2...
Qed.

Add Morphism F_Or
  with signature (≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula}) as for_mor.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ. simpl. split; intros [|].
  - left. apply Heq1...
  - right. apply Heq2...
  - left. apply Heq1...
  - right. apply Heq2...
Qed.

Add Morphism F_Implies
  with signature (≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula}) as fimplication_mor.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ. simpl.
  split; intros Himp H; apply Heq2; apply Himp; apply Heq1...
Qed.
