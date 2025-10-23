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

Add Relation (formula) (fequiv)
  reflexivity proved by (fequiv_refl)
  symmetry proved by (fequiv_sym)
  transitivity proved by (fequiv_trans)
  as fequiv_rel.

Add Morphism FNot
  with signature (≡@{formula}) ==> (≡@{formula}) as fnot_mor.
Proof with auto.
  intros A B Hequiv M σ b. simpl. split; inversion 1; subst; constructor; apply Hequiv...
Qed.

Add Morphism FAnd
  with signature (≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula}) as fand_mor.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ b. simpl.
  split; (inversion 1; subst; constructor; [apply Heq1 | apply Heq2])...
Qed.

Add Morphism FOr
  with signature (≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula}) as for_mor.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ b. simpl.
  split; (inversion 1; subst; constructor; [apply Heq1 | apply Heq2])...
Qed.

Add Morphism FImpl
  with signature (≡@{formula}) ==> (≡@{formula}) ==> (≡@{formula}) as fimplication_mor.
Proof with auto.
  intros A1 A2 Heq1 B1 B2 Heq2 M σ b. unfold FImpl.
  assert (FNot A1 ≡ FNot A2) by (apply fnot_mor; assumption). apply (for_mor _ _ H _ _ Heq2).
Qed.

Instance subst_proper {x t} : Proper ((≡@{formula}) ==> (≡@{formula})) (λ A, subst_formula A x t).
Proof with auto.
  intros A B H. unfold equiv, fequiv in *. intros. split; intros.
  - apply feval_wf in H0 as ?.
    destruct (decide (x ∈ formula_fvars A)); destruct (decide (x ∈ formula_fvars B)).
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + exfalso. rewrite subst_non_free in H0...
      rewrite feval_delete_state_var with (x:=x) in H0...
      apply H in H0. apply feval_wf in H0 as ?. apply formula_wf_state_covers in H2.
      set_solver.
    + rewrite subst_non_free in H0... rewrite subst_non_free... apply H...
  - apply feval_wf in H0 as ?.
    destruct (decide (x ∈ formula_fvars A)); destruct (decide (x ∈ formula_fvars B)).
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + exfalso. rewrite subst_non_free in H0...
      rewrite feval_delete_state_var with (x:=x) in H0...
      apply H in H0. apply feval_wf in H0 as ?. apply formula_wf_state_covers in H2.
      set_solver.
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + rewrite subst_non_free in H0... rewrite subst_non_free... apply H...
Qed.
