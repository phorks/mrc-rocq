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
  Local Notation state := (state M).

  Implicit Types A B C : formula.
  Implicit Types t : term.
  Implicit Types σ : state.

  (* ******************************************************************* *)
  (* term equivalence under a fixed state                                *)
  (* ******************************************************************* *)
  Definition tequiv_st σ t1 t2 := ∀ v, teval σ t1 v ↔ teval σ t2 v.

  Global Instance tequiv_st_refl σ : Reflexive (tequiv_st σ).
  Proof with auto. intros ? ?... Qed.

  Global Instance tequiv_st_sym σ : Symmetric (tequiv_st σ).
  Proof with auto. intros ? ? ? ?. symmetry... Qed.

  Global Instance tequiv_st_trans σ : Transitive (tequiv_st σ).
  Proof with auto. intros ? ? ? ? ? ?... unfold tequiv_st in *. naive_solver. Qed.

  Global Instance tequiv_st_equiv σ : Equivalence (tequiv_st σ).
  Proof. split; [apply tequiv_st_refl | apply tequiv_st_sym | apply tequiv_st_trans]. Qed.

  (* ******************************************************************* *)
  (* term equivalence under all states                                   *)
  (* ******************************************************************* *)
  Global Instance tequiv : Equiv term := λ t1 t2, ∀ σ v, teval σ t1 v ↔ teval σ t2 v.

  Global Instance tequiv_refl : Reflexive tequiv.
  Proof with auto. intros ? ? ?... Qed.

  Global Instance tequiv_sym : Symmetric tequiv.
  Proof with auto. intros ? ? ? ? ?. symmetry... Qed.

  Global Instance tequiv_trans : Transitive tequiv.
  Proof with auto. intros ? ? ? ? ? ? ?... unfold tequiv in *. naive_solver. Qed.

  Global Instance tequiv_equiv : Equivalence tequiv.
  Proof. split; [exact tequiv_refl | exact tequiv_sym | exact tequiv_trans]. Qed.

  (* ******************************************************************* *)
  (* ⇛ and ≡ under a specific state                                      *)
  (* ******************************************************************* *)
  Definition fent_st σ A B := feval σ A → feval σ B.
  Definition fequiv_st σ A B := feval σ A ↔ feval σ B.

  Global Instance fent_st_refl σ : Reflexive (fent_st σ).
  Proof with auto. intros ? ?... Qed.

  Global Instance fent_st_trans σ : Transitive (fent_st σ).
  Proof with auto. intros ? ? ? ? ? ?... Qed.

  Global Instance fequiv_st_refl σ : Reflexive (fequiv_st σ).
  Proof with auto. intros ?. unfold fequiv_st... Qed.

  Global Instance fequiv_st_sym σ : Symmetric (fequiv_st σ).
  Proof with auto. intros A B H. destruct H as [H1 H2]. split; [apply H2|apply H1]... Qed.

  Global Instance fequiv_st_trans σ : Transitive (fequiv_st σ).
  Proof with auto. intros A B C H H'. unfold fequiv_st in *. naive_solver. Qed.

  Global Instance fequiv_st_equiv σ : Equivalence (fequiv_st σ).
  Proof. split; [apply fequiv_st_refl | apply fequiv_st_sym | apply fequiv_st_trans]. Qed.

  Global Instance fent_st_antisym σ : Antisymmetric formula (fequiv_st σ) (fent_st σ).
  Proof. intros A B H1 H2. unfold fent_st, fequiv_st in *. naive_solver. Qed.

  Global Instance fent_st_proper_fequiv_st σ
    : Proper ((fequiv_st σ) ==> (fequiv_st σ) ==> iff) (fent_st σ).
  Proof with auto. intros A B HAB C D HCD. unfold fent_st, fequiv_st in *. naive_solver. Qed.

  Global Instance feval_proper_fent_st σ : Proper ((fent_st σ) ==> impl) (feval σ).
  Proof with auto. intros A B H. apply H. Qed.

  Global Instance feval_proper_fequiv_st σ : Proper ((fequiv_st σ) ==> iff) (feval σ).
  Proof with auto. intros A B H. apply H. Qed.

  (* ******************************************************************* *)
  (* ⇛ and ≡ under all states                                            *)
  (* ******************************************************************* *)

  Definition fent A B : Prop := ∀ σ, feval σ A → feval σ B.
  Global Instance fequiv : Equiv formula := λ A B, ∀ σ, feval σ A ↔ feval σ B.

  Global Instance fent_refl : Reflexive fent.
  Proof with auto. intros ? ? ?... Qed.

  Global Instance fent_trans : Transitive fent.
  Proof with auto. intros ? ? ? ? ? ? ?... Qed.

  Global Instance fequiv_refl : Reflexive (≡@{formula}).
  Proof with auto. intros ? ?... Qed.

  Global Instance fequiv_sym : Symmetric (≡@{formula}).
  Proof with auto. intros A B H σ. destruct (H σ) as [H1 H2]. naive_solver. Qed.

  Global Instance fequiv_trans : Transitive (≡@{formula}).
  Proof with auto. intros A B C H H' σ. unfold equiv, fequiv in *. naive_solver. Qed.

  Global Instance fequiv_equiv : Equivalence (≡@{formula}).
  Proof. split; [exact fequiv_refl | exact fequiv_sym | exact fequiv_trans]. Qed.

  Global Instance fent_antisym : Antisymmetric formula (≡@{formula}) fent.
  Proof. intros A B H1 H2 σ. specialize (H1 σ). specialize (H2 σ). naive_solver. Qed.

  Global Instance fent_proper : Proper ((≡@{formula}) ==> (≡@{formula}) ==> iff) fent.
  Proof with auto.
    intros A B HAB C D HCD. split; intros Hent σ; specialize (HAB σ); specialize (HCD σ);
      naive_solver.
  Qed.

  Global Instance feval_proper_fent : Proper ((=) ==> fent ==> impl) feval.
  Proof with auto. intros σ ? <- A B H. exact (H σ). Qed.

  Global Instance feval_proper : Proper ((=) ==> (≡@{formula}) ==> iff) feval.
  Proof with auto. intros σ ? <- A B H. split; intros; apply H... Qed.

  (* ******************************************************************* *)
  (* ⇛_σ and ≡_σ proper under ⇛ and ≡                                    *)
  (* ******************************************************************* *)
  Global Instance fent_st_proper σ : Proper ((≡@{formula}) ==> (≡@{formula}) ==> iff) (fent_st σ).
  Proof.
    intros A B HAB C D HCD. unfold fent_st in *. split; intros Himpl H; apply HAB in H;
      apply HCD; apply (Himpl H).
  Qed.

  Global Instance fent_st_proper_fent σ : Proper ((flip fent) ==> fent ==> impl) (fent_st σ).
  Proof.
    intros A B HAB C D HCD HAC HB. apply HAB in HB. apply HAC in HB. apply HCD. apply HB.
  Qed.

  (* ******************************************************************* *)
  (* ⇛_{σ} and ≡_{σ} proper formula constructors                         *)
  (* ******************************************************************* *)
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

  (* ******************************************************************* *)
  (* ⇛ and ≡ proper formula constructors                                 *)
  (* ******************************************************************* *)
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

End equiv.

Infix "≡_{ σ }" := (fequiv_st σ) (at level 70, no associativity) : refiney_scope.
Infix "≡_{ σ }@{ M }" := (@fequiv_st M σ) (at level 70, only parsing, no associativity)
    : refiney_scope.
Notation "(≡_{ σ } )" := (fequiv_st σ) (only parsing, no associativity) : refiney_scope.
Notation "(≡_{ σ }@{ M } )" := (@fequiv_st M σ) (only parsing, no associativity) : refiney_scope.
Infix "≡ₗ@{ M }" := (@equiv (formula M) _) (at level 70, only parsing, no associativity)
    : refiney_scope.
Notation "(≡ₗ@{ M } )" := ((≡@{formula M})) (only parsing) : refiney_scope.
Infix "⇛" := fent (at level 70, no associativity) : refiney_scope.
Notation "(⇛)" := fent (only parsing) : refiney_scope.
Notation "(⇛ₗ@{ M } )" := (@fent M) (only parsing) : refiney_scope.
Infix "⇚" := (flip fent) (at level 70, no associativity) : refiney_scope.
Notation "(⇚)" := (flip fent) (only parsing) : refiney_scope.
Notation "(⇚ₗ@{ M } )" := (flip (@fent M)) (only parsing) : refiney_scope.

Section ent.
  Context {M : model}.
  Implicit Types A B C : formula (value M).

  Lemma flip_fent A B :
    A ⇛ B ↔ B ⇚ A.
  Proof with auto.
    unfold flip...
  Qed.

  Lemma fequiv_fent A B :
    A ≡ B ↔ A ⇛ B ∧ B ⇛ A.
  Proof.
    split.
    - intros H. rewrite H. split; reflexivity.
    - intros []. split.
      + apply H.
      + apply H0.
  Qed.

  Global Instance FNot_proper_fent : Proper ((⇛ₗ@{M}) --> (⇛)) FNot.
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

  Global Instance FAnd_proper_fent : Proper ((⇛ₗ@{M}) ==> (⇛) ==> (⇛)) FAnd.
  Proof with auto.
    intros A1 A2 Hent1 B1 B2 Hent2 σ. simp feval.
    intros [? ?]; split; [apply Hent1 | apply Hent2]...
  Qed.

  Global Instance FOr_proper_fent : Proper ((⇛ₗ@{M}) ==> (⇛) ==> (⇛)) FOr.
  Proof with auto.
    intros A1 A2 Hent1 B1 B2 Hent2 σ. simp feval.
    intros [|]; [left; apply Hent1 | right; apply Hent2]...
  Qed.

  Global Instance FImpl_proper_fent : Proper ((⇛ₗ@{M}) --> (⇛) ==> (⇛)) FImpl.
  Proof with auto.
    intros A1 A2 Hent1 B1 B2 Hent2. unfold FImpl. rewrite f_ent_reverse_direction in Hent1.
    rewrite Hent1. rewrite Hent2. reflexivity.
  Qed.

End ent.
