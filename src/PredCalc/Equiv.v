From Equations Require Import Equations.
From stdpp Require Import base tactics.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.Basic.

Section equiv.
  Close Scope stdpp_scope.

  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).
  Local Notation state := (state M).

  Implicit Types A B C : formula.
  Implicit Types t : term.
  Implicit Types σ : state.

  (** * Two notions of equivalence for [term]s: [≡] and [≡_{σ}]  *)
  Definition tequiv_st σ t1 t2 := ∀ v, teval σ t1 v ↔ teval σ t2 v.
  Global Instance tequiv : Equiv term := λ t1 t2, ∀ σ v, teval σ t1 v ↔ teval σ t2 v.

  Local Notation "(≡ₜ_{ σ } )" := (tequiv_st σ).
  Local Notation "(≡ₜ)" := (@equiv term).

  (** [≡] is a subrelation of [≡_{σ}] *)
  Global Instance tequiv_subrelation_tequiv_st {σ} : subrelation (≡ₜ) (≡ₜ_{σ}).
  Proof. intros ? ? ?. specialize (H σ). auto. Qed.

  (** ** [≡_{σ}] is an equivalence relation  *)
  Global Instance tequiv_st_refl {σ} : Reflexive (≡ₜ_{σ}).
  Proof with auto. intros ? ?... Qed.

  Global Instance tequiv_st_sym {σ} : Symmetric (≡ₜ_{σ}).
  Proof with auto. intros ? ? ? ?. symmetry... Qed.

  Global Instance tequiv_st_trans {σ} : Transitive (≡ₜ_{σ}).
  Proof with auto. intros ? ? ? ? ? ?... unfold tequiv_st in *. naive_solver. Qed.

  Global Instance tequiv_st_equiv {σ} : Equivalence (≡ₜ_{σ}).
  Proof. split; [apply tequiv_st_refl | apply tequiv_st_sym | apply tequiv_st_trans]. Qed.

  (** ** [≡ₜ] is an equivalence relation *)
  Global Instance tequiv_refl : Reflexive (≡ₜ).
  Proof with auto. intros ? ? ?... Qed.

  Global Instance tequiv_sym : Symmetric (≡ₜ).
  Proof with auto. intros ? ? ? ?. symmetry. auto. Qed.

  Global Instance tequiv_trans : Transitive (≡ₜ).
  Proof with auto. intros ? ? ? ? ? ? ?... unfold equiv, tequiv, tequiv_st in *. naive_solver. Qed.

  Global Instance tequiv_equiv : Equivalence (≡ₜ).
  Proof. split; [exact tequiv_refl | exact tequiv_sym | exact tequiv_trans]. Qed.

  (** * [formula] entailment and equivalence *)
  (** ** Two notions of entailment: [⇛] and [⇛_{σ}]  **)
  Definition fent_st σ A B := feval σ A → feval σ B.
  Definition fent A B : Prop := ∀ σ, feval σ A → feval σ B.

  Local Notation "(⇛_{ σ } )" := (fent_st σ).
  Local Notation "(⇛)" := (fent).
  Local Notation "(⇚_{ σ } )" := (flip (fent_st σ)).
  Local Notation "(⇚)" := (flip fent).

  (** [⇛] is a subrelation of [⇛_{σ}] *)
  Instance fent_subrelation_fent_st {σ} : subrelation (⇛) (⇛_{σ}).
  Proof. intros ? ? ?. specialize (H σ). auto. Qed.

  (** *** [⇛_{σ}] is reflexive and transitive *)
  Global Instance fent_st_refl {σ} : Reflexive (⇛_{σ}).
  Proof with auto. intros ? ?... Qed.

  Global Instance fent_st_trans {σ} : Transitive (⇛_{σ}).
  Proof with auto. intros ? ? ? ? ? ?... Qed.

  (** *** [⇛] is reflexive and transitive *)
  Global Instance fent_refl : Reflexive (⇛).
  Proof with auto. intros ? ? ?... Qed.

  Global Instance fent_trans : Transitive (⇛).
  Proof with auto. intros ? ? ? ? ? ? ?... Qed.

  (** ** Two notions of equivalence: [≡] and [≡_{σ}]  *)
  Definition fequiv_st σ A B := feval σ A ↔ feval σ B.
  Global Instance fequiv : Equiv formula := λ A B, ∀ σ, feval σ A ↔ feval σ B.

  (* a local tactic for solving formula equivalences *)
  Local Ltac solve_equiv :=
    hnf; unfold FIff, FImpl, tequiv_st, tequiv, fent_st, fent, equiv, fequiv, fequiv_st,
      respectful, impl; intros; simpl in *; simp feval in *; naive_solver.

  Local Notation "(≡_{ σ } )" := (fequiv_st σ).
  Local Notation "(≡)" := (@equiv formula).

  (** [≡] is a subrelation of [≡_{σ}] *)
  Instance fequiv_subrelation_fequiv_st {σ} : subrelation (≡) (≡_{σ}).
  Proof. solve_equiv. Qed.

  (** *** [≡_{σ}] is an equivalence relation *)
  Global Instance fequiv_st_refl {σ} : Reflexive (≡_{σ}).
  Proof. solve_equiv. Qed.

  Global Instance fequiv_st_sym {σ} : Symmetric (≡_{σ}).
  Proof. solve_equiv. Qed.

  Global Instance fequiv_st_trans {σ} : Transitive (≡_{σ}).
  Proof. solve_equiv. Qed.

  Global Instance fequiv_st_equiv {σ} : Equivalence (≡_{σ}).
  Proof. split; [apply fequiv_st_refl | apply fequiv_st_sym | apply fequiv_st_trans]. Qed.

  (** *** [≡] is an equivalence relation *)
  Global Instance fequiv_refl : Reflexive (≡).
  Proof. solve_equiv. Qed.

  Global Instance fequiv_sym : Symmetric (≡).
  Proof. solve_equiv. Qed.

  Global Instance fequiv_trans : Transitive (≡).
  Proof. solve_equiv. Qed.

  Global Instance fequiv_equiv : Equivalence (≡).
  Proof. split; [exact fequiv_refl | exact fequiv_sym | exact fequiv_trans]. Qed.

  (** ** Connections between entailment and equivalence *)
  (** [⇛] is antisymmetric with respect to [≡] *)
  Global Instance fent_st_antisym {σ} : Antisymmetric formula (≡_{σ}) (⇛_{σ}).
  Proof. solve_equiv. Qed.

  Global Instance fent_antisym : Antisymmetric formula (≡) (⇛).
  Proof. solve_equiv. Qed.

  (** [≡] is subrelation of [⇛] and [⇚]: although technically this is true, but adding the
      subrelation instances causes [rewrite]s to be very slow. *)
  (* Global Instance fequiv_st_subrelation_fent_st {σ} : subrelation (≡_{σ}) (⇛_{σ}). *)
  (* Proof. solve_equiv. Qed. *)

  (* Global Instance fequiv_st_subrelation_flip_fent_st {σ} : subrelation (≡_{σ}) (⇚_{σ}). *)
  (* Proof. solve_equiv. Qed. *)

  (* Global Instance fequiv_subrelation_fent : subrelation (≡) (⇛). *)
  (* Proof. solve_equiv. Qed. *)

  (* Global Instance fequiv_subrelation_flip_fent : subrelation (≡) (⇚). *)
  (* Proof. solve_equiv. Qed. *)

  (** [⇛] respects [⇛] in left and [⇚] in right *)
  Global Instance fent_st_proper_fent_st {σ} : Proper ((⇚_{σ}) ==> (⇛_{σ}) ==> impl) (⇛_{σ}).
  Proof. solve_equiv. Qed.

  Global Instance fent_proper_fent : Proper ((⇚) ==> (⇛) ==> impl) (⇛).
  Proof. solve_equiv. Qed.

  Global Instance fent_st_proper_fequiv_st {σ} : Proper ((≡_{σ}) ==> (≡_{σ}) ==> iff) (⇛_{σ}).
  Proof. solve_equiv. Qed.

  Global Instance fent_proper : Proper ((≡) ==> (≡) ==> iff) (⇛).
  Proof. solve_equiv. Qed.

  (** [feval σ] respects [⇛_{σ}] and [⇚_{σ}] *)
  Global Instance feval_proper_fent_st {σ} : Proper ((⇛_{σ}) ==> impl) (feval σ).
  Proof. solve_equiv. Qed.

  Global Instance feval_proper_flip_fent_st {σ} : Proper ((⇚_{σ}) ==> flip impl) (feval σ).
  Proof. solve_equiv. Qed.

  Global Instance feval_proper_st {σ} : Proper ((≡_{σ}) ==> iff) (feval σ).
  Proof. solve_equiv. Qed.

  Global Instance feval_proper_fent {σ} : Proper ((⇛) ==> impl) (feval σ).
  Proof. solve_equiv. Qed.

  Global Instance feval_proper_flip_fent {σ} : Proper ((⇚) ==> flip impl) (feval σ).
  Proof. solve_equiv. Qed.

  Global Instance feval_proper : Proper (eq ==> (≡) ==> iff) feval.
  Proof. solve_equiv. Qed.

  (** ** [formula] constructors respect [≡], [⇛], and the state-specific variants *)

  (** *** [FAtomic AT_Eq] *)

  Global Instance ATEq_proper_st {σ} : Proper ((≡ₜ_{σ}) ==> (≡ₜ_{σ}) ==> (≡_{σ})) AT_Eq.
  Proof. solve_equiv. Qed.

  Global Instance ATEq_proper : Proper ((≡ₜ) ==> (≡ₜ) ==> (≡)) AT_Eq.
  Proof. solve_equiv. Qed.

  (** *** [FNot] *)
  Global Instance FNot_proper_fent_st {σ} : Proper ((⇚_{σ}) ==> (⇛_{σ})) FNot.
  Proof. solve_equiv. Qed.

  Global Instance FNot_proper_st {σ} : Proper ((≡_{σ}) ==> (≡_{σ})) FNot.
  Proof. solve_equiv. Qed.

  Global Instance FNot_proper_fent : Proper ((⇚) ==> (⇛)) FNot.
  Proof. solve_equiv. Qed.

  Global Instance FNot_proper : Proper ((≡) ==> (≡)) FNot.
  Proof. solve_equiv. Qed.

  (** *** [FAnd] *)
  Global Instance FAnd_proper_fent_st {σ} :
    Proper ((⇛_{σ}) ==> (⇛_{σ}) ==> (⇛_{σ})) FAnd.
  Proof. solve_equiv. Qed.

  (* Global Instance FAnd_proper_flip_fent {σ} : *)
  (*   Proper ((⇚_{σ}) ==> (⇚_{σ}) ==> (⇚_{σ})) FAnd. *)
  (* Proof. solve_equiv. Qed. *)

  Global Instance FAnd_proper_st {σ} :
    Proper ((≡_{σ}) ==> (≡_{σ}) ==> (≡_{σ})) FAnd.
  Proof. solve_equiv. Qed.

  Global Instance FAnd_proper_fent :
    Proper ((⇛) ==> (⇛) ==> (⇛)) FAnd.
  Proof. solve_equiv. Qed.

  Global Instance FAnd_proper :
    Proper ((≡) ==> (≡) ==> (≡)) FAnd.
  Proof. solve_equiv. Qed.

  (** *** [FOr] *)
  Global Instance FOr_proper_fent_st {σ} :
    Proper ((⇛_{σ}) ==> (⇛_{σ}) ==> (⇛_{σ})) FOr.
  Proof. solve_equiv. Qed.

  (* Global Instance FOr_proper_flip_fent {σ} : *)
  (*   Proper ((⇚_{σ}) ==> (⇚_{σ}) ==> (⇚_{σ})) FOr. *)
  (* Proof. solve_equiv. Qed. *)

  Global Instance FOr_proper_st {σ} :
    Proper ((≡_{σ}) ==> (≡_{σ}) ==> (≡_{σ})) FOr.
  Proof. solve_equiv. Qed.

  Global Instance FOr_proper_fent :
    Proper ((⇛) ==> (⇛) ==> (⇛)) FOr.
  Proof. solve_equiv. Qed.

  Global Instance FOr_proper :
    Proper ((≡) ==> (≡) ==> (≡)) FOr.
  Proof. solve_equiv. Qed.

  (** *** [FImpl] *)
  Global Instance FImpl_proper_fent_st {σ} :
    Proper ((⇚_{σ}) ==> (⇛_{σ}) ==> (⇛_{σ})) FImpl.
  Proof. solve_equiv. Qed.

  (* Global Instance FImpl_proper_flip_fent {σ} : *)
  (*   Proper ((⇚_{σ}) ==> (⇚_{σ}) ==> (⇚_{σ})) FImpl. *)
  (* Proof. solve_equiv. Qed. *)

  Global Instance FImpl_proper_st {σ} :
    Proper ((≡_{σ}) ==> (≡_{σ}) ==> (≡_{σ})) FImpl.
  Proof. solve_equiv. Qed.

  Global Instance FImpl_proper_fent :
    Proper ((⇚) ==> (⇛) ==> (⇛)) FImpl.
  Proof. solve_equiv. Qed.

  Global Instance FImpl_proper :
    Proper ((≡) ==> (≡) ==> (≡)) FImpl.
  Proof. solve_equiv. Qed.

  (** *** [FIff] *)
  Global Instance FIff_proper_st {σ} :
    Proper ((≡_{σ}) ==> (≡_{σ}) ==> (≡_{σ})) FIff.
  Proof. solve_equiv. Qed.

  Global Instance FIff_proper :
    Proper ((≡) ==> (≡) ==> (≡)) FIff.
  Proof. solve_equiv. Qed.

End equiv.

Infix "≡_{ σ }" := (fequiv_st σ) (at level 70, no associativity) : refiney_scope.
Infix "≡_{ σ }@{ M }" := (@fequiv_st M σ) (at level 70, only parsing, no associativity)
    : refiney_scope.
Notation "(≡_{ σ } )" := (fequiv_st σ) (only parsing, no associativity) : refiney_scope.
Notation "(≡_{ σ }@{ M } )" := (@fequiv_st M σ) (only parsing, no associativity) : refiney_scope.

Infix "⇛_{ σ }" := (fent_st σ) (at level 70, no associativity) : refiney_scope.
Infix "⇛_{ σ }@{ M }" := (@fent_st M σ) (at level 70, only parsing, no associativity)
    : refiney_scope.
Notation "(⇛_{ σ } )" := (fent_st σ) (only parsing, no associativity) : refiney_scope.
Notation "(⇛_{ σ }@{ M } )" := (@fent_st M σ) (only parsing, no associativity) : refiney_scope.

Infix "≡ₜ_{ σ }" := (tequiv_st σ) (at level 70, no associativity) : refiney_scope.
Infix "≡ₜ_{ σ }@{ M }" := (@tequiv_st M σ) (at level 70, only parsing, no associativity)
    : refiney_scope.
Notation "(≡ₜ_{ σ } )" := (tequiv_st σ) (only parsing, no associativity) : refiney_scope.
Notation "(≡ₜ_{ σ }@{ M } )" := (@tequiv_st M σ) (only parsing, no associativity) : refiney_scope.

Infix "≡ₗ@{ M }" := (@equiv (formula M) _) (at level 70, only parsing, no associativity)
    : refiney_scope.
Notation "(≡ₗ@{ M } )" := ((≡@{formula M})) (only parsing) : refiney_scope.
Infix "⇛" := fent (at level 70, no associativity) : refiney_scope.
Notation "(⇛)" := fent (only parsing) : refiney_scope.
Notation "(⇛ₗ@{ M } )" := (@fent M) (only parsing) : refiney_scope.
Infix "⇚" := (flip fent) (at level 70, no associativity) : refiney_scope.
Notation "(⇚)" := (flip fent) (only parsing) : refiney_scope.
Notation "(⇚ₗ@{ M } )" := (flip (@fent M)) (only parsing) : refiney_scope.

Global Hint Extern 0 (?A ⇛ ?A) => reflexivity : core.
Global Hint Extern 0 (?A ⇛_{_} ?A) => reflexivity : core.

Section lemmas.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).
  Local Notation state := (state M).

  Implicit Types A B C : formula.
  Implicit Types t : term.
  Implicit Types σ : state.

  Lemma f_ent_contrapositive A B :
    <! ¬ B !> ⇛ <! ¬ A !> ↔ <! A !> ⇛ <! B !>.
  Proof with auto.
    split; intros.
    - intros σ. specialize (H σ). simp feval in H. intros. pose proof (feval_lem σ B) as []...
      apply H in H1. contradiction.
    - rewrite H...
  Qed.

  Lemma f_ent_reverse_direction A B :
    <! A !> ⇚ <! B !> ↔ <! ¬ A !> ⇛ <! ¬ B !>.
  Proof with auto.
    unfold flip. rewrite f_ent_contrapositive...
  Qed.

End lemmas.
