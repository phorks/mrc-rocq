From Equations Require Import Equations.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From stdpp Require Import base list_monad.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.SemanticFacts.

(* TODO: move it *)
Definition of_same_length_rest {A B} {x1 : A} {l1 : list A} {x2 : B} {l2 : list B}
                              (H : OfSameLength (x1::l1) (x2::l2)) : OfSameLength l1 l2.
Proof. unfold OfSameLength in *. simpl in H. lia. Defined.

Instance of_same_length_rev {A B} {l1 : list A} {l2 : list B}
                              `{OfSameLength _ _ l1 l2} : OfSameLength (rev l1) (rev l2).
Proof. unfold OfSameLength in *. do 2 rewrite length_rev. assumption. Defined.

Definition of_same_length_rect {A B X Y} (f_nil : X → Y) (f_cons : (X → Y) → A → B → X → Y)
  (x : X)
  (l1 : list A) (l2 : list B)
  `{OfSameLength _ _ l1 l2} : Y.
Proof.
  generalize dependent x. generalize dependent l2.
  induction l1 as [|x1 l1' rec], l2 as [|x2 l2']; intros H.
  - exact f_nil.
  - inversion H.
  - inversion H.
  - apply of_same_length_rest in H. specialize (rec _ H). exact (f_cons rec x1 x2).
Defined.

Open Scope refiney_scope.

Section sequential_subst.
  Context {M : model}.

  Local Notation value := (value M).
  Local Notation term := (term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A : formula.
  Implicit Types xs : list variable.
  Implicit Types ts : list term.
  Implicit Types vs : list value.

  Definition seq_subst A xs ts `{OfSameLength _ _ xs ts} : formula :=
    of_same_length_rect (λ A, A) (λ rec x t B, <! $(rec B)[x \ t] !>) A xs ts.

  Definition teval_var_term_list σ xs vs :=
    OfSameLength xs vs ∧ Forall2 (λ x v, teval σ x v) xs vs.

  Lemma teval_var_list_total σ xs :
    ∃ vs, teval_var_term_list σ xs vs.
  Proof with auto.
    induction xs as [|x xs IH].
    - exists []. split... apply of_same_length_nil.
    - destruct IH as [vs [H1 H2]]. pose proof (teval_total σ x) as [v Hv].
      exists (v :: vs). split... apply of_same_length_cons.
  Qed.

  Lemma simpl_feval_forall_list σ xs A :
    feval σ <! ∀* xs, A !> ↔
    ∀ vs (H : OfSameLength xs (TConst <$> vs)), feval σ (@seq_subst A xs (TConst <$> vs) H).
  Proof with auto.
    split.
    - intros H. generalize dependent σ. induction xs as [|x xs' IH]; simpl in *; intros.
      + inversion H0. symmetry in H2. rewrite length_zero_iff_nil in H2.
        apply fmap_nil_inv in H2. subst...
      + inversion H0. symmetry in H2. apply length_nonzero_iff_cons in H2 as (t&ts'&?&?).
        destruct vs; [discriminate|]. rewrite fmap_cons in H1. inversion H1.
        subst. simpl. rewrite simpl_feval_fforall in H. specialize (H v).
        rewrite feval_subst with (v:=v) in H... rewrite feval_subst with (v:=v)...
    - intros H. generalize dependent σ. induction xs as [|x xs' IH]; simpl in *; intros.
      + specialize (H [] (of_same_length_nil)). simpl in H...
      + rewrite simpl_feval_fforall. intros. rewrite feval_subst with (v:=v)...
        apply IH. intros.
        apply @of_same_length_cons with (x1:=x) (x2:=TConst v) in H0 as ?.
        rewrite <- fmap_cons in H1. specialize (H (v :: vs) H1).
        simpl in H. rewrite feval_subst with (v:=v) in H... unfold fmap.
        assert ((@of_same_length_rest variable term x xs' (@TConst value v)
            (list_fmap value term (@TConst value) vs) H1) = H0) as <-...
        apply eq_pi. solve_decision.
  Qed.

  (* Fixpoint seq_subst' A xs ts : formula := *)
  (*   match xs, ts with *)
  (*   | [], [] => A *)
  (*   | x::xs, t::ts => let rest := seq_subst' A xs ts in <! rest[x \ t] !> *)
  (*   | _, _ => <! false !> *)
  (*   end. *)
  (* Fixpoint seq_subst'' A xs ts : formula := *)
  (*   match xs, ts with *)
  (*   | [], [] => A *)
  (*   | x::xs, t::ts => seq_subst'' <! A[x \ t] !> xs ts *)
  (*   | _, _ => <! false !> *)
  (*   end. *)
  (* Axiom A : formula. *)
  (* Axiom x1 : variable. *)
  (* Axiom x2 : variable. *)
  (* Axiom x3 : variable. *)
  (* Axiom t1 : term. *)
  (* Axiom t2 : term. *)
  (* Axiom t3 : term. *)
  (* Axiom xs : list variable. *)
  (* Axiom ts : list term. *)

  (* Eval simpl in (seq_subst A [x1; x2; x3] [t1; t2; t3]). *)

  (* Lemma xxx : (seq_subst A [x1; x2; x3] [t1; t2; t3]) = A. *)
  (* Proof. *)
  (*   unfold seq_subst. simpl. *)

  (*   match xs, ts with *)
  (*   | [], [] => A *)
  (*   | x::xs, t::ts => *)

  (* Implicit Types x y : variable. *)
  (* Implicit Types t : term. *)
  (* Implicit Types af : atomic_formula. *)
  (* Implicit Types A : formula. *)
  (* Implicit Types m : gmap variable term. *)
  (* Implicit Types mv : gmap variable value. *)
