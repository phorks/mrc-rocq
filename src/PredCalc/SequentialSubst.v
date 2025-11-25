From Equations Require Import Equations.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From stdpp Require Import base list_monad sets.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import SeqNotation.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.EquivLemmas.

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


  (** Expanding teval_total to a list of terms **)
  (* Definition teval_var_term_list σ xs vs := *)
  (*   OfSameLength xs vs ∧ Forall2 (λ x v, teval σ x v) xs vs. *)

  (* Lemma teval_var_list_total σ xs : *)
  (*   ∃ vs, teval_var_term_list σ xs vs. *)
  (* Proof with auto. *)
  (*   induction xs as [|x xs IH]. *)
  (*   - exists []. split... apply of_same_length_nil. *)
  (*   - destruct IH as [vs [H1 H2]]. pose proof (teval_total σ x) as [v Hv]. *)
  (*     exists (v :: vs). split... apply of_same_length_cons. *)
  (* Qed. *)

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


  (** Expanding equality atomic formulas to list of  **)

  Lemma term_list_eq_cons t1 t2 ts1 ts2
    {H1 : OfSameLength ts1 ts2}
    {H2 : OfSameLength (t1 :: ts1) (t2 :: ts2)} :
    AT_TermListEq (t1 :: ts1) (t2 :: ts2) ≡ <! ⌜t1 = t2⌝ ∧ $(AT_TermListEq ts1 ts2) !>.
  Proof. unfold AT_TermListEq. simpl. f_equiv. f_equiv. apply eq_pi. solve_decision. Qed.

  (* Lemma f_forall_list_unused x A : *)
  (*   x  *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∀ x, A !> ≡ A. *)
  (* Proof with auto. *)
  (*   unfold FForall. intros. rewrite fexists_unused... intros σ. *)
  (*   simp feval. rewrite feval_stable... *)
  (* Qed. *)

  (* A.65 *)
  Lemma f_forall_list_and xs A B :
    <! ∀* xs, A ∧ B !> ≡ <! (∀* xs, A) ∧ (∀* xs, B) !>.
  Proof with auto.
    induction xs... simpl. rewrite <- f_forall_and. rewrite IHxs...
  Qed.

  (* A.78 *)
  Lemma f_forall_list_impl_unused_l xs A B :
    list_to_set xs ∩ formula_fvars A = ∅ →
    <! ∀* xs, A ⇒ B !> ≡ <! A ⇒ (∀* xs, B) !>.
  Proof with auto.
    intros. induction xs as [|x xs IH]... simpl. rewrite IH; [rewrite f_forall_impl_unused_l|];
      set_solver.
  Qed.

  Lemma f_forall_list_one_point xs ts A `{OfSameLength _ _ xs ts} :
    NoDup xs →
    (list_to_set xs) ∩ ⋃ (term_fvars <$> ts) = ∅ →
    <! ∀* xs, $(AT_TermListEq (TVar <$> xs) ts) ⇒ A !> ≡ seq_subst A xs ts.
  Proof with auto.
    intros Hnodup Hfree. generalize dependent ts.
    induction xs as [|x xs' IH]; simpl in *; intros.
    - inversion H. symmetry in H1. rewrite length_zero_iff_nil in H1. subst.
      unfold AT_TermListEq. simpl. rewrite f_true_implies...
    - inversion H. symmetry in H1. apply length_nonzero_iff_cons in H1 as (t&ts'&?&?).
      subst ts. rename ts' into ts. rewrite term_list_eq_cons.
      apply NoDup_cons in Hnodup as []. rewrite <- IH by set_solver.
      rewrite <- f_impl_curry. rewrite f_forall_list_impl_unused_l by set_solver.
      rewrite f_forall_one_point by set_solver. f_equiv...
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
