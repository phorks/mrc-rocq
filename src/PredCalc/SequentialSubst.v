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

(* TODO: move it *)
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

  (** Equivalene of lists of terms **)
  Global Instance term_list_equiv : Equiv (list term) :=
    λ ts1 ts2, length ts1 = length ts2 ∧ Forall2 (≡@{term}) ts1 ts2.

  Global Instance term_list_equiv_refl : Reflexive term_list_equiv.
  Proof with auto.
    intros ts. induction ts; hnf... split... apply Forall2_cons. split... apply IHts.
  Qed.

  Global Instance term_list_equiv_sym : Symmetric term_list_equiv.
  Proof with auto.
    intros ts1. induction ts1 as [|t1 ts1 IH]; intros ts2 [H1 H2]; hnf.
    - simpl in H1. symmetry in H1. apply length_zero_iff_nil in H1. subst ts2...
    - simpl in H1. symmetry in H1. apply length_nonzero_iff_cons in H1 as (t2&ts2'&?&?).
      subst ts2. rename ts2' into ts2. split.
      + do 2 rewrite length_cons...
      + apply Forall2_cons. apply Forall2_cons in H2 as []. split... apply IH.
        split...
  Qed.

  Global Instance term_list_equiv_trans : Transitive term_list_equiv.
  Proof with auto.
    intros ts1. induction ts1 as [|t1 ts1 IH]; intros ts2 ts3 [] [].
    - simpl in H. rewrite <- H in H1. symmetry in H, H1.
      apply length_zero_iff_nil in H, H1. subst. split...
    - simpl in H. rewrite <- H in H1. symmetry in H, H1.
      apply length_nonzero_iff_cons in H as (t2&ts2'&?&?). subst ts2. rename ts2' into ts2.
      apply length_nonzero_iff_cons in H1 as (t3&ts3'&?&?). subst ts3. rename ts3' into ts3.
      split.
      + do 2 rewrite length_cons...
      + rewrite Forall2_cons in *. destruct H0 as [], H2 as []. split.
        * trans t2...
        * forward (IH ts2 ts3) by (split; auto). forward IH by (split; auto; lia).
          apply IH.
  Qed.

  Global Instance term_list_equiv_equiv : Equivalence term_list_equiv.
  Proof.
    split; [exact term_list_equiv_refl | exact term_list_equiv_sym |
             exact term_list_equiv_trans].
  Qed.

  Global Instance cons_proper_term_list_equiv :
    Proper ((≡@{term}) ==> term_list_equiv ==> term_list_equiv) cons.
  Proof.
    intros t1 t2 Ht ts1 ts2 Hts. unfold term_list_equiv in *.
    do 2 rewrite length_cons. rewrite Forall2_cons. naive_solver.
  Qed.

  Lemma term_list_equiv_cons_l t1 ts1 ts2 :
    t1 :: ts1 ≡ ts2 ↔ ∃ t2 ts2', ts2 = t2 :: ts2' ∧ t1 ≡ t2 ∧ ts1 ≡ ts2'.
  Proof with auto.
    split.
    - intros []. symmetry in H. rewrite length_cons in H.
      apply length_nonzero_iff_cons in H as (t2&ts2'&?&?). subst ts2. rename ts2' into ts2.
      exists t2, ts2. apply Forall2_cons in H0 as []. split_and!... split...
    - intros (t2&ts2'&?&?&?). rewrite H. apply cons_proper_term_list_equiv...
  Qed.

  Lemma term_list_equiv_cons_r ts1 t2 ts2 :
    ts1 ≡ t2 :: ts2 ↔ ∃ t1 ts1', ts1 = t1 :: ts1' ∧ t1 ≡ t2 ∧ ts1' ≡ ts2.
  Proof with auto.
    split.
    - intros. symmetry in H. apply term_list_equiv_cons_l in H as (t1&ts1'&?&?&?).
      exists t1, ts1'. split_and!...
    - intros (t1&ts1'&?&?&?). rewrite H. apply cons_proper_term_list_equiv...
  Qed.

  Lemma term_list_equiv_nil_l ts :
    [] ≡ ts ↔ ts = [].
  Proof with auto.
    unfold equiv, term_list_equiv. simpl. split.
    - intros []. symmetry in H. apply length_zero_iff_nil in H. subst...
    - intros ->. simpl...
  Qed.

  Lemma term_list_equiv_nil_r ts :
    ts ≡ [] ↔ ts = [].
  Proof with auto.
    unfold equiv, term_list_equiv. simpl. split.
    - intros []. apply length_zero_iff_nil in H. subst...
    - intros ->. simpl...
  Qed.

  Global Instance app_proper_term_list_equiv :
    Proper ((term_list_equiv) ==> term_list_equiv ==> term_list_equiv) app.
  Proof with auto.
    intros ts1 ts3 H13 ts2 ts4 H24. generalize dependent ts3.
    induction ts1 as [|t1 ts1 IH]; intros ts3 H13.
    - simpl. apply term_list_equiv_nil_l in H13. subst. simpl...
    - simpl. apply term_list_equiv_cons_l in H13 as (t3&ts3'&->&?&?). rename ts3' into ts3.
      simpl. f_equiv...
  Qed.

  Lemma term_list_equiv_cons_inv t1 ts1 t2 ts2 :
    t1 :: ts1 ≡ t2 :: ts2 → t1 ≡ t2 ∧ ts1 ≡ ts2.
  Proof with auto.
    intros []. do 2 rewrite length_cons in H. apply Forall2_cons in H0 as [].
    split... split...
  Qed.

  (** Sequential substitution **)
  Definition seq_subst A xs ts `{OfSameLength _ _ xs ts} : formula :=
    of_same_length_rect (λ A, A) (λ rec x t B, <! $(rec B)[x \ t] !>) A xs ts.

  Local Notation "A [; xs \ ts ;]" := (seq_subst A xs ts)
                              (in custom formula at level 74, left associativity,
                                xs custom seq_notation,
                                ts custom term_seq_notation) : refiney_scope.

  Lemma seq_subst_cons A x t xs ts
    {Hl1 : OfSameLength xs ts} {Hl2 : OfSameLength (x :: xs) (t :: ts)} :
    @seq_subst A (x :: xs) (t :: ts) Hl2 ≡ <! $(@seq_subst A xs ts Hl1)[x \ t] !>.
  Proof with auto.
    unfold seq_subst. simpl. f_equiv. f_equiv. apply eq_pi. solve_decision.
  Qed.

  Lemma seq_subst_app A xs1 ts1 xs2 ts2
    {Hl1 :OfSameLength xs1 ts1}
    {Hl2 : OfSameLength xs2 ts2}
    {Hl3 : OfSameLength (xs1 ++ xs2) (ts1 ++ ts2)} :
    @seq_subst A (xs1 ++ xs2) (ts1 ++ ts2) Hl3 ≡
    @seq_subst (@seq_subst A xs2 ts2 Hl2) xs1 ts1 Hl1.
  Proof with auto.
    generalize dependent ts1. generalize dependent xs2. generalize dependent ts2.
    induction xs1; intros.
    - inversion Hl1. symmetry in H0. apply length_zero_iff_nil in H0. subst.
      simpl. f_equiv. apply eq_pi. solve_decision.
    - inversion Hl1. symmetry in H0. apply length_nonzero_iff_cons in H0 as (t1&ts1'&?&?).
      subst ts1. rename ts1' into ts1. simpl. intros σ.
      pose proof (teval_total σ t1) as [v1 Hv1]. rewrite feval_subst with (v:=v1)...
      rewrite feval_subst with (v:=v1)... specialize (IHxs1 ts2 xs2).
      assert (OfSameLength xs2 ts2).
      { unfold OfSameLength. unfold OfSameLength in Hl3. simpl in Hl3.
        do 2 rewrite length_app in Hl3. rewrite H0 in Hl3. lia. }
      assert (OfSameLength xs1 ts1) by (symmetry in H0; apply H0).
      assert (OfSameLength (xs1 ++ xs2) (ts1 ++ ts2)).
      { apply of_same_length_app. }
      specialize (IHxs1 H ts1 H1 H2 (<[a:=v1]> σ)).
      eapply eq_rect.
      + symmetry. eapply eq_rect.
        * symmetry. exact IHxs1.
        * f_equiv. f_equiv. apply eq_pi. solve_decision.
      + f_equiv. f_equal.
        * f_equiv. apply eq_pi. solve_decision.
        * apply eq_pi. solve_decision.
  Qed.

  Lemma seq_subst_snoc A x t xs ts
    {Hl1 : OfSameLength xs ts}
    {Hl2 : OfSameLength (xs ++ [x]) (ts ++ [t])} :
    @seq_subst A (xs ++ [x]) (ts ++ [t]) Hl2 ≡ @seq_subst (<! A [x \ t] !>) xs ts Hl1.
  Proof with auto.
    simpl. rewrite (seq_subst_app A xs ts [x] [t]). f_equiv.
  Qed.

  (**  [seq_subst] respects [fequiv] and [fent] when [ts] are equivalent under
       [term_list_equiv].
       The important part about the following instances is that they discard [OfSameLength]
       instances. This can be done since equality proofs are proof irrelevant *)
  Global Instance seq_subst_proper : Proper ((≡@{formula}) ==>
        respectful_hetero (list variable) (list variable)
        (λ xs, ∀ ts, OfSameLength xs ts → formula)
        (λ xs, ∀ ts, OfSameLength xs ts → formula)
        (=)
        (λ xs xs', (respectful_hetero (list term) (list term)
                      (λ ts, OfSameLength xs ts → formula)
                      (λ ts, OfSameLength xs' ts → formula)
                      (term_list_equiv)
                      (λ ts ts', (respectful_hetero (OfSameLength xs ts) (OfSameLength xs' ts')
                                    (λ _, formula)
                                    (λ _, formula)
                                    (λ _ _, True)
                                    (λ _ _, (≡@{formula}))))))) seq_subst.
  Proof with auto.
    intros A B Hequiv xs ? <- ts1 ts2 Hts Hl1 Hl2 _.
    generalize dependent ts2. generalize dependent ts1.
    induction xs as [|x xs IH]; intros.
    - inversion Hl1. inversion Hl2. symmetry in H0, H1. apply length_zero_iff_nil in H0, H1.
      subst. simpl...
    - inversion Hl1. inversion Hl2. symmetry in H0, H1.
      apply length_nonzero_iff_cons in H0 as (t1&ts1'&?&?). subst ts1. rename ts1' into ts1.
      apply length_nonzero_iff_cons in H1 as (t2&ts2'&?&?). subst ts2. rename ts2' into ts2.
      apply of_same_length_rest in Hl1 as Hl1'. apply of_same_length_rest in Hl2 as Hl2'.
      do 2 rewrite seq_subst_cons. apply term_list_equiv_cons_inv in Hts as [].
       f_equiv...
      Unshelve.
      + exact Hl1'.
      + exact Hl2'.
  Qed.

  Global Instance seq_subst_proper_fent : Proper ((⇛@{M}) ==>
        respectful_hetero (list variable) (list variable)
        (λ xs, ∀ ts, OfSameLength xs ts → formula)
        (λ xs, ∀ ts, OfSameLength xs ts → formula)
        (=)
        (λ xs xs', (respectful_hetero (list term) (list term)
                      (λ ts, OfSameLength xs ts → formula)
                      (λ ts, OfSameLength xs' ts → formula)
                      (term_list_equiv)
                      (λ ts ts', (respectful_hetero (OfSameLength xs ts) (OfSameLength xs' ts')
                                    (λ _, formula)
                                    (λ _, formula)
                                    (λ _ _, True)
                                    (λ _ _, (⇛@{M}))))))) seq_subst.
  Proof with auto.
    intros A B Hequiv xs ? <- ts1 ts2 Hts Hl1 Hl2 _.
    generalize dependent ts2. generalize dependent ts1.
    induction xs as [|x xs IH]; intros.
    - inversion Hl1. inversion Hl2. symmetry in H0, H1. apply length_zero_iff_nil in H0, H1.
      subst. simpl...
    - inversion Hl1. inversion Hl2. symmetry in H0, H1.
      apply length_nonzero_iff_cons in H0 as (t1&ts1'&?&?). subst ts1. rename ts1' into ts1.
      apply length_nonzero_iff_cons in H1 as (t2&ts2'&?&?). subst ts2. rename ts2' into ts2.
      apply of_same_length_rest in Hl1 as Hl1'. apply of_same_length_rest in Hl2 as Hl2'.
      do 2 rewrite seq_subst_cons. apply term_list_equiv_cons_inv in Hts as [].
       f_equiv...
      Unshelve.
      + exact Hl1'.
      + exact Hl2'.
  Qed.

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

  Definition AT_TermListEq ts1 ts2 `{OfSameLength _ _ ts1 ts2} : formula :=
    of_same_length_rect (λ A, A) (λ rec t1 t2 B, <! ⌜t1 = t2⌝ ∧ $(rec B) !>) <! true !> ts1 ts2.

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

  Lemma fvars_forall_list xs A :
    formula_fvars <! ∀* xs, A !> = formula_fvars A ∖ list_to_set xs.
  Proof with auto. induction xs; simpl; set_solver. Qed.

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
