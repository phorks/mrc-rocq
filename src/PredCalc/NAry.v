From Equations Require Import Equations.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From stdpp Require Import base list_monad sets gmap.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import SeqNotation.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SyntacticFacts.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.EquivLemmas.

Section syntactic.
  Context {value : Type}.
  Local Notation term := (term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A B : formula.
  Implicit Types Bs : list formula.
  Implicit Types xs : list variable.
  Implicit Types ts : list term.
  Implicit Types vs : list value.

  Fixpoint FAndList Bs :=
    match Bs with
    | [] => <! true !>
    | A :: Bs => <! A ∧ $(FAndList Bs) !>
    end.

  Fixpoint FOrList Bs :=
    match Bs with
    | [] => <! false !>
    | A :: Bs => <! A ∨ $(FOrList Bs) !>
    end.

  Fixpoint FExistsList xs A :=
    match xs with
    | [] => A
    | x :: xs => <! ∃ x, $(FExistsList xs A) !>
    end.

  Fixpoint FForallList xs A :=
    match xs with
    | [] => A
    | x :: xs => <! ∀ x, $(FForallList xs A) !>
    end.

  Definition FEqList ts1 ts2 `{OfSameLength _ _ ts1 ts2} : formula :=
    FAndList (zip_with (λ t1 t2, <! ⌜t1 = t2⌝ !>) ts1 ts2).

  Definition seq_subst A xs ts `{OfSameLength _ _ xs ts} : formula :=
    of_same_length_rect (λ A, A) (λ rec x t B, <! $(rec B)[x \ t] !>) A xs ts.

  Definition subst_initials A (w : list final_variable) : formula :=
    seq_subst A (initial_var_of <$> w) (TVar ∘ as_var <$> w).

  Lemma fvars_and_list Bs :
    formula_fvars (FAndList Bs) = ⋃ (formula_fvars <$> Bs).
  Proof. induction Bs; simpl; set_solver. Qed.

  Lemma fvars_or_list Bs :
    formula_fvars (FOrList Bs) = ⋃ (formula_fvars <$> Bs).
  Proof. induction Bs; simpl; set_solver. Qed.

  Lemma fvars_exists_list xs A :
    formula_fvars (FExistsList xs A) = formula_fvars A ∖ list_to_set xs.
  Proof with auto. induction xs; simpl; set_solver. Qed.

  Lemma fvars_forall_list xs A :
    formula_fvars (FForallList xs A) = formula_fvars A ∖ list_to_set xs.
  Proof with auto. induction xs; simpl; set_solver. Qed.

  Lemma fvars_seq_subst_superset A xs ts `{OfSameLength _ _ xs ts} :
    formula_fvars (seq_subst A xs ts) ⊆ formula_fvars A ∪ ⋃ (term_fvars <$> ts).
  Proof.
    generalize dependent ts. induction xs as [|x xs IH]; intros ts Hl.
    - unfold OfSameLength in Hl. assert (Hl':=Hl). symmetry in Hl'. simpl in Hl'.
      apply length_zero_iff_nil in Hl'. subst. simpl. set_solver.
    - unfold OfSameLength in Hl. assert (Hl':=Hl). symmetry in Hl'. simpl in Hl'.
      apply length_nonzero_iff_cons in Hl' as (t&ts'&->&?). rename ts' into ts.
      simpl.
      pose proof (fvars_subst_superset <! $(@seq_subst A xs ts (of_same_length_rest Hl)) !> x t).
      set_solver.
  Qed.

  Definition subst_initials_var_fvars A (w : list final_variable) : gset variable :=
    ⋃ (map (λ x : final_variable,
             if decide (initial_var_of x ∈ formula_fvars A) then {[as_var x]} else ∅) w).

  Lemma elem_of_subst_initials_var_fvars A w x :
    (∃ x' : final_variable, x = as_var x' ∧ x' ∈ w ∧ initial_var_of x' ∈ formula_fvars A) ↔
    x ∈ subst_initials_var_fvars A w.
  Proof with auto.
    unfold subst_initials_var_fvars. split.
    - intros (x'&?&?&?). apply elem_of_union_list. exists {[x]}.
      split; [| set_solver]. subst. apply elem_of_list_fmap. exists x'. split...
      case_match... contradiction.
    - intros. apply elem_of_union_list in H as (x'&?&?).
      apply elem_of_list_fmap in H as (x''&?&?).
      destruct (decide (₀x'' ∈ formula_fvars A)); set_solver.
  Qed.

  Lemma not_elem_of_subst_initials_var_fvars_free A w x :
    (var_is_initial x = true ∨
       var_with_is_initial x true ∉ formula_fvars A ∨
       to_final_var x ∉ w) ↔
      x ∉ subst_initials_var_fvars A w.
  Proof with auto.
    split.
    - intros H contra. apply elem_of_subst_initials_var_fvars in contra as (x'&?&?).
      subst. destruct_or! H.
      + rewrite var_is_initial_as_var in H. discriminate.
      + subst. destruct H1 as []. rewrite initial_var_of_eq_var_with_is_initial in H1.
        contradiction.
      + destruct H1 as []. rewrite to_final_var_as_var in H. contradiction.
    - intros. destruct (decide (var_is_initial x = true))... right.
      destruct (decide (var_with_is_initial x true ∈ formula_fvars A))... right.
      destruct (decide (to_final_var x ∈ w))... exfalso. apply H.
      apply elem_of_subst_initials_var_fvars. exists (to_final_var x).
      split_and!...
      rewrite as_var_to_final_var. symmetry. apply var_with_is_initial_id.
      destruct (decide (var_is_initial x = false))... apply not_false_is_true in n0.
      contradiction.
  Qed.

  Lemma fvars_subst_initials A w :
    formula_fvars (subst_initials A w) = ((formula_fvars A ∖ (list_to_set (initial_var_of <$> w)))
                                             ∪ subst_initials_var_fvars A w).
  Proof with auto.
    induction w as [|x w IH].
    - cbn. set_solver.
    - unfold subst_initials. simpl. unfold subst_initials_var_fvars. simpl.
      (* Folding [subst_initials] and [subst_initials_var_fvars] back *)
      assert (
          (@seq_subst A (list_fmap final_variable variable initial_var_of w)
              (list_fmap final_variable term (@TVar value ∘ as_var) w)
              (@of_same_length_rest variable term ₀x (list_fmap final_variable variable initial_var_of w) x
                (list_fmap final_variable term (@TVar value ∘ as_var) w)
                (@of_same_length_fmap final_variable variable final_variable term
                    (x :: w) (x :: w) initial_var_of (@TVar value ∘ as_var)
                    (@of_same_length_id final_variable (x :: w))))) = subst_initials A w
        ).
      { unfold subst_initials. f_equal. apply eq_pi. solve_decision. }
      rewrite H. clear H.
      pose proof (@eq_refl _ (subst_initials_var_fvars A w)).
      unfold subst_initials_var_fvars at 2 in H. rewrite <- H. clear H.
      (* Actual proof steps *)
      destruct (decide (x ∈ w)).
      + rewrite fvars_subst_non_free.
        * rewrite IH. clear IH. destruct (decide (₀x ∈ formula_fvars A)).
          -- enough (as_var x ∈ subst_initials_var_fvars A w) by set_solver.
             apply elem_of_subst_initials_var_fvars. set_solver.
          -- set_solver.
        * rewrite IH. clear IH.
          enough (₀x ∉ subst_initials_var_fvars A w) by set_solver.
          destruct (decide (₀x ∈ subst_initials_var_fvars A w))...
          apply elem_of_subst_initials_var_fvars in e0. set_solver.
      + destruct (decide (₀x ∈ formula_fvars A)).
        * rewrite fvars_subst_free.
          -- rewrite IH. clear IH.
             enough (₀x ∉ subst_initials_var_fvars A w) by set_solver.
             destruct (decide (₀x ∈ subst_initials_var_fvars A w))...
             apply elem_of_subst_initials_var_fvars in e0. set_solver.
          -- rewrite IH. clear IH. set_unfold. left. split... intros (x'&?&?).
             enough (x = x') as -> by contradiction. destruct x. destruct x'.
             inversion H. f_equal...
        * assert (₀x ∉ subst_initials_var_fvars A w).
          { destruct (decide (₀x ∈ subst_initials_var_fvars A w))...
             apply elem_of_subst_initials_var_fvars in e. set_solver. }
          rewrite fvars_subst_non_free; rewrite IH; clear IH; set_solver.
  Qed.

End syntactic.

Notation "ts =* us" := (FEqList ts us)
                      (in custom term_relation at level 60,
                          ts custom term at level 60,
                          us custom term at level 60,
                          no associativity) : refiney_scope.
Notation "∧* As" := (FAndList As) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "∧* As" := (FAndList As) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "∨* As" := (FOrList As) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "∃* xs , A" := (FExistsList xs A)
                          (in custom formula at level 99, only parsing)
    : refiney_scope.
Notation "∃* xs ● A" := (FExistsList xs A)
                          (in custom formula at level 99, only printing)
    : refiney_scope.
Notation "∀* xs , A" := (FForallList xs A)
                              (in custom formula at level 99, only parsing)
    :refiney_scope.
Notation "∀* xs ● A" := (FForallList xs A)
                              (in custom formula at level 99, only parsing)
    :refiney_scope.

Notation "A [; xs \ ts ;]" := (seq_subst A xs ts)
                                (in custom formula at level 74, left associativity,
                                    xs custom seq_notation,
                                    ts custom term_seq_notation) : refiney_scope.

Section semantic.
  Context {M : model}.

  Local Notation value := (value M).
  Local Notation term := (term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A B : formula.
  Implicit Types xs : list variable.
  Implicit Types ts : list term.
  Implicit Types Bs : list formula.
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

  Lemma term_list_equiv_teval_list ts1 ts2 :
    ts1 ≡ ts2 →
    ∀ σ vs, teval_list σ ts1 vs ↔ teval_list σ ts2 vs.
  Proof with auto.
    generalize dependent ts2. induction ts1 as [|t1 ts1 IH].
    - intros. apply term_list_equiv_nil_l in H. subst...
    - intros. apply term_list_equiv_cons_l in H as (t2&ts2'&->&?&?). rename ts2' into ts2.
      split; inversion 1.
      + constructor.
        * unfold equiv, tequiv in H. rewrite <- H...
        * apply IH...
      + constructor.
        * unfold equiv, tequiv in H. rewrite H...
        * apply IH with (ts2:=ts2)...
  Qed.

  (** Equivalence of lists of formulas **)
  Global Instance formula_list_equiv : Equiv (list formula) :=
    λ Bs1 Bs2, length Bs1 = length Bs2 ∧ Forall2 (≡@{formula}) Bs1 Bs2.

  Global Instance formula_list_equiv_refl : Reflexive formula_list_equiv.
  Proof with auto.
    intros Bs. induction Bs; hnf... split... apply Forall2_cons. split...
    apply IHBs.
  Qed.

  Global Instance formula_list_equiv_sym : Symmetric formula_list_equiv.
  Proof with auto.
    intros Bs1. induction Bs1 as [|B1 Bs1 IH]; intros Bs2 [H1 H2]; hnf.
    - simpl in H1. symmetry in H1. apply length_zero_iff_nil in H1. subst Bs2...
    - simpl in H1. symmetry in H1. apply length_nonzero_iff_cons in H1 as (B2&Bs2'&?&?).
      subst Bs2. rename Bs2' into Bs2. split.
      + do 2 rewrite length_cons...
      + apply Forall2_cons. apply Forall2_cons in H2 as []. split... apply IH.
        split...
  Qed.

  Global Instance formula_list_equiv_trans : Transitive formula_list_equiv.
  Proof with auto.
    intros Bs1. induction Bs1 as [|B1 Bs1 IH]; intros Bs2 Bs3 [] [].
    - simpl in H. rewrite <- H in H1. symmetry in H, H1.
      apply length_zero_iff_nil in H, H1. subst. split...
    - simpl in H. rewrite <- H in H1. symmetry in H, H1.
      apply length_nonzero_iff_cons in H as (B2&Bs2'&?&?). subst Bs2. rename Bs2' into Bs2.
      apply length_nonzero_iff_cons in H1 as (B3&Bs3'&?&?). subst Bs3. rename Bs3' into Bs3.
      split.
      + do 2 rewrite length_cons...
      + rewrite Forall2_cons in *. destruct H0 as [], H2 as []. split.
        * trans B2...
        * forward (IH Bs2 Bs3) by (split; auto). forward IH by (split; auto; lia).
          apply IH.
  Qed.

  Global Instance formula_list_equiv_equiv : Equivalence formula_list_equiv.
  Proof.
    split; [exact formula_list_equiv_refl | exact formula_list_equiv_sym |
             exact formula_list_equiv_trans].
  Qed.

  Global Instance cons_proper_formula_list_equiv :
    Proper ((≡@{formula}) ==> formula_list_equiv ==> formula_list_equiv) cons.
  Proof.
    intros B1 B2 Ht Bs1 Bs2 Hts. unfold formula_list_equiv in *.
    do 2 rewrite length_cons. rewrite Forall2_cons. naive_solver.
  Qed.

  Lemma formula_list_equiv_cons_l B1 Bs1 Bs2 :
    B1 :: Bs1 ≡ Bs2 ↔ ∃ B2 Bs2', Bs2 = B2 :: Bs2' ∧ B1 ≡ B2 ∧ Bs1 ≡ Bs2'.
  Proof with auto.
    split.
    - intros []. symmetry in H. rewrite length_cons in H.
      apply length_nonzero_iff_cons in H as (B2&Bs2'&?&?). subst Bs2. rename Bs2' into Bs2.
      exists B2, Bs2. apply Forall2_cons in H0 as []. split_and!... split...
    - intros (B2&Bs2'&?&?&?). rewrite H. apply cons_proper_formula_list_equiv...
  Qed.

  Lemma formula_list_equiv_cons_r Bs1 B2 Bs2 :
    Bs1 ≡ B2 :: Bs2 ↔ ∃ B1 Bs1', Bs1 = B1 :: Bs1' ∧ B1 ≡ B2 ∧ Bs1' ≡ Bs2.
  Proof with auto.
    split.
    - intros. symmetry in H. apply formula_list_equiv_cons_l in H as (B1&Bs1'&?&?&?).
      exists B1, Bs1'. split_and!...
    - intros (B1&Bs1'&?&?&?). rewrite H. apply cons_proper_formula_list_equiv...
  Qed.

  Lemma formula_list_equiv_nil_l Bs :
    [] ≡ Bs ↔ Bs = [].
  Proof with auto.
    unfold equiv, formula_list_equiv. simpl. split.
    - intros []. symmetry in H. apply length_zero_iff_nil in H. subst...
    - intros ->. simpl...
  Qed.

  Lemma formula_list_equiv_nil_r Bs :
    Bs ≡ [] ↔ Bs = [].
  Proof with auto.
    unfold equiv, formula_list_equiv. simpl. split.
    - intros []. apply length_zero_iff_nil in H. subst...
    - intros ->. simpl...
  Qed.

  Global Instance app_proper_formula_list_equiv :
    Proper ((formula_list_equiv) ==> formula_list_equiv ==> formula_list_equiv) app.
  Proof with auto.
    intros Bs1 ts3 H13 Bs2 ts4 H24. generalize dependent ts3.
    induction Bs1 as [|B1 Bs1 IH]; intros ts3 H13.
    - simpl. apply formula_list_equiv_nil_l in H13. subst. simpl...
    - simpl. apply formula_list_equiv_cons_l in H13 as (t3&ts3'&->&?&?). rename ts3' into ts3.
      simpl. f_equiv...
  Qed.

  Lemma formula_list_equiv_cons_inv B1 Bs1 B2 Bs2 :
    B1 :: Bs1 ≡ B2 :: Bs2 → B1 ≡ B2 ∧ Bs1 ≡ Bs2.
  Proof with auto.
    intros []. do 2 rewrite length_cons in H. apply Forall2_cons in H0 as [].
    split... split...
  Qed.

  (** Sequential substitution **)

  Lemma seq_subst_cons A x t xs ts
    {Hl1 : OfSameLength xs ts} {Hl2 : OfSameLength (x :: xs) (t :: ts)} :
    @seq_subst _ A (x :: xs) (t :: ts) Hl2 ≡ <! $(@seq_subst _ A xs ts Hl1)[x \ t] !>.
  Proof with auto.
    unfold seq_subst. simpl. f_equiv. f_equiv. apply eq_pi. solve_decision.
  Qed.

  Lemma seq_subst_app A xs1 ts1 xs2 ts2
    {Hl1 :OfSameLength xs1 ts1}
    {Hl2 : OfSameLength xs2 ts2}
    {Hl3 : OfSameLength (xs1 ++ xs2) (ts1 ++ ts2)} :
    @seq_subst _ A (xs1 ++ xs2) (ts1 ++ ts2) Hl3 ≡
    @seq_subst _ (@seq_subst _ A xs2 ts2 Hl2) xs1 ts1 Hl1.
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
    @seq_subst _ A (xs ++ [x]) (ts ++ [t]) Hl2 ≡ @seq_subst _ (<! A [x \ t] !>) xs ts Hl1.
  Proof with auto.
    simpl. rewrite (seq_subst_app A xs ts [x] [t]). f_equiv.
  Qed.

  (**  Proper Instances  **)

  Global Instance teval_list_proper : Proper ((=@{@state M}) ==> (term_list_equiv) ==> (=@{list value}) ==> (iff)) teval_list.
  Proof with auto.
    intros σ ? <- ts1 ts2 Hequiv vs ? <-. apply term_list_equiv_teval_list...
  Qed.

  Global Instance ATPred_proper : Proper ((=) ==> (term_list_equiv) ==> (≡@{formula}))
                                        AT_Pred.
  Proof with auto.
    intros psym ? <- ts1 ts2 Hequiv σ. simp feval. split; intros.
    - simpl in H. destruct H as (vargs&?&?). exists vargs. split... revert H.
      rewrite Hequiv...
    - simpl in H. destruct H as (vargs&?&?). exists vargs. split... revert H.
      rewrite <- Hequiv...
  Qed.

  Global Instance FAndList_proper :
    Proper ((formula_list_equiv) ==> (≡@{formula})) FAndList.
  Proof with auto.
    intros Bs1. induction Bs1 as [|B1 Bs1 IH].
    - intros. apply formula_list_equiv_nil_l in H. subst...
    - intros. apply formula_list_equiv_cons_l in H as (B2&Bs2&->&?&?). simpl.
      rewrite H. f_equiv. apply IH...
  Qed.

  Global Instance FOrList_proper :
    Proper ((formula_list_equiv) ==> (≡@{formula})) FAndList.
  Proof with auto.
    intros Bs1. induction Bs1 as [|B1 Bs1 IH].
    - intros. apply formula_list_equiv_nil_l in H. subst...
    - intros. apply formula_list_equiv_cons_l in H as (B2&Bs2&->&?&?). simpl.
      rewrite H. f_equiv. apply IH...
  Qed.

  Global Instance FEq_proper :
    Proper ((formula_list_equiv) ==> (≡@{formula})) FAndList.
  Proof with auto.
    intros Bs1. induction Bs1 as [|B1 Bs1 IH].
    - intros. apply formula_list_equiv_nil_l in H. subst...
    - intros. apply formula_list_equiv_cons_l in H as (B2&Bs2&->&?&?). simpl.
      rewrite H. f_equiv. apply IH...
  Qed.

  Global Instance FExistsList_proper :
    Proper ((=) ==> (≡@{formula}) ==> (≡@{formula})) FExistsList.
  Proof with auto.
    intros xs ? <- A B H. induction xs.
    - simpl. rewrite H...
    - simpl. rewrite IHxs...
  Qed.

  Global Instance FForallList_proper :
    Proper ((=) ==> (≡@{formula}) ==> (≡@{formula})) FForallList.
  Proof with auto.
    intros xs ? <- A B H. induction xs.
    - simpl. rewrite H...
    - simpl. rewrite IHxs...
  Qed.

  Global Instance FExistsList_proper_fent : Proper ((=) ==> (⇛) ==> (⇛@{M})) FExistsList.
  Proof with auto.
    intros xs ? <- A B H. induction xs.
    - simpl...
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  Global Instance FForallList_proper_fent : Proper ((=) ==> (⇛) ==> (⇛@{M})) FForallList.
  Proof with auto.
    intros xs ? <- A B H. induction xs.
    - simpl...
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  Global Instance FEqList_proper : Proper (
        respectful_hetero (list term) (list term)
        (λ ts1, ∀ ts2, OfSameLength ts1 ts2 → formula)
        (λ ts1, ∀ ts2, OfSameLength ts1 ts2 → formula)
        (term_list_equiv)
        (λ ts1 ts1', (respectful_hetero (list term) (list term)
                      (λ ts2, OfSameLength ts1 ts2 → formula)
                      (λ ts2, OfSameLength ts1' ts2 → formula)
                      (term_list_equiv)
                      (λ ts2 ts2', (respectful_hetero (OfSameLength ts1 ts2) (OfSameLength ts1' ts2')
                                    (λ _, formula)
                                    (λ _, formula)
                                    (λ _ _, True)
                                    (λ _ _, (≡@{formula}))))))) FEqList.
  Proof with auto.
    intros ts1 ts1' H1 ts2 ts2' H2 Hl1 Hl2 _.
    generalize dependent ts2'. generalize dependent ts2. generalize dependent ts1'.
    induction ts1 as [|t1 ts1 IH]; intros ts1' H1 ts2 Hl1 ts2' H2 Hl2.
    - apply term_list_equiv_nil_l in H1. subst. unfold FEqList. simpl...
    - apply term_list_equiv_cons_l in H1 as (t1'&ts1''&->&?&?). rename ts1'' into ts1'.
      assert (Hl1':=Hl1). assert (Hl2':=Hl2). unfold OfSameLength in Hl1', Hl2'.
      symmetry in Hl1', Hl2'. simpl in Hl1', Hl2'.
      apply length_nonzero_iff_cons in Hl1' as (t2&ts2''&->&?). rename ts2'' into ts2.
      apply length_nonzero_iff_cons in Hl2' as (t2'&ts2''&->&?). rename ts2'' into ts2'.
      apply term_list_equiv_cons_inv in H2 as [? ?].
      unfold FEqList. simpl. f_equiv.
      + apply (@ATEq_proper M)...
      + eapply IH...
        Unshelve.
        * eapply of_same_length_rest. exact Hl1.
        * eapply of_same_length_rest. exact Hl2.
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
End semantic.
