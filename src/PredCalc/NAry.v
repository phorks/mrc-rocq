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

  Definition seqsubst A xs ts `{OfSameLength _ _ xs ts} : formula :=
    of_same_length_rect id (λ rec x t B, <! $(rec B)[x \ t] !>) A xs ts.

  Definition subst_initials A (w : list final_variable) : formula :=
    seqsubst A (initial_var_of <$> w) (TVar ∘ as_var <$> w).

  Lemma fvars_andlist Bs :
    formula_fvars (FAndList Bs) = ⋃ (formula_fvars <$> Bs).
  Proof. induction Bs; simpl; set_solver. Qed.

  Lemma fvars_orlist Bs :
    formula_fvars (FOrList Bs) = ⋃ (formula_fvars <$> Bs).
  Proof. induction Bs; simpl; set_solver. Qed.

  Lemma fvars_existslist xs A :
    formula_fvars (FExistsList xs A) = formula_fvars A ∖ list_to_set xs.
  Proof with auto. induction xs; simpl; set_solver. Qed.

  Lemma fvars_foralllist xs A :
    formula_fvars (FForallList xs A) = formula_fvars A ∖ list_to_set xs.
  Proof with auto. induction xs; simpl; set_solver. Qed.

  Lemma fvars_seqsubst_superset A xs ts `{OfSameLength _ _ xs ts} :
    formula_fvars (seqsubst A xs ts) ⊆ formula_fvars A ∪ ⋃ (term_fvars <$> ts).
  Proof.
    generalize dependent ts. induction xs as [|x xs IH]; intros ts Hl.
    - assert (Hl':=Hl). apply of_same_length_nil_inv_l in Hl' as ->. set_solver.
    - assert (Hl':=Hl). apply of_same_length_cons_inv_l in Hl' as (t&ts'&->&?).
      rename ts' into ts. simpl.
      pose proof (fvars_subst_superset (@seqsubst A xs ts (of_same_length_rest Hl)) x t).
      set_solver.
  Qed.

  Lemma fvars_seqsubst_vars_not_free_in_terms_superset A xs ts `{OfSameLength _ _ xs ts} :
    (list_to_set xs) ∩ ⋃ (term_fvars <$> ts) = ∅ →
    formula_fvars (seqsubst A xs ts) ⊆ (formula_fvars A ∖ list_to_set xs) ∪ ⋃ (term_fvars <$> ts).
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros ts Hl H.
    - assert (Hl':=Hl). apply of_same_length_nil_inv_l in Hl' as ->. set_solver.
    - assert (Hl':=Hl). apply of_same_length_cons_inv_l in Hl' as (t&ts'&->&?).
      rename ts' into ts. simpl.
      destruct (decide (x ∈ formula_fvars (@seqsubst A xs ts (of_same_length_rest Hl)))).
      + rewrite fvars_subst_free... specialize (IH ts (of_same_length_rest Hl)).
        forward IH by set_solver. set_solver.
      + rewrite fvars_subst_non_free... specialize (IH ts (of_same_length_rest Hl)).
        forward IH by set_solver. set_solver.
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
          (@seqsubst A (list_fmap final_variable variable initial_var_of w)
              (list_fmap final_variable term (@TVar value ∘ as_var) w)
              (@of_same_length_rest variable term ₀x (list_fmap final_variable variable initial_var_of w) x
                (list_fmap final_variable term (@TVar value ∘ as_var) w)
                (@of_same_length_fmap final_variable variable final_variable term
                    (x :: w) (x :: w) initial_var_of (@TVar value ∘ as_var)
                    (@of_same_length_id final_variable (x :: w))))) = subst_initials A w
        ).
      { unfold subst_initials. f_equiv. apply OfSameLength_pi. }
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

  Lemma simpl_seqsubst_not A xs ts `{OfSameLength _ _ xs ts} :
    seqsubst <! ¬ A !> xs ts = <! ¬ $(seqsubst A xs ts) !>.
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros.
    - apply of_same_length_nil_inv_l in H as H'. subst. simpl...
    - apply of_same_length_cons_inv_l in H as H'. destruct H' as (t&ts'&->&?).
      rename ts' into ts. simpl. rewrite IH. rewrite simpl_subst_not...
  Qed.

  Lemma simpl_seqsubst_and A B xs ts `{OfSameLength _ _ xs ts} :
    seqsubst <! A ∧ B !> xs ts = <! $(seqsubst A xs ts) ∧ $(seqsubst B xs ts) !>.
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros.
    - apply of_same_length_nil_inv_l in H as H'. subst. simpl...
    - apply of_same_length_cons_inv_l in H as H'. destruct H' as (t&ts'&->&?).
      rename ts' into ts. simpl. rewrite IH. rewrite simpl_subst_and...
  Qed.

  Lemma simpl_seqsubst_or A B xs ts `{OfSameLength _ _ xs ts} :
    seqsubst <! A ∨ B !> xs ts = <! $(seqsubst A xs ts) ∨ $(seqsubst B xs ts) !>.
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros.
    - apply of_same_length_nil_inv_l in H as H'. subst. simpl...
    - apply of_same_length_cons_inv_l in H as H'. destruct H' as (t&ts'&->&?).
      rename ts' into ts. simpl. rewrite IH. rewrite simpl_subst_or...
  Qed.

  Lemma simpl_seqsubst_impl A B xs ts `{OfSameLength _ _ xs ts} :
    seqsubst <! A ⇒ B !> xs ts = <! $(seqsubst A xs ts) ⇒ $(seqsubst B xs ts) !>.
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros.
    - apply of_same_length_nil_inv_l in H as H'. subst. simpl...
    - apply of_same_length_cons_inv_l in H as H'. destruct H' as (t&ts'&->&?).
      rename ts' into ts. simpl. rewrite IH. rewrite simpl_subst_impl...
  Qed.

  Lemma simpl_seqsubst_iff A B xs ts `{OfSameLength _ _ xs ts} :
    seqsubst <! A ⇔ B !> xs ts = <! $(seqsubst A xs ts) ⇔ $(seqsubst B xs ts) !>.
  Proof with auto.
    generalize dependent ts. induction xs as [|x xs IH]; intros.
    - apply of_same_length_nil_inv_l in H as H'. subst. simpl...
    - apply of_same_length_cons_inv_l in H as H'. destruct H' as (t&ts'&->&?).
      rename ts' into ts. simpl. rewrite IH. rewrite simpl_subst_iff...
  Qed.

  Lemma simpl_subst_initials_not A (xs : list final_variable) :
    subst_initials <! ¬ A !> xs = <! ¬ $(subst_initials A xs) !>.
  Proof with auto.
    unfold subst_initials. apply simpl_seqsubst_not.
  Qed.

  Lemma simpl_subst_initials_and A B (xs : list final_variable) :
    subst_initials <! A ∧ B !> xs = <! $(subst_initials A xs) ∧ $(subst_initials B xs) !>.
  Proof with auto.
    unfold subst_initials. apply simpl_seqsubst_and.
  Qed.

  Lemma simpl_subst_initials_or A B (xs : list final_variable) :
    subst_initials <! A ∨ B !> xs = <! $(subst_initials A xs) ∨ $(subst_initials B xs) !>.
  Proof with auto.
    unfold subst_initials. apply simpl_seqsubst_or.
  Qed.

  Lemma simpl_subst_initials_impl A B (xs : list final_variable) :
    subst_initials <! A ⇒ B !> xs = <! $(subst_initials A xs) ⇒ $(subst_initials B xs) !>.
  Proof with auto.
    unfold subst_initials. apply simpl_seqsubst_impl.
  Qed.

  Lemma simpl_subst_initials_iff A B (xs : list final_variable) :
    subst_initials <! A ⇔ B !> xs = <! $(subst_initials A xs) ⇔ $(subst_initials B xs) !>.
  Proof with auto.
    unfold subst_initials. apply simpl_seqsubst_iff.
  Qed.

End syntactic.

Notation "ts =* us" := (FEqList ts us)
                      (in custom term_relation at level 60,
                          ts custom term at level 60,
                          us custom term at level 60,
                          no associativity) : refiney_scope.
Notation "@ x" := (TVar x)
                       (in custom term at level 0,
                           only parsing,
                           x constr at level 0) : refiney_scope.
Notation "@* xs" := (TVar <$> xs)
                       (in custom term at level 0,
                           xs constr at level 0) : refiney_scope.
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
                              (in custom formula at level 99, only printing)
    :refiney_scope.

Notation "A [; xs \ ts ;]" := (seqsubst A xs ts)
                                (in custom formula at level 74, left associativity,
                                    xs custom seq_notation,
                                    ts custom term_seq_notation) : refiney_scope.

Notation "A [_₀\ w ]" := (subst_initials A w)
                            (in custom formula at level 74, left associativity,
                                A custom formula,
                                w constr at level 200) : refiney_scope.

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

  Global Instance term_list_equiv_equivalence : Equivalence term_list_equiv.
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

  Lemma seqsubst_cons A x t xs ts
    {Hl1 : OfSameLength xs ts} {Hl2 : OfSameLength (x :: xs) (t :: ts)} :
    @seqsubst _ A (x :: xs) (t :: ts) Hl2 ≡ <! $(@seqsubst _ A xs ts Hl1)[x \ t] !>.
  Proof with auto.
    unfold seqsubst. simpl. f_equiv. f_equiv. apply OfSameLength_pi.
  Qed.

  Lemma seqsubst_app A xs1 ts1 xs2 ts2
    {Hl1 :OfSameLength xs1 ts1}
    {Hl2 : OfSameLength xs2 ts2}
    {Hl3 : OfSameLength (xs1 ++ xs2) (ts1 ++ ts2)} :
    @seqsubst _ A (xs1 ++ xs2) (ts1 ++ ts2) Hl3 ≡
    @seqsubst _ (@seqsubst _ A xs2 ts2 Hl2) xs1 ts1 Hl1.
  Proof with auto.
    generalize dependent ts1. generalize dependent xs2. generalize dependent ts2.
    induction xs1; intros.
    - inversion Hl1. symmetry in H0. apply length_zero_iff_nil in H0. subst.
      simpl. f_equiv. apply OfSameLength_pi.
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
        * f_equiv. f_equiv. apply OfSameLength_pi.
      + f_equiv. f_equal.
        * f_equiv. apply OfSameLength_pi.
        * apply OfSameLength_pi.
  Qed.

  Lemma seqsubst_snoc A x t xs ts
    {Hl1 : OfSameLength xs ts}
    {Hl2 : OfSameLength (xs ++ [x]) (ts ++ [t])} :
    @seqsubst _ A (xs ++ [x]) (ts ++ [t]) Hl2 ≡ @seqsubst _ (<! A [x \ t] !>) xs ts Hl1.
  Proof with auto.
    simpl. rewrite (seqsubst_app A xs ts [x] [t]). f_equiv.
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
    Proper ((formula_list_equiv) ==> (≡@{formula})) FOrList.
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

  Global Instance FExistsList_proper_fent : Proper ((=) ==> (⇛) ==> (⇛ₗ@{M})) FExistsList.
  Proof with auto.
    intros xs ? <- A B H. induction xs.
    - simpl...
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  Global Instance FForallList_proper_fent : Proper ((=) ==> (⇛) ==> (⇛ₗ@{M})) FForallList.
  Proof with auto.
    intros xs ? <- A B H. induction xs.
    - simpl...
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  (** Proper instances for eqlist and seqsubst:
      The first three instances are not registered as [Instance] because setoid rewrite is not
      able to automatically use them. It expects ts1 and ts1' be the same (it also expects
      ts2 and ts2' be the same in the case of eqlist). They must be manually used for rewriting.
      The second three instances are weaker versions of the first three that don't respect
      [term_list_equiv]. However, setoid rewrite will use them.
   **)

  Definition FEqList_proper_strong_manual : Proper (
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

  Definition seqsubst_proper_strong_manual : Proper ((≡@{formula}) ==>
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
                                    (λ _ _, (≡@{formula}))))))) seqsubst.
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
      do 2 rewrite seqsubst_cons. apply term_list_equiv_cons_inv in Hts as [].
       f_equiv...
      Unshelve.
      + exact Hl1'.
      + exact Hl2'.
  Qed.

  Definition seqsubst_proper_fent_strong_manual : Proper ((⇛ₗ@{M}) ==>
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
                                    (λ _ _, (⇛ₗ@{M}))))))) seqsubst.
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
      do 2 rewrite seqsubst_cons. apply term_list_equiv_cons_inv in Hts as [].
       f_equiv...
      Unshelve.
      + exact Hl1'.
      + exact Hl2'.
  Qed.

  (** The following three instances are weaker version of the last three.
      The don't allow replacing ts with ts' in cases like
      [<! A [; *xs, *ts ;] !> ≡ <! A [; *xs, *ts' ;] !>] even if we have
      [term_list_equiv ts ts']. From what I understood Rocq doesn't allow
      such replacements because there are two implicit [OfSameLength]
      instances hidden inside seqsubst that depend on ts and ts'.
      If this proves to be necessary, it might be a good idea to remove
      [OfSameLength] requirement from seqsubst and move it to lemmas and
      notation parsing.
   *)

  Global Instance FEqList_of_same_length_pi :
    Proper (forall_relation (λ ts1,
                forall_relation (λ ts2, respectful universal_relation (=)))) FEqList.
  Proof with auto.
    intros ts1 ts2 H1 H2 _. f_equiv. apply OfSameLength_pi.
  Qed.

  Global Instance seqsubst_proper : Proper ((≡@{formula}) ==>
            forall_relation
              (λ xs, forall_relation (λ ts, universal_relation ==> (≡@{formula}))))
           seqsubst.
  Proof with auto.
    intros A B Hequiv xs ts Hl1 Hl2 _. apply seqsubst_proper_strong_manual...
    reflexivity.
  Qed.

  Global Instance seqsubst_proper_fent : Proper ((⇛) ==>
            forall_relation
              (λ xs, forall_relation (λ ts, universal_relation ==> (⇛))))
           seqsubst.
  Proof with auto.
    intros A B Hequiv xs ts Hl1 Hl2 _. assert (Hinv:=Hl1). generalize dependent ts.
    induction xs as [|x xs IH]; intros.
    - apply of_same_length_nil_inv_l in Hinv as ->. simpl...
    - apply of_same_length_cons_inv_l in Hinv as (t&ts'&->&?). rename ts' into ts.
      simpl. f_equiv. rewrite IH...
      + reflexivity.
      + apply of_same_length_rest in Hl1 as ?...
  Qed.

  Global Instance subst_initials_proper_fent : Proper ((⇛ₗ@{M}) ==> (=) ==> (⇛)) subst_initials.
  Proof. intros A B Hent w ? <-. unfold subst_initials. rewrite Hent. reflexivity. Qed.

  Global Instance subst_initials_proper :
    Proper ((≡@{formula}) ==> (=) ==> (≡@{formula})) subst_initials.
  Proof. intros A B Hent w ? <-. unfold subst_initials. rewrite Hent. reflexivity. Qed.

  (* Global Instance FImpl_proper_fent : Proper ((⇚) ==> (⇛ₗ@{M}) ==> (⇛)) FImpl. *)
  (* Proof with auto. *)
  (*   intros A1 A2 Hent1 B1 B2 Hent2. unfold FImpl. rewrite f_ent_reverse_direction in Hent1. *)
  (*   rewrite Hent1. rewrite Hent2. reflexivity. *)
  (* Qed. *)
  (* Lemma fff A B C xs xs' ts ts' (H : term_list_equiv ts ts') `{OfSameLength _ _ xs ts} `{OfSameLength _ _ xs' ts'} : *)
  (*   A ⇛ B → *)
  (*     <! (∀* xs, (B ⇒ C)) [; *xs \ *ts ;] !> ⇛ *)
  (*                                  <! (∀* xs, (A ⇒ C))[; *xs' \ *ts' ;] !> . *)
  (* Proof. *)
  (*   intros. rewrite <- H2. setoid_rewrite H. *)


  (** Simplification lemmas for feval of n-ary variants **)
  Lemma simpl_feval_andlist σ Bs :
    feval σ <! ∧* Bs !> ↔ ∀ B, B ∈ Bs → feval σ B.
  Proof with auto.
    split.
    - intros ? B' ?. induction Bs as [|B BS IH]; [set_solver|]. simpl in H. simp feval in H.
      destruct H as []. apply elem_of_cons in H0 as [|].
      + subst...
      + apply IH...
    - induction Bs as [|B BS IH]; [set_solver|]. simpl. simp feval. split.
      + apply H. set_unfold. left...
      + apply IH. intros B' ?. apply H. set_unfold. right...
  Qed.

  Lemma simpl_feval_orlist σ Bs :
    feval σ <! ∨* Bs !> ↔ ∃ B, B ∈ Bs ∧ feval σ B.
  Proof with auto.
    split; intros.
    - induction Bs as [|B BS IH]; [set_solver|]. simpl in H. simp feval in H. destruct H as [|].
      + exists B. set_solver.
      + apply IH in H as [B' HB]. exists B'. set_solver.
    - destruct H as (B'&?&?). induction Bs as [|B Bs IH]; [set_solver|]. simpl.
      simp feval. apply elem_of_cons in H as [|].
      + subst. left...
      + right. apply IH...
  Qed.

  Lemma simpl_feval_existslist σ xs A :
    feval σ <! ∃* xs, A !> ↔
    ∃ vs (H : OfSameLength xs vs),
      feval σ (@seqsubst _ A xs (TConst <$> vs) of_same_length_fmap_r).
  Proof with auto.
    split; intros.
    - generalize dependent σ. induction xs as [|x xs IH]; simpl in *; intros.
      + exists [], (of_same_length_nil). simpl...
      + simp feval in H. destruct H as [v Hv]. rewrite feval_subst with (v:=v) in Hv...
        apply IH in Hv as (vs&Hl&?). exists (v :: vs), of_same_length_cons.
        simpl. rewrite feval_subst with (v:=v)...
        eapply feval_proper; [reflexivity| | apply H]. apply seqsubst_proper... reflexivity.
    - generalize dependent σ. induction xs as [|x xs' IH]; intros.
      + destruct H as (vs&Hl&?). apply of_same_length_nil_inv_l in Hl as ?. subst. simpl in H...
      + destruct H as (vs&Hl&?). apply of_same_length_cons_inv_l in Hl as ?.
        destruct H0 as (v&vs'&?&?). subst. simpl. simp feval.
        simpl in H. rewrite feval_subst with (v:=v) in H... exists v.
        rewrite feval_subst with (v:=v)... apply IH. exists vs'.
        apply of_same_length_rest in Hl as ?. exists H0.
        eapply feval_proper; [reflexivity| | apply H]. apply seqsubst_proper... reflexivity.
  Qed.

  Lemma simpl_feval_foralllist σ xs A :
    feval σ <! ∀* xs, A !> ↔
    ∀ vs (H : OfSameLength xs vs),
      feval σ (@seqsubst _ A xs (TConst <$> vs) of_same_length_fmap_r).
  Proof with auto.
    split; intros.
    - generalize dependent σ. generalize dependent vs.
      induction xs as [|x xs IH]; simpl in *; intros.
      + apply of_same_length_nil_inv_l in H0 as ?. subst. simpl in H...
      + apply of_same_length_cons_inv_l in H0 as ?.
        destruct H1 as (v&vs'&?&?). subst. simpl. rewrite feval_subst with (v:=v)...
        rewrite simpl_feval_fforall in H. specialize (H v).
        rewrite feval_subst with (v:=v) in H...
        apply (IH vs' (@of_same_length_rest _ _ _ _ _ _ H0)) in H.
        eapply feval_proper; [reflexivity| | apply H]. apply seqsubst_proper... reflexivity.
    - generalize dependent σ. induction xs as [|x xs IH]; simpl in *; intros.
      + specialize (H [] of_same_length_nil). simpl in H...
      + rewrite simpl_feval_fforall. intros. rewrite feval_subst with (v:=v)...
        (* TODO: maybe rename fforall in [simpl_feval_fforall] to forall? *)
        apply IH. intros. specialize (H (v::vs) (of_same_length_cons)). simpl in H.
        rewrite feval_subst with (v:=v) in H...
        eapply feval_proper; [reflexivity| | apply H]. apply seqsubst_proper... reflexivity.
  Qed.

End semantic.
