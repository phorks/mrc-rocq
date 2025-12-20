(* From Stdlib Require Import Lists.List. *)
From stdpp Require Import base sets gmap.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import SeqNotation.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SyntacticFacts.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.EquivLemmas.
From MRC Require Import PredCalc.NAry.
From MRC Require Import PredCalc.MultiSubst.
From MRC Require Import PredCalc.Variables.

Section set_solver.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation term := (termM M).
  Local Notation formula := (formulaM M).

  Implicit Types A B C : formula.
  Implicit Types xs : list variable.
  Implicit Types ts : list term.

  Global Instance set_unfold_elem_of_term_fvars x ts P1 P2 :
    (∀ t, SetUnfoldElemOf x (@term_fvars value t) (P1 t)) →
    (∀ t, SetUnfoldElemOf t ts (P2 t)) →
    SetUnfoldElemOf x
      (⋃ (term_fvars <$> ts))
      (∃ t, P1 t ∧ P2 t) | 10.
  Proof with auto.
    intros. constructor. rewrite elem_of_union_list. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_term_fvars_of_initial_vars x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
      (⋃ (term_fvars <$> (@TVar value <$> (initial_var_of <$> w))))
      (¬ var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (t&?&tx&->&x'&->&?). set_unfold in H0. subst x. split... apply H.
      rewrite to_final_var_initial_var_of...
    - intros []. exists x. simpl. split; [set_solver|]. exists x. split...
      exists (to_final_var x). apply H in H1. split... unfold var_final in H0.
      apply not_false_is_true in H0. unfold initial_var_of. destruct x. simpl. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_term_fvars_of_vars x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
      (⋃ (term_fvars <$> (@TVar value <$> (as_var <$> w))))
      (var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (t&?&tx&->&x'&->&?). set_unfold in H0. subst x. split... apply H.
      rewrite to_final_var_as_var...
    - intros []. exists x. simpl. split; [set_solver|]. exists x. split...
      exists (to_final_var x). apply H in H1. split... unfold var_final in H0.
      unfold to_final_var, as_var. destruct x. simpl. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_list_to_set_as_var_final_vars x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
      (list_to_set (as_var <$> w) : gset variable)
      (var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (x'&?&?). subst. split; [apply var_final_as_var |]... apply H.
      rewrite to_final_var_as_var...
    - intros []. exists (to_final_var x). set_unfold. split... unfold var_final in H.
      destruct x. cbv. f_equal...
  Qed.

  Global Instance set_unfold_elem_of_subst_initials_var_fvars x A w P1 P2 :
    (∀ x', SetUnfoldElemOf x' w (P1 x')) →
    (∀ x', SetUnfoldElemOf (initial_var_of x') (formula_fvars A) (P2 x')) →
    SetUnfoldElemOf x
                      (subst_initials_var_fvars A w)
                      (∃ x' : final_variable, x = as_var x' ∧ P1 x' ∧ P2 x').
  Proof. constructor. rewrite <- elem_of_subst_initials_var_fvars. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_subst_initials x A w Q1 Q2 Q3 :
    SetUnfoldElemOf x (formula_fvars A) Q1 →
    SetUnfoldElemOf x (list_to_set (initial_var_of <$> w) : gset variable) Q2 →
    SetUnfoldElemOf x (subst_initials_var_fvars A w) Q3 →
    SetUnfoldElemOf x (formula_fvars <! A[_₀\ w] !>)
                      ((Q1 ∧ ¬Q2) ∨ Q3).
  Proof. constructor. rewrite fvars_subst_initials. set_solver. Qed.

  Global Instance set_unfold_initial_var_of_elem_of_formula_fvars_subst_initials x A w Q1 Q2 :
    SetUnfoldElemOf (initial_var_of x) (formula_fvars A) Q1 →
    SetUnfoldElemOf x w Q2 →
    SetUnfoldElemOf (initial_var_of x)
        (formula_fvars <! A[_₀\ w] !>)
        (Q1 ∧ ¬Q2).
  Proof with auto.
    constructor. split; intros.
    - set_unfold in H. set_unfold in H1. destruct H1 as [[] | ].
      + split... intros ?. apply H2. exists x. set_solver.
      + destruct H1 as (x'&?&?&?). set_solver.
    - destruct H1. rewrite <- (@set_unfold_elem_of _ _ _ _ _ _ H) in H1.
      rewrite <- (@set_unfold_elem_of _ _ _ _ _ _ H0) in H2. clear H. clear H0.
      set_solver.
  Qed.

  Global Instance set_unfold_elem_of_list_to_set_intials_of_final_variables x w Q :
    SetUnfoldElemOf (to_final_var x) w Q →
    SetUnfoldElemOf x
        (list_to_set (initial_var_of <$> w) : gset variable)
        (¬ var_final x ∧ Q).
  Proof with auto.
    constructor. set_unfold. split.
    - intros (x'&?&?). subst. split; [apply var_final_initial_var_of|]. apply H.
      rewrite to_final_var_initial_var_of...
    - intros []. exists (to_final_var x). set_unfold. split... unfold var_final in H0.
      apply not_false_is_true in H0. destruct x. simpl in H0. rewrite H0. f_equal.
  Qed.

  Global Instance set_unfold_elem_of_fvars_FAnd x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (formula_fvars <! A1 ∧ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FOr x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (formula_fvars <! A1 ∨ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FImpl x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (formula_fvars <! A1 ⇒ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FIff x A1 A2 Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A1) Q1 →
    SetUnfoldElemOf x (formula_fvars A2) Q2 →
    SetUnfoldElemOf x (formula_fvars <! A1 ⇔ A2 !>) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FExists x y A Q :
    SetUnfoldElemOf x (formula_fvars A) Q →
    SetUnfoldElemOf x (formula_fvars <! ∃ y, A !>) (x ≠ y ∧ Q).
  Proof with auto. intros. constructor. simpl. set_solver. Qed.
  Global Instance set_unfold_elem_of_fvars_FForall x y A Q :
    SetUnfoldElemOf x (formula_fvars A) Q →
    SetUnfoldElemOf x (formula_fvars <! ∀ y, A !>) (x ≠ y ∧ Q).
  Proof with auto. intros. constructor. simpl. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_FAndList x Bs P1 P2 :
    (∀ A, SetUnfoldElemOf A Bs (P1 A)) →
    (∀ A, SetUnfoldElemOf x (formula_fvars A) (P2 A)) →
    SetUnfoldElemOf x (formula_fvars <! ∧* Bs !>) (∃ A, P1 A ∧ P2 A).
  Proof with auto.
    intros. constructor. rewrite fvars_andlist. rewrite elem_of_union_list. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_fvars_FOrList x Bs P1 P2 :
    (∀ A, SetUnfoldElemOf A Bs (P1 A)) →
    (∀ A, SetUnfoldElemOf x (formula_fvars A) (P2 A)) →
    SetUnfoldElemOf x (formula_fvars <! ∨* Bs !>) (∃ A, P1 A ∧ P2 A).
  Proof with auto.
    intros. constructor. rewrite fvars_orlist. rewrite elem_of_union_list. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_fvars_FExistsList x xs A Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A) Q1 →
    SetUnfoldElemOf x (list_to_set xs : gset variable) Q2 →
    SetUnfoldElemOf x (formula_fvars <! ∃* xs, A !>) (Q1 ∧ ¬Q2).
  Proof with auto. intros. constructor. rewrite fvars_existslist. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_FForallList x xs A Q1 Q2 :
    SetUnfoldElemOf x (formula_fvars A) Q1 →
    SetUnfoldElemOf x (list_to_set xs : gset variable) Q2 →
    SetUnfoldElemOf x (formula_fvars <! ∀* xs, A !>) (Q1 ∧ ¬Q2).
  Proof with auto. intros. constructor. rewrite fvars_foralllist. set_solver. Qed.

  Global Instance set_unfold_elem_of_fvars_FEqList x ts1 ts2 Hsl Q1 Q2 :
    SetUnfoldElemOf x (⋃ (term_fvars <$> ts1)) Q1 →
    SetUnfoldElemOf x (⋃ (term_fvars <$> ts2)) Q2 →
    SetUnfoldElemOf x (formula_fvars (@FEqList _ value_ty ts1 ts2 Hsl)) (Q1 ∨ Q2).
  Proof with auto. intros. constructor. rewrite fvars_eqlist. set_solver. Qed.

End set_solver.
