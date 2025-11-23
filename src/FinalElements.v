From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Model.
From MRC Require Import PredCalcBasic.
From MRC Require Import PredCalcSubst.

Section final_elements.
  Context {M : model}.
  Notation term := (term (value M)).
  Notation final_term := (final_term (value M)).
  Notation formula := (formula (value M)).
  Notation final_formula := (final_formula (value M)).

  Definition var_final (x : variable) := var_is_initial x = false.
  Definition term_final (t : term) := ∀ x, x ∈ term_fvars t → var_final x.
  Definition term_list_final (ts : list term) := Forall term_final ts.
  Definition formula_final (A : formula) :=
    ∀ x, x ∈ formula_fvars A → var_final x.

  Class VarFinal (v : variable) := var_is_final : var_final v.

  Instance non_initial_var_final {x i} : VarFinal (mkVar x i false).
  Proof. reflexivity. Qed.

  Instance final_var_final {x} : VarFinal (as_var x).
  Proof. reflexivity. Qed.

  Class TermFinal (t : term) := term_is_final : term_final t.
  Class TermListFinal (ts : list term) := term_list_is_final : term_list_final ts.

  Instance term_list_final_nil : TermListFinal [].
  Proof. unfold TermListFinal, term_list_final. auto. Qed.

  Instance term_list_final_cons {t ts} `{TermFinal t} `{TermListFinal ts} :
    TermListFinal (t :: ts).
  Proof. unfold TermListFinal, term_list_final. auto. Qed.

  Instance const_term_final {v} : TermFinal (TConst v).
  Proof. unfold TermFinal, term_final. simpl. intros. set_solver. Qed.

  Instance var_term_final {x} `{VarFinal x} : TermFinal (TVar x).
  Proof.
    unfold TermFinal, term_final. simpl. intros. apply elem_of_singleton in H0.
    subst. auto.
  Qed.

  Instance app_term_final {fsym args} `{TermListFinal args} :
    TermFinal (TApp fsym args).
  Proof.
    unfold TermFinal, term_final. simpl. intros.
    unfold TermListFinal, term_list_final, term_final in H.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. rewrite Forall_forall in H. apply H with (x:=arg); assumption.
  Qed.

  Instance subst_term_final {t x t'} `{TermFinal t} `{TermFinal t'} :
    TermFinal (subst_term t x t').
  Proof with auto.
    unfold TermFinal, term_final. intros. destruct (decide (x ∈ term_fvars t)).
    - rewrite subst_term_free_fvars with (t':=t') in H1... set_solver.
    - rewrite subst_term_non_free_eq in H1...
  Qed.

  Class FormulaFinal (A : formula) := formula_is_final : formula_final A.

  Instance true_atomic_formula_final : FormulaFinal <! true !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Qed.

  Instance false_atomic_formula_final : FormulaFinal <! false !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Qed.

  Instance eq_atomic_formula_final {t1 t2} `{TermFinal t1} `{TermFinal t2} :
    FormulaFinal <! ⌜t1 = t2⌝ !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance pred_atomic_formula_final {psym args} `{TermListFinal args} :
    FormulaFinal (FAtom (AT_Pred psym args)).
  Proof.
    unfold FormulaFinal, formula_final. simpl. intros.
    unfold TermListFinal, term_list_final, term_final in H.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. rewrite Forall_forall in H. apply H with (x:=arg); assumption.
  Qed.

  Instance f_not_formula_final {A} `{FormulaFinal A} : FormulaFinal <! ¬ A !>.
  Proof. unfold FormulaFinal, formula_final. auto. Qed.

  Instance f_and_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ∧ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance f_or_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ∨ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance f_impl_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ⇒ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance f_iff_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ⇔ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance f_exists_formula_final {x A} `{FormulaFinal A} :
    FormulaFinal <! ∃ x, A !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance f_forall_formula_final {x A} `{FormulaFinal A} :
    FormulaFinal <! ∀ x, A !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Instance subst_formula_final {A x t} `{FormulaFinal A} `{TermFinal t} :
    FormulaFinal <! A[x \ t] !>.
  Proof.
    unfold FormulaFinal, formula_final. intros. apply fvars_subst_superset in H1.
    set_solver.
  Qed.
