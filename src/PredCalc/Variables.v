From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Model.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.SyntacticFacts.

Section variables.
  Context {value : Type}.
  Notation term := (term value).
  Notation formula := (formula value).

  Definition var_final (x : variable) := var_is_initial x = false.
  Definition term_final (t : term) := ∀ x, x ∈ term_fvars t → var_final x.
  Definition term_list_final (ts : list term) := Forall term_final ts.
  Definition formula_final (A : formula) :=
    ∀ x, x ∈ formula_fvars A → var_final x.

  Instance var_final_dec x : Decision (var_final x).
  Proof. unfold var_final. solve_decision. Qed.

  Record final_term := mkFinalTerm {
    as_term : term;
    final_term_final : term_final as_term
  }.

  Record final_formula := mkFinalFormula {
    as_formula : formula;
    final_formula_final : formula_final as_formula
  }.

  Coercion as_term : final_term >-> term.
  Coercion as_formula : final_formula >-> formula.

  Definition as_term_F `{FMap F} (x : F final_term) : F term :=
    as_term <$> x.

  Definition as_formula_F `{FMap F} (x : F final_formula) : F formula :=
    as_formula <$> x.

  Class VarFinal (v : variable) := var_is_final : var_final v.

  Global Instance non_initial_var_final {x i} : VarFinal (mkVar x i false).
  Proof. reflexivity. Defined.

  Global Instance as_var_var_final {x} : VarFinal (as_var x).
  Proof. reflexivity. Defined.

  Lemma var_final_as_var x :
    var_final (as_var x).
  Proof. reflexivity. Defined.

  Lemma var_final_initial_var_of x :
    ¬ var_final (initial_var_of x).
  Proof. cbv. discriminate. Qed.

  Class TermFinal (t : term) := term_is_final : term_final t.
  Class TermListFinal (ts : list term) := term_list_is_final : term_list_final ts.

  Global Instance term_list_final_nil : TermListFinal [].
  Proof. unfold TermListFinal, term_list_final. auto. Defined.

  Global Instance term_list_final_cons {t ts} `{TermFinal t} `{TermListFinal ts} :
    TermListFinal (t :: ts).
  Proof. unfold TermListFinal, term_list_final. auto. Defined.

  Global Instance const_term_final {v} : TermFinal (TConst v).
  Proof. unfold TermFinal, term_final. simpl. intros. set_solver. Defined.

  Global Instance var_term_final {x} `{VarFinal x} : TermFinal (TVar x).
  Proof.
    unfold TermFinal, term_final. simpl. intros. apply elem_of_singleton in H0.
    subst. auto.
  Defined.

  Global Instance app_term_final {fsym args} `{TermListFinal args} :
    TermFinal (TApp fsym args).
  Proof.
    unfold TermFinal, term_final. simpl. intros.
    unfold TermListFinal, term_list_final, term_final in H.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. rewrite Forall_forall in H. apply H with (x:=arg); assumption.
  Defined.

  Global Instance subst_term_final {t x t'} `{TermFinal t} `{TermFinal t'} :
    TermFinal (subst_term t x t').
  Proof with auto.
    unfold TermFinal, term_final. intros. destruct (decide (x ∈ term_fvars t)).
    - rewrite fvars_subst_term_free with (t':=t') in H1... set_solver.
    - rewrite subst_term_non_free in H1...
  Defined.

  Global Instance final_term_term_final {t} : TermFinal (as_term t).
  Proof. unfold TermFinal. apply (final_term_final t). Defined.

  Class FormulaFinal (A : formula) := formula_is_final : formula_final A.

  Global Instance true_atomic_formula_final : FormulaFinal <! true !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Defined.

  Global Instance false_atomic_formula_final : FormulaFinal <! false !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Defined.

  Global Instance eq_atomic_formula_final {t1 t2} `{TermFinal t1} `{TermFinal t2} :
    FormulaFinal <! ⌜t1 = t2⌝ !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance pred_atomic_formula_final {psym args} `{TermListFinal args} :
    FormulaFinal (FAtom (AT_Pred psym args)).
  Proof.
    unfold FormulaFinal, formula_final. simpl. intros.
    unfold TermListFinal, term_list_final, term_final in H.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. rewrite Forall_forall in H. apply H with (x:=arg); assumption.
  Defined.

  Global Instance f_not_formula_final {A} `{FormulaFinal A} : FormulaFinal <! ¬ A !>.
  Proof. unfold FormulaFinal, formula_final. auto. Defined.

  Global Instance f_and_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ∧ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance f_or_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ∨ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance f_impl_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ⇒ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance f_iff_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ⇔ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance f_exists_formula_final {x A} `{FormulaFinal A} :
    FormulaFinal <! ∃ x, A !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance f_forall_formula_final {x A} `{FormulaFinal A} :
    FormulaFinal <! ∀ x, A !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Defined.

  Global Instance subst_formula_final {A x t} `{FormulaFinal A} `{TermFinal t} :
    FormulaFinal <! A[x \ t] !>.
  Proof.
    unfold FormulaFinal, formula_final. intros. apply fvars_subst_superset in H1.
    set_solver.
  Defined.

  Global Instance final_formula_formula_final {A} : FormulaFinal (as_formula A).
  Proof. unfold FormulaFinal. apply (final_formula_final A). Defined.

  Definition as_final_var x `{VarFinal x} : final_variable :=
    mkFinalVar (var_name x) (var_sub x).

  Lemma as_final_var_as_var x : as_final_var (as_var x) = x.
  Proof. unfold as_var, as_final_var. destruct x. simpl. reflexivity. Qed.

  Lemma as_var_as_final_var x `{VarFinal x} : as_var (as_final_var x) = x.
  Proof.
    unfold as_var, as_final_var. unfold VarFinal, var_final in H. destruct x.
    simpl in *. rewrite H. reflexivity.
  Qed.

  Definition as_final_term t `{H : TermFinal t} : final_term :=
    mkFinalTerm t (@term_is_final t H).

  Lemma as_final_term_as_term t : as_final_term (as_term t) = t.
  Proof.
    unfold as_final_term, term_is_final. destruct t. simpl. reflexivity.
  Qed.

  Lemma as_term_as_final_term t `{TermFinal t} : as_term (as_final_term t) = t.
  Proof. unfold as_final_term, as_term. reflexivity. Qed.

  Definition as_final_formula A `{H : FormulaFinal A} : final_formula :=
    mkFinalFormula A (@formula_is_final A H).

  Lemma as_formula_term_as_formula A : as_final_formula (as_formula A) = A.
  Proof.
    unfold as_final_formula, formula_is_final. destruct A. simpl. reflexivity.
  Qed.

  Lemma as_formula_as_final_formula A `{FormulaFinal A} : as_formula (as_final_formula A) = A.
  Proof. unfold as_final_formula, as_formula. reflexivity. Qed.

  Lemma initial_var_of_elem_of_formula_fvars x A :
    initial_var_of x ∈ formula_fvars A →
    ¬ formula_final A.
  Proof. intros. intros contra. apply contra in H. cbv in H. discriminate. Qed.

  Lemma elem_of_fvars_final_formula_inv A x `{FormulaFinal A} :
    x ∈ formula_fvars A →
    var_final x.
  Proof. intros. apply H in H0. assumption. Qed.



  (* Axiom v : V. *)
  (* Axiom x : final_variable. *)
  (* Axiom y : variable. *)
  (* Axiom ts : list term. *)
  (* Axiom H : `{TermListFinal ts}. *)
  (* Axiom t : final_term. *)
  (* Axiom u : term. *)
  (* Axiom A : final_formula. *)
  (* Axiom B : formula. *)
  (* Axiom fsym : Strings.String.string. *)
  (* Axiom psym : Strings.String.string. *)

  (* Definition tt : final_term := as_final_term (TApp fsym (TVar x :: [TVar x])). *)
  (* Definition aa : final_formula := as_final_formula <! ⌜t + x = t + t⌝ !>. *)
  (* Definition aa1 : final_formula := as_final_formula <! ⌜t + x = t + t⌝ ∧ A[y \ u] !>. *)

  Lemma final_var_list_as_var_disjoint_term_fvars_initial_var_of (xs : list final_variable) :
    list_to_set (as_var <$> xs) ## ⋃ (term_fvars <$> (@TVar value <$> (initial_var_of <$> xs))).
  Proof.
    intros x H1 H2. apply elem_of_union_list in H2 as (fvars&?&?).
    rewrite <- list_fmap_compose in H. set_unfold in H. destruct H as (x0&?&(x'&?&?)).
    subst. simpl in *. set_solver.
  Qed.

End variables.


Hint Resolve var_final_as_var : core.
Hint Resolve var_final_initial_var_of : core.
Hint Resolve final_var_list_as_var_disjoint_term_fvars_initial_var_of : core.
Hint Extern 3 (FormulaFinal _) => typeclasses eauto : core.


Notation "₀ x" := (initial_var_of x) (in custom term at level 5) : refiney_scope.

Declare Custom Entry variable_list.
Declare Custom Entry term_list.
Declare Custom Entry formula_list.

(* ******************************************************************* *)
(* variable lists (e.g., binders of [∀*], [∃*])                        *)
(* ******************************************************************* *)
Notation "e" := e (in custom variable_list at level 0, e constr at level 0)
    : refiney_scope.
Notation "↑ₓ xs" := (as_var <$> xs)
                      (in custom variable_list at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑ₓ( xs )" := (as_var <$> xs)
                      (in custom variable_list at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "↑₀ xs" := (initial_var_of <$> xs)
                      (in custom variable_list at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑₀( xs )" := (initial_var_of <$> xs)
                      (in custom variable_list at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "$( e )" := e (in custom variable_list at level 5,
                           only parsing,
                           e constr at level 200)
    : refiney_scope.

(* ******************************************************************* *)
(* term lists (e.g., both sides of [=*])                               *)
(* ******************************************************************* *)
Notation "e" := e (in custom term_list at level 0, e constr at level 0)
    : refiney_scope.
Notation "⇑ₓ xs" := (TVar <$> (as_var <$> xs))
                      (in custom term_list at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ( xs )" := (TVar <$> (as_var <$> xs))
                      (in custom term_list at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₓ₊ xs" := (TVar <$> xs)
                      (in custom term_list at level 3, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ₊( xs )" := (TVar <$> xs)
                      (in custom term_list at level 3, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑₀ xs" := (TVar <$> (initial_var_of <$> xs))
                      (in custom term_list at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑₀( xs )" := (TVar <$> (initial_var_of <$> xs))
                      (in custom term_list at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₜ ts" := (as_term <$> ts)
                      (in custom term_list at level 5, ts constr at level 0)
    : refiney_scope.
Notation "⇑ₜ( ts )" := (as_term <$> ts)
                      (in custom term_list at level 5, only parsing, ts constr at level 200)
    : refiney_scope.
Notation "$( e )" := e (in custom term_list at level 5,
                           only parsing,
                           e constr at level 200)
    : refiney_scope.

(* ******************************************************************* *)
(* formula lists (e.g., args of [∧*], [∨*])                            *)
(* ******************************************************************* *)
Notation "e" := e (in custom formula_list at level 0, e constr at level 0)
    : refiney_scope.
Notation "⤊ Bs" := (as_formula <$> Bs)
                      (in custom formula_list at level 5, Bs constr at level 0)
    : refiney_scope.
Notation "⤊( Bs )" := (as_formula <$> Bs)
                      (in custom formula_list at level 5, only parsing, Bs constr at level 200)
    : refiney_scope.
Notation "$( e )" := e (in custom formula_list at level 5,
                           only parsing,
                           e constr at level 200)
    : refiney_scope.

(* ******************************************************************* *)
(* term_seq elements (e.g., right part of [[_ \ _]])                   *)
(* ******************************************************************* *)
Notation "⇑ₓ xs" := (TVar <$> (as_var <$> xs))
                      (in custom term_seq_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ( xs )" := (TVar <$> (as_var <$> xs))
                      (in custom term_seq_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₓ₊ xs" := (TVar <$> xs)
                      (in custom term_seq_elem at level 3, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ₊( xs )" := (TVar <$> xs)
                      (in custom term_seq_elem at level 3, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑₀ xs" := (TVar <$> (initial_var_of <$> xs))
                      (in custom term_seq_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑₀( xs )" := (TVar <$> (initial_var_of <$> xs))
                      (in custom term_seq_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₜ ts" := (as_term <$> ts)
                      (in custom term_seq_elem at level 5, ts constr at level 0)
    : refiney_scope.
Notation "<!! e !!>" := (as_final_formula e) (e custom formula) : refiney_scope.


(* ******************************************************************* *)
(* adding notations to Rocq's default scope                            *)
(* ******************************************************************* *)
Notation "↑ₓ xs" := (as_var <$> xs)
                      (at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑ₓ( xs )" := (as_var <$> xs)
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "↑₀ xs" := (initial_var_of <$> xs)
                      (at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑₀( xs )" := (initial_var_of <$> xs)
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₓ xs" := (TVar <$> (as_var <$> xs))
                      (at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ( xs )" := (TVar <$> (as_var <$> xs))
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₓ₊ xs" := (TVar <$> xs)
                      (at level 3, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ₊( xs )" := (TVar <$> xs)
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑₀ xs" := (TVar <$> (initial_var_of <$> xs))
                      (at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑₀( xs )" := (TVar <$> (initial_var_of <$> xs))
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₜ ts" := (as_term <$> ts)
                      (at level 5, ts constr at level 0)
    : refiney_scope.
Notation "⇑ₜ( ts )" := (as_term <$> ts)
                      (at level 5, only parsing, ts constr at level 200)
    : refiney_scope.
Notation "⤊ Bs" := (as_formula <$> Bs)
                      (at level 5, Bs constr at level 0)
    : refiney_scope.
Notation "⤊( Bs )" := (as_formula <$> Bs)
                      (at level 5, only parsing, Bs constr at level 200)
    : refiney_scope.

Arguments final_term value : clear implicits.
Arguments final_formula value : clear implicits.

Section lemmas.
  Context {value : Type}.

  Lemma disjoint_initial_var_of (xs1 xs2 : list final_variable) :
    xs1 ## xs2 →
    ↑₀ xs1 ## ↑₀ xs2.
  Proof. set_solver. Qed.

  Lemma NoDup_initial_var_of xs :
    NoDup xs →
    NoDup ↑₀ xs.
  Proof. intros. apply NoDup_fmap; [apply initial_var_of_inj | assumption]. Qed.

  Lemma NoDup_as_var xs :
    NoDup xs →
    NoDup ↑ₓ xs.
  Proof. intros. apply NoDup_fmap; [apply as_var_inj | assumption]. Qed.

  Lemma disjoint_initial_var_of_term_fvars xs1 xs2 :
    xs1 ## xs2 →
    list_to_set ↑₀ xs1 ## ⋃ (@term_fvars value <$> ⇑ₓ xs2).
  Proof.
    intros. set_unfold. intros x (x'&->&?) ?. apply elem_of_union_list in H1 as (fvars&?&?).
    apply elem_of_list_fmap in H1 as (tx&->&?). rewrite <- list_fmap_compose in H1.
    apply elem_of_list_fmap in H1 as (y&->&?). set_solver.
  Qed.

  Lemma disjoint_initial_final_vars (xs1 xs2 : gset variable) :
    (∀ x, x ∈ xs1 → ¬ var_final x) →
    (∀ x, x ∈ xs2 → var_final x) →
    xs1 ## xs2.
  Proof. intros. set_solver. Qed.

  Lemma disjoint_final_initial_vars (xs1 xs2 : gset variable) :
    (∀ x, x ∈ xs1 → var_final x) →
    (∀ x, x ∈ xs2 → ¬ var_final x) →
    xs1 ## xs2.
  Proof. intros. set_solver. Qed.
End lemmas.

Hint Resolve disjoint_initial_var_of : core.
Hint Resolve NoDup_initial_var_of : core.
Hint Resolve NoDup_as_var : core.
Hint Resolve disjoint_initial_var_of_term_fvars : core.
