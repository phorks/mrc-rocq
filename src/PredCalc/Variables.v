From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SyntacticFacts.

Section variables.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Notation term := (term M).
  Notation formula := (formula M).

  (* ******************************************************************* *)
  (* properties of final and initial variables                           *)
  (* ******************************************************************* *)

  Definition var_final x := var_is_initial x = false.
  Definition var_initial x := var_is_initial x = true.

  Lemma var_final_as_var x : var_final (as_var x).
  Proof. reflexivity. Qed.

  Lemma var_final_initial_var_of x : ¬ var_final (initial_var_of x).
  Proof. cbv. discriminate. Qed.

  Lemma initial_var_of_to_final_var x : var_initial x → ₀(to_final_var x) = x.
  Proof.
    unfold to_final_var, initial_var_of, var_initial. destruct x. simpl. intros; by subst.
  Qed.

  Lemma initial_var_of_to_final_var_inv x : ₀(to_final_var x) = x → var_initial x.
  Proof.
    unfold to_final_var, initial_var_of, var_initial. destruct x. simpl. by inversion 1.
  Qed.

  Lemma initial_var_of_initial x : var_initial ₀x.
  Proof. done. Qed.

  Lemma var_final_not_initial x : var_final x ↔ ¬ var_initial x.
  Proof. unfold var_final, var_initial. by destruct (var_is_initial x). Qed.

  Lemma var_initial_not_final x : var_initial x ↔ ¬ var_final x.
  Proof. unfold var_final, var_initial. by destruct (var_is_initial x). Qed.

  Lemma var_initial_or_final x : var_initial x ∨ var_final x.
  Proof. unfold var_initial, var_final. destruct (var_is_initial x); auto. Qed.

  Lemma var_final_ne_initial_var_of x (y : final_variable) :
    var_final x →
    x ≠ ₀ y.
  Proof.
    intros ? contra. destruct x, y. unfold initial_var_of in contra.
    inversion contra. subst. unfold var_final in H. simpl in H. done.
  Qed.


  Lemma to_initial_var_inj' x y :
    var_final x →
    var_final y →
    to_initial_var x = to_initial_var y →
    x = y.
  Proof.
    intros. destruct x. destruct y. unfold var_final in H, H0. simpl in H, H0.
    inversion H1. subst. reflexivity.
  Qed.

  Lemma var_initial_to_initial_var x : var_initial (to_initial_var x).
  Proof. done. Qed.

  Lemma to_final_var_inj_initial {x y} :
    var_initial x →
    var_initial y →
    to_final_var x = to_final_var y →
    x = y.
  Proof.
    unfold var_initial, to_final_var. intros. inversion H1.
    destruct x; destruct y. simpl in *. naive_solver.
  Qed.

  Global Instance set_unfold_var_initial_as_var x : SetUnfold (var_initial (as_var x)) False.
  Proof. done. Qed.

  Class VarFinal (v : variable) := var_is_final : var_final v.

  Global Instance non_initial_var_final {x i} : VarFinal (mkVar x i false).
  Proof. reflexivity. Qed.

  Global Instance as_var_var_final {x} : VarFinal (as_var x).
  Proof. reflexivity. Qed.

  Global Instance fresh_var_final x fvars `{VarFinal x} : VarFinal (fresh_var x fvars).
  Proof with auto.
    unfold VarFinal. generalize dependent x. unfold fresh_var. induction (S (size fvars)); intros.
    - simpl. apply H.
    - simpl. destruct (decide (x ∈ fvars)).
      + apply IHn. unfold VarFinal, var_final in H. destruct x. simpl in H.
        rewrite H. reflexivity.
      + apply H.
  Qed.

  Lemma to_initial_var_inj x y `{!VarFinal x} `{!VarFinal y} :
    to_initial_var x = to_initial_var y →
    x = y.
  Proof with auto. intros. apply to_initial_var_inj'... Qed.

  (* ******************************************************************* *)
  (* properties of final and initial terms and formula                   *)
  (* ******************************************************************* *)

  Definition term_final (t : term) := ∀ x, x ∈ term_fvars t → var_final x.
  Definition term_list_final (ts : list term) := Forall term_final ts.
  Definition formula_final (A : formula) :=
    ∀ x, x ∈ formula_fvars A → var_final x.

  (* The following instances use the functional extensionality axiom to prove proof irrelevance
     of term_final and formula_final. This can be avoided by defining differently using [every]
     as follows or directly via [Forall]. But then working with them becomes harder.
     I believe, nothing except these uses functional extensionality in our formalization uses.
     HACK: If for whatever reason we want to avoid the functional extensionality axiom, change
           these definitions to the following (the fix_wp branch does this, but is unfinished):

      [Definition term_final t := every var_final (term_fvars t).]
      [Definition term_list_final ts := every term_final ts.]
      [Definition formula_final A := every var_final (formula_fvars A).]
   *)
  Global Instance term_final_pi {t} : ProofIrrel (term_final t).
  Proof.
    unfold term_final. intros p q. apply functional_extensionality_dep. intros.
    apply functional_extensionality_dep. intros H. apply eq_pi. solve_decision.
  Qed.

  Global Instance formula_final_pi {A} : ProofIrrel (formula_final A).
  Proof.
    unfold formula_final. intros p q. apply functional_extensionality_dep. intros.
    apply functional_extensionality_dep. intros H. apply eq_pi. solve_decision.
  Qed.

  Global Instance var_initial_dec {x} : Decision (var_initial x).
  Proof. unfold var_initial. solve_decision. Defined.

  Global Instance var_final_dec {x} : Decision (var_final x).
  Proof. unfold var_final. solve_decision. Defined.

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

  Class TermFinal (t : term) := term_is_final : term_final t.
  Class TermListFinal (ts : list term) := term_list_is_final : term_list_final ts.

  Global Instance term_list_final_nil : TermListFinal [].
  Proof. unfold TermListFinal, term_list_final. auto. Qed.

  Global Instance term_list_final_cons {t ts} `{TermFinal t} `{TermListFinal ts} :
    TermListFinal (t :: ts).
  Proof. unfold TermListFinal, term_list_final. auto. Qed.

  Global Instance const_term_final {v} : TermFinal (TConst v).
  Proof. unfold TermFinal, term_final. simpl. intros. set_solver. Qed.

  Global Instance var_term_final {x} `{VarFinal x} : TermFinal (TVar x).
  Proof.
    unfold TermFinal, term_final. simpl. intros. apply elem_of_singleton in H0.
    subst. auto.
  Qed.

  Global Instance app_term_final {fsym args} `{TermListFinal args} :
    TermFinal (TApp fsym args).
  Proof.
    unfold TermFinal, term_final. simpl. intros.
    unfold TermListFinal, term_list_final, term_final in H.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. rewrite Forall_forall in H. apply H with (x:=arg); assumption.
  Qed.

  Global Instance subst_term_final {t x t'} `{TermFinal t} `{TermFinal t'} :
    TermFinal (subst_term t x t').
  Proof with auto.
    unfold TermFinal, term_final. intros. destruct (decide (x ∈ term_fvars t)).
    - rewrite fvars_subst_term_free with (t':=t') in H1... set_solver.
    - rewrite subst_term_non_free in H1...
  Qed.

  Global Instance final_term_term_final {t} : TermFinal (as_term t).
  Proof. unfold TermFinal. apply (final_term_final t). Defined.

  Class FormulaFinal (A : formula) := formula_is_final : formula_final A.

  Global Instance true_atomic_formula_final : FormulaFinal <! true !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Qed.

  Global Instance false_atomic_formula_final : FormulaFinal <! false !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Qed.

  Global Instance eq_atomic_formula_final {t1 t2} `{TermFinal t1} `{TermFinal t2} :
    FormulaFinal <! ⌜t1 = t2⌝ !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance hastype_final_final {t ty} `{!TermFinal t}
    : FormulaFinal (FAtom (AT_HasType t ty)).
  Proof. intros x H. set_solver. Qed.

  Global Instance pred_atomic_formula_final {psym args} `{TermListFinal args} :
    FormulaFinal (FAtom (AT_Pred psym args)).
  Proof.
    unfold FormulaFinal, formula_final. simpl. intros.
    unfold TermListFinal, term_list_final, term_final in H.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. rewrite Forall_forall in H. apply H with (x:=arg); assumption.
  Qed.

  Global Instance f_not_formula_final {A} `{FormulaFinal A} : FormulaFinal <! ¬ A !>.
  Proof. unfold FormulaFinal, formula_final. auto. Qed.

  Global Instance f_and_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ∧ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance f_or_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ∨ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance f_impl_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ⇒ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance f_iff_formula_final {A B} `{FormulaFinal A} `{FormulaFinal B} :
    FormulaFinal <! A ⇔ B !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance f_exists_formula_final {x A} `{FormulaFinal A} :
    FormulaFinal <! ∃ x, A !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance f_forall_formula_final {x A} `{FormulaFinal A} :
    FormulaFinal <! ∀ x, A !>.
  Proof. unfold FormulaFinal, formula_final. set_solver. Qed.

  Global Instance subst_formula_final {A x t} `{FormulaFinal A} `{TermFinal t} :
    FormulaFinal <! A[x \ t] !>.
  Proof.
    unfold FormulaFinal, formula_final. intros. apply fvars_subst_superset in H1.
    set_solver.
  Qed.

  Global Instance final_formula_formula_final {A} : FormulaFinal (as_formula A).
  Proof. unfold FormulaFinal. apply (final_formula_final A). Defined.

  Definition as_final_var x `{VarFinal x} : final_variable :=
    mkFinalVar (var_name x) (var_sub x).

  Lemma as_final_var_as_var x H :
    @as_final_var (as_var x) H = x.
  Proof. destruct x. unfold as_final_var. simpl. f_equal. Qed.

  Lemma as_var_as_final_var x `{VarFinal x} : as_var (as_final_var x) = x.
  Proof.
    unfold as_var, as_final_var. unfold VarFinal, var_final in H. destruct x.
    simpl in *. rewrite H. reflexivity.
  Qed.

  Definition as_final_term t `{H : TermFinal t} : final_term :=
    mkFinalTerm t (@term_is_final t H).

  Lemma as_final_term_eq {t t' H} :
    t = as_term t' →
    @as_final_term t H = t'.
  Proof.
    intros. subst. destruct t'. unfold as_final_term. simpl. f_equal. unfold TermFinal in H.
    apply term_final_pi.
  Qed.

  Lemma as_final_term_as_term t : as_final_term (as_term t) = t.
  Proof.
    unfold as_final_term, term_is_final. destruct t. simpl. reflexivity.
  Qed.

  Lemma as_term_as_final_term t `{TermFinal t} : as_term (as_final_term t) = t.
  Proof. unfold as_final_term, as_term. reflexivity. Qed.

  Definition as_final_formula A `{H : FormulaFinal A} : final_formula :=
    mkFinalFormula A (@formula_is_final A H).

  Lemma as_final_formula_eq {A A' H} :
    A = as_formula A' →
    @as_final_formula A H = A'.
  Proof.
    intros. subst. destruct A'. unfold as_final_formula. simpl. f_equal. unfold FormulaFinal in H.
    apply formula_final_pi.
  Qed.

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

  Lemma as_var_to_final_var_final (x : variable) :
    var_final x →
    as_var (to_final_var x) = x.
  Proof.
    intros. rewrite as_var_to_final_var. destruct x. unfold var_final in H.
    unfold Model.var_is_initial in H. rewrite H. apply var_with_is_initial_id.
    reflexivity.
  Qed.

  Lemma final_var_list_as_var_disjoint_term_fvars_initial_var_of (xs : list final_variable) :
    list_to_set (as_var <$> xs) ## ⋃ (term_fvars <$> (@TVar M <$> (initial_var_of <$> xs))).
  Proof.
    intros x H1 H2. apply elem_of_union_list in H2 as (fvars&?&?).
    rewrite <- list_fmap_compose in H. set_unfold in H. destruct H as (x0&?&(x'&?&?)).
    subst. simpl in *. set_solver.
  Qed.

  (* ******************************************************************* *)
  (* lifting fequiv ≡ to final formulas                                  *)
  (* ******************************************************************* *)

  Global Instance ffequiv : Equiv final_formula := λ F1 F2, as_formula F1 ≡ as_formula F2.
  Global Instance ffequiv_refl : Reflexive ffequiv.
  Proof with auto. split; done. Qed.

  Global Instance ffequiv_sym : Symmetric ffequiv.
  Proof with auto. intros A B. unfold ffequiv. done. Qed.

  Global Instance ffequiv_trans : Transitive ffequiv.
  Proof with auto. intros A B C ??. unfold ffequiv in *. trans B... Qed.

  Global Instance ffequiv_equiv : Equivalence ffequiv.
  Proof. split; [exact ffequiv_refl | exact ffequiv_sym | exact ffequiv_trans]. Qed.

  Lemma ffequiv_fequiv (A B : formula) `{!FormulaFinal A} `{!FormulaFinal B} :
    as_final_formula A ≡ as_final_formula B ↔ A ≡ B.
  Proof. unfold equiv, ffequiv. do 2 rewrite as_formula_as_final_formula. done. Qed.

  (* ******************************************************************* *)
  (* some useful functions for extracting final and initials free        *)
  (*  variables from formulas                                            *)
  (* ******************************************************************* *)

  Definition final_fvars (A : formula) :=
    to_final_var <$> (set_to_list (filter var_final (formula_fvars A))).
  Definition initial_fvars (A : formula) :=
    filter var_initial (set_to_list (formula_fvars A)).
  Definition finalized_initial_fvars A :=
    to_final_var <$> (initial_fvars A).

  Lemma elem_of_initial_fvars {x A} :
    x ∈ initial_fvars A ↔ x ∈ formula_fvars A ∧ var_initial x.
  Proof.
    unfold initial_fvars. split; intros.
    - apply elem_of_list_filter in H. set_solver.
    - apply elem_of_list_filter. set_solver.
  Qed.

  Global Instance set_unfold_elem_of_initial_fvars x A P1 P2 :
    SetUnfoldElemOf x (formula_fvars A) P1 →
    SetUnfold (var_initial x) P2 →
    SetUnfoldElemOf x (initial_fvars A) (P1 ∧ P2).
  Proof.
    intros. constructor. rewrite elem_of_initial_fvars.
    rewrite set_unfold_elem_of by exact H.
    by rewrite set_unfold with (P:=var_initial x) by exact (H0).
  Qed.

  Lemma elem_of_final_fvars {x A} :
    x ∈ final_fvars A ↔ as_var x ∈ formula_fvars A.
  Proof.
    unfold final_fvars. split; intros.
    - apply elem_of_list_fmap in H as (?&?&?). set_unfold in H0. simpl in H0. destruct H0 as [].
      symmetry in H. apply as_var_to_final_var_final in H0. subst. rewrite <- H0 in H1.
      done.
    - apply elem_of_list_fmap. exists (as_var x).
      split.
      + rewrite to_final_var_as_var. done.
      + set_unfold. split; set_solver.
  Qed.

  Global Instance set_unfold_elem_of_final_fvars x A P :
    SetUnfoldElemOf (as_var x) (formula_fvars A) P →
    SetUnfoldElemOf x (final_fvars A) P.
  Proof.
    intros. constructor. rewrite elem_of_final_fvars.
    by rewrite set_unfold_elem_of by exact H.
  Qed.

  Lemma elem_of_finalized_initial_fvars {x A} :
    x ∈ finalized_initial_fvars A ↔ ₀x ∈ formula_fvars A.
  Proof with auto.
    unfold finalized_initial_fvars. rewrite elem_of_list_fmap.
    setoid_rewrite elem_of_initial_fvars. split; intros.
    - destruct H as (y&->&?&?). rewrite initial_var_of_to_final_var...
    - exists ₀x. rewrite to_final_var_initial_var_of. split_and!... done.
  Qed.

  Global Instance set_unfold_elem_of_finalized_initial_fvars x A P :
    SetUnfoldElemOf ₀x (formula_fvars A) P →
    SetUnfoldElemOf x (finalized_initial_fvars A) P.
  Proof.
    intros. constructor. rewrite elem_of_finalized_initial_fvars.
    by rewrite set_unfold_elem_of by exact H.
  Qed.

  Lemma finalized_initial_fvars_subst_perm x A :
    ₀x ∈ formula_fvars A →
    finalized_initial_fvars <! A[₀x \ x] !> ≡ₚ delete x (finalized_initial_fvars A).
  Proof with auto.
    intros. assert (H0:=H). apply union_difference_singleton_L in H.
    unfold finalized_initial_fvars, initial_fvars.
    rewrite H. rewrite fvars_subst...
    rewrite set_to_list_union_perm with (s1:={[₀x]}) by set_solver.
    rewrite filter_app. rewrite set_to_list_singleton.
    rewrite fmap_app. simpl. unfold fmap at 2. unfold filter at 2.
    simpl.
    rewrite to_final_var_initial_var_of. rewrite list_delete_elem_cons.
    rewrite list_delete_elem_eq.
    2:{
      intros contra. set_unfold in contra. destruct contra as (?&->&?).
      apply elem_of_list_filter in H1 as [].
      set_unfold in H2. simpl in H2. rewrite initial_var_of_to_final_var in H2...
      naive_solver.
    }
    destruct (decide (as_var x ∈ formula_fvars A)).
    - replace (formula_fvars A ∖ {[₀x]} ∪ {[as_var x]})
        with (formula_fvars A ∖ {[₀x]}) by set_solver...
    - rewrite set_to_list_union_perm by set_solver. rewrite Permutation_app_comm.
      rewrite filter_app. rewrite set_to_list_singleton, fmap_app. simpl...
  Qed.

  Lemma finalized_initial_fvars_NoDup A : NoDup (finalized_initial_fvars A).
  Proof with auto.
    unfold finalized_initial_fvars, initial_fvars. induction (formula_fvars A) using set_ind_L.
    - rewrite set_to_list_empty. simpl. constructor.
    - rewrite set_to_list_union_perm by set_solver. rewrite set_to_list_singleton.
      simpl. rewrite filter_cons... destruct (decide _)... rewrite fmap_cons.
      constructor... inversion IHg; [set_solver|]. rewrite H0. contradict H.
      apply elem_of_list_fmap in H as (?&?&?). apply elem_of_list_filter in H3 as [].
      apply to_final_var_inj_initial in H... set_solver.
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

Arguments final_term M : clear implicits.
Arguments final_formula M : clear implicits.

Section lemmas.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

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
    list_to_set ↑₀ xs1 ## ⋃ (@term_fvars M <$> ⇑ₓ xs2).
  Proof.
    intros. set_unfold. intros x (x'&->&?) (fvars&?&tx&->&y&->&?). set_solver.
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

Global Hint Resolve disjoint_initial_var_of : core.
Global Hint Resolve NoDup_initial_var_of : core.
Global Hint Resolve NoDup_as_var : core.
Global Hint Resolve disjoint_initial_var_of_term_fvars : core.

Tactic Notation "mk_fresh" uconstr(X) "as" ident(x) :=
  let H := fresh in
  pose proof (fresh_var_fresh ""%string X) as H;
  let Hfinal := fresh "Hfinal" in
  pose proof (fresh_var_final ""%string X) as Hfinal;
  repeat rewrite not_elem_of_union in H;
  let E := fresh in
  remember (fresh_var ""%string X) as x eqn:E;
  clear E.

Tactic Notation "mk_fresh" uconstr(y) uconstr(X) "as" ident(x) :=
  let H := fresh in
  pose proof (fresh_var_fresh y X) as H;
  let Hfinal := fresh "Hfinal" in
  try pose proof (fresh_var_final y X) as Hfinal;
  repeat rewrite not_elem_of_union in H;
  let E := fresh in
  remember (fresh_var y X) as x eqn:E;
  clear E.

Global Hint Mode VarFinal ! : typeclass_instances.
Global Hint Mode TermFinal ! ! : typeclass_instances.
Global Hint Mode FormulaFinal ! ! : typeclass_instances.

Global Hint Extern 100 (var_final _) => apply var_final_not_initial : core.
Global Hint Resolve var_initial_to_initial_var : core.

Global Hint Extern 0 =>
match goal with
| H : ¬ var_initial (to_initial_var _) |- _ =>
    exfalso; apply H; apply var_initial_to_initial_var
| H : ¬ var_final (as_var ?x) |- _ =>
    destruct (H (var_final_as_var x)) as []
| H : var_final (initial_var_of _) |- _ =>
    apply var_final_initial_var_of in H as []
end : core.

Global Hint Extern 0 (var_final (initial_var_of _)) => apply var_final_initial_var_of : core.
Global Hint Extern 0 (as_var _ = as_var _) => apply as_var_inj : core.
Global Hint Extern 0 (as_final_var (as_var ?x) = ?x) => apply as_final_var_as_var : core.
Global Hint Extern 0 (?x = as_final_var (as_var ?x)) => symmetry; apply as_final_var_as_var : core.
Global Hint Extern 0 (as_var (as_final_var ?x) = ?x) => apply as_var_as_final_var : core.
Global Hint Extern 0 (?x = as_var (as_final_var ?x)) => symmetry; apply as_var_as_final_var : core.

Global Hint Extern 0 =>
  match goal with
  | H1 : var_final ?x, H2 : ?x = initial_var_of ?y |- _ =>
      apply (var_final_ne_initial_var_of x y H1) in H2 as []
  | H1 : var_final ?x, H2 : initial_var_of ?y = ?x |- _ =>
      symmetry in H2;
      apply (var_final_ne_initial_var_of x y H1) in H2 as []
  end : core.

Global Hint Extern 0 =>
  match goal with
  | H : var_final ?x     |- VarFinal ?x => apply H
  | H : term_final ?t    |- TermFinal ?t => apply H
  | H : formula_final ?t |- FormulaFinal ?t => apply H
  end : typeclass_instances.

Global Instance set_unfold_to_final_var_initial_var_of {C}
    x (X : C) P `{ElemOf final_variable C} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (to_final_var (₀x)) X P.
Proof. by rewrite to_final_var_initial_var_of. Qed.

Global Instance set_unfold_to_final_var_as_var {C}
    (x : final_variable) (X : C) P `{ElemOf final_variable C} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (to_final_var (as_var x)) X P.
Proof. by rewrite to_final_var_as_var. Qed.

Global Instance set_unfold_as_final_var_as_var {C}
    (x : final_variable) (X : C) P `{ElemOf final_variable C} `{VarFinal x} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (as_final_var (as_var x)) X P.
Proof. by rewrite as_final_var_as_var. Qed.

Global Instance set_unfold_as_var_as_final_var {C}
    (x : variable) (X : C) P `{ElemOf variable C} `{VarFinal x} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (as_var (as_final_var x)) X P.
Proof. by rewrite as_var_as_final_var. Qed.

Global Instance set_unfold_as_var_to_final_var {C}
    (x : variable) (X : C) P `{ElemOf variable C} `{VarFinal x} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (as_var (to_final_var x)) X P.
Proof. by rewrite as_var_to_final_var_final. Qed.

Global Instance set_unfold_elem_of_term_fvars_of_initial_vars {M} x w Q :
  SetUnfoldElemOf (to_final_var x) w Q →
  SetUnfoldElemOf x
    (⋃ (term_fvars <$> (@TVar M <$> (initial_var_of <$> w))))
    (¬ var_final x ∧ Q).
Proof with auto.
  constructor. set_unfold. split.
  - intros (t&?&tx&->&x'&->&?). set_unfold in H0. subst x. split... apply H.
    rewrite to_final_var_initial_var_of...
  - intros []. exists x. simpl. split; [set_solver|]. exists x. split...
    exists (to_final_var x). apply H in H1. split... unfold var_final in H0.
    apply not_false_is_true in H0. unfold initial_var_of. destruct x. simpl. f_equal...
Qed.

Global Instance set_unfold_elem_of_term_fvars_of_vars {M} x w Q :
  SetUnfoldElemOf (to_final_var x) w Q →
  SetUnfoldElemOf x
    (⋃ (term_fvars <$> (@TVar M <$> (as_var <$> w))))
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

Global Instance set_unfold_elem_of_list_to_set_initials_of_final_variables x w Q :
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
