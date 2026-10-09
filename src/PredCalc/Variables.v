From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Lib.
From MRC Require Import Model.
From MRC.PredCalc Require Import Basic Equiv SyntacticFacts SemanticFacts.

Section variables.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Notation term := (term M).
  Notation formula := (formula M).

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

  Lemma term_list_is_final' ts t `{!TermListFinal ts} :
    t ∈ ts →
    term_final t.
  Proof with auto.
    intros. pose proof (@term_list_is_final ts _). unfold term_list_final in H0.
    apply elem_of_list_lookup_1 in H as (i&?). eapply Forall_lookup_1 in H; [| exact H0]...
  Qed.

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

  Global Instance set_unfold_initial_var_elem_of_final_formula {x} {A : formula} `{!FormulaFinal A} :
    SetUnfoldElemOf ₀x (formula_fvars A) False.
  Proof with auto.
    constructor. split; intros; [|done]. apply formula_is_final in H.
    apply var_final_initial_var_of in H as [].
  Qed.

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

  Lemma finalized_initial_fvars_final A `{!FormulaFinal A} :
    finalized_initial_fvars A = [].
  Proof with auto.
    enough (finalized_initial_fvars A ≡ₚ []).
    { by apply Permutation_nil_r in H. }
    unfold finalized_initial_fvars, initial_fvars.
    rename FormulaFinal0 into H. unfold FormulaFinal, formula_final in H.
    induction (formula_fvars A) using set_ind_L...
    rewrite filter_set_to_list_delete_union_singleton_l.
    - apply IHg. set_solver.
    - apply var_final_not_initial. set_solver.
  Qed.

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
    rewrite list_delete_elem_id.
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
Hint Extern 5 (FormulaFinal _) => typeclasses eauto : core.

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

Section facts.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).
  Local Notation final_term := (final_term M).

  Lemma disjoint_initial_var_of_term_fvars xs1 xs2 :
    xs1 ## xs2 →
    list_to_set ↑₀ xs1 ## ⋃ (@term_fvars M <$> ⇑ₓ xs2).
  Proof.
    intros. set_unfold. intros. destruct H1 as (fvars&?&tx&->&y&->&?). set_solver.
  Qed.

  Global Instance as_term_term_list_final {ts : list final_term} : TermListFinal (⇑ₜ ts).
  Proof.
    unfold TermListFinal, term_list_final. rewrite Forall_lookup. intros ? t ?.
    apply elem_of_list_lookup_2 in H. set_unfold in H. destruct H as (t'&->&?).
    apply final_term_final.
  Qed.

End facts.

Global Hint Resolve disjoint_initial_var_of_term_fvars : core.

Global Hint Mode TermFinal ! ! : typeclass_instances.
Global Hint Mode FormulaFinal ! ! : typeclass_instances.

Global Hint Extern 0 =>
  match goal with
  | H : term_final ?t    |- TermFinal ?t => apply H
  | H : formula_final ?t |- FormulaFinal ?t => apply H
  end : typeclass_instances.

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

Global Instance set_unfold_elem_of_initial_var_of_final_term_fvars {M} {x}
  {t : final_term M} :
  SetUnfoldElemOf (₀x) (term_fvars t) False.
Proof.
  constructor. split; [|done]. intros. by apply term_is_final in H.
Qed.

Global Instance set_unfold_elem_of_initial_var_of_final_formula_fvars {M} {x}
  {A : final_formula M} :
  SetUnfoldElemOf (₀x) (formula_fvars A) False.
Proof. constructor. split; [|done]. intros. by apply formula_is_final in H. Qed.

Section initials_closed.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Implicit Types A B C : formula.
  Implicit Types w xs : list final_variable.

  Definition initials_closed A w := ∀ x, x ∉ w → <! A [₀x\x] !> ≡ A.

  Lemma initials_closed_alt' A w :
    initials_closed A w ↔
    ∀ x, x ∉ w → ₀x ∈ formula_fvars A → <! A [₀x\x] !> ≡ A.
  Proof with auto.
    unfold initials_closed; split; intros... destruct (decide (₀x ∈ formula_fvars A)).
    - rewrite H...
    - rewrite subst_non_free...
  Qed.

  Lemma initials_closed_alt A w :
    (∀ x, var_initial x → x ∈ formula_fvars A → to_final_var x ∈ w) →
    initials_closed A w.
  Proof.
    rewrite initials_closed_alt'. intros H x??. ospecialize (H ₀x _ H1); [done|].
    by rewrite to_final_var_initial_var_of in H.
  Qed.

  Lemma initials_closed_strong A w :
    initials_closed A w →
    (∀ x t, x ∉ w → <! A [₀x\t] !> ≡ A).
  Proof with auto.
    intros.
    intros σ. destruct (feval_lem σ <! A [₀x \ t] !>); destruct (feval_lem σ <! A !>).
    1,4: naive_solver.
    - exfalso. pose proof (teval_total σ t) as [v ?].
      rewrite feval_subst with (v:=v) in H1... rewrite <- (H x) in H1...
      opose proof (teval_total _ x) as [v' ?].
      rewrite feval_subst with (v:=v') in H1; [|exact H4].
      rewrite teval_delete_state_var_head in H4 by set_solver.
      unfold state in *. rewrite insert_insert in H1.
      rewrite <- feval_subst in H1 by exact H4. rewrite (H x) in H1...
    - exfalso. pose proof (teval_total σ t) as [v ?].
      rewrite feval_subst with (v:=v) in H1... rewrite <- (H x) in H1...
      opose proof (teval_total _ x) as [v' ?].
      rewrite feval_subst with (v:=v') in H1; [|exact H4].
      rewrite teval_delete_state_var_head in H4 by set_solver.
      unfold state in *. rewrite insert_insert in H1.
      rewrite <- feval_subst in H1 by exact H4. rewrite (H x) in H1...
  Qed.

  Global Instance initials_closed_proper : Proper ((=) ==> (≡ₚ) ==> iff) initials_closed.
  Proof.
    intros A ? -> w1 w2 ?. unfold initials_closed. by setoid_rewrite H.
  Qed.

  Lemma initials_closed_final A `{!FormulaFinal A} :
    ∀ w, initials_closed A w.
  Proof.
    setoid_rewrite initials_closed_alt'. intros w x ??.
    apply formula_is_final in H0. by apply var_final_not_initial in H0.
  Qed.

  Lemma initials_closed_app_l A w1 w2 :
    initials_closed A w1 →
    initials_closed A (w1 ++ w2).
  Proof with auto. unfold initials_closed in *. intros. apply H. set_solver. Qed.

  Lemma initials_closed_app_r A w1 w2 :
    initials_closed A w2 →
    initials_closed A (w1 ++ w2).
  Proof with auto. unfold initials_closed in *. intros. apply H. set_solver. Qed.

  Lemma initials_closed_and A B w :
    initials_closed A w →
    initials_closed B w →
    initials_closed <! A ∧ B !> w.
  Proof with auto.
    intros. unfold initials_closed in *. intros. rewrite simpl_subst_and.
    rewrite H... rewrite H0...
  Qed.

End initials_closed.

Global Hint Extern 100 (initials_closed _ _) => apply initials_closed_final : core.

Global Hint Extern 0 =>
  match goal with
  | H : initials_closed ?A ?w1 |- initials_closed ?A (?w1 ++ _) =>
      apply initials_closed_app_l; exact H
  | H : initials_closed ?A ?w2 |- initials_closed ?A (_ ++ ?wp2) =>
      apply initials_closed_app_r; exact H
  end : core.
