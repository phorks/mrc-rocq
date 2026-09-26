From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Model.
From MRC Require Import Smp.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SyntacticFacts.

(* TODO: move these to stdppp *)
Lemma dne {P : Prop} `{Decision P} : ¬ (¬ P) ↔ P.
Proof. destruct (decide P); tauto. Qed.

Lemma not_or {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q.
Proof. tauto. Qed.

Notation PredDecision P := (∀ x, Decision (P x)).

Global Instance list_empty {A} : Empty (list A) := [].

Class LawfulEmpty (A B : Type) `{ElemOf A B} `{Empty B} :=
  empty_forall : ∀ (x : A), ¬ x ∈ (@empty B _).

Global Instance gset_empty_lawful {A} `{Countable A} : LawfulEmpty _ (gset A).
Proof. intros x. set_solver. Qed.

Global Instance list_empty_lawful {A} : LawfulEmpty _ (list A).
Proof. intros x. set_solver. Qed.

Class LawfulSingleton (A B : Type) `{ElemOf A B} `{Singleton A B} :=
  singleton_forall : ∀ (x y : A), x ∈ (@singleton A B _ y) ↔ x = y.

Global Instance gset_singleton_lawful {A} `{Countable A} : LawfulSingleton A (gset A).
Proof. intros ??. set_solver. Qed.

Class Every (A B : Type) := every : ∀ (P : A → Prop) `{PredDecision P}, B → Prop.
Global Hint Mode Every - ! : typeclass_instances.

Class LawfulEvery (A B : Type) `{Every A B} `{ElemOf A B} :=
  every_forall : ∀ P {P_dec} (X : B), @every _ _ _ P P_dec X ↔ ∀ x, x ∈ X → P x.

Lemma every_elim {A B} `{LawfulEvery A B} :
  ∀ {x : A} {X : B} {P P_dec}, @every _ _ _ P P_dec X → x ∈ X → P x.
Proof with auto. intros. eapply every_forall with (X:=X)... Qed.

Lemma every_empty {A B} `{LawfulEvery A B, !Empty B, !LawfulEmpty A B}
    {P : A → Prop} `{PredDecision P} :
  every (B:=B) P ∅.
Proof. rewrite every_forall. intros. by eapply empty_forall in H2. Qed.

Global Hint Extern 0 (every _ ∅) => apply every_empty : core.

Lemma every_singleton {A B} `{LawfulEvery A B, !Singleton A B, !LawfulSingleton A B}
    {P : A → Prop} `{PredDecision P} x :
  every (B:=B) P {[x]} ↔ P x.
Proof. rewrite every_forall. setoid_rewrite singleton_forall. naive_solver. Qed.

Global Instance set_unfold_every_singleton {A} {x : A}
    `{LawfulEvery A B, !Singleton A B, !LawfulSingleton A B}
    {P : A → Prop} `{PredDecision P} :
  SetUnfold (every (B:=B) P {[x]}) (P x).
Proof. constructor. by rewrite every_singleton. Qed.

Global Instance smp_every_singleton {A} {x : A}
    `{LawfulEvery A B, !Singleton A B, !LawfulSingleton A B}
    {P : A → Prop} `{PredDecision P} :
  Smp (every (B:=B) P {[x]}) (P x).
Proof. constructor. by rewrite every_singleton. Qed.

Global Instance gset_every {A} `{Countable A} : Every A (gset A) :=
  λ P _ X, filter (λ x, ¬ P x) X = ∅.

Global Instance gset_every_lawful {A} `{Countable A} : @LawfulEvery _ (gset A) gset_every _.
Proof.
  intros ???. induction X using set_ind_L; [set_solver|].
  unfold every, gset_every. set_unfold. setoid_rewrite not_and_l. setoid_rewrite dne.
  setoid_rewrite not_or. split; intros; [set_solver|]. rename x0 into y.
  destruct (decide (y = x)); [set_solver|]. destruct (decide (y ∈ X)); set_solver.
Qed.

Global Instance gset_every_dec {A} `{Countable A} :
  ∀ P P_dec (X : gset A), Decision (@every _ _ gset_every P P_dec X).
Proof. unfold every, gset_every. solve_decision. Qed.

Global Instance gset_every_pi {A} `{Countable A} :
  ∀ P P_dec (X : gset A), ProofIrrel (@every _ _ gset_every P P_dec X).
Proof. intros. apply eq_pi. solve_decision. Qed.

Global Instance list_every {A} : Every A (list A) := λ P _ l, Forall P l.

Global Instance list_every_lawful {A} : @LawfulEvery _ (list A) list_every _.
Proof.
  intros ???. unfold every, list_every. by rewrite Forall_forall.
Qed.

Global Instance list_every_dec {A} :
  ∀ P P_dec (l : list A), Decision (@every _ _ list_every P P_dec l).
Proof. unfold every. solve_decision. Qed.

(* TODO: move this to the head of stdppp *)
From Stdlib Require Import Program.
Global Instance Forall_pi {A} {P : A → Prop} {X : list A} `{∀ x, ProofIrrel (P x)} :
  ProofIrrel (Forall P X).
Proof with auto.
  induction X.
  - intros p q. dependent destruction p. dependent destruction q...
  - intros p q. dependent destruction p. dependent destruction q... f_equal.
    + apply H.
    + apply IHX.
Qed.

Global Instance list_every_pi {A} {P : A → Prop} `{PredDecision P}
    `{∀x, ProofIrrel (P x)} :
  ∀ l, ProofIrrel (@every _ _ list_every P _ l).
Proof. intros. unfold every, list_every. apply Forall_pi. Qed.

Lemma list_every_cons {A} {x : A} {X : list A} {P : A → Prop} `{PredDecision P} :
  every P (x :: X) ↔ P x ∧ every P X.
Proof. unfold every, list_every. do 2 rewrite Forall_forall. set_solver. Qed.

Lemma list_every_app {A} {X Y : list A} {P : A → Prop} `{PredDecision P} :
  every P (X ++ Y) ↔ every P X ∧ every P Y.
Proof. unfold every, list_every. do 3 rewrite Forall_forall. set_solver. Qed.

Global Instance set_unfold_list_every_cons {A} {x : A} {X : list A}
    {P : A → Prop} `{PredDecision P} :
  SetUnfold (every P (x :: X)) (P x ∧ every P X).
Proof. constructor. exact list_every_cons. Qed.

Global Instance smp_list_every_cons {A} {x : A} {X : list A}
    {P : A → Prop} `{PredDecision P} :
  Smp (every P (x :: X)) (P x ∧ every P X).
Proof. constructor. exact list_every_cons. Qed.

Global Instance set_unfold_list_every_app {A} {X Y : list A}
    {P : A → Prop} `{PredDecision P} :
  SetUnfold (every P (X ++ Y)) (every P X ∧ every P Y).
Proof. constructor. exact list_every_app. Qed.

Global Instance smp_list_every_app {A} {X Y : list A}
    {P : A → Prop} `{PredDecision P} :
  Smp (every P (X ++ Y)) (every P X ∧ every P Y).
Proof. constructor. exact list_every_app. Qed.

Section variables.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Notation term := (term M).
  Notation formula := (formula M).

  Implicit Type t : term.
  Implicit Type ts : list term.
  Implicit Type A : formula.

  Definition var_final x := var_is_initial x = false.
  Definition term_final t := every var_final (term_fvars t).
  Definition term_list_final ts := every term_final ts.
  Definition formula_final A := every var_final (formula_fvars A).

  Lemma term_final_alt {t} : term_final t ↔ ∀ x, x ∈ term_fvars t → var_final x.
  Proof. unfold term_final. apply every_forall. Qed.

  Lemma term_list_final_alt {ts} : term_list_final ts ↔
                                     ∀ t x, t ∈ ts → x ∈ term_fvars t → var_final x.
  Proof. unfold term_list_final, term_final. do 2 setoid_rewrite every_forall. naive_solver. Qed.

  Lemma formula_final_alt {A} : formula_final A ↔ ∀ x, x ∈ formula_fvars A → var_final x.
  Proof. apply every_forall. Qed.

  Global Instance set_unfold_term_final {t} :
    SetUnfold (term_final t) (∀ x, x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_final_alt. Qed.
  Global Instance smp_term_final {t} :
    Smp (term_final t) (∀ x, x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_final_alt. Qed.

  Global Instance smp_term_list_final {ts} :
    Smp (term_list_final ts) (∀ t x, t ∈ ts → x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_list_final_alt. Qed.
  Global Instance set_unfold_term_list_final {ts} :
    SetUnfold (term_list_final ts) (∀ t x, t ∈ ts → x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_list_final_alt. Qed.

  Global Instance smp_formula_final {A} :
    Smp (formula_final A) (∀ x, x ∈ formula_fvars A → var_final x).
  Proof. constructor. apply formula_final_alt. Qed.
  Global Instance set_unfold_formula_final {A} :
    SetUnfold (formula_final A) (∀ x, x ∈ formula_fvars A → var_final x).
  Proof. constructor. apply formula_final_alt. Qed.

  Global Instance term_final_pi {t} : ProofIrrel (term_final t).
  Proof. apply gset_every_pi. Qed.

  Global Instance term_list_final_pi {ts} : ProofIrrel (term_list_final ts).
  Proof. apply list_every_pi. Qed.

  Global Instance formula_final_pi {A} : ProofIrrel (formula_final A).
  Proof. apply gset_every_pi. Qed.

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
  Proof. reflexivity. Qed.

  Global Instance as_var_var_final {x} : VarFinal (as_var x).
  Proof. reflexivity. Qed.

  Global Instance fresh_var_final x fvars `{VarFinal x} : VarFinal (fresh_var x fvars).
  Proof with auto.
    unfold VarFinal. generalize dependent x. unfold fresh_var. induction (S (size fvars)); intros.
    - simpl. apply H.
    - simpl. destruct (decide (x ∈ fvars))...
  Qed.

  Lemma var_final_as_var x :
    var_final (as_var x).
  Proof. reflexivity. Qed.

  Lemma var_final_initial_var_of x :
    ¬ var_final (initial_var_of x).
  Proof. cbv. discriminate. Qed.

  Local Notation final_f := (λ x r, bool_decide (var_final x) && r) (only parsing).
  Local Lemma set_fold_union_bool {X Y : gset variable} {b : bool} :
    set_fold final_f b (X ∪ Y : gset variable) =
      set_fold final_f (set_fold final_f b (X : gset variable)) Y.
  Proof.
    apply set_fold_union_strong; try typeclasses eauto.
    - intros. generalize (bool_decide (var_final x)) as b1. intros.
      destruct b1; destruct b'; simpl; done.
    - intros. generalize (bool_decide (var_final x1)) as b1.
      generalize (bool_decide (var_final x2)) as b2. intros.
      destruct b1; destruct b2; simpl; done.
  Qed.

  Local Lemma set_fold_union_singleton_bool {x : variable} {X : gset variable} {b : bool} :
    set_fold final_f b ({[x]} ∪ X : gset variable) =
      set_fold final_f (bool_decide (var_final x) && b) X.
  Proof.
    rewrite set_fold_union_bool. rewrite set_fold_singleton. done.
  Qed.

  Class TermFinal t := term_is_final : term_final t.
  Class TermListFinal ts := term_list_is_final : term_list_final ts.

  Global Instance set_unfold_TermFinal {t} :
    SetUnfold (TermFinal t) (∀ x, x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_final_alt. Qed.
  Global Instance smp_TermFinal {t} :
    Smp (TermFinal t) (∀ x, x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_final_alt. Qed.

  Global Instance smp_TermListFinal {ts} :
    Smp (TermListFinal ts) (∀ t x, t ∈ ts → x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_list_final_alt. Qed.
  Global Instance set_unfold_TermListFinal {ts} :
    SetUnfold (TermListFinal ts) (∀ t x, t ∈ ts → x ∈ term_fvars t → var_final x).
  Proof. constructor. apply term_list_final_alt. Qed.

  Global Instance TermFinal_pi {t} : ProofIrrel (TermFinal t).
  Proof with auto. apply term_final_pi. Qed.

  Global Instance TermListFinal_pi {ts} : ProofIrrel (TermListFinal ts).
  Proof with auto. apply term_list_final_pi. Qed.

  Global Instance term_list_final_nil : TermListFinal [].
  Proof. unfold TermListFinal, term_list_final. auto. auto with core. apply every_empty. Qed.

  Global Instance term_list_final_cons {t ts} `{TermFinal t} `{TermListFinal ts} :
    TermListFinal (t :: ts).
  Proof. unfold TermListFinal, term_list_final. by apply list_every_cons. Qed.

  Global Instance const_term_final {v} : TermFinal (TConst v).
  Proof. unfold TermFinal, term_final. simpl. intros. set_solver. Qed.

  Global Instance var_term_final {x} `{VarFinal x} : TermFinal (TVar x).
  Proof. unfold TermFinal. unfold term_final. simpl. intros. by smp. Qed.

  Global Instance app_term_final {fsym args} `{TermListFinal args} :
    TermFinal (TApp fsym args).
  Proof.
    unfold TermFinal. unfold TermListFinal in H. smp. simpl. intros.
    apply elem_of_union_list in H0 as (fvars&?&?). apply elem_of_list_fmap in H0 as (arg&?&?).
    subst. apply H with (t:=arg); assumption.
  Qed.

  Global Instance subst_term_final {t x t'} `{TermFinal t} `{TermFinal t'} :
    TermFinal (subst_term t x t').
  Proof with auto.
    unfold TermFinal in *. smp. intros.
    destruct (decide (x ∈ term_fvars t)).
    - rewrite fvars_subst_term_free with (t':=t') in H1... set_solver.
    - rewrite subst_term_non_free in H1...
  Qed.

  Global Instance final_term_term_final {t : final_term} : TermFinal (as_term t).
  Proof. apply (final_term_final t). Defined.

  Class FormulaFinal A := formula_is_final : formula_final A.

  Global Instance smp_FormulaFinal {A} :
    Smp (FormulaFinal A) (∀ x, x ∈ formula_fvars A → var_final x).
  Proof. constructor. apply formula_final_alt. Qed.
  Global Instance set_unfold_FormulaFinal {A} :
    SetUnfold (FormulaFinal A) (∀ x, x ∈ formula_fvars A → var_final x).
  Proof. constructor. apply formula_final_alt. Qed.

  Global Instance true_atomic_formula_final : FormulaFinal <! true !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Qed.

  Global Instance false_atomic_formula_final : FormulaFinal <! false !>.
  Proof. unfold FormulaFinal, formula_final. simpl. intros. set_solver. Qed.

  Global Instance eq_atomic_formula_final {t1 t2} `{TermFinal t1} `{TermFinal t2} :
    FormulaFinal <! ⌜t1 = t2⌝ !>.
  Proof. unfold FormulaFinal, formula_final. unfold TermFinal in *. smp. set_solver. Qed.

  Global Instance hastype_final_final {t ty} `{!TermFinal t}
    : FormulaFinal (FAtom (AT_HasType t ty)).
  Proof. smp. intros x H. smp. set_solver. Qed.

  Global Instance pred_atomic_formula_final {psym args} `{TermListFinal args} :
    FormulaFinal (FAtom (AT_Pred psym args)).
  Proof.
    smp. intros. apply elem_of_union_list in H0 as (fvars&?&?).
    apply elem_of_list_fmap in H0 as (arg&?&?). subst. smp.
    apply H with (t:=arg); assumption.
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
    smp. intros. apply fvars_subst_superset in H1. set_solver.
  Qed.

  Global Instance final_formula_formula_final {A : final_formula} : FormulaFinal (as_formula A).
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

  Lemma as_final_term_as_term (t : final_term) : as_final_term (as_term t) = t.
  Proof. destruct t. simpl. unfold as_final_term. f_equal. Qed.

  Lemma as_term_as_final_term t `{TermFinal t} : as_term (as_final_term t) = t.
  Proof. unfold as_final_term, as_term. reflexivity. Qed.

  Definition as_final_formula A `{H : FormulaFinal A} : final_formula :=
    mkFinalFormula A (@formula_is_final A H).

  Lemma as_formula_term_as_formula (A : final_formula) : as_final_formula (as_formula A) = A.
  Proof.
    unfold as_final_formula, formula_is_final. destruct A. simpl. reflexivity.
  Qed.

  Lemma as_formula_as_final_formula A `{FormulaFinal A} : as_formula (as_final_formula A) = A.
  Proof. unfold as_final_formula, as_formula. reflexivity. Qed.

  Lemma initial_var_of_elem_of_formula_fvars x A :
    initial_var_of x ∈ formula_fvars A →
    ¬ formula_final A.
  Proof. intros. intros contra. smp. apply contra in H. cbv in H. discriminate. Qed.

  Lemma elem_of_fvars_final_formula_inv A x `{FormulaFinal A} :
    x ∈ formula_fvars A →
    var_final x.
  Proof. intros. smp. apply H in H0. assumption. Qed.
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

  Lemma to_initial_var_inj' x y :
    var_final x →
    var_final y →
    to_initial_var x = to_initial_var y →
    x = y.
  Proof.
    intros. destruct x. destruct y. unfold var_final in H, H0. simpl in H, H0.
    inversion H1. subst. reflexivity.
  Qed.

  Lemma to_initial_var_inj x y `{!VarFinal x} `{!VarFinal y} :
    to_initial_var x = to_initial_var y →
    x = y.
  Proof with auto. intros. apply to_initial_var_inj'... Qed.

  Global Instance ffequiv : Equiv final_formula := λ F1 F2, as_formula F1 ≡ as_formula F2.
  Global Instance ffequiv_refl : Reflexive ffequiv.
  Proof with auto. split; done. Qed.

  Global Instance ffequiv_sym : Symmetric ffequiv.
  Proof with auto. intros A B. unfold ffequiv. done. Qed.

  Global Instance ffequiv_trans : Transitive ffequiv.
  Proof with auto. intros A B C ??. unfold ffequiv in *. trans B... Qed.

  Global Instance ffequiv_equiv : Equivalence ffequiv.
  Proof. split; [exact ffequiv_refl | exact ffequiv_sym | exact ffequiv_trans]. Qed.

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
