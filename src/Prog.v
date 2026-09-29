From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From Equations Require Import Equations.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section moveme.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Implicit Types (t : term).
  Implicit Types (A : formula).

  Lemma subst_non_free A x t :
    x ∉ formula_fvars A →
    <! A[x \ t] !> = A.
  Proof with auto.
    apply subst_formula_ind with (P:=λ A B, x ∉ formula_fvars B → A = B); intros.
    - rewrite subst_af_non_free...
    - f_equiv...
    - simpl in H1. apply not_elem_of_union in H1 as [? ?].
      f_equiv; [apply H|apply H0]...
    - simpl in H1. apply not_elem_of_union in H1 as [? ?].
      f_equiv; [apply H|apply H0]...
    - reflexivity.
    - simpl in H2. apply not_elem_of_difference in H2. rewrite elem_of_singleton in H2.
      destruct H2; subst; contradiction.
  Qed.


  Lemma equiv_subst {x} {t : term} {A B : formula} :
    x ∉ formula_fvars A →
    A ≡ B →
    <! B[x \ t] !> ≡ B.
  Proof with auto.
    intros. trans A... rewrite <- fequiv_subst_non_free with (A:=A) (x:=x) (t:=t)...
    f_equiv...
  Qed.

  Lemma fvars_subst_superset' A x (t : term) :
    formula_fvars (<! A[x \ t] !>) ⊆ (formula_fvars A ∖ {[x]}) ∪ term_fvars t.
  Proof with auto.
    destruct (decide (x ∈ formula_fvars A)).
    - rewrite fvars_subst_free...
    - rewrite fvars_subst_non_free... set_solver.
  Qed.

  Lemma elem_of_subst_fvars x A y (t : term) :
    x ∈ formula_fvars (<! A[y \ t] !>) ↔
      (x ∈ formula_fvars A ∧ x ≠ y) ∨ (y ∈ formula_fvars A ∧ x ∈ term_fvars t).
  Proof with auto.
    destruct (decide (y ∈ formula_fvars A)).
    + rewrite fvars_subst_free... set_solver.
    + rewrite fvars_subst_non_free... set_solver.
  Qed.

  Global Instance fresh_var_final x fvars `{VarFinal x} : VarFinal (fresh_var x fvars).
  Proof with auto.
    unfold VarFinal. generalize dependent x. unfold fresh_var. induction (S (size fvars)); intros.
    - simpl. apply H.
    - simpl. destruct (decide (x ∈ fvars)).
      + apply IHn. unfold VarFinal, var_final in H. destruct x. simpl in H.
        rewrite H. reflexivity.
      + apply H.
  Qed.


  Global Instance f_orlist_formula_final {Bs : list final_formula} :
    FormulaFinal <! ∨* ⤊ Bs !>.
  Proof with auto. induction Bs... Qed.

  Global Instance f_andlist_formula_final {Bs : list final_formula} :
    FormulaFinal <! ∧* ⤊ Bs !>.
  Proof with auto. induction Bs... Qed.

  Lemma as_final_var_as_var {x : final_variable} {H} :
    @as_final_var (as_var x) H = x.
  Proof. destruct x. unfold as_final_var. simpl. f_equal. Qed.

  Global Instance term_final_pi {t} : ProofIrrel (term_final t).
  Proof.
    unfold term_final. intros p q. apply functional_extensionality_dep. intros.
    apply functional_extensionality_dep. intros H. apply eq_pi. solve_decision.
  Qed.

  Lemma as_final_term_eq {t} {t' : final_term} {H} :
    t = as_term t' →
    @as_final_term _ t H = t'.
  Proof.
    intros. subst. destruct t'. unfold as_final_term. simpl. f_equal. unfold TermFinal in H.
    apply term_final_pi.
  Qed.

  Global Instance formula_final_pi {A} : ProofIrrel (formula_final A).
  Proof.
    unfold formula_final. intros p q. apply functional_extensionality_dep. intros.
    apply functional_extensionality_dep. intros H. apply eq_pi. solve_decision.
  Qed.

  Lemma as_final_formula_eq {A} {A' : final_formula} {H} :
    A = as_formula A' →
    @as_final_formula _ A H = A'.
  Proof.
    intros. subst. destruct A'. unfold as_final_formula. simpl. f_equal. unfold FormulaFinal in H.
    apply formula_final_pi.
  Qed.

  Lemma msubst_subst_comm' (A : formula) x t xs ts `{!OfSameLength xs ts} :
    x ∉ xs →
    x ∉ ⋃ (term_fvars <$> ts) →
    list_to_set xs ## term_fvars t →
    <! A[[*xs \ *ts]][x \ t] !> ≡ <! A[x \ t][[*xs \ *ts]] !>.
  Proof with auto.
    intros. rewrite <- msubst_extract_l... rewrite msubst_extract_r...
  Qed.


  Lemma fequiv_fent_iff {A B : formula} :
    A ≡ B ↔ A ⇛ B ∧ B ⇛ A.
  Proof with auto.
    split.
    - intros. split; intros σ; apply H.
    - intros []. split; intros...
  Qed.

  Lemma fold_fent {A B : formula} :
    (∀ σ, feval σ A → feval σ B) ↔ A ⇛ B.
  Proof. reflexivity. Qed.

  Lemma elem_of_set_to_list {x} {X : gset variable} :
    x ∈ set_to_list X ↔ x ∈ X.
  Proof with auto.
    unfold elem_of at 1. split; intros.
    - induction X using set_ind_L.
      + rewrite set_to_list_empty in H. inversion H.
      + rewrite set_to_list_union_singleton_l_perm in H... set_solver.
    - induction X using set_ind_L.
      + set_solver.
      + rewrite set_to_list_union_singleton_l_perm... set_solver.
  Qed.

  Global Instance set_unfold_elem_of_set_to_list x (X : gset variable) P :
    (∀ x, SetUnfoldElemOf x X (P x)) →
    SetUnfoldElemOf x
      (set_to_list X)
      (P x) | 10.
  Proof. constructor. rewrite elem_of_set_to_list. apply H. Qed.

Notation "t [ₜ x \ u ]" := (subst_term t x u)
                            (in custom formula at level 74, left associativity,
                                t custom formula,
                                x constr at level 0, u custom term) : refiney_scope.


  Lemma term_subst_trans : ∀ (t : term) (x1 x2 : variable) (u : term),
      x2 ∉ term_fvars t →
      <! t [ₜ x1 \ x2][ₜ x2 \ u] !> = <! t [ₜ x1 \ u] !>.
  Proof with auto.
    intros. induction t...
    - simpl. destruct (decide _).
      + subst. simpl. destruct (decide _)... done.
      + simpl. destruct (decide _)... subst. set_solver.
    - simpl. f_equiv. induction args... simpl. f_equiv.
      + apply H0.
        * left...
        * set_solver.
      + apply IHargs.
        * intros. apply H0... right...
        * set_solver.
  Qed.

  Lemma fvars_term_subst_non_free t x u :
    x ∉ term_fvars t →
    term_fvars (<! t[ₜ x \ u] !>) = term_fvars t.
  Proof with auto.
    intros. rewrite subst_term_non_free...
  Qed.

  Lemma fvars_term_subst_superset t x (u : term) :
    term_fvars (<! t[ₜ x \ u] !>) ⊆ (term_fvars t ∖ {[x]}) ∪ term_fvars u.
  Proof with auto.
    destruct (decide (x ∈ term_fvars t)).
    - rewrite fvars_subst_term_free...
    - rewrite fvars_term_subst_non_free... set_solver.
  Qed.

  Lemma subst_subst_l A x1 t1 x2 t2 (z : variable) :
    x1 ≠ x2 →
    z ≠ x1 →
    z ≠ x2 →
    z ∉ formula_fvars A →
    z ∉ term_fvars t1 →
    z ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    <! A [x1 \ t1][x2 \ t2] !> ≡ <! A [x2 \ t2[x1 \ z]][x1 \ t1][z \ x1] !>.
  Proof with auto.
    intros ? Hz1 Hz2 Hz3 Hz4 Hz5 Hfree σ.
    opose proof (teval_total σ _) as [v1 ?].
    rewrite feval_subst with (v:=v1) by exact H0.
    opose proof (teval_total _ _) as [v2 ?].
    rewrite feval_subst with (v:=v2) by exact H1.
    opose proof (teval_total σ _) as [v3 ?].
    rewrite feval_subst with (v:=v3) by exact H2.
    opose proof (teval_total _ _) as [v4 ?].
    rewrite feval_subst with (v:=v4) by exact H3.
    opose proof (teval_total _ _) as [v5 ?].
    rewrite feval_subst with (v:=v5) by exact H4.
    unfold state. rewrite insert_commute with (j:=z)...
    rewrite insert_commute with (j:=z)... rewrite feval_delete_state_var_head with (x:=z)...
    f_equiv. unfold state. apply map_eq. intros x.
    destruct (decide (x = x1)); destruct (decide (x = x2)).
    1:{ subst. contradiction. }
    3:{ repeat rewrite lookup_insert_ne... }
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t1).
      + rewrite <- teval_delete_state_var_head; [exact H1|]...
      + rewrite <- teval_delete_state_var_head; [exact H3|]...
    - subst. rewrite lookup_insert. rewrite lookup_insert_ne... rewrite lookup_insert.
      f_equal. eapply (teval_det t2).
      + exact H0.
      + rewrite teval_delete_state_var_head in H4.
        2:{ intros ?. apply fvars_term_subst_superset in H5. set_solver. }
        erewrite teval_subst in H4; [|exact H2]. rewrite term_subst_trans in H4...
        rewrite subst_term_diag in H4...
  Qed.

  Lemma subst_subst_eq A x t u :
    <! A [x \ t[x \ u]] !> ≡ <! A [x \ t] [x \ u] !>.
  Proof with auto.
    intros σ.
    opose proof (teval_total σ _) as [v1 ?].
    rewrite feval_subst with (v:=v1) by exact H.
    opose proof (teval_total _ _) as [v2 ?].
    rewrite feval_subst with (v:=v2) by exact H0.
    opose proof (teval_total _ _) as [v3 ?].
    rewrite feval_subst with (v:=v3) by exact H1.
    f_equiv. unfold state. rewrite insert_insert.
    apply map_eq. intros y. destruct (decide (x = y)).
    2:{ repeat rewrite lookup_insert_ne... }
    subst. do 2 rewrite lookup_insert. f_equal. eapply (teval_det <! t[ₜ y\u] !>).
    - exact H.
    - erewrite <- teval_subst with (H:=H0)...
  Qed.

  Definition var_initial x := var_is_initial x = true.

  Lemma initial_var_of_to_final_var x :
    var_initial x → ₀(to_final_var x) = x.
  Proof.
    unfold to_final_var, initial_var_of, var_initial. destruct x. simpl. intros; by subst.
  Qed.

  Lemma initial_var_of_to_final_var_inv {x : variable} :
    ₀(to_final_var x) = x → var_initial x.
  Proof.
    unfold to_final_var, initial_var_of, var_initial. destruct x. simpl. by inversion 1.
  Qed.

  Lemma initial_var_of_initial x : var_initial ₀x.
  Proof. done. Qed.

  Lemma fresh_var_ne_inv y X :
    fresh_var y X ≠ y →
    y ∈ X.
  Proof with auto.
    intros. unfold fresh_var in H. induction X using set_ind_L.
    - unfold fresh_var_aux in H. destruct (decide (y ∈ ∅))... set_solver.
    - unfold fresh_var_aux in H. simpl in H. destruct (decide (y ∈ _))... set_solver.
  Qed.

  Definition final_fvars A :=
    to_final_var <$> (set_to_list (filter var_final (formula_fvars A))).
  Definition initial_fvars A := filter var_initial (set_to_list (formula_fvars A)).
  Definition finalized_initial_fvars A := to_final_var <$> (initial_fvars A).
  Definition subst_all_initials A := subst_initials A (finalized_initial_fvars A).

  (* Lemma not_elem_of_finalized_initial_fvars {x A} : *)
  (*   x ∉ finalized_initial_fvars A ↔ ₀x ∈ formula_fvars A. *)
  (* Proof with auto. *)
  (*   unfold finalized_initial_fvars. rewrite elem_of_list_fmap. *)
  (*   setoid_rewrite elem_of_initial_fvars. split; intros. *)
  (*   - destruct H as (y&->&?&?). rewrite initial_var_of_to_final_var... *)
  (*   - exists ₀x. rewrite to_final_var_initial_var_of. split_and!... done. *)
  (* Qed. *)

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

  Lemma var_final_not_initial {x} :
    var_final x ↔ ¬ var_initial x.
  Proof. unfold var_final, var_initial. by destruct (var_is_initial x). Qed.

  Lemma var_initial_not_final {x} :
    var_initial x ↔ ¬ var_final x.
  Proof. unfold var_final, var_initial. by destruct (var_is_initial x). Qed.

  Lemma var_initial_or_final x :
    var_initial x ∨ var_final x.
  Proof. unfold var_initial, var_final. destruct (var_is_initial x); auto. Qed.

  Lemma elem_of_subst_initials_fvars {x w A} :
    x ∈ formula_fvars (subst_initials A w) ↔
      (var_final x ∧ (x ∈ formula_fvars A ∨ (to_initial_var x ∈ formula_fvars A
                                             ∧ to_final_var x ∈ w)))
      ∨ (var_initial x ∧ x ∈ formula_fvars A ∧ to_final_var x ∉ w).
  Proof with auto.
    rewrite fvars_subst_initials. rewrite elem_of_union, elem_of_difference. split; intros.
    - destruct H.
      + destruct H. apply not_elem_of_list_to_set in H0. set_unfold in H0.
        destruct (var_initial_or_final x); [|set_solver].
        right. split_and!... contradict H0. exists (to_final_var x).
        rewrite initial_var_of_to_final_var...
      + set_unfold in H. left. destruct H as (x'&->&?&?). split... right. split...
        rewrite to_final_var_as_var...
    - destruct H; [|set_solver]. destruct H. destruct H0; [set_solver|].
      destruct H0. right. set_unfold. exists (to_final_var x). split...
      rewrite as_var_to_final_var_final...
  Qed.

  Lemma elem_of_subst_all_initials_fvars {x A} :
    x ∈ formula_fvars (subst_all_initials A) ↔
      var_final x ∧ (x ∈ formula_fvars A ∨ to_initial_var x ∈ formula_fvars A).
  Proof with auto.
    unfold subst_all_initials. rewrite elem_of_subst_initials_fvars.
    split; [|set_solver]. intros [|(?&?&?)]; [set_solver|]. set_unfold in H1.
    destruct H1. rewrite initial_var_of_to_final_var...
  Qed.

  Lemma subst_all_initials_final' A :
    formula_final (subst_all_initials A).
  Proof. intros x?. apply elem_of_subst_all_initials_fvars in H. naive_solver. Qed.

  Global Instance subst_all_initials_final {A} :
    FormulaFinal (subst_all_initials A).
  Proof. intros x?. apply elem_of_subst_all_initials_fvars in H. naive_solver. Qed.

  Lemma subst_initials_cons_l A (x : final_variable) (xs : list final_variable) :
    <! A[_₀\ (x :: xs)] !> ≡ <! A[₀x\x][_₀\ xs] !>.
  Proof.
    replace (x :: xs) with ([x] ++ xs) by auto. rewrite subst_initials_app_comm.
    by rewrite subst_initials_snoc.
  Qed.

  Global Instance list_delete_elem {A : Type} `{E : EqDecision A} : Delete A (list A)
    := λ x l, remove (decide_rel _) x l.

  Global Instance list_delete_elem_proper {A : Type} `{E : EqDecision A} {x : A}
    : Proper ((≡ₚ) ==> (≡ₚ@{A})) (delete x).
  Proof with auto.
    intros X Y ?. unfold delete, list_delete_elem. generalize dependent Y.
    induction X; intros...
    - apply Permutation_nil_l in H. subst...
    - apply Permutation_cons_inv_l in H as (Y1&Y2&?&?). subst Y.
      rewrite remove_app. simpl. destruct (decide_rel _).
      + rewrite <- remove_app...
      + rewrite <- Permutation_cons_app.
        2:{ rewrite <- remove_app. reflexivity. }
        f_equiv. apply IHX...
  Qed.

  Lemma fvars_subst A x t :
    x ∈ formula_fvars A →
    formula_fvars <! A[x \ t] !> = (formula_fvars A ∖ {[x]}) ∪ term_fvars t.
  Proof.
    intros. apply set_eq. intros. rewrite elem_of_subst_fvars. set_solver.
  Qed.

  Lemma delete_nil {A : Type} {x : A}  `{EqDecision A} :
    delete x [] = [].
  Proof. reflexivity. Qed.

  Lemma delete_cons {A : Type} {x : A} {X} `{EqDecision A} :
    delete x (x :: X) = delete x X.
  Proof. apply remove_cons. Qed.

  (* Lemma delete_cons' {A : Type} {x : A} {X} `{EqDecision A} : *)
  (*   delete x (y :: X) = delete x X ↔ . *)
  (* Proof. apply remove_cons. Qed. *)

  Lemma elem_of_delete_inv {A : Type} (x y : A) (X : list A) `{EqDecision A} :
    x ∈ delete y X → x ≠ y.
  Proof.
    induction X.
    - rewrite delete_nil. set_solver.
    - intros. unfold delete, list_delete_elem in H. simpl in H.
      destruct (decide_rel _).
      + subst. apply IHX. done.
      + set_solver.
  Qed.

  Lemma delete_eq_iff {A : Type} (x : A) (X : list A) `{EqDecision A} :
    delete x X = X ↔ x ∉ X.
  Proof with auto.
    unfold delete, list_delete_elem. induction X; [set_solver|].
    simpl. (destruct (decide_rel _)).
    - subst. split; [|set_solver]. intros. 
      exfalso. pose proof (elem_of_delete_inv a a X). unfold delete, list_delete_elem in H0.
      apply H0... rewrite H. set_solver.
    - split; intros; [set_solver|]. f_equal. apply IHX. set_solver.
  Qed.

  Lemma delete_eq {A : Type} (x : A) (X : list A) `{EqDecision A} :
    x ∉ X →
    delete x X = X.
  Proof. apply delete_eq_iff. Qed.

  Lemma finalized_initial_fvars_subst_perm x A :
    ₀x ∈ formula_fvars A →
    finalized_initial_fvars <! A[₀x \ x] !> ≡ₚ delete x (finalized_initial_fvars A).
  Proof with auto.
    intros. assert (H0:=H). apply union_difference_singleton_L in H.
    unfold finalized_initial_fvars, initial_fvars. 
    rewrite H. rewrite fvars_subst...
    rewrite set_to_list_union_perm with (s1:={[₀x]}) by set_solver.
    rewrite filter_app. rewrite set_to_list_singleton.
    rewrite fmap_app. simpl.
    rewrite to_final_var_initial_var_of. rewrite delete_cons.
    rewrite delete_eq.
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

  (* Lemma subst_all_initials_congr {A B} : A ≡ B → subst_all_initials A ≡ subst_all_initials B. *)
  (* Proof with auto. *)
  (*   unfold subst_all_initials. generalize dependent B. *)
  (*   remember (finalized_initial_fvars A) as la eqn:E. *)
  (*   revert E. generalize dependent A. *)
  (*   induction la; intros. *)
  (*   - induction (finalized_initial_fvars B)... rewrite subst_initials_cons_l. *)
  (*     assert (₀a ∉ formula_fvars A). *)
  (*     { intros contra. rewrite <- elem_of_finalized_initial_fvars in contra. *)
  (*       rewrite <- E in contra. set_solver. } *)
  (*     rewrite (equiv_subst H0)... *)
  (*   - rewrite subst_initials_cons_l. destruct (decide (₀a ∈ (formula_fvars B))). *)
  (*     + rewrite <- elem_of_finalized_initial_fvars in e. apply elem_of_list_In in e. *)
  (*       apply in_split in e as (l1&l2&?). rewrite H0. rewrite subst_initials_app_comm. *)
  (*       simpl. rewrite subst_initials_cons_l. *)
  (*       ospecialize (IHla <! A[₀a \ a] !> _ <! B[₀a \ a] !> _). *)
  (*       1-2: admit. *)
  (*       rewrite IH *)
  (*       rewrite <- app_comm_cons. *)
  (*       SearchRewrite ((_ :: _) ++ _). *)
  (*       rewrite cons_app *)

  Local Lemma subst_initials_add A x xs :
    <! A [_₀\xs] !> ≡ <! A [_₀\finalized_initial_fvars A] !> →
    <! A [_₀\xs] !> ≡ <! A [_₀\xs] [₀x \ x] !>.
  Proof with auto.
    intros. rewrite H. rewrite fequiv_subst_non_free... set_solver.
  Qed.

  Lemma to_final_var_inj_initial {x y} :
    var_initial x →
    var_initial y →
    to_final_var x = to_final_var y →
    x = y.
  Proof.
    unfold var_initial, to_final_var. intros. inversion H1.
    destruct x; destruct y. simpl in *. naive_solver.
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

  Lemma subst_all_initials_extract_l x A :
    <! A [_₀\finalized_initial_fvars A] !>
    ≡ <! A [₀x \ x] [_₀\finalized_initial_fvars <! A [₀x \ x] !>] !>.
  Proof with auto.
    destruct (decide (₀x ∈ formula_fvars A)).
    - assert (e':=e). rewrite <- elem_of_finalized_initial_fvars in e.
      apply elem_of_list_In in e. apply in_split in e as (l1&l2&?).
      rewrite H. rewrite subst_initials_app_comm. simpl.
      rewrite subst_initials_cons_l. f_equiv.
      rewrite finalized_initial_fvars_subst_perm...
      rewrite H. rewrite Permutation_app_comm with (l:=l1). simpl.
      rewrite delete_cons. pose proof (finalized_initial_fvars_NoDup A).
      rewrite H in H0. apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H2 as [].
      rewrite delete_eq... set_solver.
    - rewrite subst_non_free...
  Qed.

  Lemma subst_all_initials_congr {A B} : A ≡ B → subst_all_initials A ≡ subst_all_initials B.
  Proof with auto.
    unfold subst_all_initials.
    remember (finalized_initial_fvars A) as la eqn:E.
    assert (<! A[_₀\la] !> ≡ <! A [_₀\finalized_initial_fvars A] !>) by (by subst).
    clear E.
    remember (finalized_initial_fvars B) as lb eqn:E.
    assert (<! B[_₀\lb] !> ≡ <! B [_₀\finalized_initial_fvars B] !>) by (by subst).
    clear E.
    generalize dependent lb. generalize dependent B.
    revert H. generalize dependent A.
    induction la; intros.
    - clear H0. induction lb... rewrite subst_initials_cons.
      rewrite (subst_initials_add A a [])... f_equiv...
    - destruct (decide (₀a ∈ (formula_fvars B))).
      + assert (e':=e). rewrite <- elem_of_finalized_initial_fvars in e.
        apply elem_of_list_In in e. apply in_split in e as (l1&l2&?). rewrite H2 in H0.
        rewrite H0. rewrite subst_initials_app_comm. simpl.
        do 2 rewrite subst_initials_cons_l. apply IHla.
        * rewrite subst_initials_cons_l in H. rewrite H.
          rewrite <- subst_all_initials_extract_l...
        * rewrite <- subst_all_initials_extract_l... rewrite <- subst_initials_cons_l.
          f_equiv. rewrite Permutation_app_comm. rewrite Permutation_cons_append.
          rewrite <- app_assoc. rewrite Permutation_app_comm with (l:=l2).
          rewrite H2...
        * rewrite H1...
      + rewrite subst_initials_cons_l in *. rewrite (equiv_subst n) in H |- *...
  Qed.

  Global Instance subst_all_initials_proper : Proper ((≡) ==> (≡)) subst_all_initials.
  Proof. intros A B ?. by apply subst_all_initials_congr. Qed.

End moveme.

Notation "A [_₀\*]" := (subst_all_initials A)
                            (in custom formula at level 74, left associativity,
                                A custom formula) : refiney_scope.
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


Section syntax.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation sgn := (model_sgn M).

  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Unset Elimination Schemes.
  Inductive prog : Type :=
  | PAsgn (xs : list final_variable) (ts: list final_term) `{!OfSameLength xs ts}
  | PSeq (p1 p2 : prog)
  | PIf (gcs : list (final_formula * prog))
  | PWhile (g inv : final_formula) (variant : final_term) (p : prog)
  | PSpec (w : list final_variable) (pre : final_formula) (post : formula)
  | PVar (x : final_variable) (ty : value_ty) (p : prog)
  | PConst (x : final_variable) (ty : value_ty) (p : prog).
  Set Elimination Schemes.

  Fixpoint prog_ind P :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcs, Forall (λ fp, P fp.2) gcs → P (PIf gcs)) →
    (∀ g inv v p, P p → P (PWhile g inv v p)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x ty p, P p → P (PVar x ty p)) →
    (∀ x ty p, P p → P (PConst x ty p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hwhile Hspec Hvar Hcons. destruct p.
    - apply Hasgn.
    - apply Hseq; apply prog_ind...
    - apply Hif. induction gcs... constructor... apply prog_ind...
    - apply Hwhile. apply prog_ind...
    - apply Hspec.
    - apply Hvar. apply prog_ind...
    - apply Hcons. apply prog_ind...
  Qed.

  Fixpoint PVarList (xs : list final_variable) (ty : value_ty) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PVar x ty (PVarList xs ty p)
    end.

  Fixpoint PConstList (xs : list final_variable) (ty : value_ty) (p : prog) :=
    match xs with
    | [] => p
    | x :: xs => PConst x ty (PConstList xs ty p)
    end.


  Notation gcmd_list := (list (final_formula * prog)).
  Definition gcmd_comprehension (gs : list final_formula) (f : final_formula → prog) : gcmd_list :=
    map (λ A, (A, f A)) gs.

  Fixpoint modified_final_vars p : gset final_variable :=
    match p with
    | PAsgn xs ts => list_to_set xs
    | PSeq p1 p2 => modified_final_vars p1 ∪ modified_final_vars p2
    | PIf gcs => ⋃ ((modified_final_vars ∘ snd) <$> gcs)
    | PWhile _ _ _ p => modified_final_vars p
    | PSpec w pre post => list_to_set w
    | PVar x _ p => modified_final_vars p ∖ {[x]}
    | PConst x _ p => modified_final_vars p ∖ {[x]}
    end.

  (* TODO: move it near to as_var_F *)
  Definition as_var_set (vs : gset final_variable) : gset variable :=
    set_map as_var vs.

  Definition modified_vars p : gset variable := as_var_set (modified_final_vars p).
  Notation "'Δ' p" := (modified_vars p) (at level 50).

  Fixpoint prog_fvars p : gset variable :=
    match p with
    | PAsgn xs ts => (list_to_set (as_var <$> xs)) ∪ ⋃ (term_fvars ∘ as_term <$> ts)
    | PSeq p1 p2 => prog_fvars p1 ∪ prog_fvars p2
    | PIf gcs => ⋃ ((λ gcmd, prog_fvars (snd gcmd) ∪
                                 formula_fvars (as_formula (fst gcmd))) <$> gcs)
    | PWhile g inv v p => formula_fvars g ∪ formula_fvars inv ∪ term_fvars v ∪ prog_fvars p
    | PSpec w pre post =>
        (list_to_set (as_var_F w) ∪
        formula_fvars pre ∪
        (formula_fvars post ∖ (list_to_set (initial_fvars post))) ∪
        list_to_set (as_var_F (finalized_initial_fvars post)))
    | PVar x _ p => prog_fvars p ∖ {[as_var x]}
    | PConst x _ p => prog_fvars p ∖ {[as_var x]}
  end.

  Lemma modified_vars_subseteq_fvars {p : prog} :
    Δ p ⊆ prog_fvars p.
  Proof.
    unfold modified_vars. induction p.
    - simpl. simpl. induction_same_length xs ts as x t.
      + simpl. unfold as_var_set. set_solver.
      + simpl. unfold as_var_set. rewrite set_map_union. apply union_subseteq. split.
        * rewrite set_map_singleton. set_solver.
        * set_solver.
    - simpl. unfold as_var_set. set_solver.
    - simpl. unfold as_var_set. induction gcs.
      + simpl. set_solver.
      + simpl in *. rewrite set_map_union. apply union_subseteq. split.
        * apply union_subseteq_l'. inversion H. subst. etrans; [exact H2|set_solver].
        * apply union_subseteq_r'. etrans.
          -- apply IHgcs... inversion H. set_solver.
          -- set_solver.
    - simpl. unfold as_var_set. set_solver.
    - unfold as_var_set. simpl. do 3 apply union_subseteq_l'. induction w; set_solver.
    - simpl. set_solver.
    - simpl. set_solver.
  Qed.

  Fixpoint any_guard (gcs : gcmd_list) : formula :=
    match gcs with
    | [] => <! true !>
    | (g, _)::cmds => <! g ∨ $(any_guard cmds) !>
    end.

  Fixpoint all_cmds (gcs : gcmd_list) (A : formula) : formula :=
    match gcs with
    | [] => <! true !>
    | (g, _)::cmds => <! (g ⇔ A) ∧ $(all_cmds cmds A) !>
    end.

  (* ******************************************************************* *)
  (* some extreme programs                                               *)
  (* ******************************************************************* *)

  Definition abort := PSpec [] <!! false !!> <! true !>.
  Definition abort_w w := PSpec w <!! false !!> <! true !>.
  Definition choose_w w := PSpec w <!! true !!> <! true !>.
  Definition skip := PSpec [] <!! true !!> <! true !>.
  Definition magic := PSpec [] <!! true !!> <! false !>.
  Definition magic_w w := PSpec w <!! true !!> <! false !>.

  (* ******************************************************************* *)
  (* subst and rank induction                                            *)
  (* ******************************************************************* *)

  Fixpoint prog_rank (p : prog) : nat :=
    match p with
    | PAsgn xs ts => 0
    | PSeq p1 p2 => 1 + max (prog_rank p1) (prog_rank p2)
    | PIf gcs => 1 + max_list_with (prog_rank ∘ snd) gcs
    | PWhile _ _ _ p => 1 + prog_rank p
    | PSpec w pre post => 0
    | PVar x _ p => 1 + prog_rank p
    | PConst x _ p => 1 + prog_rank p
    end.

  Fixpoint subst_prog p (x x' : final_variable) :=
    match p with
    | PAsgn xs ts => PAsgn
                       ((λ y, if (decide (y = x)) then x' else y) <$> xs)
                       ((λ (t : final_term), as_final_term (subst_term t x (TVar x'))) <$> ts)
    | PSeq p1 p2 => PSeq (subst_prog p1 x x') (subst_prog p2 x x')
    | PIf gcs => PIf ((λ gc : final_formula * prog,
                          (as_final_formula (subst_formula gc.1 x (TVar x')),
                            subst_prog gc.2 x x')) <$> gcs)
    | PWhile g inv v p => PWhile
                            (as_final_formula $ subst_formula g x (TVar x'))
                            (as_final_formula $ subst_formula inv x (TVar x'))
                            (as_final_term    $ subst_term v x (TVar x'))
                            (subst_prog p x x')
    | PSpec w pre post => PSpec
                            ((λ y, if (decide (y = x)) then x' else y) <$> w)
                            (as_final_formula $ subst_formula pre x (TVar x'))
                            (seqsubst post [₀x; as_var x] [TVar ₀x'; TVar x'])
    | PVar y ty p => if (decide (y = x))
                     then PVar y ty p
                     else PVar y ty (subst_prog p x x')
    | PConst y ty p => if (decide (y = x))
                     then PConst y ty p
                     else PConst y ty (subst_prog p x x')
  end.

  Lemma subst_prog_preserves_rank {p x x'} :
    prog_rank p = prog_rank (subst_prog p x x').
  Proof with auto.
    induction p; simpl; try lia.
    - induction gcs... f_equal. simpl. inversion H. subst. rewrite H2. f_equal.
      specialize (IHgcs H3). inversion IHgcs...
    - destruct (decide (x0 = x)); simpl...
    - destruct (decide (x0 = x)); simpl...
  Qed.

  Lemma prog_rank_ind P :
      (∀ n,
          (∀ m, m < n →
                     ∀ p', prog_rank p' = m → P p') →
          (∀ p, prog_rank p = n → P p)) →
      ∀ p, P p.
  Proof with auto.
    intros Hind.
    assert (H : ∀ n p, prog_rank p < n → P p).
    { induction n; intros p Hrank; [lia|]. apply Hind with (prog_rank p)...
      intros. apply IHn. lia. }
    intros p. apply H with (S (prog_rank p)). lia.
  Qed.

  Fixpoint prog_strong_ind (P : prog → Prop) :
    (∀ xs ts H, P (@PAsgn xs ts H)) →
    (∀ p1 p2, P p1 → P p2 → P (PSeq p1 p2)) →
    (∀ gcs, Forall (λ fp, P fp.2) gcs → P (PIf gcs)) →
    (∀ g inv v p, P p → P (PWhile g inv v p)) →
    (∀ w pre post, P (PSpec w pre post)) →
    (∀ x ty p, (∀ p', prog_rank p' = prog_rank p → P p') → P (PVar x ty p)) →
    (∀ x ty p, (∀ p', prog_rank p' = prog_rank p → P p') → P (PConst x ty p)) →
    ∀ p, P p.
  Proof with auto.
    intros Hasgn Hseq Hif Hwhile Hspec Hvar Hcons. induction p using prog_rank_ind.
    destruct p.
    - apply Hasgn.
    - apply Hseq.
      + eapply H; [|reflexivity]. subst. simpl. lia.
      + eapply H; [|reflexivity]. subst. simpl. lia.
    - apply Hif. generalize dependent n. induction gcs... intros. constructor.
      + subst. apply H with (m:=prog_rank a.2)... simpl. lia.
      + eapply IHgcs; [|reflexivity]. intros. eapply H; [|reflexivity]. subst. simpl.
        simpl in H1. lia.
    - apply Hwhile. eapply H; [|reflexivity]. subst. simpl. lia.
    - apply Hspec.
    - apply Hvar. intros. eapply H; [|reflexivity]. subst. simpl. rewrite H1. lia.
    - apply Hcons. intros. eapply H; [|reflexivity]. subst. simpl. rewrite H1. lia.
  Qed.

  Lemma PAsgn_eq {xs xs' ts ts' H H'} :
    xs = xs' →
    ts = ts' →
    @PAsgn xs ts H = @PAsgn xs' ts' H'.
  Proof. intros. subst. f_equal. apply OfSameLength_pi. Qed.

  Local Notation term := (term M).

  (* TODO: Move me *)
  Global Instance set_unfold_var_initial_as_var x : SetUnfold (var_initial (as_var x)) False.
  Proof. done. Qed.

  Lemma subst_prog_non_free {p x x'} :
    as_var x ∉ prog_fvars p →
    subst_prog p x x' = p.
  Proof with auto.
    induction p; intros; simpl.
    - apply PAsgn_eq.
      + simpl in H0. apply not_elem_of_union in H0 as [? _]. clear ts H.
        induction xs; simpl... simpl in H0. destruct (decide (a = x)); [subst; set_solver|].
        f_equal. apply IHxs. set_solver.
      + simpl in H0. apply not_elem_of_union in H0 as [_ ?]. clear xs H.
        induction ts as [|t ts]... simpl in H0. simpl. f_equal.
        * apply as_final_term_eq. apply subst_term_non_free. set_solver.
        * apply IHts. set_solver.
    - f_equal; set_solver.
    - f_equal. induction gcs... simpl. f_equal.
      + destruct a. f_equal.
        * simpl. apply as_final_formula_eq. apply subst_non_free. set_solver.
        * simpl. inversion H. subst. simpl in H3. apply H3. set_solver.
      + inversion H. subst. apply IHgcs; set_solver.
    - f_equal.
      1-2: apply as_final_formula_eq; apply subst_non_free; set_solver.
      + apply as_final_term_eq. apply subst_term_non_free. set_solver.
      + apply IHp. set_solver.
    - f_equiv.
      + induction w as [|y xs]... simpl. destruct (decide (y = x)); [subst; set_solver|].
        f_equal. apply IHxs. simpl in H. simpl.
        contradict H.
        repeat rewrite elem_of_union in H. rewrite elem_of_difference in H.
        repeat rewrite elem_of_union. rewrite elem_of_difference.
        destruct_or! H.
        1-3: set_solver.
        right. assumption.
      + apply as_final_formula_eq. apply subst_non_free. set_solver.
      + simpl in H. repeat rewrite not_elem_of_union in H. destruct_and! H.
        rewrite subst_non_free.
        * rewrite subst_non_free... set_solver.
        * intros contra. apply fvars_subst_superset' in contra. set_solver.
    - destruct (decide (x0 = x))... f_equal. apply IHp. set_solver.
    - destruct (decide (x0 = x))... f_equal. apply IHp. set_solver.
  Qed.

  (* ******************************************************************* *)
  (* open assignment                                                     *)
  (* ******************************************************************* *)
  Variant asgn_rhs_term :=
    | OpenRhsTerm
    | FinalRhsTerm (t : final_term).

  Record asgn_args := mkAsgnArgs {
    asgn_opens : list final_variable;
    asgn_xs : list final_variable;
    asgn_ts : list final_term;
    asgn_of_same_length : OfSameLength asgn_xs asgn_ts;
  }.

  Definition asgn_args_with_open (args : asgn_args) x :=
    let (opens, xs, ts, _) := args in
    mkAsgnArgs (x :: opens) xs ts _.

  Definition asgn_args_with_closed (args : asgn_args) x t :=
    let (opens, xs, ts, _) := args in
    mkAsgnArgs opens (x :: xs) (t :: ts) _.

  Definition split_asgn_list (xs : list final_variable) (rhs : list asgn_rhs_term)
    `{H : !OfSameLength xs rhs} : asgn_args :=
    of_same_length_rect
      id
        (λ rec x t args,
          match t with
          | OpenRhsTerm => asgn_args_with_open (rec args) x
          | FinalRhsTerm t => asgn_args_with_closed (rec args) x t
          end)
        (mkAsgnArgs [] [] [] _)
        xs rhs.

  Lemma split_asgn_list_cons_closed x t xs rhs
      `{Hl1 : !OfSameLength xs rhs} `{Hl2 : !OfSameLength (x :: xs) (FinalRhsTerm t :: rhs)} :
    @split_asgn_list (x :: xs) (FinalRhsTerm t :: rhs) Hl2  =
    asgn_args_with_closed (@split_asgn_list xs rhs Hl1) x t.
  Proof.
    unfold split_asgn_list. simpl. repeat f_equiv. apply OfSameLength_pi.
  Qed.

  Lemma split_asgn_list_cons_open x xs rhs `{!OfSameLength xs rhs}
    `{Hl' : !OfSameLength (x :: xs) (OpenRhsTerm :: rhs)} :
    @split_asgn_list (x :: xs) (OpenRhsTerm :: rhs) Hl' =
    asgn_args_with_open (split_asgn_list xs rhs) x.
  Proof.
    unfold split_asgn_list. simpl. repeat f_equiv. apply OfSameLength_pi.
  Qed.

  Lemma split_asgn_list_no_opens xs ts `{!OfSameLength xs ts} :
    split_asgn_list xs (FinalRhsTerm <$> ts) = mkAsgnArgs [] xs ts _.
  Proof with auto.
    induction_same_length xs ts as x t.
    - unfold split_asgn_list. simpl. f_equiv. apply OfSameLength_pi.
    - assert (Hl:=H'). apply of_same_length_rest in Hl.
      pose proof (@split_asgn_list_cons_closed x t xs (FinalRhsTerm <$> ts)
                    (of_same_length_fmap_r) _).
      rewrite (IH Hl) in H. unfold asgn_args_with_closed in H.
      assert (H'=of_same_length_cons) by apply OfSameLength_pi.
      rewrite H0. rewrite <- H. f_equiv. apply OfSameLength_pi.
  Qed.

  Definition PAsgnWithOpens (xs : list final_variable) (rhs : list asgn_rhs_term)
                            `{!OfSameLength xs rhs} : prog :=
    let (opens, xs, ts, _) := split_asgn_list xs rhs in
    PVarList opens ⊤ (PAsgn xs ts).

  Lemma PAsgnWithOpens_cons_open x xs rhs `{!OfSameLength xs rhs}
      `{!OfSameLength (x :: xs) (OpenRhsTerm :: rhs)} :
    PAsgnWithOpens (x :: xs) (OpenRhsTerm :: rhs) =
      PVar x ⊤ (PAsgnWithOpens xs rhs).
  Proof.
    simpl. unfold PAsgnWithOpens at 1. erewrite split_asgn_list_cons_open.
    unfold asgn_args_with_open. destruct (split_asgn_list xs rhs) eqn:E.
    simpl. unfold PAsgnWithOpens. rewrite E. reflexivity.
  Qed.

  Lemma PAsgnWithOpens_no_opens xs ts `{OfSameLength _ _ xs ts} :
    PAsgnWithOpens xs (FinalRhsTerm <$> ts) = PAsgn xs ts.
  Proof.
    unfold PAsgnWithOpens. rewrite split_asgn_list_no_opens. simpl. reflexivity.
  Qed.

  Lemma PAsgnWithOpens_app_nil_r xs rhs `{!OfSameLength xs rhs} {Hl} :
    @PAsgnWithOpens (xs ++ []) (rhs ++ []) Hl = PAsgnWithOpens xs rhs.
  Proof with auto.
    unfold PAsgnWithOpens.
    replace (split_asgn_list (xs ++ []) (rhs ++ [])) with (split_asgn_list xs rhs);
      [reflexivity|].
    apply rewrite_of_same_length; rewrite app_nil_r; reflexivity.
  Qed.

  Lemma asgn_opens_with_open x xs rhs `{!OfSameLength xs rhs} :
    asgn_opens (asgn_args_with_open (split_asgn_list xs rhs) x) =
      x :: asgn_opens (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_opens_with_closed x t xs rhs `{!OfSameLength xs rhs} :
    asgn_opens (asgn_args_with_closed (split_asgn_list xs rhs) x t) =
      asgn_opens (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_xs_with_open x xs rhs `{!OfSameLength xs rhs} :
    asgn_xs (asgn_args_with_open (split_asgn_list xs rhs) x) =
      asgn_xs (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_xs_with_closed x t xs rhs `{!OfSameLength xs rhs} :
    asgn_xs (asgn_args_with_closed (split_asgn_list xs rhs) x t) =
      x :: asgn_xs (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_ts_with_open x xs rhs `{!OfSameLength xs rhs} :
    asgn_ts (asgn_args_with_open (split_asgn_list xs rhs) x) =
      asgn_ts (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_ts_with_closed x t xs rhs `{!OfSameLength xs rhs} :
    asgn_ts (asgn_args_with_closed (split_asgn_list xs rhs) x t) =
      t :: asgn_ts (split_asgn_list xs rhs).
  Proof.
    destruct (split_asgn_list xs rhs). simpl. reflexivity.
  Qed.

  Lemma asgn_opens_submseteq xs rhs `{!OfSameLength xs rhs} :
    asgn_opens (split_asgn_list xs rhs) ⊆+ xs.
  Proof with auto.
    induction_same_length xs rhs as l r; [set_solver|]. apply submseteq_cons_r.
    assert (Hl:=of_same_length_rest H'). destruct r.
    - right. erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
      eexists. split; [reflexivity | apply IH].
    - left. erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
      apply IH.
  Qed.

  Lemma asgn_xs_submseteq xs rhs `{!OfSameLength xs rhs} :
    asgn_xs (split_asgn_list xs rhs) ⊆+ xs.
  Proof with auto.
    induction_same_length xs rhs as l r; [set_solver|]. apply submseteq_cons_r.
    assert (Hl:=of_same_length_rest H'). destruct r.
    - left. erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. apply IH.
    - right. erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed. eexists.
      split; [reflexivity | apply IH].
  Qed.

  Lemma asgn_opens_app xs1 rhs1 xs2 rhs2
    `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2}
    `{!OfSameLength (xs1 ++ xs2) (rhs1 ++ rhs2)} :
    asgn_opens (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) =
      asgn_opens (split_asgn_list xs1 rhs1) ++ asgn_opens (split_asgn_list xs2 rhs2).
  Proof with auto.
    generalize dependent rhs2. generalize dependent xs2.
    induction_same_length xs1 rhs1 as l1 r1; simpl.
    - repeat f_equiv. apply OfSameLength_pi.
    - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        erewrite IH. set_solver.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        erewrite IH...
  Qed.

  Lemma asgn_xs_app xs1 rhs1 xs2 rhs2
    `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2}
    `{!OfSameLength (xs1 ++ xs2) (rhs1 ++ rhs2)} :
    asgn_xs (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) =
      asgn_xs (split_asgn_list xs1 rhs1) ++ asgn_xs (split_asgn_list xs2 rhs2).
  Proof with auto.
    generalize dependent rhs2. generalize dependent xs2.
    induction_same_length xs1 rhs1 as l1 r1; simpl.
    - repeat f_equiv. apply OfSameLength_pi.
    - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
        erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
        erewrite IH. set_solver.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        erewrite IH...
  Qed.

  Lemma asgn_ts_app xs1 rhs1 xs2 rhs2
    `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2}
    `{!OfSameLength (xs1 ++ xs2) (rhs1 ++ rhs2)} :
    asgn_ts (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) =
      asgn_ts (split_asgn_list xs1 rhs1) ++ asgn_ts (split_asgn_list xs2 rhs2).
  Proof with auto.
    generalize dependent rhs2. generalize dependent xs2. induction_same_length xs1 rhs1 as l1 r1;
      simpl.
    - repeat f_equiv. apply OfSameLength_pi.
    - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
      + erewrite split_asgn_list_cons_open. rewrite asgn_ts_with_open.
        erewrite split_asgn_list_cons_open. rewrite asgn_ts_with_open.
        erewrite IH. set_solver.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_ts_with_closed.
        erewrite split_asgn_list_cons_closed. rewrite asgn_ts_with_closed.
        erewrite IH...
  Qed.

  Lemma elem_of_asgn_opens x xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    x ∈ asgn_opens (split_asgn_list xs rhs) ↔ (x, OpenRhsTerm) ∈ (xs, rhs).
  Proof with auto.
    induction_same_length xs rhs as l r.
    - simpl. unfold zip_pair_elem_of. pose proof (elem_of_zip_pair_nil x (OpenRhsTerm)).
      set_solver.
    - intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as [].
      destruct (decide (x = l)).
      2:{ rewrite elem_of_zip_pair_hd_ne... destruct r.
          - erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
            rewrite elem_of_cons. rewrite IH... naive_solver.
          - erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
            rewrite IH... }
      subst l. destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        rewrite elem_of_cons. rewrite IH... rewrite elem_of_zip_pair_hd... split...
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        rewrite IH... rewrite elem_of_zip_pair_hd... split; [|discriminate]. intros (i&?&?).
        simpl in H1, H2. apply elem_of_list_lookup_2 in H1. contradiction.
  Qed.

  Lemma elem_of_asgn_xs_ts x t xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), asgn_ts (split_asgn_list xs rhs)) ↔
      (x, FinalRhsTerm t) ∈ (xs, rhs).
  Proof with auto.
    induction_same_length xs rhs as l r.
    - simpl. unfold zip_pair_elem_of. pose proof (elem_of_zip_pair_nil x t).
      pose proof (elem_of_zip_pair_nil x (FinalRhsTerm t)). set_solver.
    - intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as [].
      destruct (decide (x = l)).
      2:{ rewrite elem_of_zip_pair_hd_ne... destruct r.
          - erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
            rewrite asgn_ts_with_open. rewrite IH...
          - erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
            rewrite asgn_ts_with_closed. rewrite elem_of_zip_pair_hd_ne... }
      subst l. destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open.
        rewrite IH... rewrite elem_of_zip_pair_hd... split; [|discriminate]. intros (i&?&?).
        simpl in H1, H2. apply elem_of_list_lookup_2 in H1. contradiction.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
        rewrite asgn_ts_with_closed. rewrite (elem_of_zip_pair_hd (FinalRhsTerm t))...
        split.
        * intros (i&?). destruct i.
          -- apply elem_of_zip_pair_hd_indexed in H1 as [_ ?]. subst...
          -- apply elem_of_zip_pair_tl_indexed in H1. apply elem_of_zip_pair_indexed_inv in H1.
             rewrite IH in H1... destruct H1 as (j&?&?). simpl in H1.
             apply elem_of_list_lookup_2 in H1. contradiction.
        * intros. inversion H1. subst t0. exists 0. split; simpl...
  Qed.

  Lemma elem_of_asgn_ts_inv t xs rhs `{!OfSameLength xs rhs} :
    t ∈ asgn_ts (split_asgn_list xs rhs) →
    ∃ x, (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), (asgn_ts (split_asgn_list xs rhs))).
  Proof with auto.
    intros. apply elem_of_list_lookup in H as (i&?).
    opose proof (lookup_of_same_length_r (asgn_xs (split_asgn_list xs rhs)) H) as (x&?).
    { apply asgn_of_same_length. }
    exists x, i. split...
  Qed.

  Lemma elem_of_asgn_ts t xs rhs `{!OfSameLength xs rhs} :
    NoDup xs →
    t ∈ asgn_ts (split_asgn_list xs rhs) ↔
      ∃ x, (x, t) ∈ (asgn_xs (split_asgn_list xs rhs), (asgn_ts (split_asgn_list xs rhs))).
  Proof with auto.
    intros Hnodup. split; [apply elem_of_asgn_ts_inv|].
    intros (x&?). apply elem_of_asgn_xs_ts in H as [i []]... simpl in H, H0.
    generalize dependent i. induction_same_length xs rhs as l r; [set_solver|].
    intros Hnodup ???. assert (Hl:=of_same_length_rest H'). apply NoDup_cons in Hnodup as [].
    destruct r.
    + erewrite split_asgn_list_cons_open. rewrite asgn_ts_with_open.
      destruct i.
      * simpl in H0. discriminate.
      * apply IH with (i:=i)...
    + erewrite split_asgn_list_cons_closed. rewrite asgn_ts_with_closed. destruct i.
      * simpl in H0. inversion H0. subst. set_solver.
      * set_unfold. right. eapply IH; [assumption | exact H | exact H0].
  Qed.

  Lemma asgn_opens_Permutation xs rhs xs' rhs'
    `{!OfSameLength xs rhs} `{!OfSameLength xs' rhs'} :
    NoDup xs →
    NoDup xs' →
    (xs, rhs) ≡ₚₚ (xs', rhs') →
    asgn_opens (split_asgn_list xs rhs) ≡ₚ asgn_opens (split_asgn_list xs' rhs').
  Proof with auto.
    generalize dependent xs'. generalize dependent rhs'. induction_same_length xs rhs as l r.
    - apply zip_pair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
    - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
      apply zip_pair_Permutation_cons_inv_l in H1...
      destruct H1 as (xs'0&ys'0&xs'1&ys'1&?&?&?&?&?). destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
        subst. erewrite asgn_opens_app. erewrite split_asgn_list_cons_open.
        rewrite asgn_opens_with_open. rewrite app_Permutation_comm.
        simpl. f_equiv. etrans.
        * apply IH with (xs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
          apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
          split_and!... intros. apply H1 in H6. set_solver.
        * erewrite asgn_opens_app. apply Permutation_app_comm.
      + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
        subst. erewrite asgn_opens_app. erewrite split_asgn_list_cons_closed.
        rewrite asgn_opens_with_closed. rewrite app_Permutation_comm.
        simpl. etrans.
        * apply IH with (xs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
          apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
          split_and!... intros. apply H1 in H6. set_solver.
        * erewrite asgn_opens_app. apply Permutation_app_comm.
  Qed.

  Lemma asgn_xs_ts_Permutation xs rhs xs' rhs'
    `{!OfSameLength xs rhs} `{!OfSameLength xs' rhs'} :
    NoDup xs →
    NoDup xs' →
    (xs, rhs) ≡ₚₚ (xs', rhs') →
    (asgn_xs (split_asgn_list xs rhs), asgn_ts (split_asgn_list xs rhs)) ≡ₚₚ
      (asgn_xs (split_asgn_list xs' rhs'), asgn_ts (split_asgn_list xs' rhs')).
  Proof with auto.
    generalize dependent xs'. generalize dependent rhs'. induction_same_length xs rhs as l r.
    - apply zip_pair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
    - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
      apply zip_pair_Permutation_cons_inv_l in H1...
      destruct H1 as (xs'0&ys'0&xs'1&ys'1&?&?&?&?&?). destruct r.
      + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open.
        subst.
        rewrite IH with (xs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
        2:{ apply NoDup_app in H0 as [? []]. apply NoDup_cons in H3 as []. apply NoDup_app.
            split_and!... intros. apply H1 in H6. set_solver. }
        repeat erewrite asgn_xs_app. repeat erewrite asgn_ts_app.
        erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open...
        Unshelve. typeclasses eauto.
      + subst. erewrite asgn_xs_app. erewrite asgn_ts_app.
        repeat erewrite split_asgn_list_cons_closed. repeat erewrite asgn_xs_with_closed.
        repeat erewrite asgn_ts_with_closed. rewrite zip_pair_Permutation_app_comm.
        2:{ apply asgn_of_same_length. }
        2:{ eapply of_same_length_cons. Unshelve. apply asgn_of_same_length. }
        simpl. apply zip_pair_Permutation_cons.
        1:{ apply asgn_of_same_length. }
        1:{ eapply of_same_length_app. Unshelve. all: apply asgn_of_same_length. }
        rewrite IH with (xs':=xs'1 ++ xs'0) (rhs':=ys'1 ++ ys'0)...
        2:{ apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
            split_and!... intros. intros contra. apply H1 in contra. set_solver. }
        2:{ rewrite zip_pair_Permutation_app_comm... }
        erewrite asgn_xs_app. erewrite asgn_ts_app...
        Unshelve. typeclasses eauto.
  Qed.


End syntax.

Arguments prog M : clear implicits.

Notation "'Δ' p" := (modified_vars p) (at level 50).

Declare Custom Entry asgn_rhs_seq.
Declare Custom Entry asgn_rhs_elem.

Notation "xs" := (xs) (in custom asgn_rhs_seq at level 0,
                       xs custom asgn_rhs_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom asgn_rhs_seq at level 0)
    : refiney_scope.

Notation "x" := ([FinalRhsTerm (as_final_term x)]) (in custom asgn_rhs_elem at level 0,
                      x custom term at level 200)
    : refiney_scope.
Notation "?" := ([OpenRhsTerm]) (in custom asgn_rhs_elem at level 0) : refiney_scope.
Notation "* x" := x (in custom asgn_rhs_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "*$( x )" := x (in custom asgn_rhs_elem at level 5, only parsing, x constr at level 200)
    : refiney_scope.
Notation "⇑ₓ xs" := (TVar ∘ as_var <$> xs)
                      (in custom asgn_rhs_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ( xs )" := (TVar ∘ as_var <$> xs)
                      (in custom asgn_rhs_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₓ₊ xs" := (TVar <$> xs)
                      (in custom asgn_rhs_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑ₓ₊( xs )" := (TVar <$> xs)
                      (in custom asgn_rhs_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑₀ xs" := (TVar ∘ initial_var_of <$> xs)
                      (in custom asgn_rhs_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "⇑₀( xs )" := (TVar ∘ initial_var_of <$> xs)
                      (in custom asgn_rhs_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "⇑ₜ ts" := (as_term <$> ts)
                      (in custom asgn_rhs_elem at level 5, ts constr at level 0)
    : refiney_scope.
Infix "," := app (in custom asgn_rhs_elem at level 10, right associativity) : refiney_scope.

Declare Custom Entry prog.
Declare Custom Entry gcmd.

Notation "<{ e }>" := e (e custom prog) : refiney_scope.

Notation "$ e" := e (in custom prog at level 0, e constr at level 0)
    : refiney_scope.

Notation "$( e )" := e (in custom prog at level 0, only parsing,
                           e constr at level 200)
    : refiney_scope.

Notation "xs := ts" := (PAsgnWithOpens xs ts)
                       (in custom prog at level 95,
                           xs custom var_seq at level 94,
                           ts custom asgn_rhs_seq at level 94,
                           no associativity)
    : refiney_scope.

Notation "p ; q" := (PSeq p q)
                      (in custom prog at level 120, right associativity)
    : refiney_scope.

Notation "A → p" := ((as_final_formula A), p) (in custom gcmd at level 60,
                           A custom formula,
                           p custom prog,
                           no associativity) : refiney_scope.

Notation "'if' x | .. | y 'fi'" :=
  (PIf (cons (x) .. (cons (y) nil) ..))
    (in custom prog at level 95,
        x custom gcmd,
        y custom gcmd, no associativity) : refiney_scope.

Notation "'if' | g : gs → p 'fi'" := (PIf (gcmd_comprehension gs (λ g, p)))
                                     (in custom prog at level 95, g name,
                                         gs global, p custom prog)
    : refiney_scope.

Notation "'while' A 'invariant' I 'variant' v ⟶ p 'end'" :=
  (PWhile (as_final_formula A) (<!! I ∧ ⌜v ∈ₜ ℕ⌝ !!>) v p)
    (in custom prog at level 95,
        A custom formula,
        I custom formula,
        v constr at level 0,
        p custom prog, no associativity) : refiney_scope.

Notation "w : [ p , q ]" :=
  (PSpec w (as_final_formula p) q)
    (in custom prog at level 95, no associativity,
        w custom var_seq at level 94,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation "w : [ q ]" :=
  (PSpec w (as_final_formula <! true !>) q)
    (in custom prog at level 95, no associativity,
        w custom var_seq at level 94, q custom formula at level 85)
    : refiney_scope.

Notation ": [ p , q ]" :=
  (PSpec [] (as_final_formula p) q)
    (in custom prog at level 95, no associativity,
        p custom formula at level 85, q custom formula at level 85)
    : refiney_scope.

Notation ": [ q ]" :=
  (PSpec [] (as_final_formula <! true !>) q)
    (in custom prog at level 95, no associativity, q custom formula at level 85)
    : refiney_scope.

Notation "'|[' 'var' x .. y : ty '⦁' p ']|' " :=
  (PVar x ty .. (PVar y ty p) ..)
    (in custom prog at level 95, no associativity,
        x constr at level 0, ty custom term_ty, p custom prog) : refiney_scope.

Notation "'|[' 'var*' xs '⦁' y ']|' " :=
  (PVarList xs ⊤ y)
    (in custom prog at level 95, xs custom variable_list) : refiney_scope.

Notation "'|[' 'con' x .. y : ty '⦁' p ']|' " :=
  (PConst x ty .. (PConst y ty p) ..)
    (in custom prog at level 95, no associativity,
        x constr at level 0, ty custom term_ty, p custom prog) : refiney_scope.

Notation "'|[' 'con*' xs '⦁' y ']|' " :=
  (PConstList xs ⊤ y)
    (in custom prog at level 95, xs custom variable_list) : refiney_scope.

Notation "{ A }" := (PSpec [] (as_final_formula A) <! true !>)
                        (in custom prog at level 95, no associativity,
                            A custom formula at level 200)
    : refiney_scope.

(* Axiom M : model. *)
(* Axiom p1 p2 : @prog M. *)
(* Axiom pre : @final_formula (value M). *)
(* Axiom post : @formula (value M). *)
(* Axiom x y z : final_variable. *)
(* Axiom xs ys : list final_variable. *)
(* Definition pp := <{ $p1 ; $p2 }>. *)

(* Definition pp2 := <{ ∅ : [<! pre !>, post] }>. *)
(* Definition pp3 := <{ x, y, z := y, x, ? }> : @prog M. *)
(* Definition pp4 := <{ x : [pre, post] }> : @prog M. *)

Section semantics.
  Context {M : model}.
  Context {MNat : ModelWithNat M}.
  Local Notation value := (value M).
  Local Notation value_ty := (value_ty M).
  Local Notation prog := (prog M).
  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Definition ty_ctx := gmap variable value_ty.

  Definition get_ty (Γ : ty_ctx) (x : variable) : value_ty :=
    match Γ !! x with
    | Some τ => τ
    | None => ⊤
    end.

  Local Definition while_fvars (g inv : final_formula) (var : final_term) (p : prog) :=
    formula_fvars inv ∪ formula_fvars g ∪ term_fvars var ∪ prog_fvars p.


  (* TODO: move me to multisubst.v *)
  Hint Extern 0 (FormulaFinal <! _ [[ ↑ₓ _ \ ⇑ₜ _ ]] !>) =>
    class_apply msubst_formula_final : typeclass_instances.

  Fixpoint wp (p : prog) (A : formula) : formula :=
    match p with
    | PAsgn xs ts => <! A [[ ↑ₓ xs \ ⇑ₜ ts]] !>
    | PSeq p1 p2 => wp p1 (wp p2 A)
    | PIf gcs => <! ∨* ⤊(gcs.*1) ∧
                      ∧* (map (λ gc, <! $(as_formula gc.1) ⇒ $(wp gc.2 A) !>) gcs) !>
    | PWhile g inv var p =>
        let var₀ := fresh_var (raw_var "") (while_fvars g inv var p) in
        <! ∀* $(set_to_list (Δ p)),
            (inv ∧ g ⇒ $(wp p inv)) ∧
            (inv ∧ ¬ g ⇒ A) ∧
            (inv ∧ g ⇒ ⌜var ∈ₜ ℕ⌝) ∧
            (∀ var₀, inv ∧ g ∧ ⌜var = var₀⌝ ⇒ $(wp p (<! ⌜var < var₀⌝ !>))) !>
    | PSpec w pre post =>
        <! pre ∧ (∀* ↑ₓ w, post ⇒ A)[_₀\*]  !>
    | PVar x ty p =>
        let x' := fresh_var x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) in
        <! (∀ x : ty, $(wp p <! A[x \ x'] !>))[x' \ x] !>
    | PConst x ty p =>
        let x' := fresh_var x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) in
        <! (∃ x : ty, $(wp p <! A[x \ x'] !>))[x' \ x] !>
    end.

  Global Instance wp_final {p A} `{!FormulaFinal A} : FormulaFinal (wp p A).
  Proof with auto.
    generalize dependent A. induction p; intros; simpl; try typeclasses eauto.
    unshelve eapply f_and_formula_final. unfold FormulaFinal in *. unfold formula_final.
    intros. set_unfold in H0. destruct H0 as (B&(gc&->&?)&?). destruct gc. simpl in *.
    apply elem_of_union in H1 as [|].
    - apply (final_formula_final _ _ H1).
    - rewrite Forall_forall in H. unfold elem_of in H1. specialize (H (f, p) H0).
      simpl in H. specialize (H A FormulaFinal0). apply H...
  Qed.

  (* TODO: move me; don't forget to make Hints global *)
  Lemma var_initial_to_initial_var x : var_initial (to_initial_var x).
  Proof. done. Qed.

  Hint Extern 1 (var_final _) => apply var_final_not_initial : core.
  Hint Resolve var_initial_to_initial_var : core.
  Hint Extern 1 =>
    match goal with
    | H : ¬ var_initial (to_initial_var _) |- _ => exfalso; apply H; apply var_initial_to_initial_var
    end : core.

  Lemma fvars_wp {p A} `{!FormulaFinal A} :
    formula_fvars (wp p A) ⊆ prog_fvars p ∪ formula_fvars A.
  Proof with auto.
    intros. generalize dependent A. induction p; intros; intros z; intros.
    - simpl in *. apply fvars_msubst_superset in H0.
      set_unfold in H0. destruct H0; [set_solver|]. set_unfold.
      left. right. apply elem_of_union_list. destruct H0 as (?&?&?&?&?).
      exists (term_fvars x). split... set_unfold. subst. exists x0. split...
    - simpl. simpl in H. apply IHp1 in H; [|typeclasses eauto]. set_solver.
    - simpl in *. induction gcs.
      + simpl. set_solver.
      + simpl. inversion H. subst. set_solver.
    - simpl in *. rewrite fvars_foralllist in H. simpl in *. set_unfold in H.
      destruct H. destruct_or! H.
      1-2: set_solver.
      2-7: set_solver.
      1:{ apply IHp in H... set_solver. }
      destruct H. destruct_or! H.
      1-4: set_solver.
      specialize (IHp <!! ⌜ v < $(fresh_var ""%string (while_fvars g inv v p)) ⌝ !!>).
      apply IHp in H... set_solver.
    - simpl in *. apply elem_of_union in H as [|]; [set_solver|].
      apply elem_of_subst_all_initials_fvars in H as [].
      destruct H0; rewrite fvars_foralllist in H0.
      + set_unfold in H0. rewrite not_and_l in H0. destruct H0. destruct H0; [|set_solver].
        destruct H1.
        * set_solver.
        * set_unfold. left. left. right. split... apply not_and_l. right.
          apply var_final_not_initial...
      + set_unfold in H0. rewrite not_and_l in H0. destruct H0. destruct H0; [set_solver|].
        apply formula_is_final in H0... apply var_final_not_initial in H0...
    - simpl wp in H. apply elem_of_subst_fvars in H. destruct H as [[] | []].
      + simpl in H. set_unfold in H. destruct H. destruct H; [contradiction|].
        apply IHp in H... set_unfold in H. destruct H; [set_solver|].
        apply fvars_subst_superset' in H. set_solver.
      + pose proof (fresh_var_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A)).
        set_unfold in H0. subst. simpl in H. set_unfold in H. destruct H.
        destruct H; [contradiction|]. apply IHp in H... set_unfold in H.
        destruct H; [set_solver|]. apply elem_of_subst_fvars in H.
        destruct H as [[] | []]; set_solver.
    - simpl wp in H. apply elem_of_subst_fvars in H. destruct H as [[] | []].
      + simpl in H. set_unfold in H. destruct H. destruct H; [contradiction|].
        apply IHp in H... set_unfold in H. destruct H; [set_solver|].
        apply fvars_subst_superset' in H. set_solver.
      + pose proof (fresh_var_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A)).
        set_unfold in H0. subst. simpl in H. set_unfold in H. destruct H.
        destruct H; [contradiction|]. apply IHp in H... set_unfold in H.
        destruct H; [set_solver|]. apply elem_of_subst_fvars in H.
        destruct H as [[] | []]; set_solver.
  Qed.

  Local Definition k_subst p := ∀ (x : variable) (t : term) A,
    VarFinal x →
    FormulaFinal A →
    TermFinal t →
    x ∉ prog_fvars p →
    term_fvars t ## prog_fvars p →
    <! $(wp p A)[x \ t] !> ≡ wp p <! A[x \ t] !>.

  Local Definition k_congr p := ∀ A B, FormulaFinal A → FormulaFinal B → A ≡ B → wp p A ≡ wp p B.

  Local Definition k_var p := ∀ x ty A y,
    VarFinal y →
    FormulaFinal A →
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PVar x ty p) A ≡ <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.

  Local Definition k_const p := ∀ x ty A y,
    VarFinal y →
    FormulaFinal A →
    as_var x ≠ y →
    y ∉ prog_fvars p →
    y ∉ formula_fvars A →
    wp (PConst x ty p) A ≡ <! (∃ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !>.

  (* TODO: move me *)
  Hint Extern 0 (as_var _ = as_var _) => apply as_var_inj : core.

  Lemma L_var' p :
    k_congr p →
    k_subst p →
    ∀ (x : final_variable) ty A (y z : variable) `{VarFinal y} `{VarFinal z} `{!FormulaFinal A},
      as_var x ≠ y →
      y ∉ prog_fvars p →
      y ∉ formula_fvars A →
      as_var x ≠ z →
      z ∉ prog_fvars p →
      z ∉ formula_fvars A →
      <! (∀ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !> ⇛
        <! (∀ x : ty, $(wp p <! A[x \ z] !>))[z \ x] !>.
  Proof with auto.
    intros Hcongr Hsubst. intros x ty A y z Hy Hz Ha Hne1 Hp1 Ha1 Hne2 Hp2 Ha2.
    destruct (decide (y = z)).
    { rewrite <- e in *. reflexivity. }
    intros σ?.
    unfold FForallT in *.
    rewrite <- f_forall_one_point by set_solver.
    rewrite <- f_forall_one_point in H by set_solver.
    rewrite fforall_alpha_equiv with (x':=y).
    2:{
      intros contra. simpl in contra. set_unfold in contra. destruct contra.
      - destruct H0; [done|]. subst. set_solver.
      - destruct H0. destruct H0; [contradiction|]. apply fvars_wp in H0.
        set_unfold in H0. destruct H0.
        + set_solver.
        + apply fvars_subst_superset' in H0. set_solver.
    }
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl.
    destruct (decide _); [|contradiction].
    destruct (decide _); [done|].
    clear e n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?. rewrite simpl_subst_forall.
    2:{ unfold quant_subst_fvars. set_solver. }
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl.
    destruct (decide _); [done|].
    clear n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?.
    eapply (Hsubst z (as_final_term y) <! A [x \ z] !> _ _ _ Hp2 _ σ).
    clear Hsubst.
    unfold k_congr in Hcongr.
    revert H. apply Hcongr... apply fequiv_subst_trans...
    Unshelve. simpl. set_solver.
  Qed.

  Lemma final_fequiv (A B : formula) `{!FormulaFinal A} `{!FormulaFinal B} :
    <!! A !!> ≡ <!! B !!> ↔ A ≡ B.
  Proof. unfold equiv, ffequiv. do 2 rewrite as_formula_as_final_formula. done. Qed.

  Lemma L_var p : k_congr p → k_subst p → k_var p.
  Proof with auto.
    intros. unfold k_var. intros. simpl.
    mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) as z.
    repeat rewrite not_elem_of_union in H4. destruct_and! H6.
    apply fequiv_fent_iff. split.
    - apply L_var'... set_solver.
    - apply L_var'... set_solver.
  Qed.

  Lemma L_const' p :
    k_congr p →
    k_subst p →
    ∀ (x : final_variable) ty A (y z : variable) `{VarFinal y} `{VarFinal z} `{!FormulaFinal A},
      as_var x ≠ y →
      y ∉ prog_fvars p →
      y ∉ formula_fvars A →
      as_var x ≠ z →
      z ∉ prog_fvars p →
      z ∉ formula_fvars A →
      <! (∃ x : ty, $(wp p <! A[x \ y] !>))[y \ x] !> ⇛
        <! (∃ x : ty, $(wp p <! A[x \ z] !>))[z \ x] !>.
  Proof with auto.
    intros Hcongr Hsubst. intros x ty A y z Hy Hz Ha Hne1 Hp1 Ha1 Hne2 Hp2 Ha2.
    destruct (decide (y = z)).
    { rewrite <- e in *. reflexivity. }
    intros σ?.
    unfold FExistsT in *.
    rewrite <- f_exists_one_point by set_solver.
    rewrite <- f_exists_one_point in H by set_solver.
    rewrite fexists_alpha_equiv with (x':=y).
    2:{
      intros contra. simpl in contra. set_unfold in contra. destruct contra.
      - destruct H0; [done|]. subst. set_solver.
      - destruct H0. destruct H0; [contradiction|]. apply fvars_wp in H0.
        set_unfold in H0. destruct H0.
        + set_solver.
        + apply fvars_subst_superset' in H0. set_solver.
    }
    rewrite simpl_subst_and. rewrite simpl_subst_af. simpl.
    destruct (decide _); [|contradiction].
    destruct (decide _); [done|].
    clear e n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?. rewrite simpl_subst_exists.
    2:{ unfold quant_subst_fvars. set_solver. }
    rewrite simpl_subst_and. rewrite simpl_subst_af. simpl.
    destruct (decide _); [done|].
    clear n. revert H. revert σ. rewrite fold_fent. f_equiv. f_equiv.
    intros σ?.
    eapply (Hsubst z (as_final_term y) <! A [x \ z] !> _ _ _ Hp2 _ σ).
    clear Hsubst.
    unfold k_congr in Hcongr.
    revert H. apply Hcongr... apply fequiv_subst_trans...
    Unshelve. simpl. set_solver.
  Qed.

  Lemma L_const p : k_congr p → k_subst p → k_const p.
  Proof with auto.
    intros. unfold k_const. intros. simpl.
    mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A) as z.
    repeat rewrite not_elem_of_union in H4. destruct_and! H6.
    apply fequiv_fent_iff. split.
    - apply L_const'... set_solver.
    - apply L_const'... set_solver.
  Qed.

  Local Lemma L_congr p :
    (∀ p' : prog, prog_rank p' < prog_rank p → k_var p' ∧ k_const p') →
    k_congr p.
  Proof with auto.
    unfold k_congr. induction p using prog_strong_ind; intros.
    - simpl. rewrite H3...
    - simpl. apply IHp1... 2: apply IHp2...
      + intros. apply H... simpl. lia.
      + intros. apply H... simpl. lia.
    - simpl. f_equiv. generalize dependent B. generalize dependent A.
      induction gcs; intros; simpl... apply Forall_cons in H as [].
      rewrite H with (B:=B)...
      2: {intros. apply H0... simpl. lia. }
      f_equiv. apply IHgcs... intros. apply H0... simpl. simpl in *. lia.
    - simpl. do 3 f_equiv. by rewrite H2.
    - simpl. f_equiv. f_equiv. by rewrite H2.
    - simpl. mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A ∪ formula_fvars B) as z.
      assert (H6:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_var p) by naive_solver. unfold k_var in H5.
      simpl in H5. rewrite H5 with (y:=z)...
      2-4: set_solver.
      rewrite H5 with (y:=z)...
      2-4: set_solver.
      do 2 f_equiv. apply H...
      + intros. apply H6... simpl. lia.
      + f_equiv...
    - simpl. mk_fresh x ({[as_var x]} ∪ prog_fvars p ∪ formula_fvars A ∪ formula_fvars B) as z.
      assert (H6:=H0). simpl in H0. forward (H0 p) by lia.
      assert (k_const p) by naive_solver. unfold k_const in H5.
      simpl in H5. rewrite H5 with (y:=z)...
      2-4: set_solver.
      rewrite H5 with (y:=z)...
      2-4: set_solver.
      do 2 f_equiv. apply H...
      + intros. apply H6... simpl. lia.
      + f_equiv...
  Qed.

  Local Lemma L_subst p :
    (∀ p', prog_rank p' < prog_rank p → k_congr p' ∧ k_var p' ∧ k_const p') →
    k_subst p.
  Proof with auto.
    unfold k_subst. induction p using prog_strong_ind;
      intros Hind ??? Hfinal1 Hfinal2 Hfinal3; intros.
    - simpl. simpl in H0. apply not_elem_of_union in H0 as []. rewrite msubst_subst_comm'...
      + contradict H0. apply elem_of_list_to_set...
      + set_unfold. contradict H2. apply elem_of_union_list. destruct H2 as (t'&?&x'&?&?).
        subst. exists (term_fvars x'). split... set_unfold. eauto.
      + set_solver.
    - simpl. rewrite IHp1...
      + apply Hind; auto; [simpl; lia|]. apply IHp2...
        * intros. apply Hind. simpl. lia.
        * set_solver.
        * set_solver.
      + intros. apply Hind. simpl. lia.
      + set_solver.
      + set_solver.
    - simpl. rewrite simpl_subst_and. simpl in H0. f_equiv.
      + apply fequiv_subst_non_free. contradict H0.
        set_unfold in H0. simpl in H0. apply elem_of_union_list.
        destruct H0 as (?&(B&->&([]&->&?))&?). simpl in *.
        exists (prog_fvars p ∪ formula_fvars f).
        split; [|set_solver]. set_unfold. exists (f, p). simpl. set_solver.
      + induction gcs; simpl... inversion H. subst. rewrite simpl_subst_and. f_equiv.
        * rewrite simpl_subst_impl. f_equiv.
          -- apply fequiv_subst_non_free. simpl in H1. set_solver.
          -- apply H4...
             ++ intros. apply Hind. simpl. lia.
             ++ set_solver.
             ++ set_solver.
        * apply IHgcs...
          -- intros. apply Hind. simpl. simpl in H2. lia.
          -- set_solver.
          -- set_solver.
    - simpl. rewrite simpl_subst_foralllist.
      2:{ contradict H. apply elem_of_set_to_list in H. apply modified_vars_subseteq_fvars in H.
          set_solver. }
      2:{ intros z??. rewrite list_to_set_set_to_list in H1.
          apply modified_vars_subseteq_fvars in H1. set_solver. }
      f_equiv. rewrite simpl_subst_and.
      rewrite simpl_subst_impl. rewrite simpl_subst_and.
      rewrite fequiv_subst_non_free by set_solver.
      rewrite fequiv_subst_non_free by set_solver.
      rewrite IHp...
      2:{ intros. apply Hind. simpl in *. lia. }
      2-3: set_solver.
      f_equiv.
      { f_equiv. apply Hind... apply fequiv_subst_non_free. set_solver. }
      rewrite simpl_subst_and. rewrite simpl_subst_impl. rewrite simpl_subst_and.
      rewrite fequiv_subst_non_free by set_solver.
      rewrite fequiv_subst_non_free by set_solver.
      f_equiv. rewrite simpl_subst_and.
      rewrite simpl_subst_impl. rewrite simpl_subst_and.
      rewrite fequiv_subst_non_free by set_solver.
      rewrite fequiv_subst_non_free by set_solver.
      rewrite simpl_subst_af. simpl. rewrite subst_term_non_free by set_solver.
      f_equiv. mk_fresh (while_fvars g inv v p) as y.
      mk_fresh ({[x]} ∪
          prog_fvars p ∪
          formula_fvars <! inv ∧ g ∧ ⌜ v = y ⌝ ⇒ $(wp p <! ⌜ v < y ⌝ !>) !> ∪
            quant_subst_fvars y <! inv ∧ g ∧ ⌜ v = y ⌝ ⇒ $(wp p <! ⌜ v < y ⌝ !>) !> x t)
        as z.
      rewrite fforall_alpha_equiv with (x':=z) by set_solver.
      rewrite simpl_subst_forall by set_solver. f_equiv.
      repeat rewrite simpl_subst_impl. repeat rewrite simpl_subst_and.
      rewrite fequiv_subst_non_free with (x:=y) by set_solver.
      rewrite fequiv_subst_non_free with (x:=x) by set_solver.
      rewrite fequiv_subst_non_free with (x:=y) by set_solver.
      rewrite fequiv_subst_non_free with (x:=x) by set_solver.
      repeat rewrite simpl_subst_af. simpl. destruct (decide _); [|contradiction]. clear e.
      rewrite subst_term_non_free with (x:=y) by set_solver.
      rewrite subst_term_non_free with (x:=x) by set_solver.
      repeat rewrite simpl_subst_af. simpl. destruct (decide _); [set_solver|]. clear n.
      f_equiv. erewrite IHp...
      2:{ intros. apply Hind. simpl in *. lia. }
      3-4: set_solver.
      2: typeclasses eauto.
      rewrite IHp...
      2:{ intros. apply Hind. simpl in *. lia. }
      2-3: set_solver.
      apply Hind... unfold term_lt. repeat rewrite simpl_subst_af.
      simpl. destruct (decide _); [|contradiction]. clear e. simpl.
      destruct (decide _); [set_solver|]. rewrite subst_term_non_free with (t:=v) by set_solver.
      rewrite subst_term_non_free with (t:=v) by set_solver...
    - simpl. rewrite simpl_subst_and. rewrite fequiv_subst_non_free by set_solver.
      f_equiv.
      simpl in H.
      repeat rewrite not_elem_of_union in H. destruct_and! H.
      apply not_elem_of_difference in H3.
      apply not_elem_of_list_to_set in H1.
      unfold subst_all_initials. do 2 rewrite subst_initials_msubst.
      rewrite msubst_subst_comm'.
      2:{ intros contra. set_unfold in contra. destruct contra as (?&->&?&?).
          apply not_and_l in H5. destruct H5; [set_solver|].
          rewrite to_final_var_initial_var_of in H5. destruct H; [set_solver|].
          apply formula_is_final in H. apply var_final_initial_var_of in H... }
      2:{ intros contra. set_unfold in contra. destruct contra as (?&?&?).
          rewrite not_and_l in H6. destruct H6; [set_solver|]. destruct H5; [set_solver|].
          apply formula_is_final in H5. apply var_final_initial_var_of in H5... }
      2: set_solver.
      f_equiv.
      2:{
        unfold to_vtmap. f_equal. f_equal.
        - unfold finalized_initial_fvars, initial_fvars.
          do 2 rewrite fvars_foralllist.
          simpl. f_equal. f_equal. admit.
        - unfold finalized_initial_fvars, initial_fvars.
          do 2 rewrite fvars_foralllist.
          simpl. f_equal. f_equal. f_equal. admit.
      }
      rewrite simpl_subst_foralllist...
      2: set_solver.
      rewrite simpl_subst_impl.
      rewrite subst_non_free...
      destruct H3... set_unfold in H. destruct H. apply var_initial_not_final in H3.
      destruct (H3 var_is_final).
    - assert (k_var p) by (apply Hind; naive_solver). unfold k_var in H2.
      mk_fresh ({[as_var x]} ∪
          {[x0]} ∪
          prog_fvars p ∪
          formula_fvars A ∪
          term_fvars t)
        as y.
      rewrite H2 with (y:=y) by set_solver.
      rewrite H2 with (y:=y)...
      2-3: set_solver.
      2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
      unfold FForallT.
      mk_fresh (formula_fvars <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [x \ y] !>) !> ∪
          formula_fvars <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [x0 \ t] [x \ y] !>) !> ∪
          {[as_var x]} ∪
          {[y]} ∪
          {[x0]} ∪
          prog_fvars p ∪
          formula_fvars A ∪
          term_fvars t)
        as z.
      rewrite fforall_alpha_equiv with (x':=z) by set_solver.
      rewrite fforall_alpha_equiv with (x:=x) (x':=z) by set_solver.
      rewrite simpl_subst_forall by set_solver.
      rewrite simpl_subst_forall by set_solver.
      rewrite simpl_subst_forall by set_solver.
      f_equiv. repeat rewrite simpl_subst_impl. repeat rewrite simpl_subst_af.
      simpl. destruct (decide _); [|contradiction]. clear e.
      rewrite subst_term_non_free with (x:=y) by set_solver.
      rewrite subst_term_non_free with (x:=x0) by set_solver.
      f_equiv.
      destruct (decide (as_var x = x0)).
      {
        subst. rewrite fequiv_subst_trans.
        2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
        mk_fresh
          ({[as_var x; y; z]} ∪ formula_fvars (wp p <! A [x \ y] !>) ∪ term_fvars t
             ∪ prog_fvars p ∪ formula_fvars (wp p <! A [x \ t] [x \ y] !>))
          as w.
        rewrite subst_subst_l with (z:=w) by set_solver.
        rewrite subst_subst_l with (x2:=y) (z:=w) by set_solver.
        rewrite H...
        2:{ intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_term_subst_superset in H6. set_solver. }
        rewrite H with (x:=y)...
        2:{ intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_term_subst_superset in H6. set_solver. }
        do 2 f_equiv. apply Hind...
        rewrite fequiv_subst_trans by set_solver.
        rewrite fequiv_subst_trans.
        2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
        simpl. destruct (decide (as_var x = as_var x)); [|contradiction].
        apply subst_subst_eq.
      }
      symmetry.
      trans (<! $(wp p <! A [x \ y] !>) [x0 \ t [x \ y]] [x \ z] [y \ x] !>).
      { do 2 f_equiv.
        rewrite H...
        2: { intros. apply Hind. simpl in *. lia. }
        2: typeclasses eauto.
        2: set_solver.
        2:{ intros i??. apply fvars_term_subst_superset in H5. set_solver. }
        apply Hind... rewrite fsubst_fsubst_ne; set_solver. }
      rewrite fsubst_fsubst_ne with (x2:=x) by set_solver.
      rewrite subst_term_non_free.
      2:{ intros contra. apply fvars_term_subst_superset in contra. set_solver. }
      rewrite fsubst_fsubst_ne with (x1:=x0) (x2:=y) by set_solver.
      rewrite term_subst_trans by set_solver.
      rewrite subst_term_diag...
    - admit.
  Admitted.

  Local Lemma L p : k_congr p ∧ k_const p ∧ k_subst p ∧ k_var p.
  Proof with auto.
    induction p using prog_rank_ind.
    assert (k_congr p) by (apply L_congr; naive_solver).
    assert (k_subst p) by (apply L_subst; naive_solver).
    split_and!...
    - apply L_const...
    - apply L_var...
  Qed.

  Hint Extern 0 (as_final_var (as_var ?x) = ?x) => apply as_final_var_as_var : core.
  Hint Extern 0 (?x = as_final_var (as_var ?x)) => symmetry; apply as_final_var_as_var : core.
  Hint Extern 0 (as_var (as_final_var ?x) = ?x) => apply as_var_as_final_var : core.
  Hint Extern 0 (?x = as_var (as_final_var ?x)) => symmetry; apply as_var_as_final_var : core.

  Lemma wp_congr_post {p A B} :
    A ≡ B →
    wp p A ≡ wp p B.
  Proof with auto.
    intros. induction p; simpl.
    - rewrite H...
    - admit.
    - admit.
    - admit.
    - admit.
    -

  Lemma wp_var {x ty p A} (y : final_variable) :
    as_var y ∉ prog_fvars p →
    as_var y ∉ formula_fvars A →
    wp (PVar x ty p) A ≡ <! ∀ x : ty, $(wp p <! A[x \ y] !>)[y \ x] !>.
  Proof.
    intros. simpl.
    generalize (@fresh_var_final (as_var x)
                  (prog_fvars p ∪ formula_fvars A) (@as_var_var_final x)).
    pose proof (fresh_var_fresh x (prog_fvars p ∪ formula_fvars A)).
    intros. remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as z. clear Heqz.
    f_equiv. generalize dependent A. induction p; intros.
    - simpl. rewrite msubst_subst_comm'.
      + admit.
      + admit.
      + admit.
      + admit.
    - simpl. rewrite IHp1.
    intros. simp wp. simpl.
    generalize (@fresh_var_final (as_var x) (prog_fvars p ∪ formula_fvars A) (@as_var_var_final x)).
    intros. remember (fresh_var x (prog_fvars p ∪ formula_fvars A)) as x'.
    apply f_forall_equiv. intros. do 2 rewrite simpl_subst_impl. do 2 rewrite simpl_subst_af.
    simpl. f_equiv.
    - destruct (decide (x' = x')); try done. destruct (decide (as_var y = as_var y)); try done.
    - rewrite <- wp_subst.
  (* ******************************************************************* *)
  (* definition and properties of ⊑ and ≡ on prog                        *)
  (* ******************************************************************* *)
  Global Instance refines : SqSubsetEq prog := λ p1 p2,
    ∀ A : final_formula, wp p1 A ⇛ (wp p2 A).

  Global Instance pequiv : Equiv prog := λ p1 p2, ∀ A : final_formula, wp p1 A ≡ wp p2 A.
  Global Instance refines_refl : Reflexive refines.
  Proof with auto. intros ??.  reflexivity. Qed.

  Global Instance refines_trans : Transitive refines.
  Proof with auto. intros p1 p2 p3 ?? A... transitivity (wp p2 A); naive_solver. Qed.

  Global Instance pequiv_refl : Reflexive pequiv.
  Proof with auto. split; done. Qed.

  Global Instance pequiv_sym : Symmetric pequiv.
  Proof with auto. intros p1 p2. unfold pequiv. intros. symmetry... Qed.

  Global Instance pequiv_trans : Transitive pequiv.
  Proof with auto. intros p1 p2 p3 ?? A. trans (wp p2 A)... Qed.

  Global Instance pequiv_equiv : Equivalence pequiv.
  Proof. split; [exact pequiv_refl | exact pequiv_sym | exact pequiv_trans]. Qed.

  Global Instance refines_antisym : Antisymmetric prog pequiv refines.
  Proof with auto.
    intros p1 p2 H12 H21. split; intros; [apply H12 in H | apply H21 in H]...
  Qed.

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w : list final_variable.
  Implicit Types xs : list final_variable.
  Implicit Types t : term.

  Lemma wp_asgn xs ts A `{!OfSameLength xs ts} :
    wp <{ *xs := *$(FinalRhsTerm <$> ts) }> A ≡ <! A[[ ↑ₓ xs \ ⇑ₜ ts]] !>.
  Proof with auto.
    rewrite PAsgnWithOpens_no_opens. simpl...
  Qed.

  Lemma f_hastype_unknown t :
    <! ⌜t ∈ₜ ⊤⌝ !> ≡ <! true !>.
  Proof with auto.
    intros σ. split; intros _; [done|]. destruct (teval_total σ t) as [v Hv].
    simp feval. simpl. exists v. split... apply hastype_unknown.
  Qed.

  Lemma f_forall_ty_top x A :
    <! ∀ x : ⊤, A !> ≡ <! ∀ x, A !>.
  Proof. unfold FForallT. rewrite f_hastype_unknown. fSimpl. Qed.

  Lemma f_exists_ty_top x A :
    <! ∃ x : ⊤, A !> ≡ <! ∃ x, A !>.
  Proof. unfold FExistsT. rewrite f_hastype_unknown. fSimpl. Qed.

  (* Lemma wp_varlist xs p A : *)
  (*   wp <{ |[ var* xs ⦁ $p ]| }> A ≡ <! ∀* ↑ₓ xs, $(wp p A) !>. *)
  (* Proof with auto. *)
  (*   induction xs as [|x xs IH]... simpl. rewrite f_forall_ty_top. rewrite <- IH. reflexivity. *)
  (* Qed. *)

  (* Lemma wp_constlist xs p A : *)
  (*   wp <{ |[ con* xs ⦁ $p ]| }> A ≡ <! ∃* ↑ₓ xs, $(wp p A) !>. *)
  (* Proof with auto. *)
  (*   induction xs as [|x xs IH]... simpl. rewrite f_exists_ty_top. rewrite IH. reflexivity. *)
  (* Qed. *)

  Global Instance PVar_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PVar.
  Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PVarList_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PVarList.
  Proof.
    intros xs ? <- ty ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Global Instance PConst_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PConst.
  Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PConstList_proper : Proper ((=) ==> (=) ==> (≡) ==> (≡@{prog})) PConstList.
  Proof.
    intros xs ? <- ty ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Global Instance wp_proper_fequiv : Proper ((=) ==> (≡) ==> (≡)) wp.
  Proof with auto.
    intros p ? <- A B H. generalize dependent B. generalize dependent A.
    induction p; intros A B Hequiv; intros; simpl; fSimpl;
      (try solve [rewrite Hequiv; reflexivity]).
    - apply IHp1. apply IHp2...
    - generalize dependent B. generalize dependent A. induction gcs; intros; simpl...
      apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Hequiv].
      + apply IHgcs...
    - rewrite IHp; [reflexivity|]...
    - rewrite IHp; [reflexivity|]...
  Qed.

  Global Instance wp_proper_fent : Proper ((=) ==> (⇛) ==> (⇛)) wp.
  Proof with auto.
    intros p ? <- A B H. generalize dependent B. generalize dependent A.
    induction p; intros A B Href.
    - simpl. rewrite Href. reflexivity.
    - simpl. apply IHp1. apply IHp2. done.
    - simpl. fSimpl. induction gcs; simpl... apply Forall_cons in H as []. f_equiv.
      + rewrite H; [reflexivity | exact Href].
      + apply IHgcs...
    - simpl. rewrite Href. done.
    - simpl. rewrite Href. done.
    - simpl. rewrite IHp; [reflexivity|]...
    - simpl. rewrite IHp; [reflexivity|]...
  Qed.

  Global Instance wp_proper_pequiv {A : final_formula} : Proper ((≡@{prog}) ==> (≡)) (λ p, wp p A).
  Proof. intros p1 p2 Hp. specialize (Hp A). assumption. Qed.

  Global Instance PSpec_proper : Proper ((=) ==> (≡) ==> (≡) ==> (≡@{prog})) PSpec.
  Proof.
    intros w ? <- A A' ? B B' ?. unfold equiv, ffequiv in H. intros P σ.
    simpl. rewrite H. rewrite H0. done.
  Qed.

  Global Instance ref_proper : Proper ((≡@{prog}) ==> (≡@{prog}) ==> (↔)) (⊑).
  Proof.
    intros p1 p1' ? p2 p2' ?. unfold sqsubseteq, refines. unfold equiv, pequiv, equiv, fequiv in *.
    split; intros.
    - intros σ. intros. apply H0. apply H1. apply H. apply H2.
    - intros σ. intros. apply H0. apply H1. apply H. apply H2.
  Qed.

  Global Instance PWhile_proper : Proper ((≡) ==> (≡@{final_formula}) ==> (=) ==> (=) ==> (≡)) PWhile.
  Proof.
    intros g1 g2 ? I1 I2 ? v ? <- p ? <-. intros A. simpl. unfold equiv,ffequiv in H0.
    rewrite H0. unfold equiv,ffequiv in H. rewrite H. done.
  Qed.

  Global Instance PVar_proper_ref : Proper ((=) ==> (=) ==> (⊑) ==> (⊑)) PVar.
  Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.


  Lemma pequiv_refines {p1 p2} :
    p1 ≡@{prog} p2 → p1 ⊑ p2.
  Proof. intros. intros A. specialize (H A). rewrite H. reflexivity. Qed.

  Lemma pequiv_refines_iff {p1 p2} :
    p1 ≡@{prog} p2 ↔ p1 ⊑ p2 ∧ p2 ⊑ p1.
  Proof with auto.
    split.
    - intros. split; apply pequiv_refines...
    - intros []. unfold equiv, pequiv. intros A σ. specialize (H A σ). specialize (H0 A σ).
      split; intros.
      + apply H...
      + apply H0...
  Qed.

  (*
    The type of [wp p] must be [final_formula → final_formula]. The current definition has two
    limitations that has forced us to define it as [formula → formula] but the notions of
    equivalence and refinement are limited to only final formulas. This prevents us from defining
    proper instances for some constructors like [PSeq] and [PWhile]. The two limitations are
    as follows:
    1. PWhile: [var₀] is chosen explicitly as an initial variable. Currently we do this to ensure
        the chosen new variable is fresh in [inv], [g], [var], and [A]; otherwise it might capture
        an existing variable. Another benefit of the current approach is that [var₀] doesn't
        depent on [p]. This allows to prove for example [wp_proper_fequiv] easily.
      . The correct and tricky way of doing it is to pick a [fresh_var] out
        of the union of the free variables of all these and also UNIVERSALLY QUANTIFY over it to
        ensure no unintentional capture happens.
        The new variable must also be fresh in [p]. (No concept currently corresponds to the set
        of free variables of a program; prog_fvars doesn't work: e.g., it must consider the free
        variables in rhs terms of an assignment.)
    2. PSpec: [post] can contain initial variables. We currently only substitute initial versions
        of frame variables. This approach allows treating this operation as a regular substitution.
        A correct approach is to find ALL initial variables inside post and replace them.
        A new function [initial_vars_of : formula → gset variable] is required for this reason.
    For the time being, to avoid complicating proofs, and also benefit from the proper instances
    for sequential composition and iteration, we assume totality of [pequiv] as an axiom.
   *)
  Axiom refines_total : ∀ {p1 p2}, p1 ⊑ p2 → (∀ (A : formula), wp p1 A ⇛ wp p2 A).

  Lemma pequiv_total  : ∀ {p1 p2}, p1 ≡ p2 → (∀ (A : formula), wp p1 A ≡ wp p2 A).
  Proof with auto.
    intros. apply fequiv_fent_iff. apply pequiv_refines_iff in H as []. split;
      apply refines_total...
  Qed.

  Global Instance PSeq_proper_ref : Proper ((⊑) ==> (⊑) ==> (⊑)) PSeq.
  Proof with auto.
    intros p1 p1' ? p2 p2' ?. intros A σ ?. simpl in *. apply @refines_total with (p1:=p1)...
    pose proof (wp_proper_fent p1 p1 eq_refl (wp p2 A) (wp p2' A)). apply H2...
  Qed.

  Lemma PWhile_equiv g1 g2 I1 I2 v p1 p2 :
    g1 ≡ g2 →
    I1 ≡ I2 →
    Δ p1 = Δ p2 →
    p1 ≡ p2 →
    PWhile g1 I1 v p1 ≡ PWhile g2 I2 v p2.
  Proof with auto.
    intros. rewrite H. rewrite H0. clear H g1 H0 I1. intros A. simpl. rewrite H1.
    f_equiv. f_equiv...
    - fSimpl. unfold equiv, pequiv in H2. apply H2.
    - fSimpl. pose proof (pequiv_total H2). apply H.
  Qed.


  Lemma r_while_body {g I v p1 p2} :
    Δ p1 = Δ p2 →
    p1 ⊑ p2 →
    PWhile g I v p1 ⊑ PWhile g I v p2.
  Proof with auto.
    intros. intros A. simpl. rewrite H. f_equiv. f_equiv...
    - fSimpl. apply refines_total...
    - fSimpl. apply refines_total...
  Qed.

End semantics.
