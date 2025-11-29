From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
(* From Stdlib Require Import Strings.String. *)
From MRC Require Import Prelude.
From MRC Require Import SeqNotation.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section refinement.
  Context {M : model}.
  Local Notation value := (value M).
  Local Notation prog := (@prog M).
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  (* Implicit Types ts : list term. *)


  Lemma r_strengthen_post w pre post post' `{FormulaFinal _ pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A Hinit. simpl. f_simpl. rewrite <- Hent. reflexivity.
  Qed.

  Lemma r_weaken_pre w pre pre' post `{FormulaFinal _ pre} `{FormulaFinal _ pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A Hinit. simpl. f_simpl. assumption.
  Qed.

  Lemma r_contract_frame (x : final_variable) pre post `{FormulaFinal _ pre} :
    <{ x : [pre, post] }> ⊑ <{ : [pre, post[₀x\x] ] }>.
  Proof with auto.
    intros A Hfree. simpl. f_simpl. rewrite f_forall_elim_binder.
    unfold subst_initials. simpl. rewrite simpl_subst_impl.
    rewrite fequiv_subst_non_free with (A:=A).
    - reflexivity.
    - intros contra. apply initial_var_of_elem_of_formula_fvars in contra. contradiction.
  Qed.

(* Ltac split_eqlist_fmap_app l1 l2 f g := *)
(*   repeat match goal with *)
(*     | H : context[@FEqList (f <$> l1 ++ l2) (f <$> l1 ++ l2) ?Hlength] |- _ => *)
(*         rewrite (@f_eqlist_fmap_app _ l1 l2 ?f ?g ?Hlength _ _) in H *)
(*     | |- context[@FEqList (f <$> l1 ++ l2) (g <$> l1 ++ l2) ?Hlength] => *)
(*         assert (True); *)
(*         rewrite (@f_eqlist_fmap_app _ l1 l2 ?f ?g ?Hlength _ _) *)
(*     | |- context[FEqList (?f <$> ?l1) ?l2] => *)
(*         let H := fresh in *)
(*         idtac f l1 *)
(*     end. *)

(* Notation "↑ₓ xs" := (as_var <$> xs : list variable) (at level 0, *)
(*                       xs constr at level 0) : refiney_scope. *)
(* Notation "↑₀ xs" := (initial_var_of <$> xs : list variable) (at level 0, *)
(*                       xs constr at level 0) : refiney_scope. *)
(* Notation "⇑ₓ xs" := (TVar ∘ as_var <$> xs : list term) (at level 0, *)
(*                       xs constr at level 0) : refiney_scope. *)
(* Notation "⇑₀ xs" := (TVar ∘ initial_var_of <$> xs : list term) (at level 0, *)
(*                       xs constr at level 0) : refiney_scope. *)
(* Notation "⇑ₜ ts" := (as_term <$> ts : list term) (at level 0, *)
(*                       ts constr at level 0) : refiney_scope. *)
(* Notation "₀ xs" := (initial_var_of <$> xs : list variable) (at level 0, *)
(*                       xs constr at level 0) : refiney_scope. *)

(* Notation "xs |ₓ" := (as_var <$> xs : list variable) (at level 0). *)
(* Notation "xs |ₓ₀" := (initial_var_of <$> xs : list variable) (at level 0). *)
(* Notation "xs |ₜ" := (TVar ∘ as_var <$> xs : list term) (at level 0). *)
(* Axiom xs : list final_variable. *)
(* Definition x := xs|ₓ₀. *)
(* Definition t := xs|ₜ. *)
(* Notation "'ₓ( xs )" := (as_var <$> xs : list term) (at level 0). *)
(* Notation "' xs" := (TVar ∘ as_var <$> xs : list term) *)
(*                        (in custom term at level 0, *)
(*                            xs constr at level 0) : refiney_scope. *)
(* Notation "'₀ xs" := (TVar ∘ initial_var_of <$> xs : list term) *)
(*                        (in custom term at level 0, *)
(*                            xs constr at level 0) : refiney_scope. *)

(* Notation "%% t" := (as_term t) *)
(*                      (in custom term at level 0, only parsing, *)
(*                          t constr at level 0) : refiney_scope. *)
(* (* Notation "% x" := (as_var x) *) *)
(* (*                        (in custom term at level 0, *) *)
(* (*                            only parsing, *) *)
(* (*                            x constr at level 0) : refiney_scope. *) *)
(* Notation "% xs" := (as_var <$> xs) *)
(*                        (in custom term at level 0, *)
(*                            xs constr at level 0) : refiney_scope. *)

(* Notation "%₀ xs" := (initial_var_of <$> xs) *)
(*                        (in custom term at level 0, *)
(*                            xs constr at level 0) : refiney_scope. *)

(* Notation "% A" := (as_formula A) *)
(*                     (in custom formula at level 0, only parsing, *)
(*                         A constr at level 0) : refiney_scope. *)

(* Notation "↑ₓ x" := () *)
(* ₜₓ *)

  Lemma r_assignment w xs pre post ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ ⎡⇑₀ xs =* ⇑ₓ xs⎤ ∧ pre !> ⇛ <! post[[ ↑ₓ xs \ ⇑ₜ ts ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros Hlength Hnodup proviso A Hfinal. simpl. rewrite wp_asgn.
    assert (<! pre !> ≡ <! pre [_₀\w ++ xs] !>) as ->.
    { rewrite f_subst_initials_final_formula...  }
    rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials. rewrite <- f_foralllist_one_point...
    rewrite f_foralllist_app. rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite (f_foralllist_elim_as_ssubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    2:{ apply NoDup_fmap... apply as_var_inj. }
    erewrite f_eqlist_replace. Unshelve.
    4: { do 2 rewrite fmap_app. do 2 rewrite <- list_fmap_compose. reflexivity. }
    3: { rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_ssubst_impl.
    f_simpl. rewrite <- f_eqlist_app.
    erewrite f_eqlist_replace. Unshelve.
    5: { rewrite <- fmap_app. rewrite list_fmap_compose. reflexivity. }
    3: { rewrite <- fmap_app. reflexivity. }
    pose proof (@f_foralllist_one_point M
                  (initial_var_of <$> (w ++ xs)) ((TVar ∘ as_var <$> (w++xs)))) as ->...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula.
    2: { unfold formula_final. intros. apply fvars_ssubst_superset in H1.
         set_unfold. destruct H1.
         - apply Hfinal...
         - apply elem_of_union_list in H1 as (fvars&?&?).
           apply elem_of_list_fmap in H1 as (t&->&?).
           apply elem_of_list_fmap in H1 as (t'&->&?).
           pose proof (final_term_final t').
           apply H3... }
    reflexivity.
  Qed.


  Lemma r_alternation

  Lemma r_iteration w (I : formula) (v : variable) gcs :
    w : [inv, inv ∧ ¬ (gcomc_any_guard gcs)] ⊑ `PDo gcs`






Lemma assignment : forall pre post x E,
  pre ⇛ post[x \ E] ->
  <{ x : [pre, post] ⊑ x := E }>.
Proof.
  intros pre post w E H A Hfree. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

