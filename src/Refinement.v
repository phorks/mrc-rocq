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


  (* Law 1.1 *)
  Lemma r_strengthen_post w pre post post' `{FormulaFinal _ pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl. f_simpl. rewrite <- Hent. reflexivity.
  Qed.

  (* Law 1.2 *)
  Lemma r_weaken_pre w pre pre' post `{FormulaFinal _ pre} `{FormulaFinal _ pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A. simpl. f_simpl. assumption.
  Qed.

  Lemma r_permute_frame w w' pre post `{FormulaFinal _ pre} :
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros. split; intros A.
    - simpl. f_simpl. rewrite subst_initials_perm with (xs':=w')... f_equiv.
      rewrite f_foralllist_permute with (xs':=(fmap as_var w')).
      + reflexivity.
      + apply Permutation_map...
    - symmetry in H0. simpl. f_simpl. rewrite subst_initials_perm with (xs':=w)... f_equiv.
      rewrite f_foralllist_permute with (xs':=(fmap as_var w)).
      + reflexivity.
      + apply Permutation_map...
  Qed.

  (* Law 5.4 *)
  Lemma r_contract_frame w xs pre post `{FormulaFinal _ pre} :
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs] ] }>.
  Proof with auto.
    intros Hdisjoint A. simpl. f_simpl.
    rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist.
    2: { set_solver. }
    2: { intros x. intros. apply elem_of_union_list in H1 as (fvars&?&?).
         apply elem_of_list_to_set in H0. apply elem_of_list_fmap in H0 as (x'&?&?).
         apply elem_of_list_fmap in H1 as (t&?&?). apply elem_of_list_fmap in H4 as (y'&?&?).
         set_solver. }
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    f_simpl. rewrite f_subst_initials_final_formula... reflexivity.
  Qed.

  Lemma r_skip' w pre post `{FormulaFinal _ pre} :
    pre ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A Hfinal. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    f_simpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite H0. rewrite f_impl_elim. rewrite f_foralllist_one_point...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula...
  Qed.

  Lemma r_skip w pre post `{FormulaFinal _ pre} :
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ pre !> ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A Hfinal. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    f_simpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite f_impl_dup_hyp. rewrite f_and_assoc. rewrite H0. rewrite f_impl_elim.
    rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
  Qed.

  (* Lemma something A (x y : variable) : *)
  (*   y ≠ x → *)
  (*   <! A[y \ x] !> ≡ <! ∀ y, ⌜y = x⌝ ⇒ A[x \ y] !>. *)
  (* Proof with auto. *)
  (*   intros. *)
  (*   rewrite f_forall_one_point. *)
  (*   2:{ simpl. set_solver. } *)
  (*   intros σ; split; intros. *)
  (*   -  *)
  (*   rewrite fequiv_subst_trans. *)
  (*   intros σ.  *)

  (*   intros σ. unfold FImpl. intros. destruct (feval_lem σ <! ⌜x = t⌝ !>). *)
  (*   - simp feval in *. destruct H0 as (v&?&?). right. rewrite feval_subst with (v:=v)... *)
  (*     inversion H0. rewrite (lookup_total_alt σ) in H3. unfold state in *. *)
  (*     destruct (σ !! x) eqn:E. *)
  (*     + simpl in H3. subst. rewrite (insert_id σ)... *)
  (*     + simpl in H3. subst v. rewrite feval_delete_bottom_from_state... *)
  (*       apply (not_elem_of_dom σ)... *)
  (*   - simp feval in *. simpl in *. left... *)
  (* Qed. *)

  (* Lemma other_thing A w : *)
  (*   <! A !> ⇛ <! ⎡⇑₀ w =* ⇑ₓ w⎤ ⇒ A[_₀\ w] !>. *)
  (* Proof. f_forall_one_point Admitted. *)

  (* Lemma other_thing2 w : *)
  (*   <! ⎡⇑₀ w =* ⇑ₓ w⎤ [_₀\ w] !> ≡@{formula} <! true !>. *)
  (* Proof. Admitted. *)

  (* Lemma r_seq (w : final_variable) pre mid post `{FormulaFinal _ pre} `{FormulaFinal _ mid} : *)
  (*   <{ w : [pre, post] }> ⊑ <{ w : [pre, mid]; w : [mid, post] }>. *)
  (* Proof with auto. *)
  (*   intros A Hfinal. simpl. unfold subst_initials. simpl. *)
  (*   apply f_ent_and_cancel_l. *)
  (*   rewrite f_impl_and_r. rewrite f_implies_self. rewrite f_and_comm. rewrite f_and_true. *)

  (*   rewrite <- f_forall_one_point... *)
  (*   2:{ admit. } *)

  (*   unfold subst_initials at 1. *)
  (*   repeat rewrite <- f_foralllist_one_point... *)
  (* Lemma something A w : *)
  (*   <! A[_₀\ w][_₀\ w] !> ≡ <! A[_₀\ w] !>. *)
  (* Proof with auto. Admitted. *)

  (* Lemma f_foralllist_impl (xs : list variable) A B : *)
  (*   <! ∀* xs, A ⇒ B !> ⇛ <! (∀* xs, A) ⇒ (∀* xs, B) !>. *)
  (* Proof. Admitted. *)

  Lemma r_seq w pre mid post `{FormulaFinal _ pre} `{FormulaFinal _ mid} `{FormulaFinal _ post} :
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, mid]; *w : [mid, post] }>.
  Proof with auto.
    intros A. assert (FormulaFinal A) by typeclasses eauto.
    simpl. f_simpl. rewrite f_impl_and_r. f_simpl.
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_foralllist_impl_unused_r _ mid).
    2:{ rewrite fvars_foralllist. set_solver. }
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.
    (* 2:{ apply FForallList_final. typeclasses eauto. } *)


    (* (* f_forall_ *) *)

    (* rewrite <- (f_subst_initials_final_formula mid w) at 1... *)
    (* rewrite <- simpl_subst_initials_impl. *)
    (* unfold subst_initials at 2. *)
    (* rewrite seqsubst_non_free. *)
    (* 2:{ rewrite fvars_foralllist. rewrite fvars_subst_initials. *)
    (*     set_unfold. intros x [ [ [? ?] |] ?] ?; [set_solver|]. *)
    (*     apply elem_of_subst_initials_var_fvars in H2. set_solver. } *)
    (* rewrite simpl_subst_initials_impl. *)
    (* rewrite (f_subst_initials_final_formula mid w) at 1... *)


    (* unfold subst_initials at 1. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* rewrite (f_foralllist_impl (as_var <$> w) post A) at 1. *)
    (* rewrite f_impl_curry. rewrite f_impl_and_l. rewrite f_forall_or *)



    (* f_forall_impl *)


    (* (* unfold subst_initials at 2. *) *)
    (* (* repeat rewrite <- f_foralllist_one_point... *) *)
    (* (* (* unfold subst_initials at 2. *) *) *)
    (* (* unfold subst_initials at 1. *) *)
    (* (* repeat rewrite <- f_foralllist_one_point... *) *)
    (* (* f_forall_and *) *)

    (* (* rewrite f_foralllist_comm. *) *)
    (* (* unfold subst_initials at 1. *) *)
    (* (* repeat rewrite <- f_foralllist_one_point... *) *)

    (* (*     simpl. *) *)

    (* rewrite <- (f_subst_initials_final_formula mid w) at 1... *)
    (* rewrite <- simpl_subst_initials_impl. *)
    (* rewrite <- (f_subst_initials_final_formula post w) at 2... *)
    (* unfold subst_initials at 3. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* unfold subst_initials at 2. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* rewrite (f_foralllist_impl_unused_r (initial_var_of <$> w)). *)
    (* 2:{ rewrite fvars_foralllist. simpl. rewrite fvars_foralllist. simpl. *)
    (*     assert (list_to_set (initial_var_of <$> w) ## formula_fvars mid). *)
    (*     { set_unfold. intros. apply formula_is_final in H3. *)
    (*       destruct H2 as (?&?&?). rewrite H2 in H3. unfold var_final in H3. *)
    (*       simpl in H3. discriminate. *)
    (*     } *)
    (*     set_solver. } *)
    (* assert (<! ∃* ↑₀ w, ⎡⇑₀ w =* ⇑ₓ w⎤ !> ≡@{formula} <! true !>) by admit. *)
    (* rewrite H2. rewrite f_true_implies. *)

    (* (* rewrite f_impl_curry. rewrite f_and_comm. rewrite <- f_impl_curry. *) *)
    (* (* rewrite (f_foralllist_impl_unused_l (initial_var_of <$> w)). *) *)
    (* (* 2:{ admit. } *) *)
    (* (* rewrite f_foralllist_one_point... rewrite fold_subst_initials. *) *)


    (* (* rewrite f_foralllist_one_point... rewrite fold_subst_initials. *) *)
    (* (* rewrite (f_foralllist_impl_unused_r (as_var <$> w) mid). *) *)
    (* (* rewrite  *) *)
    (* rewrite f_foralllist_comm. rewrite f_impl_curry. *)
    (* rewrite (f_foralllist_impl_unused_r (as_var <$> w) <! ⎡ ⇑₀ w =* ⇑ₓ w ⎤ ∧ mid !>). *)
    (* 2:{ rewrite fvars_foralllist. set_solver. } *)
    (* unfold subst_initials. *)
    (* repeat rewrite <- f_foralllist_one_point... *)

    (* (* rewrite (f_foralllist_impl_unused_r (initial_var_of <$> w) <! ⎡ ⇑₀ w =* ⇑ₓ w ⎤ !>). *) *)
    (* (* 2:{ rewrite fvars_foralllist. set_solver. } *) *)
    (* (* rewrite <- f_foralllist_idemp at 1. *) *)
    (* (* rewrite  *) *)
    (* f_equiv. *)
    (* f_equiv. *)
    (* rewrite <- flip_fent. *)
    (* rewrite (f_existslist_intro_binders. *)


    (* Set Printing Parentheses. *)
    (* rewrite (f_foralllist_impl_unused_r (as_var <$> w)) at 2. *)
    (* assert (<! ⎡⇑₀ w =* ⇑ₓ w⎤ !> ≡@{formula} <! ⎡⇑ₓ w =* ⇑₀ w⎤ !> ) by admit. *)
    (* rewrite H2. *)
    (* rewrite f_foralllist_one_point... *)
    (* unfold subst_initials at 1. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* f_equiv. *)

    (* rewrite <- f_foralllist_one_point... *)
    (* unfold susbt_init *)
    (* rewrite f_foralllist_one_point... *)
    (* forall_impl *)


    (* rewrite <- (f_subst_initials_final_formula mid w) at 1... *)
    (* rewrite <- simpl_subst_initials_impl. *)
    (* unfold subst_initials at 3. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* unfold subst_initials at 2. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* rewrite <- f_foralllist_app. *)
    (* unfold subst_initials. *)
    (* rewrite <- f_foralllist_one_point... *)
    (* rewrite f_foralllist_idemp. *)

    (* rewrite (f_intro_hyp mid) at 1. *)
    (* rewrite <- (f_subst_initials_final_formula mid w) at 1... *)
    (* rewrite <- simpl_subst_initials_impl. *)
    (* unfold subst_initials at 1. *)
    (* repeat rewrite <- f_foralllist_one_point... *)


    (* rewrite (other_thing _ w) at 1. *)
    (* rewrite (other_thing _ w) at 1. *)

    (* r *)
    (* unfold subst_initials at 1 3. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* rewrite <- f_foralllist_idemp at 1. *)
    (* unfold subst_initials at 1. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* rewrite (f_intro_hyp mid) at 5. *)
    (* rewrite <- (f_subst_initials_final_formula mid w) at 1... *)
    (* rewrite <- simpl_subst_initials_impl. *)
    (* rewrite f_intro_hyp *)
    (* unfold subst_initials at 1 2. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* rewrite f_impl_dup_hyp at 1. rewrite <- f_foralllist_idemp at 1. *)
    (* f_equiv. rewrite f_foralllist_one_point... rewrite fold_subst_initials. *)
    (* rewrite simpl_subst_initials_and. *)
    (* f_equiv. f_simpl. unfold subst_initials. rewrite <- f_foralllist_one_point... *)
    (* f_equiv. *)

    (* unfold subst_initials at 1 2. *)
    (* repeat rewrite <- f_foralllist_one_point... *)




    (* rewrite (f_foralllist_impl_unused_r _ mid). *)
    (* 2: { rewrite formula_fvars } *)

    (* rewrite f_implies_self. *)
    (* f_simpl. *)

    (* unfold subst_initials at 1 2. *)
    (* repeat rewrite <- f_foralllist_one_point... *)
    (* f_equiv. f_simpl. *)
    (* rewrite f_and_comm. rewrite f_and_true. *)

    (* unfold subst_initials. rewrite <- f_foralllist_one_point... f_equiv. *)
    (* rewrite <- f_foralllist_one_point at 1... *)
    (* f_foralllist_elim_as_ssubst *)
    (* rewrite (f_intro_hyp mid) at 1. *)


    (* rewrite f_impl_dup_hyp *)
    (* f_equiv. f_equiv. rewrite fold_subst_initials. *)

  Lemma r_assignment w xs pre post ts `{FormulaFinal _ pre} `{OfSameLength _ _ xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ ⎡⇑₀ xs =* ⇑ₓ xs⎤ ∧ pre !> ⇛ <! post[[ ↑ₓ xs \ ⇑ₜ ts ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts)  }>.
  Proof with auto.
    intros Hlength Hnodup proviso A. simpl. rewrite wp_asgn.
    rewrite <- (f_subst_initials_final_formula pre (w ++ xs))...
    rewrite <- simpl_subst_initials_and. rewrite fmap_app.
    unfold subst_initials. rewrite <- f_foralllist_one_point...
    rewrite f_foralllist_app. rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite (f_foralllist_elim_as_ssubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    2:{ apply NoDup_fmap... apply as_var_inj. }
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite fmap_app. reflexivity. }
    3: { do 2 rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_ssubst_impl.
    f_simpl. rewrite <- f_eqlist_app.
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    3: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    pose proof (@f_foralllist_one_point M
                  (initial_var_of <$> (w ++ xs)) ((TVar <$> (as_var <$> (w++xs))))) as ->...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula'.
    2: { unfold formula_final. intros. apply fvars_ssubst_superset in H1.
         set_unfold. destruct H1.
         - apply final_formula_final in H1...
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
  intros pre post w E H A Hfinal. simpl. etrans.
  -
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

