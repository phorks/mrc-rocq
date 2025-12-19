From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
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
  Local Notation state := (@state M).
  Local Notation term := (term value).
  Local Notation formula := (formula value).
  Local Notation final_term := (final_term value).
  Local Notation final_formula := (final_formula value).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  Implicit Types gs : list final_formula.
  (* Implicit Types ts : list term. *)

  (* TODO: reorder laws *)
  (* 1.8 *)
  Lemma r_absorb_assumption pre' w pre post `{!FormulaFinal pre'} `{!FormulaFinal pre} :
    <{ {pre'}; *w : [pre, post] }> ≡ <{ *w : [pre' ∧ pre, post] }>.
  Proof with auto.
    intros A. simpl. repeat rewrite subst_initials_nil. fSimpl. rewrite f_and_assoc...
  Qed.

  (* Law 1.1 *)
  Lemma r_strengthen_post w pre post post' `{!FormulaFinal pre} :
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl. fSimpl. rewrite <- Hent. reflexivity.
  Qed.


  (* Law 5.1 *)
  Lemma r_strengthen_post_with_initials w pre post post' `{!FormulaFinal pre} :
    <! pre[; ↑ₓ w \ ⇑₀ w ;] ∧ post' !> ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros Hent A. simpl.
    rewrite <- Hent. rewrite <- f_impl_curry. rewrite -> f_foralllist_impl_unused_l.
    2: { intros x ? ?. apply (fvars_seqsubst_superset_vars_not_free_in_terms) in H0...
         set_solver. }
    rewrite simpl_subst_initials_impl. rewrite subst_initials_inverse_l by set_solver...
    rewrite <- (f_and_idemp pre) at 1. rewrite <- f_and_assoc. fSimpl.
    reflexivity.
  Qed.

  (* Law 1.2 *)
  Lemma r_weaken_pre w pre pre' post `{!FormulaFinal pre} `{!FormulaFinal pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A. simpl. fSimpl. assumption.
  Qed.

  Lemma r_permute_frame w w' pre post `{!FormulaFinal pre} :
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros H A. simpl. fSimpl. rewrite subst_initials_perm with (xs':=w')... f_equiv.
      rewrite f_foralllist_permute with (xs':=(fmap as_var w'))... apply Permutation_map...
  Qed.

  (* Law 5.4 *)
  Lemma r_contract_frame w xs pre post `{!FormulaFinal pre} :
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs]] }>.
  Proof with auto.
    intros Hdisjoint A. simpl. fSimpl.
    rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist by set_solver.
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    fSimpl. rewrite f_subst_initials_final_formula...
  Qed.

  Lemma fequiv_st_lem σ A B :
    A ≡_{σ} B ∨ ¬ A ≡_{σ} B.
  Proof with auto.
    destruct (feval_lem σ A); destruct (feval_lem σ B).
    - left. done.
    - right. intros []...
    - right. intros []...
    - left. done.
  Qed.

  Lemma r_expand_frame_1 xs w pre post `{!FormulaFinal pre} :
    w ## xs →
    <! post[_₀\ xs] !> ≡ post →
    <{ *w : [pre, post] }> ⊑ <{ *w, *xs : [pre, post ∧ ⎡⇑ₓ xs =* ⇑₀ xs⎤] }>.
  Proof with auto.
    intros Hdisjoint H A. simpl. fSimpl.
    unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite <- f_foralllist_one_point...
    erewrite (@eqlist_rewrite _ (⇑₀ (w ++ xs))). Unshelve.
    4-5: do 2 rewrite fmap_app; reflexivity.
    rewrite f_eqlist_app. rewrite fmap_app. rewrite foralllist_app.
    rewrite <- f_impl_curry. rewrite (f_foralllist_impl_unused_l (↑₀ xs)).
    2:{ intros ???. rewrite fvars_eqlist in H1. set_solver. }
    f_equiv. f_equiv.
    rewrite f_and_comm. rewrite <- f_impl_curry.
    rewrite fmap_app. rewrite foralllist_app.
    rewrite f_foralllist_comm.
    rewrite (f_foralllist_impl_unused_l (↑ₓ w) _ <! post ⇒ A !>).
    2:{ intros ???. rewrite fvars_eqlist in H1. set_solver. }
    setoid_rewrite (f_foralllist_one_point (↑ₓ xs))...
    rewrite f_foralllist_one_point... setoid_rewrite <- H at 2. rewrite fold_subst_initials.
    rewrite subst_initials_inverse_l...
    1: { rewrite H... }
    intros x ??. set_unfold. destruct H1. clear H2.
    destruct H1 as [[[] |] |]; [set_solver|set_solver|].
    apply formula_is_final in H1. naive_solver.
    Unshelve. typeclasses eauto.
  Qed.

  (* Law 3.2 *)
  Lemma r_skip w pre post `{!FormulaFinal pre} :
    pre ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    fSimpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite H. rewrite f_impl_elim. rewrite f_foralllist_one_point...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 5.3 *)
  Lemma r_skip_with_initials w pre post `{!FormulaFinal pre} :
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ pre !> ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. simpl. unfold subst_initials. simpl. rewrite fold_subst_initials.
    fSimpl. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite f_impl_dup_hyp. rewrite f_and_assoc. rewrite H. rewrite f_impl_elim.
    rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 3.3 *)
  Lemma r_seq w pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} `{!FormulaFinal post} :
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, mid]; *w : [mid, post] }>.
  Proof with auto.
    intros A. simpl. fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_foralllist_impl_unused_r _ mid) by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* Law B.2 *)
  Lemma r_seq_frame w xs pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} :
    w ## xs →
    list_to_set (↑₀ xs) ## formula_fvars post →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs : [pre, mid]; *w, *xs : [mid, post] }>.
  Proof with auto.
    intros. intros A. simpl. fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (subst_initials_app _ w xs).
    assert (formula_fvars <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> ## list_to_set (↑₀ xs)).
    { intros x ??. set_unfold in H1. destruct H1 as ([|]&?); [set_solver|].
      set_unfold. destruct H2 as [? _]. apply elem_of_fvars_final_formula_inv in H1... }
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials _ xs) at 1 by set_solver...
    rewrite (f_foralllist_impl_unused_r (↑ₓ xs)) at 1 by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  Lemma r_following_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!OfSameLength xs ts} :
    length xs ≠ 0 →
    NoDup xs →
    <{ *w, *xs : [pre, post] }> ⊑
    <{ *w, *xs : [pre, post[[↑ₓ xs \ ⇑ₜ ts]]]; *xs := *(FinalRhsTerm <$> ts) }>.
  Proof with auto.
    intros Hlength Hnodup A. simpl. rewrite wp_asgn. fSimpl. rewrite <- simpl_msubst_impl.
    f_equiv. rewrite fmap_app. do 2 rewrite foralllist_app. f_equiv.
    rewrite <- f_foralllist_idemp. rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !>)...
    - reflexivity.
    - rewrite length_fmap...
  Qed.

  Lemma r_leading_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!FormulaFinal <! pre[[↑ₓ xs \ ⇑ₜ ts]] !>} :
    w ## xs →
    NoDup w →
    NoDup xs →
    let ts₀ := (λ t : final_term, <! t[[ₜ ↑ₓ w, ↑ₓ xs \ ⇑₀ w, ⇑₀ xs]] !>) <$> ts in
    <{ *w, *xs : [pre[[↑ₓ xs \ ⇑ₜ ts]], post[[↑₀ xs \ *ts₀]]] }> ⊑
      <{ *xs := *(FinalRhsTerm <$> ts); *w, *xs : [pre, post] }>.
  Proof with auto.
    intros Hdisjoint Hnodup1 Hnodup2 ? A. simpl. rewrite wp_asgn. rewrite simpl_msubst_and.
    fSimpl. unfold subst_initials at 1. rewrite subst_initials_app_comm.
    rewrite subst_initials_app. rewrite subst_initials_msubst.
    setoid_rewrite (msubst_trans _ (↑₀ xs) (↑ₓ xs) (⇑ₜ ts)); [| set_solver | |]...
    2:{ intros x ??. set_unfold. destruct H0 as [|]; [set_solver|].
        destruct H. destruct H0 as (x'&?&?&_&_). subst.
        rewrite to_final_var_as_var in H1. set_solver. }
    assert (zip_pair_functional ↑₀ xs ⇑ₜ ts).
    { apply NoDup_zip_pair_functional. apply NoDup_fmap... apply initial_var_of_inj. }
    assert (list_to_set ↑₀ xs ## ⋃ (term_fvars <$> ⇑ₜ ts)).
    { intros x ??. set_unfold in H0. set_unfold in H1. destruct H1 as (t&?&t'&?&?).
      subst. destruct H0 as []. apply final_term_final in H1. done. }
    assert (as_formula A ≡ <! A [[↑₀ xs \ *ts₀]] !>).
    { rewrite msubst_non_free... intros x ??. apply formula_is_final in H2. set_solver. }
    rewrite H1 at 1. clear H1. rewrite <- simpl_msubst_impl.
    assert (<! (∀* ↑ₓ (w ++ xs), (post ⇒ A) [ [↑₀ xs \ * ts₀] ]) !> ≡
              <! (∀* ↑ₓ (w ++ xs), (post ⇒ A)) [ [↑₀ xs \ * ts₀] ] !>).
    { rewrite simpl_msubst_foralllist; [auto|set_solver|]. intros x ??. set_unfold in H1.
      destruct H1 as []. set_unfold in H2. destruct H2 as (t&?&t'&?&?). subst.
      apply fvars_msubst_term_superset_vars_not_free_in_terms in H2...
      - set_unfold in H2. destruct H2 as [[] |].
        + apply Decidable.not_or in H4 as []. destruct H3.
          * apply H4. exists (to_final_var x). split... rewrite as_var_to_final_var.
            symmetry. apply var_with_is_initial_id. apply H1.
          * apply H6. exists (to_final_var x). split... rewrite as_var_to_final_var.
            symmetry. apply var_with_is_initial_id. apply H1.
        + destruct H2 as (t&?&?). destruct H4.
          * destruct H4 as (x'&->&?&?&?). simpl in H2. set_unfold in H2. subst x'.
            rewrite H4 in H1. unfold var_final in H1. simpl in H1. discriminate.
          * destruct H4 as (x'&->&?&?&?). simpl in H2. set_unfold in H2. subst x'.
            rewrite H4 in H1. unfold var_final in H1. simpl in H1. discriminate.
      - apply NoDup_app. do 2 rewrite NoDup_fmap by apply as_var_inj. set_solver.
      - apply disjoint_final_initial_vars; [set_solver|]. clear dependent x. intros x ??.
        rewrite <- fmap_app in H1. set_unfold in H1. destruct H1 as (t&?&x'&->&?).
        destruct H3; destruct H3 as (?&->&?); set_unfold in H1; subst x; done. }
    rewrite H1. clear H1.
    rewrite fold_subst_initials. rewrite subst_initials_app.
    rewrite (subst_initials_msubst xs). rewrite msubst_msubst_eq.
    2:{ apply NoDup_fmap... apply initial_var_of_inj. }
    rewrite subst_initials_msubst. rewrite msubst_msubst_disj.
    2:{ set_solver. }
    2-3: apply NoDup_fmap; auto; apply initial_var_of_inj.
    2:{ set_solver. }
    rewrite <- subst_initials_msubst. f_equiv. apply map_eq. intros x₀. unfold to_var_term_map.
    destruct (decide (x₀ ∈ ↑₀ xs)).
    - apply elem_of_list_fmap in e as (x'&?&?). apply elem_of_list_lookup in H2 as (i&?).
      destruct (lookup_of_same_length_l ts H2) as (t&?). trans (Some (as_term t)).
      + rewrite lookup_list_to_map_zip_Some by typeclasses eauto. exists i. split_and!.
        * rewrite list_lookup_fmap. rewrite H2. simpl. rewrite H1...
        * unfold ts₀. repeat rewrite list_lookup_fmap. rewrite H3.
          simpl. f_equal.
          opose proof msubst_term_app. unfold to_var_term_map in H4 at 2 3.
          assert (xs ## w) by set_solver.
          erewrite <- H4; clear H4... rewrite msubst_term_app_comm...
          opose proof (msubst_term_trans t (↑ₓ w ++ ↑ₓ xs) (↑₀ w ++ ↑₀ xs) (⇑ₓ w ++ ⇑ₓ xs)).
             trans (msubst_term t (to_var_term_map (↑ₓ w ++ ↑ₓ xs) ((@TVar value <$> (as_var <$> w)) ++
                                                           (@TVar value <$> (as_var <$> xs))))).
             -- symmetry. etrans.
                ++ rewrite <- H4; clear dependent H4 H ts₀; [reflexivity| | | | ].
                   ** set_solver.
                   ** rewrite NoDup_app.
                      repeat rewrite NoDup_fmap; [| apply as_var_inj | apply as_var_inj].
                      set_solver.
                   ** rewrite <- fmap_app. apply NoDup_fmap; [apply initial_var_of_inj|].
                      apply NoDup_app...
                   ** clear dependent x₀ x'. intros x ??. set_unfold in H.
                      apply term_is_final in H1. destruct H as [[x' [? ?]] | [x' [? ?]]]; subst;
                        done.
                ++ f_equal. f_equal. unfold to_var_term_map. f_equal. f_equal. rewrite fmap_app...
             -- unfold to_var_term_map. repeat rewrite <- fmap_app. rewrite msubst_term_diag...
                apply NoDup_fmap; [apply as_var_inj|]. apply NoDup_app...
        * intros. apply list_lookup_fmap_Some in H4 as (x''&?&?). rewrite H1 in H5.
          apply initial_var_of_inj in H5. subst x''. apply NoDup_lookup with (i:=i) in H4...
          lia.
      + symmetry. subst. apply lookup_list_to_map_zip_Some; [typeclasses eauto|]. exists i.
        split_and!...
        * rewrite list_lookup_fmap. rewrite H2. simpl...
        * rewrite list_lookup_fmap. rewrite H3. simpl...
        * intros. apply list_lookup_fmap_Some in H1 as (x''&?&?). apply initial_var_of_inj in H4.
          subst x''. apply NoDup_lookup with (i:=i) in H1... lia.
    - etrans.
      + apply lookup_list_to_map_zip_None... typeclasses eauto.
      + symmetry. apply lookup_list_to_map_zip_None... typeclasses eauto.
  Qed.


  (* Law 5.2 *)
  Lemma r_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} :
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
    rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !> _ (as_term <$> ts))...
    2:{ rewrite length_fmap... }
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite fmap_app. reflexivity. }
    3: { do 2 rewrite fmap_app. reflexivity. }
    rewrite f_eqlist_app. rewrite f_impl_dup_hyp. rewrite (f_and_assoc _ pre).
    rewrite f_and_assoc in proviso. rewrite proviso. clear proviso. rewrite simpl_msubst_impl.
    fSimpl. rewrite <- f_eqlist_app.
    erewrite eqlist_rewrite. Unshelve.
    4: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    3: { do 2 rewrite <- list_fmap_compose. rewrite <- fmap_app. rewrite list_fmap_compose.
         reflexivity. }
    setoid_rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
    apply msubst_formula_final.
    Unshelve. typeclasses eauto.
  Qed.

  (* TODO: move it *)
  Lemma fequiv_congr A B :
    A ≡ B → A ⇛ B.
  Proof. intros. rewrite H. reflexivity. Qed.

  Lemma rewrite_of_same_length {A B C : Type} (xs xs' : list A) (ys ys' : list B)
      (f : ∀ (xs : list A) (ys : list B), OfSameLength xs ys → C)
      `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
    xs = xs' →
    ys = ys' →
    f xs ys _ = f xs' ys' _.
  Proof.
    intros. subst. f_equiv. apply OfSameLength_pi.
  Qed.

  Lemma PAsgnWithOpens_app_nil_r lhs rhs `{!OfSameLength lhs rhs} {Hl} :
    @PAsgnWithOpens M (lhs ++ []) (rhs ++ []) Hl = PAsgnWithOpens lhs rhs.
  Proof with auto.
    unfold PAsgnWithOpens.
    replace (split_asgn_list (lhs ++ []) (rhs ++ [])) with (split_asgn_list lhs rhs);
      [reflexivity|].
    apply rewrite_of_same_length; rewrite app_nil_r; reflexivity.
  Qed.

  (* Lemma asgn_comm x r xs1 xs2 (rhs1 rhs2 : list (@asgn_rhs_term M)) *)
  (*     `{!OfSameLength xs1 rhs1} *)
  (*     `{!OfSameLength xs2 rhs2} : *)
  (*   <{ *xs1 := *rhs1 }> ≡ <{ *xs2 := *rhs2}>. *)
  (*   <{ *xs1, x, *xs2 := *rhs1, *[r], *rhs2 }> ≡ *)
  (*   <{ x, *xs1, *xs2 := *[r], *rhs1, *rhs2 }>. *)
  Definition is_open (r : @asgn_rhs_term M) :=
    match r with
    | OpenRhsTerm => true
    | FinalRhsTerm t => false
    end.
  Definition is_closed (r : @asgn_rhs_term M) :=
    match r with
    | OpenRhsTerm => false
    | FinalRhsTerm t => true
    end.

  (* Lemma wp_asgn_with_opens xs (rhs : list (@asgn_rhs_term M)) A {Hl} *)
  (*                          `{!OfSameLength xs rhs} *)
  (*   : *)
  (*   wp (PAsgnWithOpens xs rhs) A ≡ *)
  (*      wp (@PVarList M (omap (λ x, if is_open x.2 then Some x.1 else None) (zip xs rhs) : list final_variable) *)
  (*                    (@PAsgn _ (omap (λ x, if is_open x.2 then Some x.1 else None) (zip xs rhs)) *)
  (*                       (omap (λ x, if is_open x.2 then Some x.2 else None) (zip xs rhs)) Hl)) A. *)

  (* Lemma asgn_comm_head x1 x2 r1 r2 xs (rhs : list (@asgn_rhs_term M)) *)
  (*     `{!OfSameLength ([x1] ++ [x2] ++ xs) ([r1] ++ [r2] ++ rhs)} *)
  (*     `{!OfSameLength ([x2] ++ [x1] ++ xs) ([r2] ++ [r1] ++ rhs)} : *)
  (*   x1 ≠ x2 → *)
  (*   <{ x1, x2, *xs := *$([r1]), *$([r2]), *rhs }> ≡ *)
  (*   <{ x2, x1, *xs := *$([r2]), *$([r1]), *rhs }>. *)
  (* Proof with auto. *)
  (*   intros. unfold PAsgnWithOpens. unfold split_asgn_list. *)
  (*   assert (OfSameLength xs rhs). *)
  (*   { do 2 apply of_same_length_rest in OfSameLength0... } *)
  (*   intros Hneq A. simpl. destruct r1, r2.  *)
  (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. rewrite f_forall_comm... *)
  (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*     unfold PAsgnWithOpens. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     erewrite split_asgn_list_cons_open. *)
  (*     unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*     destruct (split_asgn_list xs rhs) eqn:E. *)
  (*     simpl. repeat f_equiv. *)
  (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*     unfold PAsgnWithOpens. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     erewrite split_asgn_list_cons_open. *)
  (*     unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*     destruct (split_asgn_list xs rhs) eqn:E. *)
  (*     simpl. repeat f_equiv. *)
  (*   - simpl. unfold PAsgnWithOpens. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     unfold asgn_args_with_closed. *)
  (*     destruct (split_asgn_list xs rhs) eqn:E. *)
  (*     simpl. clear E. induction asgn_opens; simpl; [| rewrite IHasgn_opens; auto]. *)
  (*     erewrite (rewrite_of_same_length *)
  (*                 _ ([] ++ [as_var x1] ++ [as_var x2] *)
  (*                      ++ (list_fmap final_variable variable as_var asgn_xs)) *)
  (*                 _ ([] ++ [as_term t] ++ [as_term t0] *)
  (*                      ++ list_fmap final_term term as_term asgn_ts))... *)
  (*     rewrite (msubst_comm_consecutive A [] [] (as_var x1) (as_term t) (as_var x2) (as_term t0))... *)
  (*     1-2: typeclasses eauto. *)
  (*     intros contra. apply as_var_inj in contra. subst. done. *)
  (* Qed. *)
  (* Lemma asgn_comm_tail x1 x2 r1 r2 xs (rhs : list (@asgn_rhs_term M)) *)
  (*     `{!OfSameLength (xs ++ [x1] ++ [x2]) (rhs ++ [r1] ++ [r2])} *)
  (*     `{!OfSameLength (xs ++ [x2] ++ [x1]) (rhs ++ [r2] ++ [r1])} : *)
  (*   x1 ≠ x2 → *)
  (*   <{ *xs, x1, x2 := *rhs, *$([r1]), *$([r2]) }> ≡ *)
  (*   <{ *xs, x2, x1 := *rhs, *$([r2]), *$([r1]) }>. *)
  (* Proof with auto. *)
  (*   assert (OfSameLength xs rhs). *)
  (*   {unfold OfSameLength in *. repeat rewrite length_app in OfSameLength0. *)
  (*     simpl in OfSameLength0. lia. } *)
  (*   intros Hneq A. simpl. *)
  (*   induction_same_length xs rhs as x' r'. *)
  (*   - simpl. apply asgn_comm_head... *)
  (*   - intros. simpl. destruct r'. *)
  (*   destruct r1, r2.  *)
  (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. rewrite f_forall_comm... *)
  (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*     unfold PAsgnWithOpens. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     erewrite split_asgn_list_cons_open. *)
  (*     unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*     destruct (split_asgn_list xs rhs) eqn:E. *)
  (*     simpl. repeat f_equiv. *)
  (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*     unfold PAsgnWithOpens. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     erewrite split_asgn_list_cons_open. *)
  (*     unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*     destruct (split_asgn_list xs rhs) eqn:E. *)
  (*     simpl. repeat f_equiv. *)
  (*   - simpl. unfold PAsgnWithOpens. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*     unfold asgn_args_with_closed. *)
  (*     destruct (split_asgn_list xs rhs) eqn:E. *)
  (*     simpl. clear E. induction asgn_opens; simpl; [| rewrite IHasgn_opens; auto]. *)
  (*     erewrite (rewrite_of_same_length *)
  (*                 _ ([] ++ [as_var x1] ++ [as_var x2] *)
  (*                      ++ (list_fmap final_variable variable as_var asgn_xs)) *)
  (*                 _ ([] ++ [as_term t] ++ [as_term t0] *)
  (*                      ++ list_fmap final_term term as_term asgn_ts))... *)
  (*     rewrite (msubst_comm_consecutive A [] [] (as_var x1) (as_term t) (as_var x2) (as_term t0))... *)
  (*     1-2: typeclasses eauto. *)
  (*     intros contra. apply as_var_inj in contra. subst. done. *)
  (* Qed. *)
  Global Instance PVar_proper : Proper ((=) ==> (≡) ==> (≡@{prog})) PVar.
  Proof. intros x ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

  Global Instance PVarList_proper : Proper ((=) ==> (≡) ==> (≡@{prog})) PVarList.
  Proof.
    intros xs ? <- A B ? C. induction xs as [|x xs IH].
    - simpl. apply H.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Lemma wp_varlist xs p A :
    wp (PVarList xs p) A ≡ <! ∀* ↑ₓ xs, $(wp p A) !>.
  Proof with auto. induction xs as [|x xs IH]... simpl. rewrite IH. reflexivity. Qed.

  Lemma p_varlist_permute xs xs' (p : prog) :
    xs ≡ₚ xs' →
    PVarList xs p ≡ PVarList xs' p.
  Proof.
    intros Hperm A. do 2 rewrite wp_varlist. rewrite f_foralllist_permute; [reflexivity|].
    apply Permutation_map. assumption.
  Qed.

  Lemma p_varlist_app xs1 xs2 (p : prog) :
    PVarList (xs1 ++ xs2) p ≡ PVarList (xs2 ++ xs1) p.
  Proof with auto.
    intros A. do 2 rewrite wp_varlist. do 2 rewrite fmap_app.
    do 2 rewrite foralllist_app. rewrite f_foralllist_comm...
  Qed.

Lemma elem_of_zip_pair_nil {A B : Type} x y :
  (x, y) ∈ (([] : list A), ([] : list B)) → False.
Proof with auto.
  intros (i&?&?). simpl in *. apply elem_of_list_lookup_2 in H. set_solver.
Qed.

Lemma elem_of_zip_pair_hd_ne {A B : Type} x0 y0 x y (xs : list A) (ys : list B) :
  x0 ≠ x →
  (x0, y0) ∈ (x :: xs, y :: ys) ↔ (x0, y0) ∈ (xs, ys).
Proof with auto.
  intros. split; intros (i&?).
  - destruct i.
    + apply elem_of_zip_pair_hd_indexed in H0 as []. subst. contradiction.
    + apply elem_of_zip_pair_tl_indexed in H0. exists i...
  - exists (S i). apply elem_of_zip_pair_tl_indexed...
Qed.

Lemma elem_of_zip_pair_hd {A B : Type} y0 x y (xs : list A) (ys : list B) :
  x ∉ xs →
  (x, y0) ∈ (x :: xs, y :: ys) ↔ y0 = y.
Proof with auto.
  intros. split.
  - intros (i&?). destruct i.
    + apply elem_of_zip_pair_hd_indexed in H0 as []...
    + apply elem_of_zip_pair_tl_indexed in H0 as []. simpl in *. apply elem_of_list_lookup_2 in H0.
      done.
  - intros ->. exists 0. apply elem_of_zip_pair_hd_indexed...
Qed.

Lemma elem_of_zip_pair_app {A B : Type} x y (xs1 : list A) (ys1 : list B)
  (xs2 : list A) (ys2 : list B) `{!OfSameLength xs1 ys1} :
  (x, y) ∈ (xs1 ++ xs2, ys1 ++ ys2) ↔ (x, y) ∈ (xs1, ys1) ∨ (x, y) ∈ (xs2, ys2).
Proof with auto.
  split.
  - intros (i&?&?). simpl in H, H0. destruct (decide (i < length xs1)).
    + left. rewrite lookup_app_l in H... rewrite OfSameLength0 in l. rewrite lookup_app_l in H0...
      exists i. split...
    + right. rewrite lookup_app_r in H by lia. rewrite OfSameLength0 in n.
      rewrite lookup_app_r in H0 by lia. rewrite OfSameLength0 in H. exists (i - length ys1).
      split...
  - intros [|]; destruct H as (i&?&?); simpl in H, H0.
    + exists i. split; simpl; apply lookup_app_l_Some...
    + exists (length xs1 + i). split; simpl.
      * rewrite lookup_app_r by lia. replace (length xs1 + i - length xs1) with i by lia...
      * rewrite OfSameLength0. rewrite lookup_app_r by lia.
        replace (length ys1 + i - length ys1) with i by lia...
Qed.

Lemma elem_of_zip_pair_indexed_inv {A B : Type} i x y (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) → (x, y) ∈ (xs, ys).
Proof. intros. exists i. assumption. Qed.

Lemma asgn_opens_with_open x lhs rhs `{!OfSameLength lhs rhs} :
  asgn_opens (asgn_args_with_open (split_asgn_list lhs rhs) x) =
    x :: @asgn_opens M (split_asgn_list lhs rhs).
Proof.
  destruct (split_asgn_list lhs rhs). simpl. reflexivity.
Qed.

Lemma asgn_opens_with_closed x t lhs rhs `{!OfSameLength lhs rhs} :
  asgn_opens (asgn_args_with_closed (split_asgn_list lhs rhs) x t) =
    @asgn_opens M (split_asgn_list lhs rhs).
Proof.
  destruct (split_asgn_list lhs rhs). simpl. reflexivity.
Qed.

Lemma asgn_xs_with_open x lhs rhs `{!OfSameLength lhs rhs} :
  asgn_xs (asgn_args_with_open (split_asgn_list lhs rhs) x) =
    @asgn_xs M (split_asgn_list lhs rhs).
Proof.
  destruct (split_asgn_list lhs rhs). simpl. reflexivity.
Qed.

Lemma asgn_xs_with_closed x t lhs rhs `{!OfSameLength lhs rhs} :
  asgn_xs (asgn_args_with_closed (split_asgn_list lhs rhs) x t) =
    x :: @asgn_xs M (split_asgn_list lhs rhs).
Proof.
  destruct (split_asgn_list lhs rhs). simpl. reflexivity.
Qed.

Lemma asgn_ts_with_open x lhs rhs `{!OfSameLength lhs rhs} :
  asgn_ts (asgn_args_with_open (split_asgn_list lhs rhs) x) =
    @asgn_ts M (split_asgn_list lhs rhs).
Proof.
  destruct (split_asgn_list lhs rhs). simpl. reflexivity.
Qed.

Lemma asgn_ts_with_closed x t lhs rhs `{!OfSameLength lhs rhs} :
  asgn_ts (asgn_args_with_closed (split_asgn_list lhs rhs) x t) =
    t :: @asgn_ts M (split_asgn_list lhs rhs).
Proof.
  destruct (split_asgn_list lhs rhs). simpl. reflexivity.
Qed.

Lemma elem_of_asgn_opens x lhs rhs `{!OfSameLength lhs rhs} :
  NoDup lhs →
  x ∈ asgn_opens (split_asgn_list lhs rhs) ↔ (x, @OpenRhsTerm M) ∈ (lhs, rhs).
Proof with auto.
  induction_same_length lhs rhs as l r.
  - simpl. unfold zip_pair_elem_of. pose proof (elem_of_zip_pair_nil x (@OpenRhsTerm M)).
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

Lemma elem_of_asgn_xs_ts x t lhs rhs `{!OfSameLength lhs rhs} :
  NoDup lhs →
  (x, t) ∈ (asgn_xs (split_asgn_list lhs rhs), asgn_ts (split_asgn_list lhs rhs)) ↔
         (x, @FinalRhsTerm M t) ∈ (lhs, rhs).
Proof with auto.
  induction_same_length lhs rhs as l r.
  - simpl. unfold zip_pair_elem_of. pose proof (elem_of_zip_pair_nil x t).
    pose proof (elem_of_zip_pair_nil x (@FinalRhsTerm M t)). set_solver.
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

Lemma elem_of_asgn_ts_inv t lhs rhs `{!OfSameLength lhs rhs} :
  t ∈ asgn_ts (split_asgn_list lhs rhs) →
    ∃ x, (x, t) ∈ (asgn_xs (split_asgn_list lhs rhs), (@asgn_ts M (split_asgn_list lhs rhs))).
Proof with auto.
  intros. apply elem_of_list_lookup in H as (i&?).
  opose proof (lookup_of_same_length_r (asgn_xs (split_asgn_list lhs rhs)) H) as (x&?).
  { apply asgn_of_same_length. }
  exists x, i. split...
Qed.

Lemma elem_of_asgn_ts t lhs rhs `{!OfSameLength lhs rhs} :
  NoDup lhs →
  t ∈ asgn_ts (split_asgn_list lhs rhs) ↔
    ∃ x, (x, t) ∈ (asgn_xs (split_asgn_list lhs rhs), (@asgn_ts M (split_asgn_list lhs rhs))).
Proof with auto.
  intros Hnodup. split; [apply elem_of_asgn_ts_inv|].
  intros (x&?). apply elem_of_asgn_xs_ts in H as [i []]... simpl in H, H0.
  generalize dependent i. induction_same_length lhs rhs as l r; [set_solver|].
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

Global Instance wp_proper_prog {A : final_formula} : Proper ((≡@{prog}) ==> (≡)) (λ p, wp p A).
Proof. intros p1 p2 Hp. specialize (Hp A). assumption. Qed.

Definition zip_pair_Permutation {A B : Type} (p1 p2 : list A * list B) :=
  ∀ (x : A) (y : B), (x, y) ∈ p1 ↔ (x, y) ∈ p2.

Infix "≡ₚₚ" := (zip_pair_Permutation) (at level 70, no associativity) : refiney_scope.

Global Instance zip_pair_Permutation_refl {A B : Type} : Reflexive (@zip_pair_Permutation A B).
Proof. intros p x y. reflexivity. Qed.

Hint Extern 0 (?p ≡ₚₚ ?p) => reflexivity : core.

Global Instance zip_pair_Permutation_sym {A B : Type} : Symmetric (@zip_pair_Permutation A B).
Proof. intros p1 p2 H x y. specialize (H x y). naive_solver. Qed.

Global Instance zip_pair_Permutation_trans {A B : Type} : Transitive (@zip_pair_Permutation A B).
Proof.
  intros p1 p2 p3 H12 H23. intros x y. specialize (H12 x y). specialize (H23 x y). naive_solver.
Qed.

Global Instance zip_pair_Permutation_equiv {A B : Type} : Equivalence (@zip_pair_Permutation A B).
Proof.
  split; [exact zip_pair_Permutation_refl | exact zip_pair_Permutation_sym |
           exact zip_pair_Permutation_trans].
Qed.

Lemma zip_pair_Permutation_cons {A B : Type} `{EqDecision A} (x : A) (y : B) (xs1 : list A)
  (ys1 : list B) (xs2 : list A) (ys2 : list B) `{!OfSameLength xs1 ys1} `{!OfSameLength xs2 ys2} :
  (* x ∉ xs1 → *)
  (* x ∉ xs2 → *)
  (xs1, ys1) ≡ₚₚ (xs2, ys2) →
  (x :: xs1, y :: ys1) ≡ₚₚ (x :: xs2, y :: ys2).
Proof with auto.
  unfold zip_pair_Permutation. intros. split; intros (i&?&?); simpl in H0, H1.
  - destruct i.
    + exists 0. split...
    + rewrite lookup_cons_ne_0 in H0 by lia. simpl in H0.
      rewrite lookup_cons_ne_0 in H1 by lia. simpl in H1. specialize (H x0 y0).
      pose proof (proj1 H). forward H2 by (exists i; split; auto).
      destruct H2 as (j&?&?). simpl in H2, H3.
      exists (S j). split...
  - destruct i.
    + exists 0. split...
    + rewrite lookup_cons_ne_0 in H0 by lia. simpl in H0.
      rewrite lookup_cons_ne_0 in H1 by lia. simpl in H1. specialize (H x0 y0).
      pose proof (proj2 H). forward H2 by (exists i; split; auto).
      destruct H2 as (j&?&?). simpl in H2, H3.
      exists (S j). split...
Qed.

Lemma zip_pair_Permutation_app_comm {A B : Type} (xs1 : list A) (ys1 : list B) (xs2 : list A)
    (ys2 : list B) `{!OfSameLength xs1 ys1} `{!OfSameLength xs2 ys2} :
  (xs1 ++ xs2, ys1 ++ ys2) ≡ₚₚ (xs2 ++ xs1, ys2 ++ ys1).
Proof with auto.
  unfold zip_pair_Permutation. intros x y. repeat rewrite elem_of_zip_pair_app...
  naive_solver.
Qed.

(* Global Instance app_zip_pair_Permutation {A B : Type} : *)
(*   Proper ((@zip_pair_Permutation A B) ==>  *)
(*   (@zip_pair_Permutation A B) ==> (@zip_pair_Permutation A B)) app. *)

Lemma lookup_list_to_map_zip_Some_inv {K A : Type} `{Countable K}
    (ks : list K) (xs : list A) (k : K) (x : A) `{!OfSameLength ks xs} :
  (list_to_map (zip ks xs) : gmap K A) !! k = Some x →
                                                   (k, x) ∈ (ks, xs).
Proof with auto.
  intros. apply lookup_list_to_map_zip_Some in H0 as (i&?&?&?)... exists i. split...
Qed.

(* Lemma zip_pair_Permutation_NoDup_dom_l {A B : Type} *)
(*                                        `{EqDecision A} *)
(*     (xs : list A) (ys : list B) (xs' : list A) (ys' : list B)  *)
(*     `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} : *)
(*   (xs, ys) ≡ₚₚ (xs', ys') → *)
(*   NoDup xs → *)
(*   NoDup xs'. *)
(* Proof with auto. *)
(*   intros. unfold zip_pair_Permutation in H. destruct (decide (NoDup xs'))... *)
(*   exfalso. rewrite NoDup_alt in n. apply n. clear n. intros i j x' ??. *)
(*   destruct (lookup_of_same_length_l ys' H1) as (y'&?).  *)
(*   destruct (lookup_of_same_length_l ys' H2) as (y''&?).  *)
(*   assert ((x', y') ∈ (xs', ys')). *)
(*   { exists i. split... } *)
(*   assert ((x', y'') ∈ (xs', ys')). *)
(*   { exists j. split... } *)
(*   rewrite <- H in H5. rewrite <- H in H6. destruct H5 as (k&?&?), H6 as (l&?&?). *)
(*   simpl in *. assert (l = k) as ->. *)
(*   { eapply NoDup_lookup; [exact H0 | exact H6 | exact H5]. } *)
(*   rewrite H7 in H8. inversion H8. subst y''. clear dependent xs ys H8. *)
(*   rewrite <- H3 in H4.  *)

(*   Search (¬ NoDup ?A → ?P). *)

(*   NoDup *)
(*   intros x. *)
(*   unfold elem_of, zip_pair_elem_of in H. *)
(*   unfold elem_of, zip_pair_elem_of_with_index in H. simpl in H. *)
(*   apply permutations_Permutation. apply permutations *)
(*   Permutation_ *)
(*   generalize dependent xs'. induction_same_length xs ys as x y. *)
(*   - apply zip_pair_Permutation_nil_inv_l in H0 as [-> ->]... *)
(*   - intros. assert (Hl:=of_same_length_rest H'). apply zip_pair_Permutation_cons_inv_l in H... *)
(*     destruct H as (xs'0&ys'0&xs'1&ys'1&?&?&?&?). subst.  *)
(*     apply IH. *)
(*     `{!EqDecision A} `{!Countable A} `{!OfSameLength xs' ys'} : *)

Lemma zip_pair_Permutation_nil_inv_l {A B : Type}
    (xs : list A) (ys : list B) `{!OfSameLength xs ys} :
  ([], []) ≡ₚₚ (xs, ys) →
  xs = [] ∧ ys = [].
Proof with auto.
  intros. unfold zip_pair_Permutation in H. induction_same_length xs ys as x y...
  - intros. clear IH. specialize (H x y). assert ((x, y) ∈ (x :: xs, y :: ys)).
    { exists 0. split... }
    rewrite <- H in H0. destruct H0 as (i&?&?). simpl in H0, H1. set_solver.
Qed.

Lemma zip_pair_Permutation_cons_inv_l {A B : Type} `{EqDecision A}
  (x : A) (y : B) (xs : list A) (ys : list B)
  (xs' : list A) (ys' : list B) `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  (x :: xs, y :: ys) ≡ₚₚ (xs', ys') →
  x ∉ xs →
  NoDup xs →
  NoDup xs' →
  ∃ (xs'0 : list A) (ys'0 : list B) (xs'1 : list A) (ys'1 : list B) (Hl0 : OfSameLength xs'0 ys'0) (Hl1 : OfSameLength xs'1 ys'1),
    xs' = xs'0 ++ x :: xs'1 ∧ ys' = ys'0 ++ y :: ys'1 ∧ (xs, ys) ≡ₚₚ (xs'0 ++ xs'1, ys'0 ++ ys'1).
Proof with auto.
  intros ? Hnin Hnodup Hnodup'. pose proof (H x y). assert ((x, y) ∈ (xs', ys')) as (i&?&?).
  { apply H. exists 0. split... }
  simpl in H1, H2. apply elem_of_list_split_length in H1, H2. destruct H1 as (xs'0&xs'1&?&?).
  destruct H2 as (ys'0&ys'1&?&?). subst. exists xs'0, ys'0, xs'1, ys'1. eexists; [naive_solver|].
  eexists...
  { pose proof (@of_same_length _ _ _ _ OfSameLength1). unfold OfSameLength.
    repeat rewrite length_app in H1. simpl in H1. lia. }
  split_and!... intros x' y'. specialize (H x' y').
  apply NoDup_app in Hnodup' as (?&?&?). apply NoDup_cons in H3 as [].
  destruct (decide (x' = x)).
  - subst. split; intros (i&?&_); simpl in H6.
    + apply elem_of_list_lookup_2 in H6. contradiction.
    + apply elem_of_list_lookup_2 in H6. set_solver.
  - rewrite elem_of_zip_pair_hd_ne in H... rewrite H.
    rewrite elem_of_zip_pair_app... rewrite elem_of_zip_pair_hd_ne...
    rewrite elem_of_zip_pair_app...
Qed.

Lemma zip_pair_Permutation_list_to_map_zip {A B : Type}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) `{Countable A} `{EqDecision A}
    `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  NoDup xs →
  NoDup xs' →
  (xs, ys) ≡ₚₚ (xs', ys') →
  (list_to_map (zip xs ys) : gmap A B) = list_to_map (zip xs' ys').
Proof with auto.
  intros. unfold zip_pair_Permutation in H. apply map_eq. intros x.
  destruct (list_to_map (zip xs ys) !! x) as [y|] eqn:E.
  - apply lookup_list_to_map_zip_Some_inv in E... apply H2 in E.
    symmetry. apply lookup_list_to_map_zip_Some... destruct E as (i&?&?). simpl in H3, H4.
    exists i. split_and!... intros. apply NoDup_lookup with (i:=i) in H5... lia.
  - apply lookup_list_to_map_zip_None in E... symmetry. apply lookup_list_to_map_zip_None...
    intros ?. apply elem_of_list_lookup in H3 as (i&?).
    destruct (lookup_of_same_length_l ys' H3) as (y&?)...
    assert ((x, y) ∈ (xs, ys)) as (?&?&_).
    { apply H2. exists i. split... }
    simpl in H5. apply elem_of_list_lookup_2 in H5. contradiction.
Qed.


  Lemma msubst_zip_pair_Permutation A (xs : list variable) ts (xs' : list variable) ts' `{!OfSameLength xs ts} `{!OfSameLength xs' ts'} :
    NoDup xs →
    NoDup xs' →
    (xs, ts) ≡ₚₚ (xs', ts') →
    msubst A (to_var_term_map xs ts) ≡ msubst A (to_var_term_map xs' ts').
  Proof with auto.
    intros. f_equiv. apply zip_pair_Permutation_list_to_map_zip... typeclasses eauto.
  Qed.

  Lemma asgn_opens_submseteq lhs rhs `{!OfSameLength lhs rhs} :
    @asgn_opens M (split_asgn_list lhs rhs) ⊆+ lhs.
  Proof with auto.
    induction_same_length lhs rhs as l r; [set_solver|]. apply submseteq_cons_r.
    assert (Hl:=of_same_length_rest H'). destruct r.
    - right. erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
      eexists. split; [reflexivity | apply IH].
    - left. erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
      apply IH.
  Qed.

  Lemma asgn_xs_submseteq lhs rhs `{!OfSameLength lhs rhs} :
    @asgn_xs M (split_asgn_list lhs rhs) ⊆+ lhs.
  Proof with auto.
    induction_same_length lhs rhs as l r; [set_solver|]. apply submseteq_cons_r.
    assert (Hl:=of_same_length_rest H'). destruct r.
    - left. erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. apply IH.
    - right. erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed. eexists.
      split; [reflexivity | apply IH].
  Qed.

  Lemma submseteq_NoDup {A : Type} (l k : list A) :
    NoDup k →
    l ⊆+ k →
    NoDup l.
  Proof with auto.
    intros. apply submseteq_Permutation in H0 as [k' ?]. apply Permutation_NoDup in H0...
    2:{ apply NoDup_ListNoDup... }
    apply NoDup_ListNoDup in H0. apply NoDup_app in H0 as [? _]...
  Qed.

Lemma elem_of_zip_pair_fmap {A A' B B' : Type} x' y' (xs : list A) (ys : list B)
    (f : A → A') (g : B → B')
    `{!OfSameLength xs ys} `{!OfSameLength (f <$> xs) (g <$> ys)} :
  (x', y') ∈ (f <$> xs, g <$> ys) ↔ ∃ x y, (x, y) ∈ (xs, ys) ∧ x' = f x ∧ y' = g y.
Proof with auto.
  split.
  - intros (i&?&?). simpl in H, H0. apply list_lookup_fmap_Some in H as (x&?&?).
    apply list_lookup_fmap_Some in H0 as (y&?&?). exists x, y. split_and!... exists i.
    split...
  - intros (x&y&(i&?&?)&?&?). simpl in H, H0. exists i. split; simpl; apply list_lookup_fmap_Some.
    + exists x. split...
    + exists y. split...
Qed.

Lemma zip_pair_Permutation_fmap {A A' B B' : Type}
    (xs : list A) (ys : list B)
    (xs' : list A) (ys' : list B)
    (f : A → A') (g : B → B')
    `{!OfSameLength xs ys} `{!OfSameLength (f <$> xs) (g <$> ys)}
    `{!OfSameLength xs' ys'} `{!OfSameLength (f <$> xs') (g <$> ys')} :
  (xs, ys) ≡ₚₚ (xs', ys') →
  (f <$> xs, g <$> ys) ≡ₚₚ (f <$> xs', g <$> ys').
Proof with auto.
  intros. unfold zip_pair_Permutation. intros x' y'. rewrite elem_of_zip_pair_fmap...
  rewrite elem_of_zip_pair_fmap... split; intros (x&y&?&?&?);
    exists x, y; split; auto; apply H in H0...
Qed.

Lemma asgn_opens_app lhs1 rhs1 lhs2 rhs2
  `{!OfSameLength lhs1 rhs1} `{!OfSameLength lhs2 rhs2}
  `{!OfSameLength (lhs1 ++ lhs2) (rhs1 ++ rhs2)} :
  asgn_opens (split_asgn_list (lhs1 ++ lhs2) (rhs1 ++ rhs2)) =
    asgn_opens (split_asgn_list lhs1 rhs1) ++ @asgn_opens M (split_asgn_list lhs2 rhs2).
Proof with auto.
  generalize dependent rhs2. generalize dependent lhs2. induction_same_length lhs1 rhs1 as l1 r1;
    simpl.
  - repeat f_equiv. apply OfSameLength_pi.
  - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
    + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
      erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
      erewrite IH. set_solver.
    + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
      erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
      erewrite IH...
Qed.

Lemma asgn_xs_app lhs1 rhs1 lhs2 rhs2
  `{!OfSameLength lhs1 rhs1} `{!OfSameLength lhs2 rhs2}
  `{!OfSameLength (lhs1 ++ lhs2) (rhs1 ++ rhs2)} :
  asgn_xs (split_asgn_list (lhs1 ++ lhs2) (rhs1 ++ rhs2)) =
    asgn_xs (split_asgn_list lhs1 rhs1) ++ @asgn_xs M (split_asgn_list lhs2 rhs2).
Proof with auto.
  generalize dependent rhs2. generalize dependent lhs2. induction_same_length lhs1 rhs1 as l1 r1;
    simpl.
  - repeat f_equiv. apply OfSameLength_pi.
  - intros. assert (Hl1:=of_same_length_rest H'). destruct r1.
    + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
      erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open.
      erewrite IH. set_solver.
    + erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
      erewrite split_asgn_list_cons_closed. rewrite asgn_xs_with_closed.
      erewrite IH...
Qed.

Lemma asgn_ts_app lhs1 rhs1 lhs2 rhs2
  `{!OfSameLength lhs1 rhs1} `{!OfSameLength lhs2 rhs2}
  `{!OfSameLength (lhs1 ++ lhs2) (rhs1 ++ rhs2)} :
  asgn_ts (split_asgn_list (lhs1 ++ lhs2) (rhs1 ++ rhs2)) =
    asgn_ts (split_asgn_list lhs1 rhs1) ++ @asgn_ts M (split_asgn_list lhs2 rhs2).
Proof with auto.
  generalize dependent rhs2. generalize dependent lhs2. induction_same_length lhs1 rhs1 as l1 r1;
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

Lemma asgn_opens_Permutation lhs rhs lhs' rhs'
  `{!OfSameLength lhs rhs} `{!OfSameLength lhs' rhs'} :
  NoDup lhs →
  NoDup lhs' →
  (lhs, rhs) ≡ₚₚ (lhs', rhs') →
  asgn_opens (split_asgn_list lhs rhs) ≡ₚ @asgn_opens M (split_asgn_list lhs' rhs').
Proof with auto.
  generalize dependent lhs'. generalize dependent rhs'. induction_same_length lhs rhs as l r.
  - apply zip_pair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
  - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
    apply zip_pair_Permutation_cons_inv_l in H1...
    destruct H1 as (xs'0&ys'0&xs'1&ys'1&?&?&?&?&?). destruct r.
    + erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open.
      subst. erewrite asgn_opens_app. erewrite split_asgn_list_cons_open.
      rewrite asgn_opens_with_open. rewrite app_Permutation_comm.
      simpl. f_equiv. etrans.
      * apply IH with (lhs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
        apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
        split_and!... intros. apply H1 in H6. set_solver.
      * erewrite asgn_opens_app. apply Permutation_app_comm.
    + erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed.
      subst. erewrite asgn_opens_app. erewrite split_asgn_list_cons_closed.
      rewrite asgn_opens_with_closed. rewrite app_Permutation_comm.
      simpl. etrans.
      * apply IH with (lhs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
        apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
        split_and!... intros. apply H1 in H6. set_solver.
      * erewrite asgn_opens_app. apply Permutation_app_comm.
Qed.

Lemma asgn_xs_ts_Permutation lhs rhs lhs' rhs'
  `{!OfSameLength lhs rhs} `{!OfSameLength lhs' rhs'} :
  NoDup lhs →
  NoDup lhs' →
  (lhs, rhs) ≡ₚₚ (lhs', rhs') →
  (asgn_xs (split_asgn_list lhs rhs), asgn_ts (split_asgn_list lhs rhs)) ≡ₚₚ
    (asgn_xs (split_asgn_list lhs' rhs'), @asgn_ts M (split_asgn_list lhs' rhs')).
Proof with auto.
  generalize dependent lhs'. generalize dependent rhs'. induction_same_length lhs rhs as l r.
  - apply zip_pair_Permutation_nil_inv_l in H2... destruct H2 as [-> ->]. simpl...
  - intros. apply NoDup_cons in H as []. assert (Hl:=of_same_length_rest H').
    apply zip_pair_Permutation_cons_inv_l in H1...
    destruct H1 as (xs'0&ys'0&xs'1&ys'1&?&?&?&?&?). destruct r.
    + erewrite split_asgn_list_cons_open. rewrite asgn_xs_with_open. rewrite asgn_ts_with_open.
      subst.
      rewrite IH with (lhs':=xs'0 ++ xs'1) (rhs':=ys'0 ++ ys'1)...
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
      rewrite IH with (lhs':=xs'1 ++ xs'0) (rhs':=ys'1 ++ ys'0)...
      2:{ apply NoDup_app in H0 as (?&?&?). apply NoDup_cons in H3 as []. apply NoDup_app.
          split_and!... intros. intros contra. apply H1 in contra. set_solver. }
      2:{ rewrite zip_pair_Permutation_app_comm... }
      erewrite asgn_xs_app. erewrite asgn_ts_app...
      Unshelve. typeclasses eauto.
Qed.

Local Lemma PAsgnWithOpens_equiv' xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
  NoDup xs1 →
  NoDup xs2 →
  asgn_opens (split_asgn_list xs1 rhs1) ≡ₚ asgn_opens (split_asgn_list xs2 rhs2) →
  (asgn_xs (split_asgn_list xs1 rhs1), asgn_ts (split_asgn_list xs1 rhs1)) ≡ₚₚ
    (asgn_xs (split_asgn_list xs2 rhs2), asgn_ts (split_asgn_list xs2 rhs2)) →
  @PAsgnWithOpens M xs1 rhs1 _ ≡ PAsgnWithOpens xs2 rhs2.
Proof with auto.
  intros Hnodup1 Hnodup2 Hopens Hclosed A. unfold PAsgnWithOpens.
  destruct (split_asgn_list xs1 rhs1) eqn:E1. simpl in *.
  destruct (split_asgn_list xs2 rhs2) eqn:E2. simpl in *. apply wp_proper_prog.
  rewrite p_varlist_permute.
  2:{ apply Hopens. }
  f_equiv. clear A Hopens. intros A. simpl. apply msubst_zip_pair_Permutation.
  - apply NoDup_fmap.
    + apply as_var_inj.
    + eapply submseteq_NoDup; [exact Hnodup1|].
      replace asgn_xs with (Prog.asgn_xs (split_asgn_list xs1 rhs1)).
      * apply asgn_xs_submseteq.
      * rewrite E1. reflexivity.
  - apply NoDup_fmap.
    + apply as_var_inj.
    + eapply submseteq_NoDup; [exact Hnodup2|].
      replace asgn_xs0 with (Prog.asgn_xs (split_asgn_list xs2 rhs2)).
      * apply asgn_xs_submseteq.
      * rewrite E2. reflexivity.
  - apply zip_pair_Permutation_fmap; try typeclasses eauto...
Qed.

Lemma PAsgnWithOpens_equiv lhs1 rhs1 lhs2 rhs2 `{!OfSameLength lhs1 rhs1} `{!OfSameLength lhs2 rhs2} :
  NoDup lhs1 →
  NoDup lhs2 →
  (lhs1, rhs1) ≡ₚₚ (lhs2, rhs2) →
  @PAsgnWithOpens M lhs1 rhs1 _ ≡ PAsgnWithOpens lhs2 rhs2.
Proof with auto.
  intros.
  apply PAsgnWithOpens_equiv'...
  - apply asgn_opens_Permutation...
  - apply asgn_xs_ts_Permutation...
Qed.

Lemma PAsgnWithOpens_wp_equiv (A : final_formula) lhs1 rhs1 lhs2 rhs2 `{!OfSameLength lhs1 rhs1} `{!OfSameLength lhs2 rhs2} :
  NoDup lhs1 →
  NoDup lhs2 →
  (lhs1, rhs1) ≡ₚₚ (lhs2, rhs2) →
  wp (PAsgnWithOpens lhs1 rhs1) A ≡ wp (PAsgnWithOpens lhs2 rhs2) A.
Proof with auto.
  intros. apply PAsgnWithOpens_equiv...
Qed.

  (* Lemma wp_PAsgnWithOpens (lhs : list final_variable) (rhs : list (@asgn_rhs_term M)) *)
  (*                         `{!OfSameLength lhs rhs} : *)
  (*   NoDup lhs → *)
  (*   ∃ opens xs ts (Hl : OfSameLength xs ts), *)
  (*     PAsgnWithOpens lhs rhs ≡ PVarList opens (PAsgn xs ts) ∧ *)
  (*       (∀ x, x ∈ opens ↔ (x, OpenRhsTerm) ∈ (lhs, rhs)) ∧ *)
  (*       (∀ x t, (x, t) ∈ (xs, ts) ↔ (x, FinalRhsTerm t) ∈ (lhs, rhs)). *)
  (* Proof with auto. *)
  (*   intros. *)
  (*   exists (asgn_opens (split_asgn_list lhs rhs)). *)
  (*   exists (asgn_xs (split_asgn_list lhs rhs)). *)
  (*   exists (asgn_ts (split_asgn_list lhs rhs)). *)
  (*   exists (asgn_of_same_length (split_asgn_list lhs rhs)). *)
  (*   split_and!. *)
  (*   - unfold PAsgnWithOpens. destruct (split_asgn_list lhs rhs). simpl. reflexivity. *)
  (*   - intros. rewrite elem_of_asgn_opens... *)
  (*     induction_same_length lhs rhs as l r. *)
  (*     + simpl. rewrite elem_of_nil. rewrite elem_of_zip_pair. set_solver. *)
  (*     + intros. assert (Hl := of_same_length_rest H'). apply NoDup_cons in H as []. *)
  (*       destruct (decide (x = l)). *)
  (*       2:{ ospecialize (IH _ H0). rewrite elem_of_zip_pair_hd_ne... destruct r. *)
  (*           - erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open. *)
  (*             rewrite elem_of_cons. rewrite IH. naive_solver. *)
  (*           - erewrite split_asgn_list_cons_closed. rewrite asgn_opens_with_closed. *)
  (*             rewrite IH. reflexivity. } *)
  (*       subst l. rewrite elem_of_zip_pair_hd... destruct r. *)
  (*       * erewrite split_asgn_list_cons_open. rewrite asgn_opens_with_open. rewrite elem_of_cons. *)

  (*       } *)
  (*       } *)
  (*             set_solver. *)
  (*           elem_of_zip_pair_ne *)
  (*           - admit. *)
  (*           - destruct IH as (i&?). exists (S i). apply elem_of_zip_pair_tl_indexed... } *)
  (*       subst l. *)
  (*         destruct r. *)
  (*           - *)
  (*       destruct r. *)
  (*       * exists 0. *)
  (*   induction_same_length lhs rhs as x r. *)
  (*   - exists [], [], [], of_same_length_nil. split_and!... *)
  (*     + intros. set_solver. *)
  (*     + intros. apply elem_of_zip_pair in H1. set_solver. *)
  (*   - intros. assert (Hl:=of_same_length_rest H'). *)
  (*     apply NoDup_cons in H as []. specialize (IH Hl H0). *)
  (*     destruct IH as (opens&xs&ts&?&?&?&?). destruct r eqn:E. *)
  (*     + exists (opens ++ [x]), xs, ts, x0. split_and!... *)
  (*       * unfold PAsgnWithOpens. unfold PAsgnWithOpens in H1. *)
  (*         erewrite split_asgn_list_cons_open. unfold asgn_args_with_open. *)
  (*         destruct (split_asgn_list lhs rhs) eqn:E'. *)
  (*         simpl. rewrite H1. rewrite p_varlist_app. simpl... *)
  (*       * intros. set_unfold in H4. destruct_or! H4. *)
  (*         -- apply H2 in H4 as (i&?). exists (S i). rewrite elem_of_zip_pair_tl_indexed... *)
  (*         -- subst. exists 0. rewrite elem_of_zip_pair_hd_indexed. split... *)
  (*       * intros. apply H3 in H4. destruct H4 as (i&?). *)
  (*         apply elem_of_zip_pair_indexed in H4. simpl in H4. exists (S i). *)
  (*         rewrite elem_of_zip_pair_tl_indexed... *)
  (*     + exists opens, (xs ++ [x]), (ts ++ [t]), _. split_and!... *)
  (*       * unfold PAsgnWithOpens. unfold PAsgnWithOpens in H1. *)
  (*         erewrite split_asgn_list_cons_closed. unfold asgn_args_with_closed. *)
  (*         destruct (split_asgn_list lhs rhs) eqn:E'. *)
  (*         simpl. intros A. specialize (H1 A). *)
  (*         rewrite H1. rewrite p_varlist_app. simpl... *)
  (*       * intros. set_unfold in H4. destruct_or! H4. *)
  (*         -- apply H2 in H4 as (i&?). exists (S i). rewrite elem_of_zip_pair_tl_indexed... *)
  (*         -- subst. exists 0. rewrite elem_of_zip_pair_hd_indexed. split... *)
  (*       * intros. apply H3 in H4. destruct H4 as (i&?). *)
  (*         apply elem_of_zip_pair_indexed in H4. simpl in H4. exists (S i). *)
  (*         rewrite elem_of_zip_pair_tl_indexed... *)
  (*     + *)
  (*         destruct H4 as (?&?). *)
  (*         -- *)
  (*     `{!OfSameLength xs0 rhs0} *)
  (*     `{!OfSameLength xs1 rhs1} *)
  (*     `{!OfSameLength xs2 rhs2} *)
  (*     {Hl1 Hl2} : *)
  (*   @PAsgnWithOpens M (xs0 ++ [x1] ++ xs1 ++ [x2] ++ xs2) *)
  (*     (rhs0 ++ [r1] ++ rhs1 ++ [r2] ++ rhs2) Hl1 ≡ *)
  (*   @PAsgnWithOpens M (xs0 ++ [x2] ++ xs1 ++ [x1] ++ xs2) *)
  (*     (rhs0 ++ [r2] ++ rhs1 ++ [r1] ++ rhs2) Hl2. *)

  (* Lemma msubst_comm xs0 (rhs0 : list asgn_rhs_term) x1 r1 xs1 rhs1 x2 r2 xs2 rhs2 *)
  (*     `{!OfSameLength xs0 rhs0} *)
  (*     `{!OfSameLength xs1 rhs1} *)
  (*     `{!OfSameLength xs2 rhs2} *)
  (*     {Hl1 Hl2} : *)
  (*   @PAsgnWithOpens M (xs0 ++ [x1] ++ xs1 ++ [x2] ++ xs2) *)
  (*     (rhs0 ++ [r1] ++ rhs1 ++ [r2] ++ rhs2) Hl1 ≡ *)
  (*   @PAsgnWithOpens M (xs0 ++ [x2] ++ xs1 ++ [x1] ++ xs2) *)
  (*     (rhs0 ++ [r2] ++ rhs1 ++ [r1] ++ rhs2) Hl2. *)
  (* Proof with auto. *)
  (*   intros A. unfold PAsgnWithOpens. split_asgn_list *)
  (*   intros A. *)
  (*   generalize dependent rhs1. generalize dependent rhs0. *)
  (*   generalize dependent xs1. generalize dependent xs0. *)
  (*   induction_same_length xs2 rhs2 as x2' r2'. *)
  (*   - simpl. induction_same_length xs1 rhs1 as x1' r1'. *)
  (*     + simpl. admit. *)
  (*     + intros. simpl. erewrite *)
  (*   - intros. *)
  (*   generalize dependent rhs2. *)
  (*   generalize dependent rhs2. *)
  (*   generalize dependent rhs2. *)
  (*   generalize dependent rhs2. *)
  (*   generalize dependent rhs2. *)

  (* (*                   Hl1 *) *)
  (* (*   <{ *xs0, x1, *xs1, x2, *xs2 := *rhs0, *$([r1]), *rhs1, *$([r2]), *rhs2 }> ≡ *) *)
  (* (*   <{ *xs0, x2, *xs1, x1, *xs2 := *rhs0, *$([r2]), *rhs1, *$([r1]), *rhs2 }>. *) *)
  (* (*   msubst A (@to_var_term_map _ (xs0 ++ [x1] ++ xs1 ++ [x2] ++ xs2) *) *)
  (* (*               (rhs0 ++ [t1] ++ rhs1 ++ [t2] ++ rhs2) Hl1) ≡ *) *)
  (* (*   msubst A (@to_var_term_map _ (xs0 ++ [x2] ++ xs1 ++ [x1] ++ xs2) *) *)
  (* (*               (rhs0 ++ [t2] ++ rhs1 ++ [t1] ++ rhs2) Hl2). *) *)
  (* (* Proof with auto. *) *)

  (* (* Lemma asgn_comm' x r xs1 xs2 (rhs1 rhs2 : list (@asgn_rhs_term M)) *) *)
  (* (*     `{!OfSameLength xs1 rhs1} *) *)
  (* (*     `{!OfSameLength xs2 rhs2} : *) *)
  (* (*   <{ x, *xs1, *xs2 := *$([r]), *rhs1, *rhs2 }> ≡ *) *)
  (* (*   <{ *xs1, x, *xs2 := *rhs1, *$([r]), *rhs2 }>. *) *)
  (* (* Proof with auto. *) *)
  (* (*   intros A. *) *)
  (* (*   generalize dependent r. generalize dependent x. *) *)
  (* (*   generalize dependent rhs1. generalize dependent xs1. *) *)
  (* (*   induction_same_length xs2 rhs2 as x2 r2... *) *)
  (* (*   - simpl. induction_same_length xs1 rhs1 as x1 r1... simpl. *) *)
  (* (*     + simpl... *) *)
  (* (*   intros *) *)
  (* (*   - simpl... *) *)
  (* (*   - intros. *) *)
  (* (*   generalize dependent r. generalize dependent x. *) *)
  (* (*   induction_same_length xs rhs as x' r'... intros. simpl. *) *)
  (* (* Lemma asgn_comm' x r xs (rhs : list (@asgn_rhs_term M)) *) *)
  (* (*     `{!OfSameLength xs rhs} *) *)
  (* (*     `{!OfSameLength (x :: xs) (r :: rhs)} : *) *)
  (* (*   <{ x, *xs := *$([r]), *rhs }> ≡ *) *)
  (* (*   <{ *xs, x := *rhs, *$([r]) }>. *) *)
  (* (* Proof with auto. *) *)
  (* (*   intros A. generalize dependent r. generalize dependent x. *) *)
  (* (*   induction_same_length xs rhs as x' r'... intros. *) *)
  (* (*   intros *) *)
  (* (*   - simpl... *) *)
  (* (*   - intros. *) *)
  (* (*   generalize dependent r. generalize dependent x. *) *)
  (* (*   induction_same_length xs rhs as x' r'... intros. simpl. *) *)
  (* (* Lemma asgn_comm' x r xs (rhs : list (@asgn_rhs_term M)) *) *)
  (* (*     `{!OfSameLength xs rhs} *) *)
  (* (*     `{!OfSameLength (xs ++ [x]) (rhs ++ [r])} : *) *)
  (* (*   (* x ∉ xs2 → *) *) *)
  (* (*   (* NoDup xs2 → *) *) *)
  (* (*   <{ *xs, x := *rhs, *$([r]) }> ≡ *) *)
  (* (*   <{ x, *xs := *$([r]), *rhs }>. *) *)
  (* (* Proof with auto. *) *)
  (* (*   intros A. generalize dependent r. generalize dependent x. *) *)
  (* (*   induction_same_length xs rhs as x1 r1... intros. *) *)
  (* (*   erewrite (rewrite_of_same_length *) *)
  (* (*               _ (x1 :: (xs ++ [x])) *) *)
  (* (*               _ (r1 :: (rhs ++ [r])))... *) *)
  (* (*   destruct r1, r. *) *)
  (* (*   - simpl. repeat erewrite PAsgnWithOpens_cons_open. simpl. admit. *) *)
  (* (*   - repeat erewrite PAsgnWithOpens_cons_open. simpl. *) *)
  (* (*     unfold PAsgnWithOpens. *) *)
  (* (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *) *)
  (* (*     erewrite split_asgn_list_cons_open. *) *)
  (* (*     unfold asgn_args_with_closed. unfold asgn_args_with_open. *) *)
  (* (*     destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *) *)
  (* (*     simpl. repeat f_equiv. *) *)
  (* (*   + repeat erewrite PAsgnWithOpens_cons_open. simpl. *) *)
  (* (*     unfold PAsgnWithOpens. *) *)
  (* (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *) *)
  (* (*     erewrite split_asgn_list_cons_open. *) *)
  (* (*     unfold asgn_args_with_closed. unfold asgn_args_with_open. *) *)
  (* (*     destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *) *)
  (* (*     simpl. repeat f_equiv. *) *)
  (* (*   + simpl. unfold PAsgnWithOpens. *) *)
  (* (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *) *)
  (* (*     erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *) *)
  (* (*     unfold asgn_args_with_closed. *) *)
  (* (*     destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *) *)
  (* (*     simpl. clear E. induction asgn_opens; simpl; [| rewrite IHasgn_opens; auto]. *) *)
  (* (*     erewrite (rewrite_of_same_length *) *)
  (* (*                 _ ([] ++ [as_var x] ++ [as_var x2] ++ (list_fmap final_variable variable as_var asgn_xs)) *) *)
  (* (*                 _ ([] ++ [as_term t] ++ [as_term t0] ++ list_fmap final_term term as_term asgn_ts))... *) *)
  (* (*     rewrite (msubst_comm_consecutive A [] [] (as_var x) (as_term t) (as_var x2) (as_term t0))... *) *)
  (* (*     1-2: typeclasses eauto. *) *)
  (* (*     Set Printing Coercions. intros contra. apply as_var_inj in contra. subst. done. *) *)

  (* (*   generalize dependent rhs2. generalize dependent xs2. *) *)
  (* (*   induction_same_length xs1 rhs1 as x1 r1. *) *)
  (* (*   - simpl. intros A. simpl. erewrite PAsgnWithOpens_app_nil_r... *) *)
  (* (*   - intros. intros A. simpl. *) *)
  (* (*   <{ x, *xs := *[r], *rhs }>. *) *)
  (* (* Proof with auto. *) *)
  (* (*   generalize dependent r. generalize dependent x. *) *)
  (* (*   induction_same_length xs rhs as x' r'... intros. simpl. *) *)
  (* Lemma asgn_comm x r xs1 xs2 (rhs1 rhs2 : list (@asgn_rhs_term M)) *)
  (*     `{!OfSameLength xs1 rhs1} *)
  (*     `{!OfSameLength xs2 rhs2} *)
  (*     `{!OfSameLength (xs1 ++ [x]) (rhs1 ++ [r])} *)
  (*     `{!OfSameLength (xs1 ++ [x] ++ xs2) (rhs1 ++ [r] ++ rhs2)} : *)
  (*   x ∉ xs2 → *)
  (*   NoDup xs2 → *)
  (*   <{ *xs1, x, *xs2 := *rhs1, *[r], *rhs2 }> ≡ *)
  (*   <{ x, *xs1, *xs2 := *[r], *rhs1, *rhs2 }>. *)
  (* Proof with auto. *)
  (*   generalize dependent rhs2. generalize dependent xs2. *)
  (*   generalize dependent r. generalize dependent x. *)
  (*   induction_same_length xs1 rhs1 as x1 r1. *)
  (*   - simpl. f_equiv. apply OfSameLength_pi. *)
  (*   - intros. *)

  (*     destruct r, r1. *)
  (*     + simpl. admit. *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*       unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. repeat f_equiv. *)

  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*       unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. repeat f_equiv. *)
  (*     +  *)

  (*     + opose proof (IH _ _ _) as []. intros A.  *)
  (*   simpl. intros Hdisj Hnodup. generalize dependent rhs1. generalize dependent xs1. *)
  (*   generalize dependent r. generalize dependent x. induction_same_length xs2 rhs2 as x2 r2. *)
  (*   - induction_same_length xs1 rhs1 as x1 r1... intros. simpl. split. *)
  (*      s *)
  (*   - intros. assert (Hl := of_same_length_rest H'). *)
  (*     erewrite (rewrite_of_same_length _ *)
  (*                 ((xs1 ++ [x]) ++ (x2 :: xs2)) _ ((rhs1 ++ [r]) ++ (r2 :: rhs2))). *)
  (*     2-3: rewrite cons_middle; rewrite app_assoc... *)
  (*     apply NoDup_cons in Hnodup as []. apply not_elem_of_cons in Hdisj as []. rewrite IH... *)
  (*     erewrite (rewrite_of_same_length _ *)
  (*                 ((x2 :: xs1) ++ (x :: xs2)) _ ((r2 :: rhs1) ++ (r :: rhs2))). *)
  (*     2-3: rewrite <- app_assoc; rewrite cons_middle; rewrite app_comm_cons... *)
  (*     rewrite IH... *)
  (*     erewrite (rewrite_of_same_length *)
  (*                 (x :: (xs1 ++ x2 :: xs2)) ((x :: xs1) ++ (x2 :: xs2)) *)
  (*                 _ ((r :: rhs1) ++ (r2 :: rhs2))). *)
  (*     2-3: rewrite app_comm_cons... *)
  (*     rewrite IH... simpl. clear IH. *)
  (*     Unshelve. 2-7: typeclasses eauto. *)
  (*     destruct r, r2. *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. rewrite f_forall_comm... *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*       unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. repeat f_equiv. *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*       unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. repeat f_equiv. *)
  (*     + simpl. unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       unfold asgn_args_with_closed. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. clear E. induction asgn_opens; simpl; [| rewrite IHasgn_opens; auto]. *)
  (*       erewrite (rewrite_of_same_length *)
  (*                   _ ([] ++ [as_var x] ++ [as_var x2] ++ (list_fmap final_variable variable as_var asgn_xs)) *)
  (*                   _ ([] ++ [as_term t] ++ [as_term t0] ++ list_fmap final_term term as_term asgn_ts))... *)
  (*       rewrite (msubst_comm_consecutive A [] [] (as_var x) (as_term t) (as_var x2) (as_term t0))... *)
  (*       1-2: typeclasses eauto. *)
  (*       Set Printing Coercions. intros contra. apply as_var_inj in contra. subst. done. *)

  (* Lemma asgn_comm x r xs1 xs2 (rhs1 rhs2 : list (@asgn_rhs_term M)) *)
  (*     `{!OfSameLength xs1 rhs1} *)
  (*     `{!OfSameLength xs2 rhs2} *)
  (*     `{!OfSameLength (xs1 ++ [x] ++ xs2) (rhs1 ++ [r] ++ rhs2)} : *)
  (*   x ∉ xs2 → *)
  (*   NoDup xs2 → *)
  (*   <{ *xs1, x, *xs2 := *rhs1, *[r], *rhs2 }> ≡ *)
  (*   <{ x, *xs1, *xs2 := *[r], *rhs1, *rhs2 }>. *)
  (* Proof with auto. *)
  (*   simpl. intros Hdisj Hnodup A. generalize dependent rhs1. generalize dependent xs1. *)
  (*   generalize dependent r. generalize dependent x. induction_same_length xs2 rhs2 as x2 r2. *)
  (*   (* - unfold PAsgnWithOpens.  *) *)

  (*   - *)

  (*     generalize dependent r. generalize dependent x. *)
  (*     induction_same_length xs1 rhs1 as x1 r1... intros. simpl. destruct r1, r. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       repeat erewrite split_asgn_list_cons_closed. *)
  (*       assert (Hl:=of_same_length_rest H'). *)
  (*       destruct (split_asgn_list xs1 rhs1) eqn:E. *)



  (*   - intros. assert (Hl := of_same_length_rest H'). *)
  (*     erewrite (rewrite_of_same_length _ *)
  (*                 ((xs1 ++ [x]) ++ (x2 :: xs2)) _ ((rhs1 ++ [r]) ++ (r2 :: rhs2))). *)
  (*     2-3: rewrite cons_middle; rewrite app_assoc... *)
  (*     apply NoDup_cons in Hnodup as []. apply not_elem_of_cons in Hdisj as []. rewrite IH... *)
  (*     erewrite (rewrite_of_same_length _ *)
  (*                 ((x2 :: xs1) ++ (x :: xs2)) _ ((r2 :: rhs1) ++ (r :: rhs2))). *)
  (*     2-3: rewrite <- app_assoc; rewrite cons_middle; rewrite app_comm_cons... *)
  (*     rewrite IH... *)
  (*     erewrite (rewrite_of_same_length *)
  (*                 (x :: (xs1 ++ x2 :: xs2)) ((x :: xs1) ++ (x2 :: xs2)) *)
  (*                 _ ((r :: rhs1) ++ (r2 :: rhs2))). *)
  (*     2-3: rewrite app_comm_cons... *)
  (*     rewrite IH... simpl. clear IH. *)
  (*     Unshelve. 2-7: typeclasses eauto. *)
  (*     destruct r, r2. *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. rewrite f_forall_comm... *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*       unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. repeat f_equiv. *)
  (*     + repeat erewrite PAsgnWithOpens_cons_open. simpl. *)
  (*       unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_open. *)
  (*       unfold asgn_args_with_closed. unfold asgn_args_with_open. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. repeat f_equiv. *)
  (*     + simpl. unfold PAsgnWithOpens. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       erewrite split_asgn_list_cons_closed. erewrite split_asgn_list_cons_closed. *)
  (*       unfold asgn_args_with_closed. *)
  (*       destruct (split_asgn_list (xs1 ++ xs2) (rhs1 ++ rhs2)) eqn:E. *)
  (*       simpl. clear E. induction asgn_opens; simpl; [| rewrite IHasgn_opens; auto]. *)
  (*       erewrite (rewrite_of_same_length *)
  (*                   _ ([] ++ [as_var x] ++ [as_var x2] ++ (list_fmap final_variable variable as_var asgn_xs)) *)
  (*                   _ ([] ++ [as_term t] ++ [as_term t0] ++ list_fmap final_term term as_term asgn_ts))... *)
  (*       rewrite (msubst_comm_consecutive A [] [] (as_var x) (as_term t) (as_var x2) (as_term t0))... *)
  (*       1-2: typeclasses eauto. *)
  (*       Set Printing Coercions. intros contra. apply as_var_inj in contra. subst. done. *)

Lemma as_var_to_final_var_final (x : variable) :
  var_final x →
  as_var (to_final_var x) = x.
Proof.
  intros. rewrite as_var_to_final_var. destruct x. unfold var_final in H.
  unfold Model.var_is_initial in H. rewrite H. apply var_with_is_initial_id.
  reflexivity.
Qed.

  (* Lemma asgn_comm xs1 xs2 (rhs1 rhs2 : list (@asgn_rhs_term M)) *)
  (*   `{!OfSameLength xs1 rhs1} *)
  (*   `{!OfSameLength xs2 rhs2} : *)
  (*   <{ *xs1, *xs2 := *rhs1, *rhs2 }> ⊑ *)
  (*   <{ *xs2, *xs1 := *rhs2, *rhs1 }>. *)
  (* Proof. *)
  (*   intros A. generalize dependent rhs2. generalize dependent xs2. *)
  (*   induction_same_length xs1 rhs1 as x1 r1; intros. *)
  (*   - simpl. admit. *)
  (*   - destruct r1. *)
  (*     + simpl. *)
  (*       erewrite PAsgnWithOpens_cons_open. simpl. rewrite IH. *)
  (*       ospecialize (IH _ (xs2 ++ [x1]) (rhs2 ++ [OpenRhsTerm]) _). *)
  (*       simpl in IH. *)
  (*       rewrite <- IH. *)
  (*       opose proof (@PAsgnWithOpens_cons_open _ x1 (xs1 ++ xs2) (rhs1 ++ rhs2) _). *)
  (*       rewrite H. *)
  Lemma r_open_assignment_l x (t : final_term) xs (rhs : list (@asgn_rhs_term M))
    `{!OfSameLength xs rhs}
    `{!OfSameLength ([x] ++ xs) ([OpenRhsTerm] ++ rhs)}
    `{!OfSameLength ([x] ++ xs) ([FinalRhsTerm t] ++ rhs)} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs, rhs) → as_var x ∉ term_fvars t') →
    <{ x, *xs := ?, *rhs }> ⊑
    <{ x, *xs := t, *rhs }>.
  Proof with auto.
    intros. intros A. unfold PAsgnWithOpens. simpl.
    destruct (split_asgn_list (x :: xs) (OpenRhsTerm :: rhs)) eqn:E1.
    destruct (split_asgn_list (x :: xs) (FinalRhsTerm (as_final_term t) :: rhs)) eqn:E2.
    rewrite split_asgn_list_cons_open with (OfSameLength0:=OfSameLength0) in E1.
    rewrite split_asgn_list_cons_closed with (Hl1:=OfSameLength0) in E2.
    unfold asgn_args_with_open in E1. unfold asgn_args_with_closed in E2.
    simpl in E1, E2. destruct (split_asgn_list xs rhs) eqn:E3.
    inversion E1. inversion E2. subst.
    assert (asgn_opens0 = Prog.asgn_opens (split_asgn_list xs rhs)) as Heq1 by (rewrite E3; done).
    assert (asgn_xs = Prog.asgn_xs (split_asgn_list xs rhs)) as Heq2 by (rewrite E3; done).
    assert (asgn_ts = Prog.asgn_ts (split_asgn_list xs rhs)) as Heq3 by (rewrite E3; done).
    clear E1 E2 E3. simpl. repeat rewrite wp_varlist. simpl.
    rewrite f_forall_elim with (t:=t). rewrite simpl_subst_foralllist.
    2:{ intros contra. apply elem_of_list_fmap in contra. destruct contra as (x'&?&?).
        apply as_var_inj in H3. subst. eapply elem_of_submseteq in H4;
          [| apply asgn_opens_submseteq]... }
    2:{ intros y ??. set_unfold in H3. destruct H3 as []. apply H1 with (x':=(to_final_var y)).
        - subst. apply elem_of_asgn_opens in H5...
        - rewrite as_var_to_final_var_final... }
    rewrite <- msubst_extract_r.
    - simpl. reflexivity.
    - intros contra. apply elem_of_list_fmap in contra as (x'&?&?). apply as_var_inj in H3.
      subst. eapply elem_of_submseteq in H4; [| apply asgn_xs_submseteq]. done.
    - clear dependent t. set_unfold. intros (?&?&t&->&?). subst.
      apply elem_of_asgn_ts_inv in H3 as (xt&?).
      apply elem_of_asgn_xs_ts in H3... apply H2 in H3. contradiction.
  Qed.

  Lemma r_open_assignment_r x (t : final_term) xs (rhs : list (@asgn_rhs_term M))
    `{!OfSameLength xs rhs} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ x' t', (x', FinalRhsTerm t') ∈ (xs, rhs) → as_var x ∉ term_fvars t') →
    <{ *xs, x := *rhs, ? }> ⊑
    <{ *xs, x := *rhs, t }>.
  Proof with auto.
    intros. intros A.
    rewrite PAsgnWithOpens_wp_equiv with (lhs2:=[x] ++ xs)
                                                    (rhs2:=[OpenRhsTerm] ++ rhs).
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        apply zip_pair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite PAsgnWithOpens_wp_equiv with (lhs1:=xs ++ [x]) (lhs2:=[x] ++ xs)
                                                    (rhs2:=[FinalRhsTerm t] ++ rhs)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        rewrite as_final_term_as_term. apply zip_pair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite (r_open_assignment_l x t xs rhs H H0 H1 H2 A). simpl.
    rewrite as_final_term_as_term. reflexivity.
  Qed.

  Lemma r_open_assignment x (t : final_term) xs0 xs1 (rhs0 rhs1 : list (@asgn_rhs_term M))
    `{!OfSameLength xs0 rhs0}
    `{!OfSameLength xs1 rhs1} :
    x ∉ xs0 →
    x ∉ xs1 →
    NoDup xs0 →
    NoDup xs1 →
    xs0 ## xs1 →
    <{ *xs0, x, *xs1 := *rhs0, ?, *rhs1 }> ⊑
    <{ *xs0, x, *xs1 := *rhs0, t, *rhs1 }>.
  Proof with auto.
    intros. intros A.
    rewrite PAsgnWithOpens_wp_equiv with (lhs2:=x :: xs0 ++ xs1)
                                                    (rhs2:=OpenRhsTerm :: rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons.
        split... }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm...
        2: typeclasses eauto. simpl. apply zip_pair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zip_pair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    rewrite PAsgnWithOpens_wp_equiv with (lhs1:=xs0 ++ [x] ++ xs1) (lhs2:=x :: xs0 ++ xs1)
                                                    (rhs2:=FinalRhsTerm t :: rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons.
        split... }
    3:{ simpl. rewrite zip_pair_Permutation_app_comm...
        2: typeclasses eauto. simpl. rewrite as_final_term_as_term.
        apply zip_pair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zip_pair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    unfold PAsgnWithOpens.
    destruct (split_asgn_list (x :: xs0 ++ xs1) (OpenRhsTerm :: rhs0 ++ rhs1)) eqn:E1.
    destruct (split_asgn_list (x :: xs0 ++ xs1) (FinalRhsTerm t :: rhs0 ++ rhs1)) eqn:E2.

    assert (OfSameLength (xs0 ++ xs1) (rhs0 ++ rhs1)).
    { unfold OfSameLength in *. repeat rewrite length_app. lia. }
    rewrite split_asgn_list_cons_open with (OfSameLength0:=H4) in E1.
    rewrite split_asgn_list_cons_closed with (Hl1:=H4) in E2.
    unfold asgn_args_with_open in E1. unfold asgn_args_with_closed in E2.
    simpl in E1, E2.
    destruct (split_asgn_list (xs0 ++ xs1) (rhs0 ++ rhs1)).
    inversion E1. inversion E2. clear E1 E2. subst. simpl.
    repeat rewrite wp_varlist. simpl. rewrite f_forall_elim with (t:=t).
    rewrite E2 in E1.
    inversion E. simpl.
    erewrite split_asgn_list_cons_open.
    destr
    unfold asgn_args_with_open. simpl.
    unfold asgn
    simpl.
        - typeclasses eauto.
        split... }
        - intros. set_solver.
        - apply NoDup_app.
    intros A. induction_same_length xs ts as x t.
    - simpl. apply fequiv_congr. repeat f_equiv. apply OfSameLength_pi.
    - simpl.
    - simpl.
    simpl.


  (* Law 4.1 *)
  Lemma r_alternation w pre post gs `{!FormulaFinal pre} :
    pre ⇛ <! ∨* ⤊ gs !> →
    <{ *w : [pre, post] }> ⊑ <{ if | g : gs → *w : [g ∧ pre, post] fi }>.
  Proof with auto.
    intros proviso A. simpl. rewrite fent_fent_st. intros σ.
    rewrite fent_fent_st in proviso. specialize (proviso σ).
    induction gs as [|g gs IH].
    - rewrite proviso. simpl. fSimpl...
    - simpl in *. fold (@fmap list _ final_formula formula) in *.
      fold (@fmap list _ (final_formula * prog)).
      fLem g.
      + fSimpl. fSplit... fLem pre.
        2:{ fSimpl... }
        fLem <! ∨* ⤊ gs !>.
        * forward IH... fSimpl. rewrite IH. intros ?. simp feval in H2. destruct H2 as [].
          assumption.
        * clear IH proviso H H0 g. induction gs as [|g gs IH]; simpl...
          simpl in *. apply f_or_equiv_st_false in H1 as []. rewrite H. fSimpl.
          rewrite IH...
      + fSimpl. forward IH...
  Qed.


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

