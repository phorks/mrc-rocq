From Stdlib Require Import Lists.List. Import ListNotations.
From Equations Require Import Equations.
From stdpp Require Import base tactics listset gmap.
From MRC Require Import Prelude.
From MRC Require Import Lib.
From MRC Require Import Lib.ListBag.
From MRC Require Import Model.
From MRC Require Import PredCalc.
From MRC Require Import Prog.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Section refinement.
  Context {M : model}.
  Context `{MNat : ModelWithNat M}.
  Local Notation value := (value M).
  Local Notation prog := (prog M).
  Local Notation state := (state M).
  Local Notation term := (term M).
  Local Notation formula := (formula M).
  Local Notation final_term := (final_term M).
  Local Notation final_formula := (final_formula M).

  Implicit Types A B C : formula.
  Implicit Types pre post : formula.
  Implicit Types w xs : list final_variable.
  Implicit Types gcs : list final_formula.
  Implicit Types g : final_formula.
  Implicit Types rhs : list (@asgn_rhs_term M).
  Implicit Types p : prog.

  (* FIXME: Did it do anything? *)
  (* Hint Extern 0 (<! _[_₀\[]] !>) => rewrite subst_initials_nil : core. *)

  (* 1.8 *)
  Lemma r_absorb_assumption pre' w pre post `{!FormulaFinal pre'} `{!FormulaFinal pre} :
    <{ {pre'}; *w : [pre, post] }> ≡ <{ *w : [pre' ∧ pre, post] }>.
  Proof with auto.
    intros A. simpl. rewrite subst_all_initials_id.
    fSimpl. rewrite f_and_assoc...
  Qed.

  (* Law 1.1 *)
  Lemma r_strengthen_post w pre post post' `{!FormulaFinal pre} :
    initials_closed post w →
    initials_closed post' w →
    post' ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros ?? Hent A. do 2 (rewrite wp_spec; auto). simpl. fSimpl. rewrite <- Hent...
  Qed.

  (* Law 5.1 *)
  Lemma r_strengthen_post_with_initials w pre post post' `{!FormulaFinal pre} :
    initials_closed post w →
    initials_closed post' w →
    <! pre[; ↑ₓ w \ ⇑₀ w ;] ∧ post' !> ⇛ post ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, post'] }>.
  Proof with auto.
    intros ?? Hent A. do 2 (rewrite wp_spec; auto). simpl.
    rewrite <- Hent. rewrite <- f_impl_curry. rewrite -> f_foralllist_impl_unused_l.
    2: { intros x ? ?. apply (fvars_seqsubst_superset_vars_not_free_in_terms) in H2...
         set_solver. }
    rewrite simpl_subst_initials_impl. rewrite subst_initials_inverse_l by set_solver...
    rewrite <- (f_and_idemp pre) at 1. rewrite <- f_and_assoc. fSimpl...
  Qed.

  (* Law 1.2 *)
  Lemma r_weaken_pre w pre pre' post `{!FormulaFinal pre} `{!FormulaFinal pre'} :
    pre ⇛ pre' ->
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre', post] }>.
  Proof.
    intros Hent A. simpl. fSimpl. assumption.
  Qed.

  (* Law 1.7 *)
  Lemma r_simple_spec x t `{!TermFinal t} :
    as_var x ∉ term_fvars t →
    <{ x := t }> ≡ <{ x : [⌜x = t⌝] }>.
  Proof with auto.
    intros Hfree A. rewrite wp_spec... simpl. fSimpl.
    unfold subst_all_initials, subst_initials. rewrite seqsubst_non_free.
    - rewrite f_forall_one_point... simpl. rewrite msubst_single.
      rewrite subst_non_free with (x:=₀x)... intros contra. apply fvars_subst_superset in contra.
      set_unfold. destruct contra... apply term_is_final in H...
    - set_solver.
  Qed.

  Lemma r_permute_frame w w' pre post `{!FormulaFinal pre} :
    initials_closed post w →
    w ≡ₚ w' →
    <{ *w : [pre, post] }> ≡ <{ *w' : [pre, post] }>.
  Proof with auto.
    intros ? H A. do 2 (rewrite wp_spec; auto).
    2: { rewrite <- H... }
    simpl. fSimpl.
    rewrite subst_initials_perm with (xs':=w')... f_equiv.
    rewrite f_foralllist_permute with (xs':=(fmap as_var w'))... apply Permutation_map...
  Qed.

  (* Law 5.4 *)
  Lemma r_contract_frame w xs pre post `{!FormulaFinal pre} :
    initials_closed post (w ++ xs) →
    w ## xs →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *w : [pre, post[_₀\ xs]] }>.
  Proof with auto.
    intros ? Hdisjoint A. do 2 (rewrite wp_spec; auto).
    simpl. fSimpl. rewrite fmap_app. rewrite f_foralllist_app. rewrite f_foralllist_comm.
    rewrite f_foralllist_elim_binders. rewrite subst_initials_app.
    f_equiv. unfold subst_initials at 1. rewrite simpl_seqsubst_foralllist by set_solver.
    f_equiv. rewrite fold_subst_initials. rewrite simpl_subst_initials_impl.
    fSimpl. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 8.3 *)
  Lemma r_expand_frame xs w pre post `{!FormulaFinal pre} :
    initials_closed post w →
    w ## xs →
    <{ *w : [pre, post] }> ⊑ <{ *w, *xs : [pre, post ∧ ⎡⇑ₓ xs =* ⇑₀ xs⎤] }>.
  Proof with auto.
    intros Hclosed Hdisjoint A.
    pose proof (subst_initials_closed_disjoint _ _ _ Hclosed Hdisjoint) as H.
    do 2 (rewrite wp_spec; auto)...
    2:{ intros y?. rewrite simpl_subst_and. rewrite (Hclosed y) by set_solver.
        rewrite subst_non_free... set_solver. }
    simpl. fSimpl.
    unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite <- f_foralllist_one_point...
    setoid_rewrite <- (@eqlist_rewrite _ _ (⇑₀ (w ++ xs))).
    2-3: do 2 rewrite fmap_app; reflexivity.
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
    Unshelve. all: typeclasses eauto.
  Qed.

  (* Law 3.2 *)
  Lemma r_skip w pre post `{!FormulaFinal pre} :
    initials_closed post w →
    pre ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. rewrite wp_spec... simpl.
    fSimpl. rewrite subst_all_initials_weaken with (w:=[]) by set_solver.
    rewrite subst_initials_nil. rewrite <- (f_subst_initials_final_formula pre w)...
    unfold subst_initials. simpl. do 2 rewrite fold_subst_initials.
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite H0. rewrite f_impl_elim. rewrite f_foralllist_one_point...
    rewrite fold_subst_initials. rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 5.3 *)
  Lemma r_skip_with_initials w pre post `{!FormulaFinal pre} :
    initials_closed post w →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ pre !> ⇛ post →
    <{ *w : [pre, post] }> ⊑ skip.
  Proof with auto.
    intros. intros A. rewrite wp_spec... simpl. unfold subst_initials. simpl.
    rewrite fold_subst_initials.
    fSimpl. rewrite subst_all_initials_weaken with (w:=[]) by set_solver.
    rewrite subst_initials_nil. rewrite <- (f_subst_initials_final_formula pre w)...
    rewrite <- simpl_subst_initials_and. unfold subst_initials.
    rewrite <- f_foralllist_one_point... rewrite (f_foralllist_elim_binders (as_var <$> w)).
    rewrite f_impl_dup_hyp. rewrite f_and_assoc. rewrite H0. rewrite f_impl_elim.
    rewrite f_foralllist_one_point... rewrite fold_subst_initials.
    rewrite f_subst_initials_final_formula...
  Qed.

  (* Law 3.4 *)
  Lemma r_skip_seq_l p :
    <{ $skip; $p }> ≡ p.
  Proof with auto.
    intros A. simpl. rewrite subst_all_initials_weaken with (w:=[]) by set_solver. fSimpl...
  Qed.

  (* Law 3.4 *)
  Lemma r_skip_seq_r p :
    <{ $p; $skip }> ≡ p.
  Proof with auto.
    intros A. simpl. apply wp_congr...
    rewrite subst_all_initials_weaken with (w:=[]) by set_solver. fSimpl...
  Qed.

  (* Law 3.3 *)
  Lemma r_seq w pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} `{!FormulaFinal post} :
    initials_closed mid w →
    initials_closed post w →
    <{ *w : [pre, post] }> ⊑ <{ *w : [pre, mid]; *w : [mid, post] }>.
  Proof with auto.
    intros ?? A. simpl.
    pose proof wp_spec. simpl in H1.
    rewrite (H1 w <!! pre !!> post A)... simpl.
    rewrite (H1 w <!! mid !!> post A)... simpl.
    rewrite (H1 w <!! pre !!> mid _)... simpl.
    fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_subst_initials_final_formula) at 1...
    rewrite (f_foralllist_impl_unused_r _ mid) by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* Law B.2 *)
  Lemma r_seq_frame w xs pre mid post `{!FormulaFinal pre} `{!FormulaFinal mid} :
    initials_closed post (w ++ xs) →
    initials_closed mid xs →
    w ## xs →
    list_to_set (↑₀ xs) ## formula_fvars post →
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs : [pre, mid]; *w, *xs : [mid, post] }>.
  Proof with auto.
    intros. intros A. simpl.
    pose proof wp_spec. simpl in H3.
    rewrite (H3 _ <!! pre !!> post A)... simpl.
    rewrite (H3 _ <!! pre !!> mid _)... simpl.
    rewrite (H3 _ <!! mid !!> post A)... simpl.
    fSimpl. rewrite f_impl_and_r. fSimpl.
    rewrite (subst_initials_app _ w xs).
    assert (formula_fvars <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> ## list_to_set (↑₀ xs)).
    { intros x ??. set_unfold in H4. destruct H4 as ([|]&?); [set_solver|].
      set_unfold. destruct H5 as [? _]. apply elem_of_fvars_final_formula_inv in H4... }
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials <! ∀* ↑ₓ (w ++ xs), post ⇒ A !> xs) at 1...
    rewrite (f_subst_initials_no_initials _ xs) at 1 by set_solver...
    rewrite (f_foralllist_impl_unused_r (↑ₓ xs)) at 1 by set_solver.
    erewrite f_intro_hyp at 1. reflexivity.
  Qed.

  (* Law 6.1 *)
  Lemma r_var_intro x ty {w pre post} `{!FormulaFinal pre} :
    initials_closed post w →
    x ∉ w →
    as_var x ∉ formula_fvars pre →
    as_var x ∉ formula_fvars post →
    <{ *w : [pre, post] }> ⊑ <{ |[ var x : ty ⦁ x, *w : [pre, post] ]| }>.
  Proof with auto.
    intros Hclosed Hw Hpre Hpost A.
    rewrite wp_spec...
    mk_fresh ({[as_var x]} ∪ prog_fvars <{ *w : [pre, post] }>
                ∪ formula_fvars A ∪ list_to_set ↑ₓ w
                ∪ formula_fvars post)
      as y.
    rewrite wp_var with (y:=y)...
    2-4: set_solver.
    rewrite wp_spec... etrans.
    2:{ apply subst_proper_fent. 2,3: reflexivity. apply f_forall_ty_intro. }
    rewrite f_forall_and_unused_l... rewrite simpl_subst_and.
    rewrite subst_non_free; [|set_solver]. f_equiv.
    csimpl. rewrite subst_initials_cons_l.
    rewrite simpl_subst_forall_skip' with (x:=₀x).
    2: set_solver.
    2:{
      rewrite simpl_subst_foralllist.
      2: set_solver.
      2:{ intros ???. apply elem_of_list_to_set in H0. set_solver. }
      f_equiv. rewrite simpl_subst_impl. rewrite (Hclosed x)...
      rewrite subst_non_free...
      set_solver.
    }
    rewrite fforall_unused by set_solver. repeat rewrite subst_initials_msubst.
    rewrite msubst_subst_comm by set_solver. repeat rewrite <- subst_initials_msubst.
    mk_fresh (formula_fvars <! ∀* ↑ₓ w, post ⇒ A [x \ y] !>
              ∪ {[as_var x; y]} ∪ list_to_set ↑ₓ w ∪ formula_fvars post ∪ formula_fvars A) as z.
    rewrite simpl_subst_forall_rename with (y':=z) by set_solver.
    rewrite simpl_subst_foralllist by set_solver.
    rewrite simpl_subst_foralllist.
    2:{ destruct_and! H. contradict H3. apply elem_of_list_to_set... }
    2:{ intros ???. apply elem_of_list_to_set in H1. set_solver. }
    do 2 rewrite simpl_subst_impl. rewrite subst_non_free.
    2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
    rewrite subst_non_free... rewrite subst_non_free with (x:=x) (t:=z).
    2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
    rewrite fequiv_subst_trans by set_solver. rewrite fequiv_subst_diag.
    rewrite f_forall_foralllist_comm. rewrite fforall_unused... set_solver.
  Qed.

  Lemma r_var_spec (x : final_variable) ty pre post `{!FormulaFinal pre} w p2:
    initials_closed post w →
    <{ |[ var x : ty ⦁ *w : [pre, post]; $p2 ]| }> ≡
      <{ |[ var x : ty ⦁ *w : [⌜x ∈ₜ ty⌝ ∧ pre, post]; $p2 ]| }>.
  Proof with auto.
    intros Hclosed A.
    mk_fresh ({[as_var x]} ∪
                prog_fvars <{ * w : [⌜ x ∈ₜ ty ⌝ ∧ pre, post]; $ p2 }> ∪
                prog_fvars <{ * w : [pre, post]; $ p2 }> ∪
                formula_fvars A)
      as z.
    rewrite wp_var with (y:=z) by set_solver.
    rewrite wp_var with (y:=z) by set_solver. clear H.
    unfold FForallT. do 2 f_equiv.
    intros σ. split; intros.
    - rewrite simpl_feval_impl. rewrite simpl_feval_impl in H.
      intros. specialize (H H0).
      simpl in *. apply wp_spec' in H... apply wp_spec'...
      simp feval in *. destruct H. split...
    - rewrite simpl_feval_impl in *. intros. specialize (H H0).
      simpl in *. apply wp_spec' in H... apply wp_spec'...
      simp feval in *. destruct_and! H. split...
  Qed.

  Lemma r_var_spec' (x : final_variable) ty pre post `{!FormulaFinal pre} w:
    initials_closed post w →
    <{ |[ var x : ty ⦁ *w : [pre, post] ]| }> ≡
      <{ |[ var x : ty ⦁ *w : [⌜x ∈ₜ ty⌝ ∧ pre, post] ]| }>.
  Proof with auto.
    etrans.
    1:{ apply p_var_proper. 1-2: reflexivity. rewrite <- r_skip_seq_r. reflexivity. }
    rewrite r_var_spec... f_equiv. rewrite r_skip_seq_r...
  Qed.

  Lemma r_var_intro' x ty {w pre post} `{!FormulaFinal pre} :
    initials_closed post w →
    x ∉ w →
    as_var x ∉ formula_fvars pre →
    as_var x ∉ formula_fvars post →
    <{ *w : [pre, post] }> ⊑ <{ |[ var x : ty ⦁ x, *w : [⌜x ∈ₜ ty⌝ ∧ pre, ⌜x ∈ₜ ty⌝ ∧ post] ]| }>.
  Proof with auto.
    intros Hclosed Hw Hpre Hpost.
    etrans.
    1:{ apply @r_var_intro with (x:=x) (ty:=ty)... }
    rewrite r_var_spec'...
    f_equiv. apply r_strengthen_post.
    1:{ intros u. intros. apply (Hclosed u). set_solver. }
    1:{ apply initials_closed_and... }
    apply f_and_elim_r.
  Qed.

  Lemma r_var_comm x y ty p : <{ |[ var x y : ty ⦁ $p ]| }> ≡ <{ |[ var y x : ty ⦁ $p ]| }>.
  Proof with auto.
    intros A. destruct (decide (x = y)); [subst; reflexivity|].
    mk_fresh ({[as_var x; as_var y]} ∪ prog_fvars <{ |[ var y : ty ⦁ $ p ]| }> ∪ formula_fvars A ∪
                                                                      prog_fvars p) as x'.
    mk_fresh ({[as_var y; x'; as_var x]} ∪ prog_fvars p
                ∪ formula_fvars <! A[x \ x'] !>
                ∪ prog_fvars <{ |[ var x : ty ⦁ $ p ]| }>
                ∪ formula_fvars A) as y'.
    rewrite wp_var with (y:=x') by set_solver. rewrite wp_var with (y:=y') by set_solver.
    rewrite wp_var with (y:=y') by set_solver.
    rewrite wp_var with (y:=x')... 2-3: set_solver.
    2:{ intros contra. apply fvars_subst_superset' in contra. set_solver. }
    unfold FForallT.
    mk_fresh (
      {[x'; as_var y; as_var x; y']}
        ∪ quant_subst_fvars x
        <! ⌜ x ∈ₜ ty ⌝ ⇒ (∀ y, ⌜ y ∈ₜ ty ⌝ ⇒ $(wp p <! A [x \ x'] [y \ y'] !>)) [y' \ y] !> x' x
        ∪ quant_subst_fvars x <! ⌜ x ∈ₜ ty ⌝ ⇒ $(wp p <! A [y \ y'] [x \ x'] !>) !> x' x
    ) as ux.
    rewrite simpl_subst_forall_rename with (y:=x) (y':=ux) by set_solver.
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl. destruct (decide _); [|done].
    clear e.
    mk_fresh (
      {[ux; as_var x; x'; as_var y]}
        ∪ quant_subst_fvars y <! ⌜ y ∈ₜ ty ⌝ ⇒ $(wp p <! A [x \ x'] [y \ y'] !>) !> y' y
        ∪ quant_subst_fvars y
          <! ⌜ y ∈ₜ ty ⌝ ⇒ (∀ x, ⌜ x ∈ₜ ty ⌝ ⇒
                              $(wp p <! A [y \ y'] [x \ x'] !>)) [x' \ x] !> y' y
      ) as uy.
    rewrite simpl_subst_forall_rename with (y:=y) (y':=uy) by set_solver.
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl. destruct (decide _); [set_solver|].
    rewrite simpl_subst_forall by set_solver. rewrite simpl_subst_forall by set_solver.
    repeat rewrite simpl_subst_impl. repeat rewrite simpl_subst_af. simpl.
    destruct (decide _); [| done]. simpl. destruct (decide _); [set_solver|].
    simpl. destruct (decide _); [set_solver|]. simpl. destruct (decide _); [set_solver|].
    pose proof (@f_forall_ty_comm M). unfold FForallT in H3. rewrite H3 by set_solver.
    rewrite simpl_subst_forall_rename with (y:=y) (y':=uy) by set_solver.
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl. destruct (decide _); [|done].
    clear e0.
    rewrite simpl_subst_forall_rename with (y:=x) (y':=ux) by set_solver.
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl. destruct (decide _); [set_solver|].
    rewrite simpl_subst_forall by set_solver. rewrite simpl_subst_forall by set_solver.
    repeat rewrite simpl_subst_impl. repeat rewrite simpl_subst_af. simpl.
    destruct (decide _); [| done]. simpl. destruct (decide _); [naive_solver|].
    simpl. destruct (decide _); [set_solver|]. simpl. destruct (decide _); [set_solver|].
    do 4 f_equiv. rewrite fequiv_subst_comm with (x1:=y') (x2:=x) by set_solver.
    rewrite fequiv_subst_comm with (x1:=y') (x2:=x') by set_solver.
    f_equiv.
    rewrite fequiv_subst_comm with (x1:=y) (x2:=x) by set_solver.
    rewrite fequiv_subst_comm with (x1:=y) (x2:=x') by set_solver.
    do 3 f_equiv. apply wp_congr...
    rewrite fequiv_subst_comm; set_solver.
  Qed.

  Lemma r_var_ctx (x : final_variable) ty p1 p2 :
    (∀ σ, feval σ <! ⌜x ∈ₜ ty⌝ !> → p1 ⊑_{ σ } p2) →
    <{ |[ var x : ty ⦁ $p1 ]| }> ⊑ <{ |[ var x : ty ⦁ $p2 ]| }>.
  Proof.
    intros ? A.
    mk_fresh (
        {[as_var x]}
          ∪ prog_fvars p1
          ∪ prog_fvars p2
          ∪ formula_fvars A) as y.
    do 2 rewrite wp_var with (y:=y) by set_solver.
    f_equiv. intros σ ?. eapply f_forall_ty_ent in H1; [exact H1|].
    unfold refines_st in H. intros. specialize (H σ0 H2 <!! A [x \ y] !!>).
    apply H.
  Qed.

  Lemma r_varlist_permute xs xs' p :
    xs ≡ₚ xs' →
    <{ |[ var* xs ⦁ $p ]| }> ≡ <{ |[ var* xs' ⦁ $p ]| }>.
  Proof with auto.
    intros H A. unshelve rewrite wp_varlist...
    pose proof (fresh_vars_for_varlist_spec xs p A). simpl in H0.
    pose proof (fresh_vars_for_varlist_length xs p A).
    (* pose proof (fresh_vars_for_varlist_subset xs p A). *)
    set (zs:=fresh_vars_for_varlist xs p A) in *.
    assert (OfSameLength xs' (zpair_permute xs zs xs')) as Hlen1.
    { unfold OfSameLength. rewrite zpair_permute_length... }
    assert (OfSameLength (zpair_permute xs zs xs') xs' ) as Hlen2.
    { apply of_same_length_comm... }
    assert (xs' ⊆ xs) as Htemp.
    { apply Permutation_equiv_inv in H. apply list_equiv_subseteq in H. naive_solver. }
    assert (zpair_functional xs' (zpair_permute xs zs xs')).
    { apply zpair_permute_functional; [lia| naive_solver| auto]. }
    assert (zpair_injective xs' (zpair_permute xs zs xs')).
    { apply zpair_permute_injective; [lia| naive_solver| auto]. }
    assert (zpair_permute xs zs xs' ≡ zs).
    { destruct_and! H0. apply zpair_permute_equiv... apply Permutation_equiv_inv... }
    assert (zpair_permute xs zs xs' ## xs').
    { destruct_and! H0. rewrite H4. apply Permutation_equiv_inv in H. rewrite <- H... }
    symmetry. etrans.
    - apply Permutation_equiv_inv in H.
      assert (xs' ⊆ xs).
      { apply list_equiv_subseteq in H. naive_solver. }
      destruct_and! H0.
      rewrite (wp_varlist' xs' p A (zpair_permute xs zs xs'))...
      + intros x??. apply elem_of_list_to_set in H10. set_unfold in H10.
        destruct H10 as (x'&?&?). apply H4 in H13. apply (H9 x)...
        apply elem_of_list_to_set. set_unfold. exists x'...
      + intros x??. apply elem_of_list_to_set in H10. set_unfold in H10.
        destruct H10 as (x'&?&?). apply H4 in H13. apply (H11 x)...
        apply elem_of_list_to_set. set_unfold. exists x'...
    - rewrite seqsubst_msubst...
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          apply zpair_injective_flip... }
      2:{ set_solver. }
      rewrite msubst_zpair_Permutation' with (xs':=as_var <$> zs)
                                              (ts':=@TVar M <$> (as_var <$> xs))...
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          apply zpair_injective_flip... }
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          rewrite <- zpair_injective_flip. naive_solver. }
      2:{ apply zpair_Permutation_flip.
          apply zpair_Permutation_fmap_l.
          apply zpair_Permutation_fmap_l.
          apply zpair_Permutation_fmap_r.
          symmetry. apply zpair_permute_Permutation... naive_solver. }
      rewrite <- seqsubst_msubst...
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          apply zpair_injective_flip... naive_solver. }
      2:{ set_solver. }
      apply seqsubst_proper...
      rewrite f_foralllist_permute with (xs':=↑ₓ xs) by (by f_equiv).
      f_equiv. apply wp_congr...
      rewrite seqsubst_msubst...
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          naive_solver. }
      2:{ set_solver. }
      rewrite msubst_zpair_Permutation' with (xs':=as_var <$> xs)
                                              (ts':=@TVar M <$> (as_var <$> zs))...
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|]... }
      2:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          naive_solver. }
      2:{ apply zpair_Permutation_fmap_l.
          apply zpair_Permutation_fmap_r.
          apply zpair_Permutation_fmap_r.
          symmetry. apply zpair_permute_Permutation... naive_solver. }
      rewrite <- seqsubst_msubst...
      1:{ apply zpair_functional_fmap_l; [apply as_var_inj|].
          apply zpair_functional_fmap_r; [apply TVar_inj|].
          apply zpair_functional_fmap_r; [apply as_var_inj|].
          naive_solver. }
      set_solver.
      Unshelve. typeclasses eauto.
  Qed.

  Lemma r_varlist_app xs1 xs2 p :
    <{ |[ var* $(xs1 ++ xs2) ⦁ $p ]| }> ≡ <{ |[ var* $(xs2 ++ xs1) ⦁ $p ]| }>.
  Proof. apply r_varlist_permute. apply Permutation_app_comm. Qed.

  Lemma r_following_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!OfSameLength xs ts} :
    initials_closed post (w ++ xs) →
    length xs ≠ 0 →
    NoDup xs →
    <{ *w, *xs : [pre, post] }> ⊑
    <{ *w, *xs : [pre, post[[↑ₓ xs \ ⇑ₜ ts]]]; *xs := *(FinalRhsTerm <$> ts) }>.
  Proof with auto.
    intros Hclosed Hlength Hnodup A. rewrite wp_spec...
    simpl. rewrite wp_spec'...
    2: apply initials_closed_msubst'...
    rewrite wp_asgn... f_equiv. rewrite <- simpl_msubst_impl. f_equiv.
    rewrite fmap_app. do 2 rewrite foralllist_app. f_equiv.
    rewrite <- f_foralllist_idemp. rewrite (f_foralllist_elim_as_msubst <! post ⇒ A !>)...
    - reflexivity.
    - rewrite length_fmap...
  Qed.

  Lemma r_leading_assignment w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} `{!FormulaFinal <! pre[[↑ₓ xs \ ⇑ₜ ts]] !>} :
    initials_closed post (w ++ xs) →
    w ## xs →
    NoDup w →
    NoDup xs →
    let ts₀ := (λ t : final_term, <! t[[ₜ ↑ₓ w, ↑ₓ xs \ ⇑₀ w, ⇑₀ xs]] !>) <$> ts in
    <{ *w, *xs : [pre[[↑ₓ xs \ ⇑ₜ ts]], post[[↑₀ xs \ *ts₀]]] }> ⊑
      <{ *xs := *(FinalRhsTerm <$> ts); *w, *xs : [pre, post] }>.
  Proof with auto.
    intros Hclosed Hdisjoint Hnodup1 Hnodup2 ? A. simpl. rewrite wp_asgn... rewrite wp_spec'...
    2:{
      apply initials_closed_msubst...
      - intros. set_unfold in H. destruct H as (x'&?&?). apply initial_var_of_inj in H.
        subst. set_solver.
      - intros. subst ts₀. set_unfold in H. destruct H as (t'&->&?).
        apply fvars_msubst_term_superset in H0. set_unfold in H0. destruct H0; [done|].
        destruct H0 as (t&?&?). destruct H1 as [|].
        + destruct H1 as (x'&->&x''&->&?). set_unfold in H0. apply initial_var_of_inj in H0.
            subst x''. set_solver.
        + destruct H1 as (x'&->&x''&->&?). set_unfold in H0. apply initial_var_of_inj in H0.
            subst x''. set_solver.
    }
    rewrite wp_spec'...
    rewrite simpl_msubst_and.
    fSimpl. unfold subst_initials at 1. rewrite subst_initials_app_comm.
    rewrite subst_initials_app. rewrite subst_initials_msubst.
    setoid_rewrite (msubst_trans _ (↑₀ xs) (↑ₓ xs) (⇑ₜ ts)); [| set_solver | |]...
    2:{ intros x ??. set_unfold. destruct H0 as [|]; [set_solver|].
        destruct H. destruct H0 as (x'&?&?&_&_). subst.
        rewrite to_final_var_as_var in H1. set_solver. }
    assert (zpair_functional ↑₀ xs ⇑ₜ ts).
    { apply NoDup_zpair_functional. apply NoDup_fmap... apply initial_var_of_inj. }
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
    rewrite <- subst_initials_msubst. f_equiv. apply map_eq. intros x₀. unfold to_vtmap.
    destruct (decide (x₀ ∈ ↑₀ xs)).
    - apply elem_of_list_fmap in e as (x'&?&?). apply elem_of_list_lookup in H2 as (i&?).
      destruct (lookup_of_same_length_l ts H2) as (t&?). trans (Some (as_term t)).
      + rewrite lookup_list_to_map_zip_Some by typeclasses eauto. exists i. split_and!.
        * rewrite list_lookup_fmap. rewrite H2. simpl. rewrite H1...
        * unfold ts₀. repeat rewrite list_lookup_fmap. rewrite H3.
          simpl. f_equal.
          opose proof msubst_term_app. unfold to_vtmap in H4 at 2 3.
          assert (xs ## w) by set_solver.
          erewrite <- H4; clear H4... rewrite msubst_term_app_comm...
          opose proof (msubst_term_trans t (↑ₓ w ++ ↑ₓ xs) (↑₀ w ++ ↑₀ xs) (⇑ₓ w ++ ⇑ₓ xs)).
             trans (msubst_term t (to_vtmap (↑ₓ w ++ ↑ₓ xs) ((@TVar M <$> (as_var <$> w)) ++
                                                           (@TVar M <$> (as_var <$> xs))))).
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
                ++ f_equal. f_equal. unfold to_vtmap. f_equal. f_equal. rewrite fmap_app...
             -- unfold to_vtmap. repeat rewrite <- fmap_app. rewrite msubst_term_diag'...
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
  Lemma r_asgn w xs pre post ts `{!FormulaFinal pre} `{!OfSameLength xs ts} :
    initials_closed post (w ++ xs) →
    length xs ≠ 0 →
    NoDup xs →
    <! ⎡⇑₀ w =* ⇑ₓ w⎤ ∧ ⎡⇑₀ xs =* ⇑ₓ xs⎤ ∧ pre !> ⇛ <! post[[ ↑ₓ xs \ ⇑ₜ ts ]] !> ->
    <{ *w, *xs : [pre, post] }> ⊑ <{ *xs := *$(FinalRhsTerm <$> ts) }>.
  Proof with auto.
    intros Hclosed Hlength Hnodup proviso A. rewrite wp_spec... simpl. rewrite wp_asgn...
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
    Unshelve. typeclasses eauto.
  Qed.

  Local Lemma r_asgn_equiv' xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    asgn_opens (split_asgn_list xs1 rhs1) ≡ₚ asgn_opens (split_asgn_list xs2 rhs2) →
    (asgn_xs (split_asgn_list xs1 rhs1), asgn_ts (split_asgn_list xs1 rhs1)) ≡ₚₚ
      (asgn_xs (split_asgn_list xs2 rhs2), asgn_ts (split_asgn_list xs2 rhs2)) →
    <{ * xs1 := * rhs1 }> ≡ <{ * xs2 := * rhs2 }>.
  Proof with auto.
    intros Hnodup1 Hnodup2 Hopens Hclosed A. unfold PAsgnWithOpens.
    destruct (split_asgn_list xs1 rhs1) eqn:E1. simpl in *.
    destruct (split_asgn_list xs2 rhs2) eqn:E2. simpl in *.
    do 2 f_equiv. rewrite f_foralllist_permute with (xs':=↑ₓ asgn_opens0)...
    2:{ rewrite Hopens... }
    do 2 f_equiv. apply msubst_zpair_Permutation'...
    - apply NoDup_zpair_functional. apply NoDup_fmap.
      + apply as_var_inj.
      + eapply submseteq_NoDup; [exact Hnodup1|].
        replace asgn_xs with (Prog.asgn_xs (split_asgn_list xs1 rhs1)).
        * apply asgn_xs_submseteq.
        * rewrite E1. reflexivity.
    - apply NoDup_zpair_functional. apply NoDup_fmap.
      + apply as_var_inj.
      + eapply submseteq_NoDup; [exact Hnodup2|].
        replace asgn_xs0 with (Prog.asgn_xs (split_asgn_list xs2 rhs2)).
        * apply asgn_xs_submseteq.
        * rewrite E2. reflexivity.
    - apply zpair_Permutation_fmap; try typeclasses eauto...
  Qed.

  Lemma r_asgn_equiv xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    (xs1, rhs1) ≡ₚₚ (xs2, rhs2) →
    <{ * xs1 := * rhs1 }> ≡ <{ * xs2 := * rhs2 }>.
  Proof with auto.
    intros. apply r_asgn_equiv'...
    - apply asgn_opens_Permutation...
    - apply asgn_xs_ts_Permutation...
  Qed.

  Lemma r_asgn_1 (x : final_variable) pre post t `{!FormulaFinal pre} `{!TermFinal t} :
    initials_closed post [x] →
    <! ⌜₀x = x⌝ ∧ pre !> ⇛ <! post[x \ t] !> ->
    <{ x : [pre, post] }> ⊑ <{ x := t }>.
  Proof with auto.
    intros.
    etransitivity.
    - apply r_asgn with (w:=[]) (ts:=[as_final_term t])...
      + constructor; try set_solver. constructor; try set_solver.
      + intros σ ?. specialize (H0 σ). simpl. apply msubst_single. apply H0. clear H0.
        simp feval in H1. destruct_and! H1. unfold FEqList in H1. simpl in H1.
        simp feval in H1. destruct H1. simp feval. split...
    - simpl...
  Qed.

  Lemma r_asgn_2 (x y : final_variable) pre post t1 t2
      `{!FormulaFinal pre} `{!TermFinal t1} `{!TermFinal t2} :
    initials_closed post [x; y] →
    x ≠ y →
    <! ⌜₀x = x⌝ ∧ ⌜₀y = y⌝ ∧ pre !> ⇛ <! post[[$(as_var x), $(as_var y) \ t1, t2]] !> ->
    <{ x, y : [pre, post] }> ⊑ <{ x, y := t1, t2 }>.
  Proof with auto.
    intros.
    etransitivity.
    - apply r_asgn with (w:=[]) (ts:=[as_final_term t1; as_final_term t2])...
      + constructor; try set_solver. constructor; try set_solver. constructor.
      + intros σ ?. specialize (H1 σ). simp feval in H2, H1. simpl in H2. forward H1.
        * destruct H2 as (_&?&?). unfold FEqList in H2. simpl in H2.
          simp feval in H2. destruct_and! H2. split_and!...
        * simpl. apply H1.
    - simpl...
  Qed.

  Lemma wp_asgn_equiv (A : final_formula) xs1 rhs1 xs2 rhs2 `{!OfSameLength xs1 rhs1} `{!OfSameLength xs2 rhs2} :
    NoDup xs1 →
    NoDup xs2 →
    (xs1, rhs1) ≡ₚₚ (xs2, rhs2) →
    wp (PAsgnWithOpens xs1 rhs1) A ≡ wp (PAsgnWithOpens xs2 rhs2) A.
  Proof with auto. intros. apply r_asgn_equiv... Qed.

  Lemma r_choose_cons_l x xs :
    choose_w (x :: xs) ≡ <{ x : [true]; $ (choose_w xs) }>.
  Proof with auto.
    unfold choose_w. intros A. simpl. fSimpl. do 2 f_equiv.
    unfold subst_all_initials. rewrite finalized_initial_fvars_final...
  Qed.

  Lemma r_choose_cons_r x xs :
    choose_w (x :: xs) ≡ <{ $ (choose_w xs); x : [true]  }>.
  Proof with auto.
    unfold choose_w. intros A. simpl. fSimpl. f_equiv.
    unfold subst_all_initials. rewrite finalized_initial_fvars_final...
    rewrite subst_initials_nil. apply f_forall_foralllist_comm.
  Qed.

  Lemma r_open_assignment_l x t xs rhs
      `{!OfSameLength xs rhs}
      `{!OfSameLength ([x] ++ xs) ([OpenRhsTerm] ++ rhs)}
      `{!OfSameLength ([x] ++ xs) ([FinalRhsTerm t] ++ rhs)} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ t', FinalRhsTerm t' ∈ rhs → as_var x ∉ term_fvars t') →
    <{ x, *xs := ?, *rhs }> ⊑ <{ x, *xs := t, *rhs }>.
  Proof with auto.
    intros. intros A. unfold PAsgnWithOpens. simpl.
    destruct (split_asgn_list (x :: xs) (OpenRhsTerm :: rhs)) eqn:E1.
    destruct (split_asgn_list (x :: xs) (FinalRhsTerm (as_final_term t) :: rhs)) eqn:E2.
    rewrite split_asgn_list_cons_open with (OfSameLength0:=OfSameLength0) in E1.
    rewrite split_asgn_list_cons_closed with (Hl1:=OfSameLength0) in E2.
    unfold asgn_args_with_open in E1. unfold asgn_args_with_closed in E2.
    simpl in E1, E2. destruct (split_asgn_list xs rhs) eqn:E3.
    inversion E1. inversion E2. subst.
    assert (asgn_opens0 = Prog.asgn_opens (split_asgn_list xs rhs)) as Heq1 by (by rewrite E3).
    assert (asgn_xs = Prog.asgn_xs (split_asgn_list xs rhs)) as Heq2 by (rewrite E3; done).
    assert (asgn_ts = Prog.asgn_ts (split_asgn_list xs rhs)) as Heq3 by (rewrite E3; done).
    clear E1 E2 E3. apply wp_proper_ref. etrans.
    { apply p_seq_proper_ref; [|reflexivity]. rewrite r_choose_cons_r. reflexivity. }
    clear A. intros A. simpl. f_equiv. unfold subst_all_initials.
    repeat rewrite finalized_initial_fvars_final... repeat rewrite subst_initials_nil.
    do 2 f_equiv. rewrite f_and_elim_r. rewrite f_forall_elim with (t:=t).
    rewrite simpl_subst_impl. rewrite simpl_subst_af. simpl.
    rewrite f_true_implies. rewrite <- msubst_extract_r...
    2:{ contradict H. set_unfold in H. destruct H as (x'&?&?). apply as_var_inj in H.
        subst x'. rewrite Heq2 in H3. apply asgn_xs_subseteq in H3... }
    2:{ intros H3. set_unfold in H3. destruct H3 as (?&?&t'&->&?). eapply H2 in H3 as [].
        subst asgn_ts. apply elem_of_asgn_ts' in H4... }
    simpl. f_equiv...
  Qed.

  (* Law 3.1 *)
  Lemma r_open_assignment_r x t xs rhs
      `{!OfSameLength xs rhs}
      `{!OfSameLength (xs ++ [x]) (rhs ++ [OpenRhsTerm])}
      `{!OfSameLength (xs ++ [x]) (rhs ++ [FinalRhsTerm t])} :
    x ∉ xs →
    NoDup xs →
    (∀ x', (x', OpenRhsTerm) ∈ (xs, rhs) → as_var x' ∉ term_fvars t) →
    (∀ t', FinalRhsTerm t' ∈ rhs → as_var x ∉ term_fvars t') →
    <{ *xs, x := *rhs, ? }> ⊑ <{ *xs, x := *rhs, t }>.
  Proof with auto.
    intros. intros A.
    rewrite wp_asgn_equiv with (xs2:=[x] ++ xs) (rhs2:=[OpenRhsTerm] ++ rhs)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zpair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        apply zpair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite wp_asgn_equiv with (xs1:=xs ++ [x]) (xs2:=[x] ++ xs) (rhs2:=[FinalRhsTerm t] ++ rhs)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. apply NoDup_singleton. }
    3:{ simpl. rewrite zpair_Permutation_app_comm... 2: typeclasses eauto. simpl.
        rewrite as_final_term_as_term. apply zpair_Permutation_cons... }
    2:{ apply NoDup_cons. split... }
    rewrite (r_open_assignment_l x t xs rhs H H0 H1 H2 A). simpl.
    rewrite as_final_term_as_term. reflexivity.
  Qed.

  Lemma r_open_assignment_middle x t xs0 xs1 rhs0 rhs1
      `{!OfSameLength xs0 rhs0}
      `{!OfSameLength xs1 rhs1}
      `{!OfSameLength (xs0 ++ [x] ++ xs1) (rhs0 ++ [OpenRhsTerm] ++ rhs1)}
      `{!OfSameLength (xs0 ++ [x] ++ xs1) (rhs0 ++ [FinalRhsTerm t] ++ rhs1)} :
    (∀ x', (x', OpenRhsTerm) ∈ (xs0, rhs0) → as_var x' ∉ term_fvars t) →
    (∀ x', (x', OpenRhsTerm) ∈ (xs1, rhs1) → as_var x' ∉ term_fvars t) →
    (∀ t', FinalRhsTerm t' ∈ rhs0 → as_var x ∉ term_fvars t') →
    (∀ t', FinalRhsTerm t' ∈ rhs1 → as_var x ∉ term_fvars t') →
    x ∉ xs0 →
    x ∉ xs1 →
    NoDup xs0 →
    NoDup xs1 →
    xs0 ## xs1 →
    <{ *xs0, x, *xs1 := *rhs0, ?, *rhs1 }> ⊑ <{ *xs0, x, *xs1 := *rhs0, t, *rhs1 }>.
  Proof with auto.
    intros. intros A.
    rewrite wp_asgn_equiv with (xs2:=[x] ++ xs0 ++ xs1) (rhs2:=[OpenRhsTerm] ++ rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons. split... }
    3:{ simpl. rewrite zpair_Permutation_app_comm...
        2: typeclasses eauto. simpl. apply zpair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zpair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    rewrite wp_asgn_equiv with (xs1:=xs0 ++ [x] ++ xs1) (xs2:=[x] ++ xs0 ++ xs1)
                                                    (rhs2:=[FinalRhsTerm t] ++ rhs0 ++ rhs1)...
    2:{ apply NoDup_app. split_and!; [auto | set_solver |]. simpl. apply NoDup_cons.
        split... }
    3:{ simpl. rewrite zpair_Permutation_app_comm...
        2: typeclasses eauto. simpl. rewrite as_final_term_as_term.
        apply zpair_Permutation_cons...
        1-2: typeclasses eauto. rewrite zpair_Permutation_app_comm... }
    2:{ apply NoDup_cons. rewrite NoDup_app. split_and!... set_solver. }
    opose proof (r_open_assignment_l x t (xs0 ++ xs1) (rhs0 ++ rhs1) _ _ _ _ A).
    1:{ set_solver. }
    1:{ apply NoDup_app. split_and!... }
    1:{ intros. apply elem_of_zpair_app in H8... destruct H8... }
    1:{ intros. apply elem_of_app in H8. destruct H8... }
    rewrite H8. simpl. rewrite as_final_term_as_term. reflexivity.
  Qed.

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

  Lemma r_if_2 w pre post g1 g2 `{!FormulaFinal pre} :
    pre ⇛ <! g1 ∨ g2 !> →
    <{ *w : [pre, post] }> ⊑ <{ if g1 → *w : [g1 ∧ pre, post] | g2 → *w : [g2 ∧ pre, post] fi }>.
  Proof with auto.
    intros proviso.
    pose proof (r_alternation w pre post [g1; g2]). simpl in H. simpl.
    apply H. etrans.
    - apply proviso.
    - fSimpl. reflexivity.
  Qed.

  Lemma r_if_2_proper g1 g2 {p1 p1' p2 p2'} :
    p1 ⊑ p1' →
    p2 ⊑ p2' →
    <{ if g1 → $p1 | g2 → $p2 fi }> ⊑ <{ if g1 → $p1' | g2 → $p2' fi }>.
  Proof. intros. intros A. simpl. fSimpl. f_equiv; f_equiv; by apply wp_proper_ref. Qed.

  Lemma r_iteration (w : list final_variable) (g : formula)
      (inv : final_formula) (var : final_term) `{!FormulaFinal g} :
    NoDup w →
    let var₀ := <! $(as_term var) [[ₜ ↑ₓ w \ ⇑₀ w ]] !> in
    <{ *w : [inv, inv ∧ ¬ g] }> ⊑
      <{ while g invariant inv variant var ⟶
         *w : [inv ∧ g, inv ∧ ⌜var ∈ₜ ℕ⌝ ∧ ⌜0 ≤ var⌝ ∧ ⌜var < var₀⌝] end }>.
  Proof with auto.
    intros Hnodup ? A. simpl. unfold modified_vars. simpl.
    rewrite (f_foralllist_permute (set_to_list (as_var_set (list_to_set w))) (↑ₓ w)).
    2:{ apply set_to_list_as_var_set_list_to_set... }
    unfold subst_all_initials at 1. rewrite finalized_initial_fvars_final...
    rewrite subst_initials_nil. intros σ. simp feval. simpl.
    repeat rewrite simpl_feval_foralllist. intros.
    destruct_and! H.
    assert (Haux1 : zpair_functional ↑ₓ w (@TConst M <$> vs)) by
      (apply NoDup_zpair_functional; auto).
    assert (Haux2 : list_to_set ↑ₓ w ## ⋃ (@term_fvars M <$> (TConst <$> vs))).
    { intros x ??. set_unfold in H3. destruct H3 as (t&?&vt&->&?). simpl in H3. set_solver. }
    rewrite seqsubst_msubst... epose proof (teval_vtmap_total σ _) as [mv ?].
    rewrite feval_msubst by exact H. simp feval. split_and!.
    - rewrite simpl_feval_impl. simp feval. intros. destruct_and! H3. split_and!...
      unfold subst_all_initials. unfold subst_initials. rewrite seqsubst_msubst...
      epose proof (teval_vtmap_total _ _) as [mv0 ?].
      rewrite feval_msubst by exact H4. rewrite simpl_feval_foralllist. intros.
      rewrite seqsubst_msubst...
      2:{ apply NoDup_zpair_functional... }
      2:{ intros x ??. set_unfold in H9. destruct H9 as (?&?&?&->&?). simpl in H9. set_solver. }
      epose proof (teval_vtmap_total _ _) as [mv' ?].
      rewrite feval_msubst by exact H8. rewrite simpl_feval_impl. simp feval.
      intros [? []]. split...
    - specialize (H2 vs H0). apply seqsubst_msubst in H2...
      rewrite feval_msubst in H2 by exact H... rewrite simpl_feval_impl in H2 |- *.
      simp feval in H2 |- *. intros [[] ?]. apply H2. split...
    - rewrite simpl_feval_impl. simp feval. naive_solver.
    - mk_fresh String.EmptyString
         (Prog.while_fvars <!! g !!> <!! inv ∧ ⌜ var ∈ₜ ℕ ⌝ !!> var
            <{ * w : [inv ∧ g, inv ∧ ⌜ var ∈ₜ ℕ ⌝ ∧ ⌜ 0 ≤ var < var₀ ⌝] }>)
         as y.
      rewrite simpl_feval_forall. intros var0. rewrite feval_subst with (v:=var0)...
      assert (finalized_initial_fvars <! inv ∧ ⌜ var ∈ₜ ℕ ⌝ ∧ ⌜ 0 ≤ var < var₀ ⌝ !> ⊆ w).
      1:{ unfold finalized_initial_fvars, initial_fvars.
          set_unfold. intros. destruct_or! H4. destruct H4 as (t&?&?). destruct_or! H5.
          - subst. apply term_is_final in H4. apply var_final_initial_var_of in H4 as [].
          - subst. subst var₀. apply fvars_msubst_term_superset in H4. set_unfold in H4.
            naive_solver. }
      rewrite wp_spec_weaken_subst with (xs:=w)... clear H4.
      rewrite simpl_feval_impl. simp feval. intros [[] []]. split_and!...
      unfold subst_initials. rewrite seqsubst_msubst...
      epose proof (teval_vtmap_total _ _) as [mv0 ?].
      rewrite feval_msubst by exact H8. rewrite simpl_feval_foralllist.
      intros vs' ?. rewrite seqsubst_msubst...
      2:{ apply NoDup_zpair_functional... }
      2:{ intros x ??. set_unfold in H11. destruct H11 as (?&?&?&->&?). set_solver. }
      epose proof (teval_vtmap_total _ _) as [mv' ?].
      rewrite feval_msubst by exact H10. rewrite simpl_feval_impl. simp feval.
      intros [? [? []]]. rewrite <- feval_msubst in H14 |- * by exact H10.
      unfold term_lt in H14 |- *. simp msubst in H14 |- *. simpl in H14 |- *.
      unfold var₀ in H14. eapply ATPred_proper_st in H14.
      2:{ reflexivity. }
      2:{ split.
          2:{ constructor; [reflexivity|constructor; [|reflexivity]].
              rewrite msubst_term_msubst_term_eq_cancel... reflexivity. }
          simpl... }
      rewrite <- feval_msubst in H14 |- * by exact H8. simp msubst in H14 |- *.
      simpl in H14 |- *. eapply ATPred_proper_st.
      1:{ reflexivity. }
      2:{ exact H14. }
      split... constructor; [reflexivity|]. constructor... simpl in H7.
      clear dependent H4 H5 mv0 mv' H14 H2. destruct H7 as (vv&?&?).
      symmetry. etrans.
      + erewrite (msubst_term_trans var (↑ₓ w) (↑₀ w))...
        * rewrite msubst_term_diag... reflexivity.
        * set_solver.
        * intros x ??. set_unfold in H5. apply final_term_final in H7. naive_solver.
      + destruct (to_vtmap ↑ₓ w (TConst <$> vs')
                 !! to_initial_var (fresh_var String.EmptyString (as_var_set (list_to_set w)))
                 ) eqn:E.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E.
            2:{ typeclasses eauto. }
            apply elem_of_zpair in E as (i&?&?). apply list_lookup_fmap_Some in H5 as (x&?&?).
            destruct x. unfold as_var in H8. simpl in H8. apply (f_equal var_is_initial) in H8.
            simpl in H7. discriminate. }
        simpl. clear E.
        destruct (to_vtmap ↑ₓ w (TConst <$> vs') !! y) eqn:E.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E.
            2:{ typeclasses eauto. }
            apply elem_of_zpair in E as (i&?&?). apply list_lookup_fmap_Some in H5 as (x&?&?).
            subst y. apply elem_of_list_lookup_2 in H5. unfold Prog.while_fvars in H3.
            simpl in H3. repeat rewrite not_elem_of_union in H3. destruct_and! H3.
            exfalso. revert H5 H8. clear. intros. set_solver. }
        simpl. destruct (to_vtmap ↑₀ w ⇑ₓ w !! y) eqn:E'.
        1:{ unfold to_vtmap in E. apply lookup_list_to_map_zip_Some_inv in E'.
            2:{ typeclasses eauto. }
            apply elem_of_zpair in E' as (i&?&?). apply list_lookup_fmap_Some in H5 as (x&?&?).
            subst y. unfold VarFinal in Hfinal.
            apply var_final_initial_var_of in Hfinal as []. }
        intros v. split; intros.
        * apply teval_det with (v1:=v) in H2... subst...
        * apply teval_det with (v1:=v) in H4... subst...
  Qed.

  Lemma r_iteration'
    (w : list final_variable) (g : formula) (inv inv' post : final_formula) (var : final_term)
    `{!FormulaFinal g} :
    NoDup w →
    inv ≡ inv' →
    as_formula post ≡ <! inv ∧ ¬ g !> →
    let var₀ := <! $(as_term var) [[ₜ ↑ₓ w \ ⇑₀ w ]] !> in
    <{ *w : [inv, post] }> ⊑
      <{ while g invariant inv' variant var ⟶
         *w : [inv ∧ g, inv ∧ ⌜var ∈ₜ ℕ⌝ ∧ ⌜0 ≤ var⌝ ∧ ⌜var < var₀⌝] end }>.
  Proof with auto.
    intros. rewrite H1. etrans.
    - apply r_iteration...
    - apply pequiv_refines. f_equiv.
      2: reflexivity.
      + unfold equiv, ffequiv. simpl. fSimpl...
      + unfold var₀. done.
  Qed.

  Lemma r_while_body {g I v p1 p2} :
    Δ p1 = Δ p2 →
    p1 ⊑ p2 →
    PWhile g I v p1 ⊑ PWhile g I v p2.
  Proof with auto.
    intros. intros A. simpl. rewrite H. f_equiv. f_equiv...
    - fSimpl. rewrite refines_iff_fent in H0...
    - fSimpl. rewrite refines_iff_fent in H0...
      mk_fresh (formula_fvars I ∪ formula_fvars g ∪ term_fvars v ∪
                  prog_fvars p1 ∪ prog_fvars p2) as x.
      rewrite wp_while_decrease_variant with (y:=x)...
      2-5: set_solver.
      rewrite wp_while_decrease_variant with (y:=x)...
      2-5: set_solver.
      do 2 f_equiv.
      rewrite H0...
  Qed.

  (* Lemma 7.1 *)
  Lemma r_remove_inv {w pre inv post} `{!FormulaFinal pre} `{!FormulaFinal inv} :
    list_to_set (↑ₓ w) ## formula_fvars inv →
    NoDup w →
    <{ *w : [pre ∧ inv, inv ∧ post] }> ⊑ <{ *w : [pre, post] }>.
  Proof with auto.
    intros Hdisj Hnodup. intros A. simpl. intros σ ?. simp feval in *. destruct_and! H.
    split...
    unfold subst_all_initials in H1 |- *.
    rewrite wp_spec_finalized_initial_fvars in H1 |- *...
    assert (finalized_initial_fvars <! inv ∧ post !> ≡ₚ finalized_initial_fvars <! post !>).
    { unfold finalized_initial_fvars. unfold initial_fvars. simpl.
      rewrite filter_set_to_list_delete_union_l... intros.
      apply formula_is_final in H0. rewrite var_initial_not_final... }
    rewrite H0 in H1. clear H0. unfold subst_initials in *. rewrite seqsubst_msubst in *...
    epose proof (teval_vtmap_total σ _) as [mv ?].
    rewrite feval_msubst by exact H0.
    rewrite feval_msubst in H1 by exact H0.
    rewrite simpl_feval_foralllist in *. intros. specialize (H1 vs H3).
    rewrite seqsubst_msubst...
    2:{ apply NoDup_zpair_functional... }
    2:{ set_unfold. intros. destruct H5 as (?&?&?&?&?). subst. done. }
    epose proof (teval_vtmap_total _ _) as [mv' ?].
    rewrite feval_msubst by exact H4.
    rewrite seqsubst_msubst in H1...
    2:{ apply NoDup_zpair_functional... }
    2:{ set_unfold. intros. destruct H6 as (?&?&?&?&?). subst. done. }
    rewrite feval_msubst in H1 by exact H4. rewrite simpl_feval_impl in *.
    intros. apply H1. simp feval. split... rewrite <- feval_msubst by exact H4.
    rewrite msubst_non_free... rewrite <- feval_msubst by exact H0.
    rewrite msubst_non_free... set_solver.
  Qed.

End refinement.
