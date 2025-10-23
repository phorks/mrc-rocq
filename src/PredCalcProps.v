From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc PredCalcSubst PredCalcEquiv.
From stdpp Require Import gmap fin_maps.

Lemma fequiv_subst_and_diag A x :
  <! A[x \ x] !> ≡ A ∧ ∀ M σ t v b, teval M σ t v → feval M (<[x:=v]> σ) A b ↔ feval M σ (A[x \ t]) b.
Proof with auto.
  generalize dependent x. induction A; intros.
  - unfold subst_formula. simpl. rewrite subst_sf_diag... split...
    split; inversion 1; subst.
    + constructor. apply (sfeval_subst H)...
    + constructor. apply (sfeval_subst H)...
  - split.
    + rewrite simpl_subst_not. destruct (IHA x) as [-> _]...
    + intros. rewrite simpl_subst_not. split; inversion 1; subst.
      * constructor. apply IHA with (x:=x) (b:=b0) in H. apply H...
      * constructor. apply IHA with (x:=x) (b:=b0) in H. apply H...
  - split.
    + rewrite simpl_subst_and. destruct (IHA1 x) as [-> _]. destruct (IHA2 x) as [-> _]...
    + intros. rewrite simpl_subst_and. split; inversion 1; subst.
      * apply IHA1 with (x:=x) (b:=b1) in H as ?.
        apply IHA2 with (x:=x) (b:=b2) in H. constructor.
        -- apply H1...
        -- apply H...
      * apply IHA1 with (x:=x) (b:=b1) in H as ?.
        apply IHA2 with (x:=x) (b:=b2) in H. constructor.
        -- apply H1...
        -- apply H...
  - split.
    + rewrite simpl_subst_or. destruct (IHA1 x) as [-> _]. destruct (IHA2 x) as [-> _]...
    + intros. rewrite simpl_subst_or. split; inversion 1; subst.
      * apply IHA1 with (x:=x) (b:=b1) in H as ?.
        apply IHA2 with (x:=x) (b:=b2) in H. constructor.
        -- apply H1...
        -- apply H...
      * apply IHA1 with (x:=x) (b:=b1) in H as ?.
        apply IHA2 with (x:=x) (b:=b2) in H. constructor.
        -- apply H1...
        -- apply H...
  - split.
    { rename x into y. rename x0 into x. destruct (quant_subst_skip_cond y A x).
      - rewrite simpl_subst_exists_skip...
      - rewrite simpl_subst_exists_propagate...
        generalize_fresh_var y A x x as y'.
        intros M σ b. apply feval_exists_equiv.
        + intros. destruct H4.
          * subst. pose proof (H':=H). forward (H' (A[y'\y'])) by auto. destruct (H' x) as [? _].
            rewrite H4. clear H'. clear H4.
            forward (H (A)) by auto. destruct (H y') as [? _].
            rewrite H4...
          * pose proof (H':=H). forward (H' (A[y\y'])) by auto. destruct (H' x) as [? _].
            rewrite H7. clear H7 H'. forward (H A) by auto. destruct (H y) as [_ ?].
            rewrite <- H7 with (v:=v).
            2: { constructor. apply lookup_insert. }
            destruct (decide (y = y')).
            -- subst. rewrite (insert_insert σ)...
            -- rewrite (insert_commute σ)... apply feval_delete_state_var_head...
        + destruct H4.
          * subst. do 2 rewrite formula_wf_subst_diag...
          * intros. rewrite formula_wf_subst_diag. rewrite formula_wf_subst with (τ:=τ).
            2:{ unfold term_has_type. unfold term_ty. apply lookup_insert_Some... }
            destruct (decide (y = y')).
            -- subst. rewrite (insert_insert (state_types σ))...
            -- rewrite (insert_commute (state_types σ))... apply formula_wf_delete_state_var_head... }
    + intros. rename H0 into Ht. destruct (decide (x = x0)).
      * subst. rewrite simpl_subst_exists_skip... apply feval_exists_equiv.
        -- intros. rewrite (insert_insert σ)...
        -- intros. unfold state_types. setoid_rewrite fmap_insert.
           setoid_rewrite (insert_insert (value_typeof <$> σ))...
      * destruct (decide (x0 ∈ formula_fvars A)).
        2: { rewrite simpl_subst_exists_skip... rewrite feval_delete_state_var_head... simpl.
             apply not_elem_of_difference... }
        rewrite simpl_subst_exists_propagate... generalize_fresh_var x A x0 t0 as x'.
        apply feval_exists_equiv.
        -- intros. destruct H2.
           ++ subst.
              pose proof H as H'. forward (H' (A [x' \ x'])) by auto. destruct (H' x0) as [_ ?].
              rewrite <- H2 with (v:=v)...
              2:{ apply teval_delete_state_var_head... }
              clear H3 H'.
              forward (H A)... destruct (H x') as [? _].  rewrite H3.
              rewrite (insert_commute σ)...
           ++ pose proof H as H'. forward (H' (A [x \ x'])) by auto. destruct (H' x0) as [_ ?].
              rewrite <- H5 with (v:=v)...
              2:{ apply teval_delete_state_var_head... }
              rewrite (insert_commute σ x0 x')...
              clear H0 H'.
              forward (H A)... destruct (H x) as [_ ?]. rewrite <- H0 with (v:=v0).
              2:{ apply TEval_Var. apply lookup_insert_Some. left... }
              rewrite (@feval_delete_state_var x' _ (<[x:=v0]> (<[x':=v0]> (<[x0:=v]> σ))))...
              rewrite (@feval_delete_state_var x' _ (<[x:=v0]> (<[x0:=v]> σ)))...
              clear H0 H Ht. f_equiv.
              destruct (decide (x = x')).
              ** subst. rewrite (insert_insert (<[x0:=v]> σ))...
              ** rewrite (insert_commute (<[x0:=v]> σ))...
                 rewrite (delete_insert_delete (<[x:=v0]> (<[x0:=v]> σ)))...
        -- intros. apply teval_term_has_type in Ht.
           assert (term_has_type M (<[x':=τ]> (state_types σ)) t0 (value_typeof v)).
           {
             unfold term_has_type. rewrite (term_ty_delete_state_var M x')...
             rewrite (delete_insert_delete (state_types σ)).
             rewrite <- (term_ty_delete_state_var)...
           }
           assert (term_has_type M (<[x0:=value_typeof v]> (<[x':=τ]> (state_types σ))) x' τ).
           {
             unfold term_has_type. simpl. rewrite (lookup_insert_ne (<[x':=τ]> (state_types σ)))...
             apply lookup_insert_Some...
           }
           destruct H2.
           { subst. rewrite formula_wf_subst with (t:=t0) (τ:=value_typeof v)...
             rewrite formula_wf_subst_diag. rewrite state_types_insert.
             rewrite (insert_commute (state_types σ))... }
           rewrite formula_wf_subst with (t:=t0) (τ:=value_typeof v)...
           rewrite formula_wf_subst with (t:=x') (τ:=τ)...
           rewrite state_types_insert.
           rewrite (formula_wf_delete_state_var _ x')...
           symmetry. etrans. { rewrite (formula_wf_delete_state_var _ x')... }
           f_equal.
           destruct (decide (x = x')).
           ++ subst.
              rewrite (delete_insert_delete (<[x0:=value_typeof v]> (<[x':=τ]> (state_types σ)))).
              rewrite (delete_insert_delete (<[x0:=value_typeof v]> (state_types σ))).
              rewrite (insert_commute (state_types σ))...
              rewrite (delete_insert_delete (<[x0:=value_typeof v]> (state_types σ)))...
           ++
             rewrite (delete_insert_ne (<[x0:=value_typeof v]> (<[x':=τ]> (state_types σ))))...
             rewrite (delete_insert_ne (<[x0:=value_typeof v]> (state_types σ)))...
             f_equal.
             rewrite (insert_commute (state_types σ))...
             rewrite (delete_insert_delete (<[x0:=value_typeof v]> (state_types σ)))...
Qed.


Lemma feval_subst {M} σ A x t b v :
  teval M σ t v →
  feval M (<[x:=v]> σ) A b ↔ feval M σ (A[x \ t]) b.
Proof. apply fequiv_subst_and_diag. Qed.

Lemma fequiv_subst_diag A x :
  <! A[x \ x] !> ≡ A.
Proof with auto. apply fequiv_subst_and_diag. Qed.

Instance subst_proper : Proper ((≡@{formula}) ==> (=) ==> (=) ==> (≡@{formula})) subst_formula.
Proof with auto.
  intros A B H x ? <- t ? <- M σ b; split; intros.
  - apply feval_wf in H0 as ?.
    destruct (decide (x ∈ formula_fvars A)); destruct (decide (x ∈ formula_fvars B)).
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + exfalso. rewrite subst_non_free in H0...
      rewrite feval_delete_state_var with (x:=x) in H0...
      apply H in H0. apply feval_wf in H0 as ?. apply formula_wf_state_covers in H2.
      set_solver.
    + rewrite subst_non_free in H0... rewrite subst_non_free... apply H...
  - apply feval_wf in H0 as ?.
    destruct (decide (x ∈ formula_fvars A)); destruct (decide (x ∈ formula_fvars B)).
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + exfalso. rewrite subst_non_free in H0...
      rewrite feval_delete_state_var with (x:=x) in H0...
      apply H in H0. apply feval_wf in H0 as ?. apply formula_wf_state_covers in H2.
      set_solver.
    + apply formula_wf_subst_term_wf in H1... apply term_wf_teval in H1 as [v Hv].
      rewrite <- feval_subst with (v:=v)... apply H. rewrite feval_subst with (t:=t)...
    + rewrite subst_non_free in H0... rewrite subst_non_free... apply H...
Qed.

Lemma fequiv_exists_alpha_equiv x x' τ A :
  x' ∉ formula_fvars A →
  <! exists x : τ, A !> ≡ <! exists x' : τ, A[x \ x'] !>.
Proof with auto.
  intros Hfree M σ b.
  apply feval_exists_equiv.
  - intros. rewrite <- feval_subst with (v:=v).
    2: { constructor. apply lookup_insert_Some. left... }
    destruct (decide (x = x')).
    + subst. rewrite (insert_insert σ)...
    + rewrite (insert_commute σ)...
      rewrite (feval_delete_state_var_head x')...
  - intros. rewrite formula_wf_subst with (τ:=τ).
    2:{ unfold term_has_type. unfold term_ty. apply lookup_insert_Some. left... }
    destruct (decide (x = x')).
    + subst. rewrite (insert_insert (state_types σ))...
    + rewrite (insert_commute (state_types σ))...
      rewrite (formula_wf_delete_state_var_head _ x')...
Qed.

Lemma fequiv_forall_alpha_equiv x x' τ A :
    x' ∉ formula_fvars A →
    <! forall x : τ, A !> ≡ <! forall x' : τ, A[x \ x'] !>.
Proof with auto.
  intros. unfold FForall. rewrite fequiv_exists_alpha_equiv with (x':=x')...
  rewrite simpl_subst_not...
Qed.

Lemma fequiv_exists_non_free_binder x τ A :
  x ∉ formula_fvars A →
  ((∃ v, v ∈ τ) ∧ <! exists x : τ, A !> ≡ A) ∨
    ((value_ty_is_empty τ) ∧ <! exists x : τ, A !> ≡ <! false ∧ A !>).
Proof with auto.
  intros H. destruct (value_ty_choice τ).
  - left. destruct s as [v Hv]. apply eq_dec_eq in Hv.
    apply value_elem_of_iff_typeof_eq in Hv. split; [eauto |].
    intros M σ b. split; intros.
    + inversion H0; subst.
      * destruct H5 as [v' [_ ?]]. apply feval_delete_state_var_head in H1...
      * apply H6 in Hv. apply feval_delete_state_var_head in Hv...
      * apply H5 in Hv as [].
    + destruct b.
      * apply FEval_Exists_True. exists v. split... apply feval_delete_state_var_head...
      * apply FEval_Exists_False; [eauto|]. intros. apply feval_delete_state_var_head...
  - right. assert (∀ x, x ∉ τ). { intros v contra. apply (n v). apply eq_dec_eq... }
    clear n. split... split; intros.
    + inversion H1; subst.
      * destruct H6 as [? [contra _]]. apply H0 in contra as [].
      * destruct H6 as [? contra]. apply H0 in contra as [].
      * rewrite formula_wf_delete_state_var_head in H7... apply feval_lem in H7.
        destruct H7 as [b Heval]. replace false with (false && b)...
    + inversion H1; subst. inversion H4; subst. inversion H3; subst.
      clear H4 H1 H3. simpl. apply feval_wf in H6. apply FEval_Exists_False_Empty...
      rewrite formula_wf_delete_state_var_head...
Qed.

(* Lemma fequiv_subst_trans : ∀ A (x1 x2 x3 : variable), *)
(*     x2 ∉ formula_fvars A → *)
(*     <! A[x1 \ x2][x2 \ x3] !> ≡ <! A[x1 \ x3] !>. *)
(* Proof with auto. *)
(*   induction A; intros. *)
(*   - admit. *)
(*   - do 3 rewrite simpl_subst_not. rewrite IHA... *)
(*   - simpl in H. apply not_elem_of_union in H as []. do 3 rewrite simpl_subst_and. *)
(*     rewrite IHA1... rewrite IHA2... *)
(*   - simpl in H. apply not_elem_of_union in H as []. do 3 rewrite simpl_subst_or. *)
(*     rewrite IHA1... rewrite IHA2... *)
(*   - simpl in H0. apply not_elem_of_difference in H0. rewrite elem_of_singleton in H0. *)
(*     destruct (quant_subst_skip_cond x A x1); destruct (quant_subst_skip_cond x A x2). *)
(*     + do 4 (rewrite simpl_subst_exists_skip; auto). *)
(*     + simpl in H0. destruct H0; try contradiction. symmetry in H0. contradiction. *)
(*     + destruct (decide (x ∈ formula_fvars A)). *)
(*       2:{ *)
(*         assert (x2 ∉ formula_fvars A). { destruct H0... subst... } clear H0 H3. *)
(*         destruct (fequiv_exists_non_free_binder x τ A)... *)
(*           - destruct H0 as []. *)
(*             assert (<! (exists x : τ, A) [x1 \ x2] [x2 \ x3] !> ≡ A[x1 \ x2][x2 \ x3]). *)
(*             { pose proof (@subst_proper x2 x3). apply H5... *)
(*               pose proof (@subst_proper x1 x2). apply H6... } *)
(*             rewrite H5. *)
(*             assert (<! (exists x : τ, A) [x1 \ x3] !> ≡ A[x1 \ x3]). *)
(*             { pose proof (@subst_proper x1 x3). apply H6... } *)
(*             rewrite H6. apply H... *)
(*           - destruct H0 as []. *)
(*             assert (<! (exists x : τ, A) [x1 \ x2] [x2 \ x3] !> ≡ <! (false ∧ A) [x1 \ x2][x2 \ x3] !>). *)
(*             { pose proof (@subst_proper x2 x3). apply H5... *)
(*               pose proof (@subst_proper x1 x2). apply H6... } *)
(*             rewrite H5. *)
(*             assert (<! (exists x : τ, A) [x1 \ x3] !> ≡ <! (false ∧ A) [x1 \ x3] !>). *)
(*             { pose proof (@subst_proper x1 x3). apply H6... } *)
(*             rewrite H6. do 3 rewrite simpl_subst_and. do 3 rewrite simpl_subst_sf. simpl. *)
(*             f_equiv. apply H... } *)
(*       clear H3. rewrite simpl_subst_exists_propagate... *)
(*       generalize_fresh_var x A x1 x2 as x'. *)
(*       simpl in H6. rewrite not_elem_of_singleton in H6. *)
(*       rewrite simpl_subst_exists_propagate... *)
(*       2:{ rewrite subst_free_fvars; [| rewrite subst_free_fvars; auto]; set_solver. } *)
(*       generalize_fresh_var x' <! A [x \ x'] [x1 \ x2] !> x2 x3 as y1. *)
(*       rewrite simpl_subst_exists_propagate... *)
(*       generalize_fresh_var x A x1 x3 as y2. *)

(*       simpl in H7. *)

(*       symmetry. *)

(*       rewrite simpl_subst_exists_propagate; auto... *)
(*       rewrite simpl_subst_exists_skip... *)
(*       generalize_fresh_var x A x2 x3 as x'. symmetry. *)
(*       destruct (quant_subst_skip_cond x' (A [x \ x'][x2 \ x3]) x1). *)
(*       * rewrite simpl_subst_exists_skip... *)
(*       * exfalso. destruct H3. *)
(*         -- subst x1. *)
(*            pose proof (fresh_var_fresh x (quant_subst_fvars A x2 t2)). *)
(*            apply quant_subst_fvars_inv in H3 as (?&?&?). *)
(*            assert (x ∈ formula_fvars A). *)
(*            { destruct (decide (x ∈ formula_fvars A))... exfalso. *)
(*              pose proof (fresh_var_free x (quant_subst_fvars A x2 t2)). *)
(*              forward H10; try contradiction. set_solver. } *)
(*            rewrite subst_free_fvars in H7. *)
(*            ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7. *)
(*               rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7. *)
(*               destruct H7 as [[? []]|]... simpl in H7. *)
(*               apply elem_of_union in H7. rewrite elem_of_difference in H7. *)
(*               rewrite not_elem_of_singleton in H7. destruct H7 as [[? []]|]... *)
(*               rewrite elem_of_singleton in H7. exfalso. apply H6... *)
(*            ++ rewrite subst_free_fvars... rewrite elem_of_union. *)
(*               left. rewrite elem_of_difference. rewrite elem_of_singleton. split... *)
(*         -- apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction. *)
(*            apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction. *)
(*            simpl in H7. rewrite elem_of_singleton in H7. apply H6. symmetry... *)
(*     + admit. *)
(*     + destruct (decide (x ∈ formula_fvars A)). *)
(*       2:{ destruct (fequiv_exists_non_free_binder x τ A)... *)
(*           - destruct H7 as []. *)
(*             assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ A[x1 \ t1][x2 \ t2]). *)
(*             { pose proof (@subst_proper x2 t2). apply H9... *)
(*               pose proof (@subst_proper x1 t1). apply H10... } *)
(*             rewrite H9. *)
(*             assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ A[x2 \ t2][x1 \ t1]). *)
(*             { pose proof (@subst_proper x1 t1). apply H10... *)
(*               pose proof (@subst_proper x2 t2). apply H11... } *)
(*             rewrite H10. apply H... *)
(*           - destruct H7 as []. *)
(*             assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ <! (false ∧ A) [x1 \ t1][x2 \ t2] !>). *)
(*             { pose proof (@subst_proper x2 t2). apply H9... *)
(*               pose proof (@subst_proper x1 t1). apply H10... } *)
(*             rewrite H9. *)
(*             assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ <! (false ∧ A) [x2 \ t2][x1 \ t1] !>). *)
(*             { pose proof (@subst_proper x1 t1). apply H10... *)
(*               pose proof (@subst_proper x2 t2). apply H11... } *)
(*   - *)
(*   - *)

Lemma fequiv_subst_commute : ∀ A x1 t1 x2 t2,
    x1 ≠ x2 →
    x1 ∉ term_fvars t2 →
    x2 ∉ term_fvars t1 →
    <! A[x1 \ t1][x2 \ t2] !> ≡ <! A[x2 \ t2][x1 \ t1] !>.
Proof with auto.
  induction A; intros.
  - unfold equiv. unfold fequiv. intros M σ b. split; inversion 1; subst;
      constructor; rewrite subst_sf_commute...
  - do 4 rewrite simpl_subst_not. rewrite IHA...
  - do 4 rewrite simpl_subst_and. rewrite IHA1... rewrite IHA2...
  - do 4 rewrite simpl_subst_or. rewrite IHA1... rewrite IHA2...
  - destruct (decide (x ∈ formula_fvars A)).
    2:{ destruct (fequiv_exists_non_free_binder x τ A)...
        - destruct H3 as []. rewrite H4. apply H...
        - destruct H3 as []. rewrite H4. do 4 rewrite simpl_subst_and.
          do 4 rewrite simpl_subst_sf... simpl. f_equiv. apply H... }
    remember (fresh_var x (formula_fvars A ∪ term_fvars t1 ∪
                                  term_fvars t2 ∪ {[x1]} ∪ {[x2]})) as x'.
    pose proof (fresh_var_fresh x (formula_fvars A ∪ term_fvars t1 ∪
                                       term_fvars t2 ∪ {[x1]} ∪ {[x2]})) as H'.
    rewrite <- Heqx' in H'. repeat rewrite not_elem_of_union in H'.
    repeat rewrite not_elem_of_singleton in H'. destruct H' as [[[[? ?] ?] ?] ?].
    rewrite (fequiv_exists_alpha_equiv x x' τ A H3).
    destruct (quant_subst_skip_cond x' (A [x \ x']) x1); destruct (quant_subst_skip_cond x' (A [x \ x']) x2).
    + do 4 (rewrite simpl_subst_exists_skip; auto).
    + rewrite simpl_subst_exists_skip... destruct H8; [symmetry in H8; contradiction|].
      rewrite fvars_subst_free in H8... apply not_elem_of_union in H8 as [].
      apply not_elem_of_difference in H8. rewrite elem_of_singleton in H8.
      rewrite simpl_subst_exists_propagate...
      assert (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x2 t2) = x').
      { destruct (decide (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x2 t2) = x'))...
        apply fresh_var_ne_inv in n. destruct n; contradiction. }
      rewrite H12. clear H12. rewrite simpl_subst_exists_skip...
      right. rewrite fvars_subst_free.
      * apply not_elem_of_union. split... apply not_elem_of_difference. left.
        assert (x1 ∉ formula_fvars <! A [x \ x'] !>).
        {
          rewrite fvars_subst_free... apply not_elem_of_union. split...
          apply not_elem_of_difference. rewrite elem_of_singleton... }
        rewrite fvars_subst_diag...
      * rewrite fvars_subst_diag...
    + destruct H10 as [H10 | H10]; [symmetry in H10; contradiction|].
      rewrite simpl_subst_exists_propagate...
      assert (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x1 t1) = x').
      { destruct (decide (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x1 t1) = x'))...
        apply fresh_var_ne_inv in n. destruct n; contradiction. }
      rewrite H11. rewrite simpl_subst_exists_skip...
      2:{
        right. rewrite fvars_subst_free...
        - apply not_elem_of_union. split... apply not_elem_of_difference. left.
          clear Heqx'. rewrite fvars_subst_diag...
        - rewrite fvars_subst_diag...
      }
      rewrite simpl_subst_exists_skip...
      rewrite simpl_subst_exists_propagate...
      rewrite H11...
    +
      rewrite simpl_subst_exists_propagate...
      assert (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x1 t1) = x').
      { destruct (decide (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x1 t1) = x'))...
        apply fresh_var_ne_inv in n. destruct n; contradiction. }
      rewrite H12.
      rewrite simpl_subst_exists_propagate...
      2:{ rewrite fvars_subst_free.
          - apply elem_of_union. left. apply elem_of_difference. rewrite not_elem_of_singleton.
            split... rewrite fvars_subst_diag...
          - rewrite fvars_subst_diag... }
      assert (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] [x' \ x'] [x1 \ t1] !> x2 t2) = x').
      { destruct (decide (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] [x' \ x'] [x1 \ t1] !> x2 t2) = x'))...
        apply fresh_var_ne_inv in n. destruct n; contradiction. }
      rewrite H13.
      rewrite simpl_subst_exists_propagate...
      assert (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x2 t2) = x').
      { destruct (decide (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] !> x2 t2) = x'))...
        apply fresh_var_ne_inv in n. destruct n; contradiction. }
      rewrite H14.
      rewrite simpl_subst_exists_propagate...
      2:{ rewrite fvars_subst_free.
          - apply elem_of_union. left. apply elem_of_difference. rewrite not_elem_of_singleton.
            split... rewrite fvars_subst_diag...
          - rewrite fvars_subst_diag... }
      assert (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] [x' \ x'] [x2 \ t2] !> x1 t1) = x').
      { destruct (decide (fresh_var x' (quant_subst_fvars x' <! A [x \ x'] [x' \ x'] [x2 \ t2] !> x1 t1) = x'))...
        apply fresh_var_ne_inv in n. destruct n; contradiction. }
      rewrite H15. clear H12 H13 H14 H15 Heqx'. intros M σ b. apply feval_exists_equiv.
      * intros. repeat rewrite fequiv_subst_diag. rewrite H...
      * intros. apply eq_iff_eq_true. split.
        -- intros. apply Is_true_true in H13. apply formula_wf_subst_term_wf in H13 as ?...
           2:{ rewrite fvars_subst_diag. rewrite fvars_subst_free.
               - apply elem_of_union. left. apply elem_of_difference. rewrite not_elem_of_singleton.
                 split... rewrite fvars_subst_diag...
               - rewrite fvars_subst_diag... }
           rewrite term_wf_delete_state_var_head in H14...
           apply term_wf_teval in H14 as [v2 ?]. apply teval_term_ty in H14.
           rewrite formula_wf_subst with (τ:=value_typeof v2) in H13.
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag in H13.
           apply formula_wf_subst_term_wf in H13 as ?...
           2:{ rewrite fvars_subst_diag... }
           do 2 rewrite term_wf_delete_state_var_head in H15...
           apply term_wf_teval in H15 as [v1 ?]. apply teval_term_ty in H15.
           rewrite formula_wf_subst with (τ:=value_typeof v1) in H13.
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head...
               rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag in H13.
           apply Is_true_true. rewrite formula_wf_subst with (τ:=value_typeof v1).
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag. rewrite formula_wf_subst with (τ:=value_typeof v2).
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head...
               rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag. rewrite (insert_commute (<[x':=τ]> (state_types σ)))...
        -- intros. apply Is_true_true in H13. apply formula_wf_subst_term_wf in H13 as ?...
           2:{ rewrite fvars_subst_diag. rewrite fvars_subst_free.
               - apply elem_of_union. left. apply elem_of_difference. rewrite not_elem_of_singleton.
                 split... rewrite fvars_subst_diag...
               - rewrite fvars_subst_diag... }
           rewrite term_wf_delete_state_var_head in H14...
           apply term_wf_teval in H14 as [v1 ?]. apply teval_term_ty in H14.
           rewrite formula_wf_subst with (τ:=value_typeof v1) in H13.
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag in H13.
           apply formula_wf_subst_term_wf in H13 as ?...
           2:{ rewrite fvars_subst_diag... }
           do 2 rewrite term_wf_delete_state_var_head in H15...
           apply term_wf_teval in H15 as [v2 ?]. apply teval_term_ty in H15.
           rewrite formula_wf_subst with (τ:=value_typeof v2) in H13.
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head...
               rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag in H13.
           apply Is_true_true. rewrite formula_wf_subst with (τ:=value_typeof v2).
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag. rewrite formula_wf_subst with (τ:=value_typeof v1).
           2:{ unfold term_has_type. rewrite term_ty_delete_state_var_head...
               rewrite term_ty_delete_state_var_head... }
           rewrite formula_wf_subst_diag. rewrite (insert_commute (<[x':=τ]> (state_types σ)))...
Qed.

(* Lemma fequiv_exists_subst_skip : ∀ y A x t, *)


(* Lemma subst_eq_congr : forall M σ φ x t u b, *)
(*   feval M σ <! t = u !> → *)
(*   feval M σ <! φ[x\t] !> b <→ *)
(*   feval M σ <! φ[x\u] !> b. *)
(* Proof with auto. *)

(* Lemma feval_eq_refl : forall t st, *)
(*   ~ feval M σ (F_Simple (φT_Pred "="%string [t; t])) false. *)
(* Proof with auto. *)
(*   intros t st contra. inversion contra; subst. *)
(*   inversion H0; subst. *)
(*   destruct (pctx_eq_semantics pctx) as [eq_pdef [Heqp1 Heqp2]]. *)
(*   rewrite Heqp1 in H2. inversion H2. subst pdef. *)
(*   destruct (Heqp2 st fctx) as [Heqp_refl _]. *)
(*   specialize (Heqp_refl t). *)
(*   assert (feval M σ fctx pctx <! t = t !> true). *)
(*   { apply FEval_Simple. apply SFEval_Pred with eq_pdef... *)
(*     destruct eq_pdef. *)
(*     apply Pred_Eval with n_params prel Hfnal... } *)
(*   destruct (feval_functional _ _ _ _ H contra). *)
(* Qed. *)
