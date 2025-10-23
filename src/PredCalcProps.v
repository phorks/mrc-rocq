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

Lemma fequiv_subst_diag A x :
  <! A[x \ x] !> ≡ A.
Proof with auto.
  generalize dependent A.
  apply subst_formula_ind with (P:=λ A B, A ≡ B); intros...
  - rewrite subst_sf_diag...
  - rewrite H. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - unfold y' in *. clear y'. generalize_fresh_var y A x x as y'.
    symmetry. rewrite fequiv_exists_alpha_equiv with (x':=y')...
    remember (A[y \ y']) as B. intros M σ b. apply feval_exists_equiv.
    + intros. symmetry. apply H... subst...
    + intros. symmetry. apply formula_wf_subst_diag...
Qed.

Lemma fequiv_subst_non_free A t x :
  x ∉ formula_fvars A →
  <! A [x \ t] !> ≡ <! A !>.
Proof with auto. intros H M σ b. rewrite subst_non_free... Qed.

(* (* TODO: move it  *) *)
Lemma subst_fvars_superset A x t : formula_fvars (A[x \ t]) ⊆ formula_fvars A ∪ term_fvars t.
Proof with auto.
  destruct (decide (x ∈ formula_fvars A)).
  - rewrite subst_free_fvars... apply union_mono_r. apply subseteq_difference_l...
  - rewrite subst_non_free_fvars... apply union_subseteq_l.
Qed.

Definition bool_to_term (b : bool) :=
 match b with
 | true => <! true !>
 | false => <! false !>
 end.

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
      * apply FEval_Exists_False; [eauto|].intros. apply feval_delete_state_var_head...
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

Lemma fequiv_subst_trans : ∀ A (x1 x2 x3 : variable),
    x2 ∉ formula_fvars A →
    <! A[x1 \ x2][x2 \ x3] !> ≡ <! A[x1 \ x3] !>.
Proof with auto.
  induction A; intros.
  - admit.
  - do 3 rewrite simpl_subst_not. rewrite IHA...
  - simpl in H. apply not_elem_of_union in H as []. do 3 rewrite simpl_subst_and.
    rewrite IHA1... rewrite IHA2...
  - simpl in H. apply not_elem_of_union in H as []. do 3 rewrite simpl_subst_or.
    rewrite IHA1... rewrite IHA2...
  - simpl in H0. apply not_elem_of_difference in H0. rewrite elem_of_singleton in H0.
    destruct (quant_subst_skip_cond x A x1); destruct (quant_subst_skip_cond x A x2).
    + do 4 (rewrite simpl_subst_exists_skip; auto).
    + simpl in H0. destruct H0; try contradiction. symmetry in H0. contradiction.
    + destruct (decide (x ∈ formula_fvars A)).
      2:{
        assert (x2 ∉ formula_fvars A). { destruct H0... subst... } clear H0 H3.
        destruct (fequiv_exists_non_free_binder x τ A)...
          - destruct H0 as [].
            assert (<! (exists x : τ, A) [x1 \ x2] [x2 \ x3] !> ≡ A[x1 \ x2][x2 \ x3]).
            { pose proof (@subst_proper x2 x3). apply H5...
              pose proof (@subst_proper x1 x2). apply H6... }
            rewrite H5.
            assert (<! (exists x : τ, A) [x1 \ x3] !> ≡ A[x1 \ x3]).
            { pose proof (@subst_proper x1 x3). apply H6... }
            rewrite H6. apply H...
          - destruct H0 as [].
            assert (<! (exists x : τ, A) [x1 \ x2] [x2 \ x3] !> ≡ <! (false ∧ A) [x1 \ x2][x2 \ x3] !>).
            { pose proof (@subst_proper x2 x3). apply H5...
              pose proof (@subst_proper x1 x2). apply H6... }
            rewrite H5.
            assert (<! (exists x : τ, A) [x1 \ x3] !> ≡ <! (false ∧ A) [x1 \ x3] !>).
            { pose proof (@subst_proper x1 x3). apply H6... }
            rewrite H6. do 3 rewrite simpl_subst_and. do 3 rewrite simpl_subst_sf. simpl.
            f_equiv. apply H... }
      clear H3. rewrite simpl_subst_exists_propagate...
      generalize_fresh_var x A x1 x2 as x'.
      simpl in H6. rewrite not_elem_of_singleton in H6.
      rewrite simpl_subst_exists_propagate...
      2:{ rewrite subst_free_fvars; [| rewrite subst_free_fvars; auto]; set_solver. }
      generalize_fresh_var x' <! A [x \ x'] [x1 \ x2] !> x2 x3 as y1.
      rewrite simpl_subst_exists_propagate...
      generalize_fresh_var x A x1 x3 as y2.

      simpl in H7.

      symmetry.

      rewrite simpl_subst_exists_propagate; auto...
      rewrite simpl_subst_exists_skip...
      generalize_fresh_var x A x2 x3 as x'. symmetry.
      destruct (quant_subst_skip_cond x' (A [x \ x'][x2 \ x3]) x1).
      * rewrite simpl_subst_exists_skip...
      * exfalso. destruct H3.
        -- subst x1.
           pose proof (fresh_var_fresh x (quant_subst_fvars A x2 t2)).
           apply quant_subst_fvars_inv in H3 as (?&?&?).
           assert (x ∈ formula_fvars A).
           { destruct (decide (x ∈ formula_fvars A))... exfalso.
             pose proof (fresh_var_free x (quant_subst_fvars A x2 t2)).
             forward H10; try contradiction. set_solver. }
           rewrite subst_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7.
              apply elem_of_union in H7. rewrite elem_of_difference in H7.
              rewrite not_elem_of_singleton in H7. destruct H7 as [[? []]|]...
              rewrite elem_of_singleton in H7. exfalso. apply H6...
           ++ rewrite subst_free_fvars... rewrite elem_of_union.
              left. rewrite elem_of_difference. rewrite elem_of_singleton. split...
        -- apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction.
           apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction.
           simpl in H7. rewrite elem_of_singleton in H7. apply H6. symmetry...
    + admit.
    + destruct (decide (x ∈ formula_fvars A)).
      2:{ destruct (fequiv_exists_non_free_binder x τ A)...
          - destruct H7 as [].
            assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ A[x1 \ t1][x2 \ t2]).
            { pose proof (@subst_proper x2 t2). apply H9...
              pose proof (@subst_proper x1 t1). apply H10... }
            rewrite H9.
            assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ A[x2 \ t2][x1 \ t1]).
            { pose proof (@subst_proper x1 t1). apply H10...
              pose proof (@subst_proper x2 t2). apply H11... }
            rewrite H10. apply H...
          - destruct H7 as [].
            assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ <! (false ∧ A) [x1 \ t1][x2 \ t2] !>).
            { pose proof (@subst_proper x2 t2). apply H9...
              pose proof (@subst_proper x1 t1). apply H10... }
            rewrite H9.
            assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ <! (false ∧ A) [x2 \ t2][x1 \ t1] !>).
            { pose proof (@subst_proper x1 t1). apply H10...
              pose proof (@subst_proper x2 t2). apply H11... }
  -
  -

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
  - destruct (quant_subst_skip_cond x A x1); destruct (quant_subst_skip_cond x A x2).
    + do 4 (rewrite simpl_subst_exists_skip; auto).
    + rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_propagate; auto...
      destruct (quant_subst_skip_cond (fresh_var x (quant_subst_fvars A x2 t2))
                  (A [x \ fresh_var x (quant_subst_fvars A x2 t2)][x2 \ t2]) x1).
      * rewrite simpl_subst_exists_skip...
      * exfalso. destruct H3.
        -- subst x1.
           pose proof (fresh_var_fresh x (quant_subst_fvars A x2 t2)).
           apply quant_subst_fvars_inv in H3 as (?&?&?).
           assert (x ∈ formula_fvars A).
           { destruct (decide (x ∈ formula_fvars A))... exfalso.
             pose proof (fresh_var_free x (quant_subst_fvars A x2 t2)).
             forward H10; try contradiction. set_solver. }
           rewrite subst_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7.
              apply elem_of_union in H7. rewrite elem_of_difference in H7.
              rewrite not_elem_of_singleton in H7. destruct H7 as [[? []]|]...
              rewrite elem_of_singleton in H7. exfalso. apply H6...
           ++ rewrite subst_free_fvars... rewrite elem_of_union.
              left. rewrite elem_of_difference. rewrite elem_of_singleton. split...
        -- apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction.
           apply subst_fvars_superset in H7. apply elem_of_union in H7 as [|]; try contradiction.
           simpl in H7. rewrite elem_of_singleton in H7. apply H6. symmetry...
    + admit.
    + destruct (decide (x ∈ formula_fvars A)).
      2:{ destruct (fequiv_exists_non_free_binder x τ A)...
          - destruct H7 as [].
            assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ A[x1 \ t1][x2 \ t2]).
            { pose proof (@subst_proper x2 t2). apply H9...
              pose proof (@subst_proper x1 t1). apply H10... }
            rewrite H9.
            assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ A[x2 \ t2][x1 \ t1]).
            { pose proof (@subst_proper x1 t1). apply H10...
              pose proof (@subst_proper x2 t2). apply H11... }
            rewrite H10. apply H...
          - destruct H7 as [].
            assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ <! (false ∧ A) [x1 \ t1][x2 \ t2] !>).
            { pose proof (@subst_proper x2 t2). apply H9...
              pose proof (@subst_proper x1 t1). apply H10... }
            rewrite H9.
            assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ <! (false ∧ A) [x2 \ t2][x1 \ t1] !>).
            { pose proof (@subst_proper x1 t1). apply H10...
              pose proof (@subst_proper x2 t2). apply H11... }
            rewrite H10. do 4 rewrite simpl_subst_and. do 4 rewrite simpl_subst_sf...
            simpl. f_equiv. apply H... }
      rewrite simpl_subst_exists_propagate... rewrite (simpl_subst_exists_propagate) with (A:=A)...
      rewrite simpl_subst_exists_propagate.
      * rewrite (simpl_subst_exists_propagate).
        -- generalize_fresh_var x A x1 t1 as y1'.
           generalize_fresh_var y1' (A [x \ y1'] [x1 \ t1]) x2 t2 as y1.
           generalize_fresh_var x A x2 t2 as y2'.
           generalize_fresh_var y2' (A [x \ y2'] [x2 \ t2]) x1 t1 as y2.
           rewrite fequiv_exists_alpha_equiv with (x':=y2).
           2:{ rewrite subst_non_free
             rewrite subst_non_free_fvars.
               - rewrite subst_free_fvars.
                 + rewrite subst_free_fvars.
                   * rewrite subst_free_fvars.
                     --
           f_equiv.
           remember (fresh_var x (formula_fvars A ∪ term_fvars t1 ∪
                                    term_fvars t2 ∪ {[x1; x2; y1'; y1; y2'; y2]})) as x'.

           etrans.
           ++ rewrite fequiv_exists_alpha_equiv with (x':=x'); [reflexivity|].
              admit.
          ++
              rewrite subst_free_fvars. rewrite subst_free_fvars. rewrite subst_free_fvars.
              rewrite subst_free_fvars.
              pose proof (fresh_var_fresh x (formula_fvars A ∪ term_fvars t1 ∪
                                    term_fvars t2 ∪ {[x1; x2; y1'; y1; y2'; y2]})) as H'.
              rewrite <- Heqx' in H'. set_solver.
              pose proof (fresh_var )
                     +++

                apply subst_fvars_superset. )
           }
           rewrite subst_free_fvars in H9...
           2: {  rewrite subst_free_fvars... }






          simpl. etrans.
           ++ rewrite fequiv_exists_alpha_equiv.
           pose proof (subst_fvars_superset )

          eapply elem_of_weaken in H7.
           2: {  }

      remember (fresh_var x (formula_fvars A ∪ term_fvars t1 ∪
                                  term_fvars t2 ∪ {[x1]} ∪ {[x2]})) as x'.
      pose proof (fresh_var_fresh x (formula_fvars A ∪ term_fvars t1 ∪
                                       term_fvars t2 ∪ {[x1]} ∪ {[x2]})) as H'.
      rewrite <- Heqx' in H'. apply not_elem_of_union in H' as [].
      apply not_elem_of_union in H7 as []. apply not_elem_of_union in H7 as [].
      apply not_elem_of_union in H7 as []. clear Heqx'. apply not_elem_of_singleton in H9, H8.
      assert (<! (exists x : τ, A) [x1 \ t1] [x2 \ t2] !> ≡ <! (exists x' : τ, A[x \ x']) [x1 \ t1] [x2 \ t2] !>).
      { pose proof (@subst_proper x2 t2). apply H12...
        pose proof (@subst_proper x1 t1). apply H13.
        apply fequiv_exists_alpha_equiv...}
      assert (<! (exists x : τ, A) [x2 \ t2] [x1 \ t1] !> ≡ <! (exists x' : τ, A[x \ x']) [x2 \ t2] [x1 \ t1] !>).
      { pose proof (@subst_proper x1 t1). apply H13...
        pose proof (@subst_proper x2 t2). apply H14.
        apply fequiv_exists_alpha_equiv...}
      rewrite H12. rewrite H13. clear H12 H13.
      rewrite simpl_subst_exists_propagate...
      2:{ rewrite subst_free_fvars... simpl. set_solver. }
      assert (fresh_var x' (quant_subst_fvars <! A [x \ x'] !> x1 t1) = x') as ->.
      { apply fresh_var_free. unfold quant_subst_fvars. rewrite subst_free_fvars...
        simpl. repeat rewrite not_elem_of_union. repeat rewrite not_elem_of_singleton.

      }

      pose proof (fresh_var_free
      rewrite H9.
      etrans.
      * <! (∃ x : τ ● A) [x1 \ t1] [x2 \ t2] !> ≡ ?y
        pose proof (@subst_proepr)

        rewrite fequiv_exists_alpha_equiv.
      rewrite simpl_subst_exists_propagate... rewrite (simpl_subst_exists_propagate) with (A:=A)...
      rewrite simpl_subst_exists_propagate.
      * rewrite (simpl_subst_exists_propagate).
        -- generalize_fresh_var x A x1 t1 as y1'.
           generalize_fresh_var y1' (A [x \ y1'] [x1 \ t1]) x2 t2 as y1.
           generalize_fresh_var x A x2 t2 as y2'.
           generalize_fresh_var y2' (A [x \ y2'] [x2 \ t2]) x1 t1 as y2.
           rewrite fequiv_exists_alpha_equiv with (x':=y2).
           2:{ rewrite subst_non_free
             rewrite subst_non_free_fvars.
               - rewrite subst_free_fvars.
                 + rewrite subst_free_fvars.
                   * rewrite subst_free_fvars.
                     --
           f_equiv.
           remember (fresh_var x (formula_fvars A ∪ term_fvars t1 ∪
                                    term_fvars t2 ∪ {[x1; x2; y1'; y1; y2'; y2]})) as x'.

           etrans.
           ++ rewrite fequiv_exists_alpha_equiv with (x':=x'); [reflexivity|].
              admit.
          ++
              rewrite subst_free_fvars. rewrite subst_free_fvars. rewrite subst_free_fvars.
              rewrite subst_free_fvars.
              pose proof (fresh_var_fresh x (formula_fvars A ∪ term_fvars t1 ∪
                                    term_fvars t2 ∪ {[x1; x2; y1'; y1; y2'; y2]})) as H'.
              rewrite <- Heqx' in H'. set_solver.
              pose proof (fresh_var )
                     +++

                apply subst_fvars_superset. )
           }
           rewrite subst_free_fvars in H9...
           2: {  rewrite subst_free_fvars... }






          simpl. etrans.
           ++ rewrite fequiv_exists_alpha_equiv.
           pose proof (subst_fvars_superset )

          eapply elem_of_weaken in H7.
           2: {  }





          rewrite subst_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7.
              apply elem_of_union in H7. rewrite elem_of_difference in H7.
              rewrite not_elem_of_singleton in H7. destruct H7 as [[? []]|]...
              rewrite elem_of_singleton in H7. exfalso. apply H6...
           ++ rewrite subst_free_fvars... rewrite elem_of_union.
              left. rewrite elem_of_difference. rewrite elem_of_singleton. split...

              apply not_elem_of_union.
              rewrite elem_of_difference. rewrite elem_of_singleton.
              split...
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
           rewrite subst_non_free_fvars in H7.
           ++ rewrite subst_free_fvars in H7... apply elem_of_union in H7.
              rewrite elem_of_difference in H7. rewrite not_elem_of_singleton in H7.
              destruct H7 as [[? []]|]... simpl in H7. apply elem_of_singleton in H7...
           ++ rewrite subst_free_fvars... apply not_elem_of_union.
              rewrite elem_of_difference. rewrite elem_of_singleton.
              split...
              ** intros contra.
              ** rewrite subst_free_fvars in H7... apply elem_of_union in H7.
                 rewrite elem_of_difference in H7. rewrite elem_of_singleton in H7.
                 destruct H7 as [[? []]|]... simpl in H3. apply elem_of_singleton in H3...
              **
           ++ destruct (decide (x ∈ formula_fvars A)).
              ** rewrite subst_free_fvars... apply not_elem_of_union.
                 rewrite elem_of_difference. rewrite elem_of_singleton.
                 split.
                 --- intros [? ?].
                 destruct H7 as [[? []]|]... simpl in H3. apply elem_of_singleton in H3...
              ** rewrite subst_non_free_fvars in H7...
           pose proof (subst_fvars (A [x \ (fresh_var x (quant_subst_fvars A x2 t2))]) x2 t2).
           destruct H3 as [[? ?] | [? ?]].
           ++ rewrite H8 in *. clear H8. admit.
           ++
        -- apply H3. rewrite subst_fvars
      intros M σ. simpl.


      rewrite (simpl_subst_exists_skip)... destruct H3.
      * subst.

      simpl.
      rewrite simpl_subst_exists_propagate; auto...
      do 2 (rewrite simpl_subst_exists_propagate; auto)...

      rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_skip...
      rewrite simpl_subst_exists_skip... rewrite simpl_subst_exists_skip...
Admitted.


Lemma fequiv_exists_subst_skip : ∀ y A x t,


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
