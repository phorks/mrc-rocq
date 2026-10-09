From Stdlib Require Import Reals ZArith Sorting Lra.
From stdpp Require Import listset vector.
From Equations Require Import Equations.
From MRC Require Import Prog Refinement.
From MRC Require Import SeqNotation.
From MRC Require Import Model.
From MRC.Examples Require Import Model Variables.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Notation Prog := (prog Model).
Notation Term := (term Model).
Notation Formula := (formula Model).

(* Definition final_var_to_term (x : Model.final_variable) : Term := TVar (Model.as_var x). *)
(* Coercion final_var_to_term : Model.final_variable >-> Term. *)
Definition I : Formula := <! ⌜q ∈ₜ ℕ⌝ ∧ ⌜r ∈ₜ ℕ⌝ ∧ ⌜r² ≤ s < q²⌝ !>.
Program Definition V : final_term Model := {| as_term := term_sub q r |}.
Next Obligation. unfold term_final. set_solver. Qed.
Definition I1 := <! ⌜q ∈ₜ ℕ⌝ ∧ ⌜r ∈ₜ ℕ⌝ !>.
Definition I2 : Formula := <! ⌜r² ≤ s < q²⌝ !>.
Lemma split_I : I ≡ <! I1 ∧ I2  !>.
Proof. unfold I, I1, I2. by rewrite f_and_assoc. Qed.

Definition spec : Prog := <{ |[ var r s : ℕ ⦁ r := ⌊√ s⌋ ]| }>.
Definition prog1 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r = ⌊√ s⌋⌝] ]| }>.
Definition prog2 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r ≤ √ s < r + 1⌝] ]| }>.
Definition prog3 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r² ≤ s < (r + 1)²⌝] ]| }>.
Definition prog4 : Prog :=
  <{ |[ var r s q : ℕ ⦁
                      q, r : [I ∧ ⌜r+1 = q⌝] ]| }>.
Definition prog5 : Prog :=
  <{ |[ var r s q : ℕ ⦁
                      q, r : [I];
                      q, r : [I, I ∧ ⌜r+1 = q⌝] ]| }>.
Definition prog6 : Prog :=
  <{ |[ var r s q : ℕ ⦁
                      q, r := s + 1, 0;
                      q, r : [I, I ∧ ⌜r+1 = q⌝] ]| }>.

Definition prog7 : Prog :=
  <{ |[ var r s q : ℕ ⦁
          q, r := s + 1, 0;
          while ⌜r + 1 ≠ q⌝ invariant I variant V ⟶
            q, r : [⌜r + 1 ≠ q⌝ ∧ I, I ∧ ⌜0 ≤ q - r < ₀q - ₀r⌝]
          end
        ]| }>.

Definition prog8 : Prog :=
  <{ |[ var r s q : ℕ ⦁
          q, r := s + 1, 0;
          while ⌜r + 1 ≠ q⌝ invariant I variant V ⟶
            |[
              var p : ℕ ⦁
              p : [⌜r + 1 < q⌝ ∧ I1, ⌜p ∈ₜ ℕ⌝ ∧ ⌜r < p < q⌝ ∧ I1];
              q, r : [⌜p ∈ₜ ℕ⌝ ∧ ⌜r < p < q⌝ ∧ I, I ∧ ⌜0 ≤ q - r < ₀q - ₀r⌝]
            ]|
          end
        ]| }>.

Definition prog9 : Prog :=
  <{ |[ var r s q : ℕ ⦁
          q, r := s + 1, 0;
          while ⌜r + 1 ≠ q⌝ invariant I variant V ⟶
            |[
              var p : ℕ ⦁
              p := (q - 1);
              if ⌜s < p²⌝ → q : [⌜s < p²⌝ ∧ ⌜p ∈ₜ ℕ⌝ ∧ ⌜p < q⌝ ∧ I, I ∧ ⌜q < ₀q⌝ ]
              |  ⌜s ≥ p²⌝ → r : [⌜s ≥ p²⌝ ∧ ⌜p ∈ₜ ℕ⌝ ∧ ⌜r < p⌝ ∧ I, I ∧ ⌜₀r < r⌝ ]
              fi
            ]|
          end
        ]| }>.

Definition code : Prog :=
  <{ |[ var r s q : ℕ ⦁
          q, r := s + 1, 0;
          while ⌜r + 1 ≠ q⌝ invariant I variant V ⟶
            |[
              var p : ℕ ⦁
              p := (q - 1);
              if ⌜s < p²⌝ → q := p
              |  ⌜s ≥ p²⌝ → r := p
              fi
            ]|
          end
        ]| }>.


Lemma r1 : spec ≡ prog1.
Proof with auto.
  unfold spec, prog1. rewrite r_simple_spec by set_solver.
  do 2 rewrite r_var_comm. f_equiv. intros A.
  mk_fresh (
      {[as_var s]}
        ∪ prog_fvars <{ r : [⌜ r = ⌊ √ s ⌋ ⌝] }>
        ∪ prog_fvars <{ r : [⌜ r ∈ₜ ℕ ⌝ ∧ ⌜ r = ⌊ √ s ⌋ ⌝] }>
        ∪ formula_fvars A) as x.
  rewrite wp_var by naive_solver. rewrite wp_var by naive_solver. clear H.
  f_equiv. apply f_forall_ty_equiv. intros σ H. apply wp_proper_fequiv_st...
  simpl. f_equiv. unfold subst_all_initials. rewrite finalized_initial_fvars_final...
  rewrite finalized_initial_fvars_final... do 2 rewrite subst_initials_nil.
  eapply f_forall_proper_st. intros t. pose proof (teval_total σ t) as (v&?).
  repeat rewrite simpl_subst_impl. rewrite simpl_subst_and. repeat rewrite simpl_subst_af.
  simpl. unfold fequiv_st. setoid_rewrite simpl_feval_impl. rewrite simpl_feval_and.
  split; intros.
  - destruct H2. apply H1...
  - apply H1. clear H1. split... simp feval in H2. simpl in H2. destruct H2 as (vt&?&?).
    inversion H2. clear H2. subst. inversion H5. subst. clear H5. inversion H8. subst.
    clear H8. inversion H7; clear H7.
    + subst. unfold fdef_rel in H2. simpl in H2. inversion H2. subst. clear H2. simp feval.
      simpl. inversion H4. subst. clear H4. inversion H6. subst. clear H6. inversion H9.
      subst. clear H9. inversion H8. subst. clear H8. unfold fdef_rel in H2. simpl in H2.
      inversion H2. subst. clear H2. simp feval in H. simpl in H. destruct H as (vs&?&?).
      apply teval_det with (v1:=(mkNum (r ^ 2))) in H... subst vs.
      inversion H2. subst. assert (INR (Z.to_nat i) = IZR i)%R.
      { destruct H5. apply Rle_lt_trans with (r1:=(0)%R) in H5...
        rewrite <- plus_IZR in H5. apply lt_0_IZR in H5.
        assert (0 <= i)%Z by lia. apply Z2Nat.id in H6.
        rewrite <- H6. rewrite <- INR_IZR_INZ. f_equal. lia. }
      exists (mkNat (Z.to_nat i)). split.
      * rewrite H...
      * eapply IsNat. reflexivity.
    + exfalso. destruct H as (sv&?&?). subst. inversion H6. subst. clear H6.
      inversion H4. clear H4. subst. inversion H6. subst. clear H6.
      inversion H9; subst; clear H9. inversion H8; subst; clear H8.
      * unfold fdef_rel in H3. simpl in H3. inversion H3; subst; clear H3.
        apply teval_det with (v1:=(mkNum (r ^ 2))) in H...
        apply mkNum_eq in H. eapply (H2 (mkInt (Zfloor r))). unfold fdef_rel. simpl.
        constructor. apply Zfloor_bound.
      * apply teval_det with (v1:=v1) in H... subst v1. apply (H3 (mkNum (sqrt (INR n)))).
        unfold fdef_rel. simpl. constructor.
        -- apply sqrt_pos.
        -- rewrite pow2_sqrt...
Qed.

Lemma r2 : prog1 ⊑ prog2.
Proof with auto.
  unfold prog1, prog2. do 2 f_equiv. apply r_strengthen_post...
  intros σ. repeat rewrite simpl_feval_and. simp feval. simpl. intros [].
  split... destruct H as (rv&?&?). inversion H1. subst. destruct H0.
  apply term_le_inv in H0. apply term_lt_inv in H2. destruct H0 as (?&?&?&?&?).
  apply teval_det with (v2:=mkNat n) in H0... apply mkNum_eq in H0. subst.
  destruct H2 as (sqv&?&?&?&?). apply teval_det with (v2:=mkNum sqv) in H3...
  apply mkNum_eq in H3. subst x0. apply term_sqrt_inv in H0.
  destruct H0 as (?&?&?). subst. apply term_sum_inv in H2 as (?&?&?&?&?).
  inversion H3. subst. clear H3. rename x0 into vr. exists (mkNum vr).
  split... apply TEval_App with (vargs:=[mkNum sqv]).
  - by_constructor. apply TEval_App with (vargs:=[mkNum (sqv ^ 2)%R]).
    + by_constructor.
    + constructor. unfold fdef_rel. simpl. apply FSqrt_R...
      pose proof (pos_INR n). apply Rle_trans with (r3:=sqv) in H3...
  - by_constructor. unfold fdef_rel. simpl. apply teval_det with (v2:=mkNum vr) in H...
    apply mkNum_eq in H. subst. rewrite INR_IZR_INZ. constructor.
    rewrite <- INR_IZR_INZ...
Qed.

Lemma r3 : prog2 ⊑ prog3.
Proof with auto.
  unfold prog2, prog3. do 2 f_equiv. apply r_strengthen_post... intros σ.
  repeat rewrite simpl_feval_and. simpl. intros (?&?&?). split...
  apply term_le_inv in H0 as (vr2&vs&?&?&?).
  apply term_pow2_inv in H0 as (vr&?&?). subst.
  apply term_lt_inv in H1 as (vs'&?&?&?&?).
  apply term_pow2_inv in H4 as (?&?&?). subst.
  apply term_sum_inv in H4 as (vr'&?&?&?&?). subst.
  inversion H6. clear H6. subst.
  apply teval_det with (v2:=mkNum vr) in H4... apply mkNum_eq in H4. subst vr'.
  apply teval_det with (v2:=mkNum vs') in H2... apply mkNum_eq in H2. subst vs'.
  assert (0 <= vr^2)%R as E1 by apply pow2_ge_0. apply Rle_trans with (r3:=vs) in E1...
  destruct H as (vr'&?&?). eapply teval_det with (v2:=mkNum vr) in H... subst vr'.
  inversion H2. subst. rename n into nr. assert (0 <= INR nr)%R by apply pos_INR.
  split.
  - exists [mkNat nr; mkNum (sqrt vs)]. split.
    + by_constructor. apply TEval_App with (vargs:=[mkNum vs]).
      * by_constructor.
      * by_constructor. apply pow2_sqrt...
    + apply sqrt_le_1_alt in H3. rewrite sqrt_pow2 in H3...
      unfold peval. intros. rewrite list_to_vec_2_canon. constructor...
  - exists [mkNum (sqrt vs); mkNum (INR nr+1)]. split.
    + by_constructor.
      * apply TEval_App with (vargs:=[mkNum vs]).
        -- by_constructor.
        -- by_constructor. rewrite pow2_sqrt...
      * apply TEval_App with (vargs:=[mkNat nr; mkNum 1]); by_constructor.
    + apply sqrt_lt_1 in H5...
      2:{ apply pow2_ge_0. }
      rewrite sqrt_pow2 in H5 by lra.
      unfold peval. intros. rewrite list_to_vec_2_canon. constructor...
Qed.

Lemma r4 : prog3 ⊑ prog4.
Proof with auto.
  unfold prog3, prog4, I.
  do 2 f_equiv. etrans.
  { apply @r_var_intro with (x:=q) (ty:=ℕ); set_solver. }.
  f_equiv. apply r_strengthen_post... intros σ.
  repeat rewrite simpl_feval_and. simpl. intros. destruct_and! H. split_and... split...
  revert H4. unfold term_lt. apply fequiv_tequiv in H1. unfold term_pow2.
  eapply ATPred_proper_st... f_equiv. f_equiv. rewrite <- H1... reflexivity.
Qed.

Lemma r5 : prog4 ⊑ prog5.
Proof with auto.
  unfold prog4, prog5. repeat (apply p_var_proper_ref; auto). apply r_seq...
Qed.

Lemma r6 : prog5 ⊑ prog6.
Proof with auto.
  unfold prog5, prog6.
  rewrite (r_var_comm s q). rewrite (r_var_comm s q).
  rewrite r_var_spec... rewrite r_asgn_2...
  unfold I. intros σ. intros. rewrite msubst_extract_2...
  2:{ simpl; done. }
  simpl. repeat rewrite simpl_subst_and. unfold term_le. unfold term_lt.
  repeat rewrite simpl_subst_af. simpl. simp feval in H. destruct_and! H.
  simp feval. assert (Hs:=H1). simpl in Hs. destruct Hs as (vs&Hs&Hs').
  inversion Hs'. subst. rename n into ns.
  split_and!...
  - simpl. exists (mkNum (INR ns + 1)). split.
    + apply TEval_App with (vargs:=[mkNat ns; mkInt 1]).
      * by_constructor.
      * constructor. simpl. constructor.
    + apply IsNat with (n:=ns + 1). simpl. rewrite plus_INR. done.
  - simpl. exists (mkInt 0). split... apply IsNat with (n:=0). done.
  - simpl. simpl in H1. destruct H1 as (sv&?&?). inversion H2. subst. exists [mkInt 0; mkNat n].
    split.
    + by_constructor. apply TEval_App with (vargs:=[mkInt 0; mkNat 2]).
      * by_constructor.
      * simpl. unfold fn_eval. simpl. constructor.
        replace (mkNum (1 + 1)) with (mkNat 2) by done.
        replace (mkInt 0) with (mkNum (pow 0 2)) at 2.
        2:{ rewrite pow_i... }
        constructor.
    + unfold peval. intros. rewrite list_to_vec_2_canon. constructor. done.
  - simpl. exists [mkNat ns; mkNum (pow (INR ns + 1) 2)]. split.
    + by_constructor. apply TEval_App with (vargs:=[mkNat (ns + 1); mkNat 2]).
      * by_constructor. apply TEval_App with (vargs:=[mkNat ns; mkNat 1]).
        -- by_constructor.
        -- unfold fn_eval. constructor. simpl.
           enough (mkNat (ns + 1) = mkNum (INR ns + 1)) as -> by constructor.
           rewrite plus_INR. done.
      * unfold fn_eval. constructor. rewrite plus_INR. constructor.
    + unfold peval. intros. rewrite list_to_vec_2_canon. constructor.
      assert (((INR ns  + 1) ^ 2)%R = INR ((ns + 1) ^ 2)).
      { rewrite pow_INR. rewrite plus_INR. done. }
      rewrite H4. apply lt_INR. clear H2 H4 Hs Hs' H1 H3 H H0 σ.
      induction ns; simpl; lia.
Qed.

Lemma r7 : prog6 ⊑ prog7.
Proof with auto.
  unfold prog6, prog7. repeat f_equiv. simpl.
  opose proof (r_iteration' [q; r] <!! ⌜r+1 ≠ q⌝ !!> (as_final_formula I)
                <!! I !!>
                <!! I ∧ ⌜r + 1 = q⌝ !!>
                V).
  simpl in H.
  etrans.
  - simpl. apply H...
    + by_constructor; try set_solver.
    + simpl. fSimpl.
  - unfold to_vtmap. simpl. rewrite fin_maps.lookup_insert.
    rewrite fin_maps.insert_commute... rewrite fin_maps.lookup_insert. simpl.
    apply pequiv_refines. apply PWhile_equiv...
    clear H. f_equiv.
      * unfold equiv, ffequiv. simpl. fSimpl.
      * simpl. unfold term_sub at 5.
        intros σ. unfold I. simp feval. split; intros; destruct_and! H; split_and!...
        clear H2 H4 H5. inversion H3. clear H3. destruct H1 as [].
        inversion H1. clear H1. subst. inversion H7. subst. clear H7. inversion H8. clear H8.
        subst. inversion H5. subst. clear H5. unfold term_sub in *. unfold sub_sym in *.
        simpl. exists v0. split... inversion H4. subst. unfold fn_eval in H7. inversion H7.
        -- subst v0 args. inversion H5. subst; clear H5. inversion H10; subst; clear H10.
           inversion H11; subst; clear H11. simpl in H1. inversion H1. subst.
           rename r7 into vq, r8 into vr. clear H7 H1 H4. simpl in H2. unfold peval in H2.
           simpl in H2. specialize (H2 eq_refl). rewrite list_to_vec_2_canon in H2.
           inversion H2. subst.
           simpl in H, H0. destruct H as (vq'&?&?). destruct H0 as (vr'&?&?).
           rewrite (teval_det _ _ _ H H8) in *.
           rewrite (teval_det _ _ _ H0 H6) in *.
           inversion H1. subst. rename n into nq.
           inversion H4. subst. rename n into nr.
           rewrite <- minus_INR.
           ++ apply IsNat with (nq - nr)...
           ++ rewrite Rle_0_minus in H3. apply INR_le...
        -- subst. clear H0 H4 H5 H7 H1. unfold peval in H2. simpl in H2.
           specialize (H2 eq_refl). rewrite list_to_vec_2_canon in H2. inversion H2.
Qed.

Lemma r8 : prog7 ⊑ prog8.
Proof with auto.
  unfold prog7, prog8. do 4 f_equiv. apply r_while_body.
  1: unfold modified_vars; set_solver.
  etrans.
  1:{ intros A. apply @r_var_intro with (x:=p) (ty:=ℕ); try set_solver.
    unfold I. apply initials_closed_alt'. set_solver. }
  etrans.
  - apply p_var_proper_ref. 1-2: reflexivity.
    rewrite r_permute_frame with (w':=[q; r] ++ [p]).
    2:{ apply initials_closed_alt'. set_solver. }
    2:{ simpl. apply perm_trans with (l':=[q; p; r]).
        - apply perm_swap.
        - apply perm_skip. apply perm_swap. }
    apply r_seq_frame with (mid:=<!! ⌜p ∈ₜ ℕ⌝ ∧ ⌜r < p < q⌝ ∧ I !!>).
    1-2: apply initials_closed_alt'; set_solver.
    + simpl. set_unfold. intros. destruct H0... destruct H; subst.
      * unfold p in *. unfold q in *. inversion H0.
      * destruct H... inversion H.
    + simpl. set_solver.
  - apply p_var_proper_ref... apply p_seq_proper_ref.
    2:{
      etrans.
      1:{ apply r_contract_frame; [apply initials_closed_alt'|]; set_solver. }
      rewrite f_subst_initials_no_initials by set_solver.
      simpl. reflexivity.
    }
    etrans.
    1:{ apply r_weaken_pre with (pre':=<! (⌜r + 1 < q⌝ ∧ I1)  ∧ I2 !>). unfold I, I1, I2.
        intros σ. intros. simp feval in *. destruct_and! H. split_and!...
        destruct H as (vq&?&?). destruct H1 as (vr&?&?). inversion H3. rename n into nq.
        clear H3. subst. inversion H5. rename n into nr. clear H5. subst.
        destruct (lt_eq_lt_dec (nr + 1) nq); [destruct s|].
        - unfold term_lt. simpl. simp feval. simpl. exists [mkNat (nr + 1); mkNat nq].
          split.
          + by_constructor... unfold term_sum.
            apply TEval_App with (vargs:=[mkNat nr; mkNat 1]).
              -- by_constructor.
              -- unfold fn_eval. constructor. simpl. apply fsum_iff. rewrite plus_INR...
          + unfold peval. simpl. intros. rewrite list_to_vec_2_canon. constructor.
            apply lt_INR...
        - exfalso. apply H0. simpl. exists (mkNat nq). split... subst nq.
          unfold term_sum. apply TEval_App with (vargs:=[mkNat nr; mkNat 1]).
          + by_constructor.
          + unfold fn_eval. constructor. simpl. apply fsum_iff. rewrite plus_INR...
        - exfalso. apply term_le_inv in H2 as (vr2&vs&?&?&?).
          apply term_lt_inv in H4 as (vs'&vq2&?&?&?).
          pose proof (teval_det _ _ _ H3 H4). apply mkNum_eq in H8. subst vs'.
          apply term_pow2_inv in H2. destruct H2 as (?&?&?).
          pose proof (teval_det _ _ _ H1 H2). apply mkNum_eq in H9. subst x vr2.
          apply term_pow2_inv in H6. destruct H6 as (?&?&?).
          pose proof (teval_det _ _ _ H H6). apply mkNum_eq in H9. subst x vq2.
          clear H2 H4 H6. assert (INR nr ^ 2 < INR nq ^ 2)%R.
          + apply Rle_lt_trans with (r2:=vs)...
          + apply pow2_lt in H2... apply INR_lt in H2. lia. }
      simpl.
      etrans.
      1:{ apply r_strengthen_post with (post':= <! I2 ∧ ⌜p ∈ₜ ℕ⌝ ∧ ⌜r < p < q⌝ ∧ I1 !>).
          1-2: apply initials_closed_alt'; set_solver.
          unfold I, I1, I2. intros σ. simp feval. intros. destruct_and! H. split_and!... }
      apply r_remove_inv.
      * unfold I. set_solver.
      * constructor.
        -- set_solver.
        -- constructor.
Qed.

Lemma r9 : prog8 ⊑ prog9.
Proof with auto.
  unfold prog8, prog9. repeat apply p_var_proper_ref... f_equiv. apply r_while_body.
  { simpl. unfold modified_vars. simpl. set_solver. }
  apply p_var_proper_ref... apply p_seq_proper_ref.
  - apply r_asgn_1... unfold term_lt at 2 3. repeat rewrite simpl_subst_and.
    repeat rewrite simpl_subst_af. simpl. unfold I1. intros σ ?. simp feval in *.
    simpl in H. destruct_and! H. destruct H0 as (vp&_&?). apply term_lt_inv in H.
    destruct H as (xr1&xq&?&?&?). apply term_sum_inv in H. destruct H as (xr&x1&?&?&?).
    subst. inversion H5. subst. clear H5.
    destruct H1 as (xq'&?&?). inversion H5. subst. clear H5. rename n into nq.
    pose proof (teval_det _ _ _ H2 H1). apply mkNum_eq in H5. subst xq. clear H2.
    destruct H3 as (xr'&?&?). inversion H3. subst. clear H3. rename n into nr.
    pose proof (teval_det _ _ _ H H2). apply mkNum_eq in H3. subst xr. clear H2.
    split_and!.
    + simpl. exists (mkNat (nq - 1)). split.
      * apply TEval_App with (vargs:=[mkNat nq; mkNat 1]).
        -- by_constructor.
        -- by_constructor. rewrite minus_INR; [constructor|].
           replace (1)%R with (INR 1) in H4 by reflexivity. rewrite <- plus_INR in H4.
           apply INR_lt in H4. lia.
      * eapply IsNat. reflexivity.
    + simpl. exists [mkNat nr; mkNum (INR nq - 1)]. split.
      * by_constructor. apply teval_sub_iff. exists (INR nq), 1%R. split_and!; auto.
        constructor.
      * unfold peval. intros. rewrite list_to_vec_2_canon. constructor. lra.
    + simpl. exists [mkNum (INR nq - 1); mkNat nq]. split.
      * by_constructor. apply teval_sub_iff. exists (INR nq), 1%R. split_and!; auto.
        constructor.
      * unfold peval. intros. rewrite list_to_vec_2_canon. constructor. lra.
    + rewrite simpl_subst_and. do 2 rewrite simpl_subst_af. simp feval. split.
      * simpl. exists (mkNat nq). split... eapply IsNat; reflexivity.
      * simpl. exists (mkNat nr). split... eapply IsNat; reflexivity.
  - etrans.
    + apply r_if_2 with (g1:=<!! ⌜s < p²⌝ !!>) (g2:=<!! ⌜s ≥ p²⌝ !!>).
      intros σ ?. simp feval. unfold I in H. simp feval in H.
      destruct_and! H. apply term_lt_inv in H3. destruct H3 as (xp&?&?&_&_).
      apply term_lt_inv in H6. destruct H6 as (xs&?&?&_&_).
      destruct (decide (xs < xp^2)%R).
      * left. simpl. unfold term_lt. simp feval. simpl. exists [mkNum xs; mkNum (xp^2)].
        split.
        -- by_constructor. apply teval_pow2_iff. exists xp. split...
        -- unfold peval. intros. rewrite list_to_vec_2_canon. simpl. constructor.
           lra.
      * right. simpl. unfold term_ge. unfold term_le. simp feval. simpl.
        exists [mkNum (xp^2); mkNum (xs)]. split.
        -- by_constructor. apply teval_pow2_iff. exists xp. split...
        -- unfold peval. intros. rewrite list_to_vec_2_canon. simpl. constructor. lra.
    + simpl. apply r_if_2_proper.
      * simpl. etrans.
        -- rewrite r_permute_frame with (w':=[q] ++ [r]).
           ++ apply r_contract_frame; [apply initials_closed_alt'|]; set_solver.
           ++ apply initials_closed_alt'. set_solver.
           ++ simpl. reflexivity.
        -- etrans.
           ++ apply r_weaken_pre with (pre':=<! ⌜ s < p ² ⌝ ∧ ⌜p ∈ₜ ℕ⌝ ∧ ⌜ p < q ⌝ ∧ I !>).
              intros σ ?. simp feval in *. destruct_and! H. split_and!...
           ++ apply r_strengthen_post. 1-2: apply initials_closed_alt'; set_solver.
              intros σ ?. unfold subst_initials. simpl.
              rewrite simpl_subst_and. rewrite simpl_subst_and.
              unfold term_lt, term_le. do 2 rewrite simpl_subst_af. simpl.
              rewrite subst_non_free.
              2:{ unfold I. set_solver. }
              unfold I in *. simp feval in *. destruct_and! H.
              assert (H5:=H). simpl in H5. destruct H5 as (?&?&?). inversion H5.
              subst. rename n into nq. 
              assert (H6:=H0). simpl in H6. destruct H6 as (?&?&?). inversion H7.
              subst. rename n into nr.
              assert (nr ≤ nq).
              {
                apply term_le_inv in H2.
                destruct H2 as (xr2&xs&?&?&?).
                apply term_lt_inv in H4.
                destruct H4 as (xs'&xq2&?&?&?).
                apply term_pow2_inv in H2.
                destruct H2 as (xt&?&?). subst.
                apply term_pow2_inv in H10.
                destruct H10 as (xq&?&?). subst.
                pose proof (teval_det _ _ _ H2 H6).
                pose proof (teval_det _ _ _ H3 H10).
                pose proof (teval_det _ _ _ H4 H8).
                apply mkNum_eq in H12, H13, H14. subst.
                assert (INR nr ^ 2 < INR nq ^ 2)%R.
                { apply Rle_lt_trans with (r2:=xs)... }
                apply pow2_lt in H12... apply INR_lt in H12. lia.
              }
              split_and!...
              ** simpl. exists [mkInt 0; mkNum (INR nq - INR nr)]. split.
                 --- by_constructor. apply teval_sub_iff. exists (INR nq), (INR nr).
                     split_and!...
                 --- unfold peval. intros. rewrite list_to_vec_2_canon. simpl. constructor.
                     rewrite <- minus_INR...
              ** simpl. apply term_lt_inv in H1. destruct H1 as (?&xq0&?&?).
                 pose proof (teval_det _ _ _ H3 H1). apply mkNum_eq in H10. subst x.
                 exists [mkNat (nq - nr); mkNum (xq0 - INR nr)]. split.
                 --- by_constructor.
                     +++ apply teval_sub_iff. exists (INR nq), (INR nr). split_and!...
                         rewrite minus_INR... 
                     +++ apply teval_sub_iff. exists xq0, (INR nr). split_and!...
                         destruct H9...
                 --- unfold peval. intros. rewrite list_to_vec_2_canon. simpl. constructor.
                     clear H10 H6 H7 H3 H5 H1. destruct H9 as [_ ?]. rewrite minus_INR...
                     lra.
      * simpl. etrans.
        -- rewrite r_permute_frame with (w':=[r] ++ [q]).
           ++ apply r_contract_frame; [apply initials_closed_alt'|]; set_solver.
           ++ apply initials_closed_alt'; set_solver.
           ++ simpl. apply perm_swap.
        -- etrans.
           ++ apply r_weaken_pre with (pre':=<! ⌜ s ≥ p ² ⌝ ∧ ⌜p ∈ₜ ℕ⌝ ∧ ⌜ r < p ⌝ ∧ I !>).
              intros σ ?. simp feval in *. destruct_and! H. split_and!...
           ++ apply r_strengthen_post... 1-2: apply initials_closed_alt'; set_solver.
              intros σ ?. unfold subst_initials. simpl.
              rewrite simpl_subst_and. rewrite simpl_subst_and.
              unfold term_lt, term_le. do 2 rewrite simpl_subst_af. simpl.
              rewrite subst_non_free.
              2:{ unfold I. set_solver. }
              unfold I in *. simp feval in *. destruct_and! H.
              assert (H5:=H). simpl in H5. destruct H5 as (?&?&?). inversion H5.
              subst. rename n into nq. 
              assert (H6:=H0). simpl in H6. destruct H6 as (?&?&?). inversion H7.
              subst. rename n into nr.
              assert (nr ≤ nq).
              {
                apply term_le_inv in H2.
                destruct H2 as (xr2&xs&?&?&?).
                apply term_lt_inv in H4.
                destruct H4 as (xs'&xq2&?&?&?).
                apply term_pow2_inv in H2.
                destruct H2 as (xt&?&?). subst.
                apply term_pow2_inv in H10.
                destruct H10 as (xq&?&?). subst.
                pose proof (teval_det _ _ _ H2 H6).
                pose proof (teval_det _ _ _ H3 H10).
                pose proof (teval_det _ _ _ H4 H8).
                apply mkNum_eq in H12, H13, H14. subst.
                assert (INR nr ^ 2 < INR nq ^ 2)%R.
                { apply Rle_lt_trans with (r2:=xs)... }
                apply pow2_lt in H12... apply INR_lt in H12. lia.
              }
              split_and!...
              ** simpl. exists [mkInt 0; mkNum (INR nq - INR nr)]. split.
                 --- by_constructor. apply teval_sub_iff. exists (INR nq), (INR nr).
                     split_and!...
                 --- unfold peval. intros. rewrite list_to_vec_2_canon. simpl. constructor.
                     rewrite <- minus_INR...
              ** simpl. apply term_lt_inv in H1. destruct H1 as (xr0&?&?&?&?).
                 pose proof (teval_det _ _ _ H9 H6). apply mkNum_eq in H11. subst.
                 exists [mkNat (nq - nr); mkNum (INR nq - xr0)]. split.
                 --- by_constructor.
                     +++ apply teval_sub_iff. exists (INR nq), (INR nr). split_and!...
                         rewrite minus_INR... 
                     +++ apply teval_sub_iff. exists (INR nq), xr0. split_and!...
                 --- unfold peval. intros. rewrite list_to_vec_2_canon. simpl. constructor.
                     clear H11 H6 H7 H3 H5 H9 H1. rewrite minus_INR...
                     lra.
Qed.

Lemma r10 : prog9 ⊑ code.
Proof with auto.
  unfold prog9, code. do 4 f_equiv. apply r_while_body.
  { simpl. unfold modified_vars. simpl. set_solver. }
  f_equiv. f_equiv. apply r_if_2_proper.
  - apply r_asgn_1; [apply initials_closed_alt'; set_solver|]. unfold I. intros σ ?.
    simp feval in *. destruct_and!. repeat rewrite simpl_subst_and. simp feval.
    simpl. repeat rewrite simpl_subst_af. simpl.
    unfold term_le, term_lt. repeat rewrite simpl_subst_af. simpl in *.
    split_and!... destruct H0 as (v&?&?). apply term_lt_inv in H2.
    destruct H2 as (xp&xq&?&?&?). pose proof (teval_det _ _ _ H6 H8). subst v.
    exists [mkNum xp; mkNum xq]. split.
      + by_constructor.
      + unfold peval. intros ?. rewrite list_to_vec_2_canon. simpl. constructor...
  - apply r_asgn_1; [apply initials_closed_alt'; set_solver|]. unfold I. intros σ ?.
    simp feval in *. destruct_and!. repeat rewrite simpl_subst_and. simp feval.
    simpl. repeat rewrite simpl_subst_af. simpl.
    unfold term_le, term_lt. repeat rewrite simpl_subst_af. simpl in *.
    split_and!... simp feval. simpl. destruct H0 as (v&?&?).
    apply term_lt_inv in H2. destruct H2 as (xp&xq&?&?&?).
    pose proof (teval_det _ _ _ H2 H6). subst v. exists [mkNum xp; mkNum xq]. split.
    + by_constructor.
    + unfold peval. intros ?. rewrite list_to_vec_2_canon. simpl. constructor...
Qed.

Theorem code_refines_spec : spec ⊑ code.
Proof.
  transitivity prog1; [by rewrite r1|].
  transitivity prog2; [apply r2|].
  transitivity prog3; [apply r3|].
  transitivity prog4; [apply r4|].
  transitivity prog5; [apply r5|].
  transitivity prog6; [apply r6|].
  transitivity prog7; [apply r7|].
  transitivity prog8; [apply r8|].
  transitivity prog9; [apply r9|].
  apply r10.
Qed.

Print Assumptions code_refines_spec.
Check Basic.feval_lem_admissible.
Check Basic.TotalFRel_total_admissible.
