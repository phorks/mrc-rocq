From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import Tactics PredCalc PredCalcSubst.
From MRC Require Import Tactics.
From stdpp Require Import gmap fin_maps.

Theorem subst_same_term : forall t x,
    subst_term t x x = t.
Proof with auto.
  intros t x. induction t using term_ind; simpl...
  - destruct (decide (x0 = x))... inversion e...
  - f_equal. induction args; simpl... f_equal.
    * apply H. simpl. left...
    * apply IHargs. intros. apply H. simpl. right...
Qed.

Theorem subst_same_sf : forall sf x,
    subst_simple_formula sf x x = sf.
Proof with auto.
  intros sf x. destruct sf...
  - simpl... f_equal; apply subst_same_term.
  - simpl. f_equal. induction args... rewrite map_cons. f_equal; auto; apply subst_same_term.
Qed.

(* TODO: rename this *)
(* Theorem subst_same_formula : forall φ x, *)
(*     formula_subst φ x x = φ. *)
(* Proof with auto. *)
(*   intros φ x. generalize dependent φ. *)
(*   apply formula_subst_ind with (P:=λ φ₁ φ₂, φ₁ = φ₂); intros; try solve [f_equal; auto]. *)
(*   - rewrite subst_same_sf... *)
(*   - inversion H1. destruct (String.eqb_spec x y); [contradiction|discriminate]. *)
(*   - inversion H1. destruct (String.eqb_spec x y); [contradiction|discriminate]. *)
(* Qed. *)

Hint Resolve simpl_subst_simple_formula : core.
Hint Resolve simpl_subst_not : core.
Hint Resolve simpl_subst_and : core.
Hint Resolve simpl_subst_or : core.
Hint Resolve simpl_subst_implication : core.
Hint Resolve simpl_subst_iff : core.
Hint Resolve subst_same_term : core.
Hint Resolve subst_same_sf : core.
(* Hint Resolve subst_same_formula : core. *)

(* Theorem subst_term_not_free : forall t x t', *)
(*     negb $ is_free_in_term x t -> *)
(*     subst_term t x t' = t. *)
(* Proof with auto. *)
(*   intros t x t' H. induction t using term_ind; simpl... *)
(*   - simpl in H. destruct (String.eqb_spec x0 x)... simpl in H. contradiction. *)
(*   - simpl in H. f_equal. induction args... rewrite map_cons. simpl in H. *)
(*     rewrite negb_orb in H. apply andb_prop_elim in H as [? ?]. f_equal. *)
(*     * apply H0... simpl. left... *)
(*     * apply IHargs... intros. apply H0... simpl. right... *)
(* Qed. *)

(* Theorem subst_commute_term : forall t x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ is_free_in_term x₁ t₂ -> *)
(*     negb $ is_free_in_term x₂ t₁ -> *)
(*     subst_term (subst_term t x₁ t₁) x₂ t₂ = subst_term (subst_term t x₂ t₂) x₁ t₁. *)
(* Proof with auto. *)
(*   intros t x₁ t₁ x₂ t₂ Hneq H₁ H₂. induction t using term_ind; simpl... *)
(*   - destruct (String.eqb_spec x x₁); destruct (String.eqb_spec x x₂); subst. *)
(*     + contradiction. *)
(*     + simpl. rewrite String.eqb_refl. apply subst_term_not_free... *)
(*     + simpl. rewrite String.eqb_refl. symmetry. apply subst_term_not_free... *)
(*     + simpl. rewrite (proj2 (String.eqb_neq x x₁) n). rewrite (proj2 (String.eqb_neq x x₂) n0)... *)
(*   - f_equal. induction args; simpl... f_equal. *)
(*     + apply H. left... *)
(*     + apply IHargs. intros. apply H. right... *)
(* Qed. *)

(* Theorem subst_commute_sf : forall sf x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ is_free_in_term x₁ t₂ -> *)
(*     negb $ is_free_in_term x₂ t₁ -> *)
(*     subst_simple_formula (subst_simple_formula sf x₁ t₁) x₂ t₂ = *)
(*       subst_simple_formula (subst_simple_formula sf x₂ t₂) x₁ t₁. *)
(* Proof with auto. *)
(*   intros. destruct sf; simpl... *)
(*   - f_equal; auto using subst_commute_term. *)
(*   - f_equal. induction args... repeat rewrite map_cons. f_equal... apply subst_commute_term... *)
(* Qed. *)
(* NOTE: Subst doesn't commute in feval:
          consider (∃ x, x₁ = x)[x₁ \ x][x₂ \ y] and (∃ x, x₁ = x)[x₂ \ y][x₁ \ x]:
          its behavior depends on how fresh_var picks a new quantifier
          LHS:  since to avoid capture, x must be renamed in exists,
                if the algorithm picks x₂ (it can because it is free in both the body and the value being substituted for (x))
                then LHS becomes:  (∃ x₂, x = x₂)[x₂\y] ≡ (∃) )*)

(* Lemma is_free_in_term_iff : forall x t, *)
(*     Is_true $ is_free_in_term x t <-> (x ∈ term_fvars t). *)
(* Proof with auto. *)
(*   intros x t. induction t; simpl. *)
(*   - rewrite elem_of_empty...  *)
(*   - destruct (String.eqb_spec x0 x); subst... *)
(*     + rewrite elem_of_singleton. split... *)
(*     + rewrite elem_of_singleton. split... contradiction. *)
(*   - rename H into IH. induction args. *)
(*     + simpl. rewrite elem_of_empty. split... *)
(*     + simpl. destruct (is_free_in_term x a) eqn:E. *)
(*       * simpl. split... intros _. apply elem_of_union_l. apply IH... left... *)
(*       * simpl. split; intros H. *)
(*         -- apply elem_of_union_r. apply IHargs... intros. apply IH. right... *)
(*         -- apply elem_of_union in H. destruct H. *)
(*            ++ apply IH in H. rewrite E in H. contradiction. left... *)
(*            ++ apply IHargs... intros. apply IH. right... *)
(* Qed. *)

(* Lemma is_free_in_sf_iff : forall x sf, *)
(*     Is_true $ is_free_in_sf x sf <-> (x ∈ simple_formula_fvars sf). *)
(* Proof with auto. *)
(*   destruct sf; simpl. *)
(*   - rewrite elem_of_empty... *)
(*   - rewrite elem_of_empty... *)
(*   - split; intros H. *)
(*     + apply orb_True in H. *)
(*       destruct H; [apply elem_of_union_l | apply elem_of_union_r]; apply is_free_in_term_iff... *)
(*     + rewrite elem_of_union in H. apply orb_True. *)
(*       destruct H; [left | right]; apply is_free_in_term_iff... *)
(*   - induction args; simpl. *)
(*     + rewrite elem_of_empty... *)
(*     + destruct (is_free_in_term x a) eqn:E. *)
(*       * simpl. split... intros _. apply elem_of_union_l. apply is_free_in_term_iff... *)
(*       * simpl. split; intros H. *)
(*         -- apply elem_of_union_r. apply IHargs... *)
(*         -- apply elem_of_union in H. destruct H. *)
(*            ++ apply is_free_in_term_iff in H. rewrite E in H. contradiction. *)
(*            ++ apply IHargs... *)
(* Qed. *)

(* Lemma is_free_iff : forall x φ, *)
(*     Is_true $ is_free_in x φ <-> (x ∈ formula_fvars φ). *)
(* Proof with auto. *)
(*   induction φ; simpl. *)
(*   - apply is_free_in_sf_iff. *)
(*   - assumption. *)
(*   - rewrite orb_True. rewrite elem_of_union. *)
(*     split; (destruct 1; [left; apply IHφ1 | right; apply IHφ2])... *)
(*   - rewrite orb_True. rewrite elem_of_union. *)
(*     split; (destruct 1; [left; apply IHφ1 | right; apply IHφ2])... *)
(*   - rewrite orb_True. rewrite elem_of_union. *)
(*     split; (destruct 1; [left; apply IHφ1 | right; apply IHφ2])... *)
(*   - destruct (String.eqb_spec x0 x); subst. *)
(*     + split; intros; try contradiction. apply not_elem_of_difference in H0... right. *)
(*       apply elem_of_singleton... *)
(*     + split; intros H'. *)
(*       * apply elem_of_difference. split; [apply H | apply not_elem_of_singleton]... *)
(*       * apply elem_of_difference in H'. destruct H'. apply H... *)
(*   - destruct (String.eqb_spec x0 x); subst. *)
(*     + split; intros; try contradiction. apply not_elem_of_difference in H0... right. *)
(*       apply elem_of_singleton... *)
(*     + split; intros H'. *)
(*       * apply elem_of_difference. split; [apply H | apply not_elem_of_singleton]... *)
(*       * apply elem_of_difference in H'. destruct H'. apply H... *)
(* Qed. *)

(* Lemma fresh_var_in_eq_sf_eq_iff : forall x t₁ t₂ t x', *)
(*     let φ := <! t₁ = t₂ !> in *)
(*     fresh_var x φ t = x' -> *)
(*       (negb $ is_free_in_term x t /\ x = x') \/ *)
(*         (is_free_in_term x t /\ negb $ is_free_in x' φ). *)
(* Proof with auto. *)
(*   simpl. intros x t₁ t₂ t x' H.  *)
(*   destruct (is_free_in_term x t) eqn:E.  *)
(*   2: {  left. split... admit. } *)
(*   - right. split... induction t₁; induction t₂; simpl in *... *)
(*     + unfold fresh_var in H. *)
(*       assert (Heq : formula_fvars <! v = x0 !> = {[x0]}). *)
(*       { simpl. rewrite union_empty_l_L... } rewrite E, Heq in H. *)
(*       rewrite size_singleton in H...  *)
(*     +  *)
(*   simpl. induction t₁. *)

(*   - induction t₂. *)
(*     +  *)
(*   intros  *)

(* Lemma fresh_var_eq_iff : forall x φ t x', *)
(*     fresh_var x φ t = x' -> *)
(*       (negb $ is_free_in_term x t /\ x = x') \/ *)
(*         (is_free_in_term x t /\ negb $ is_free_in x' φ). *)
(* Proof with auto. *)
(*   admit. *)
(* Admitted. *)

(* Lemma fresh_var_free : forall x φ t, *)
(*     (negb $ is_free_in_term x t /\ x = fresh_var x φ t) \/ *)
(*       (is_free_in_term x t /\ negb $ is_free_in (fresh_var x φ t) φ). *)
(* Proof with auto. *)
(*   admit. *)
(* Admitted. *)
(* Lemma fresh_var_free : forall , *)
(*     appears_ fresh_var x φ t *)

(* Theorem feval_subst_commute : forall M σ φ x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ is_free_in_term x₁ t₂ -> *)
(*     negb $ is_free_in_term x₂ t₁ -> *)
(*     feval M σ <! φ[x₁ \ t₁][x₂ \ t₂] !> <-> feval M σ <! φ[x₂ \ t₂][x₁ \ t₁] !>. *)
(* Proof with auto. *)
(*   intros M σ φ. generalize dependent σ. *)
(*   induction φ using formula_ind; intros σ x₁ t₁ x₂ t₂ Hneq Hf1 Hf2. *)
(*   - unfold formula_subst. simpl. rewrite subst_commute_sf... *)
(*   - do 4 rewrite simpl_subst_not. simpl. rewrite IHφ... *)
(*   - do 4 rewrite simpl_subst_and. simpl. rewrite IHφ1... rewrite IHφ2... *)
(*   - do 4 rewrite simpl_subst_or. simpl. rewrite IHφ1... rewrite IHφ2... *)
(*   - do 4 rewrite simpl_subst_implication. simpl. rewrite IHφ1... rewrite IHφ2... *)
(*   - destruct (String.eqb_spec x x₁); destruct (String.eqb_spec x x₂); subst. *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_eq... *)
(*       rewrite simpl_subst_exists_eq... *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*       rewrite simpl_subst_exists_eq... apply fresh_var_not_in_term... *)
(*     + rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_eq... *)
(*       2: { apply fresh_var_not_in_term... } *)
(*       rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*     + rewrite simpl_subst_exists_ne... *)
(*       destruct (String.eqb_spec (fresh_var x φ t₁) x₂). *)
(*       * rewrite simpl_subst_exists_eq... *)
(*         assert (H1 := fresh_var_free x φ t₁). subst. *)
(*         destruct H1. 1:{ destruct H0 as [_ H0]. contradiction. } *)
(*         subst. rewrite simpl_subst_exists_ne... *)
(*         destruct (String.eqb_spec (fresh_var x φ t₂) x₁); subst. *)
(*         -- apply not_eq_sym in n, n0. apply fresh_var_ne in n, n0. *)
(*            exfalso. apply Hneq. unfold fresh_var. *)
(*            apply Is_true_true in n, n0. rewrite n. rewrite n0. reflexivity. *)
(*         -- apply not_eq_sym in n0. apply fresh_var_ne in n0. *)

(*            clear Hf2. *)
(*            rewrite simpl_subst_exists_ne... simpl. split; intros [v Hv]; exists v. *)
(*            ++ *)
(*              remember (fresh_var x φ t₁) as xf₁. *)
(*              remember (fresh_var x φ t₂) as xf₂. *)
(*              assert (Heq : xf₁ =  fresh_var xf₂ <! φ [x \ xf₂] [xf₁ \ t₂] !> t₁). *)
(*              { subst.  } *)

(* (*         -- apply  *) *)


(* (*            split. intros [v Hv]; exists v. *) *)
(* (*            apply H... *) *)
(* (*            exfalso. apply hneq. unfold fresh_var. *) *)
(* (*            apply is_true_true in n, n0. rewrite n. rewrite n0. reflexivity. *) *)
(* (* -  *) *)

(*         -- rewrite simpl_subst_exists_ne... simpl. split; intros [v Hv]; exists v. *)
(*            ++ *)
(*            admit. admit. *)
(*       * admit. *)
(*            fresh_var_idem. *)
(*            ++ apply H... *)

(*            Search (Is_true ?b -> ?b = true). *)


(*            rewrite Is_true_eq_true in n. *)


(*           rewrite simpl_subst_exists_eq... subst. simpl. split; intros [v Hv]; exists v. *)
(*            ++ apply H... *)
(*               ** apply not_eq_sym in n. apply fresh_var_ne in n. *)

(*               2: { apply fresh_var_not_in_term... } *)
(*   - *)
(*     formula_subst (formula_subst φ x₁ t₁) x₂ t₂ = *)
(*       formula_subst (formula_subst φ x₂ t₂) x₁ t₁. *)


(* Theorem subst_commute_formula : forall φ x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ is_free_in_term x₁ t₂ -> *)
(*     negb $ is_free_in_term x₂ t₁ -> *)
(*     formula_subst (formula_subst φ x₁ t₁) x₂ t₂ = *)
(*       formula_subst (formula_subst φ x₂ t₂) x₁ t₁. *)
(* Proof with auto. *)
(*   induction φ; intros x₁ t₁ x₂ t₂ Hneq H1 H2. *)
(*   - rewrite simpl_subst_simple_formula. unfold formula_subst. simpl. *)
(*     rewrite subst_commute_sf... *)
(*   - do 4 rewrite simpl_subst_not. f_equal. apply IHφ... *)
(*   - do 4 rewrite simpl_subst_and. f_equal; [apply IHφ1 | apply IHφ2]... *)
(*   - do 4 rewrite simpl_subst_or. f_equal; [apply IHφ1 | apply IHφ2]... *)
(*   - do 4 rewrite simpl_subst_implication. f_equal; [apply IHφ1 | apply IHφ2]... *)
(*   - destruct (String.eqb_spec x x₁); destruct (String.eqb_spec x x₂); subst. *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_eq... *)
(*       rewrite simpl_subst_exists_eq... *)
(*     + rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*       rewrite simpl_subst_exists_eq... apply fresh_var_not_in_term... *)
(*     + rewrite simpl_subst_exists_ne... rewrite simpl_subst_exists_eq... *)
(*       2: { apply fresh_var_not_in_term... } *)
(*       rewrite simpl_subst_exists_eq... rewrite simpl_subst_exists_ne... *)
(*     + rewrite simpl_subst_exists_ne... *)
(*       destruct (String.eqb_spec (fresh_var x φ t₁) x₂). *)
(*       * rewrite simpl_subst_exists_eq... subst. rewrite simpl_subst_exists_ne... *)
(*         destruct (String.eqb_spec (fresh_var x φ t₂) x₁). *)
(*         -- rewrite simpl_subst_exists_eq... subst. f_equal... *)
(*       2: { apply fresh_var_not_in_term... } *)


(*   - rewrite simpl)sy *)
(*     simpl. *)
(*     f_equal. *)
(*   - rewrite simpl_subst_and. f_equal... *)
(*   - rewrite simpl_subst_or. f_equal... *)
(*   - rewrite simpl_subst_implication. f_equal... *)
(*   - destruct (String.eqb_spec x₀ x). *)
(*     + rewrite simpl_subst_exists_eq... *)
(*     + rewrite simpl_subst_exists_ne... rewrite fresh_var_for_var_ne... *)
(*       f_equal. etrans. *)
(*       * apply H. unfold formula_subst. apply shape_eq_sym. apply subst_preserves_shape. *)
(*       * apply H. apply shape_eq_refl. *)
(*   - destruct (String.eqb_spec x₀ x). *)
(*     + rewrite simpl_subst_forall_eq... *)
(*     + rewrite simpl_subst_forall_ne... rewrite fresh_var_for_var_ne... *)
(*       f_equal. etrans. *)
(*       * apply H. unfold formula_subst. apply shape_eq_sym. apply subst_preserves_shape. *)
(*       * apply H. apply shape_eq_refl. *)

(* Theorem subst_eq_congr : forall M σ φ x t u b, *)
(*   feval M σ <! t = u !> -> *)
(*   feval M σ <! φ[x\t] !> b -> *)
(*   feval M σ <! φ[x\u] !> b. *)
(* Proof with auto. *)

(* Theorem subst_term_id_when_not_in_term : forall x t a, *)
(*   is_free_in_term x t = false -> *)
(*   subst_term t x a = t. *)
(* Proof with auto. *)
(*   intros x t a H. induction t... *)
(*   - simpl. destruct (String.eqb_spec x0 x)... rewrite e in H. *)
(*     simpl in H. rewrite String.eqb_refl in H. discriminate H. *)
(*   - simpl. f_equal. induction args... simpl in H. *)
(*     apply Bool.orb_false_iff in H as [H1 H2]. *)
(*     simpl. f_equal. *)
(*     + apply H0... simpl... *)
(*     + apply IHargs. *)
(*       * intros arg HIn Hap. apply H0... simpl... *)
(*       * simpl. apply H2. *)
(* Qed. *)

Theorem teval_subst : forall {M σ t t' x} {v' v : value} (H : teval M σ t' v'),
  teval M (<[x:=v']>σ) t v <-> teval M σ (subst_term t x t') v.
Proof with auto.
 intros M σ t t' x v' v. split.
  - intros H'. generalize dependent t'. generalize dependent v.
    assert (Hind:=teval_ind_mut M (<[x:=v']>σ)
      (λ t v _, forall t', teval M σ t' v' -> teval M σ (subst_term t x t') v)
      (λ args vargs _, forall t', teval M σ t' v' -> teval_args M σ (map (λ arg, subst_term arg x t') args) vargs)).
    simpl in Hind. apply Hind; clear Hind.
    + constructor.
    + rename x into x'. intros x v H t' Heval. destruct (decide (x = x')).
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H₁ H₂]].
        -- assumption.
        -- exfalso. apply H₁...
      * apply lookup_insert_Some in H. destruct H as [[<- ->] | [H₁ H₂]].
        -- contradiction.
        -- constructor...
    + intros.
      (* TODO: rename TEval_Func to TEval_App and argsv to vargs  *)
      apply TEval_Func with argsv...
    + constructor.
    + constructor; [apply H | apply H0]...
  - remember (subst_term t x t') as tpre. intros H'.
    assert (Hind:=teval_ind_mut M σ
      (λ t v _, forall t', teval M σ t' v' -> forall tpre, t = subst_term tpre x t' -> teval M (<[x:=v']>σ) tpre v)
      (λ args vargs _, forall t', teval M σ t' v' -> forall args',
            args = (map (λ arg, subst_term arg x t') args') ->
            teval_args M (<[x:=v']>σ) args' vargs)).
    generalize dependent Heqtpre. generalize dependent t. generalize dependent H.
    generalize dependent t'. generalize dependent H'. generalize dependent v.
    generalize dependent tpre. simpl in Hind. apply Hind; clear Hind.
    + intros. destruct tpre; simpl in H0.
      * inversion H0. subst. constructor.
      * destruct (decide (x0 = x)); try discriminate. subst. inversion H; subst.
        constructor. apply lookup_insert_Some...
      * discriminate.
    + intros. destruct tpre; simpl in H0; try discriminate.
      simpl in H0. destruct (decide (x1 = x)); subst.
      * apply TEval_Var. inversion H; subst. rewrite e in H1. inversion H1. apply lookup_insert_Some...
      * inversion H0. subst. apply TEval_Var.  apply lookup_insert_Some...
    + intros. destruct tpre; simpl in H1; try discriminate.
      * destruct (decide (x0 = x)); try discriminate. inversion H1; subst.
        inversion H0; subst. inversion H6; subst. inversion f0; subst.
        rewrite H1 in H5. inversion H5; subst fdef0. clear H5.
        pose proof (Heq := teval_args_det H4 t0). subst.
        pose proof (Heq := UIP_nat _ _ hlen hlen0 ). subst.
        pose proof (Heq := fdef_functional _ H3 H7). subst.
        constructor. apply lookup_insert_Some...
      * inversion H1. subst. apply TEval_Func with argsv... apply H with t'...
    + intros. symmetry in H0. apply map_eq_nil in H0. subst. constructor...
    + intros. symmetry in H2. apply map_eq_cons in H2. destruct H2 as (y&ys&H3&H4&H5).
      subst. constructor.
      * apply H with t'...
      * apply H0 with t'...
Qed.

Theorem teval_args_subst : forall {M σ x t} {v : value} {args vargs},
    teval M σ t v ->
    teval_args M (<[x:=v]>σ) args vargs <->
    teval_args M σ (map (λ arg : term, subst_term arg x t) args) vargs.
Proof with auto.
  intros M σ x t v args vargs Ht. split.
  - induction 1.
    + constructor.
    + constructor; [(apply (teval_subst Ht); assumption)|]. assumption.
  - remember (map (λ arg, subst_term arg x v) args) as args'.
    generalize dependent vargs.
    generalize dependent args'.
    induction args; intros args' Heq vargs H.
    + subst. inversion H; subst. constructor.
    + subst. inversion H; subst. constructor; [(apply (teval_subst Ht); assumption)|].
      eapply IHargs.
      * reflexivity.
      * assumption.
Qed.

Theorem sfeval_subst : forall {M σ sf x t} {v : value},
    teval M σ t v ->
    sfeval M (<[x:=v]>σ) sf <-> sfeval M σ (subst_simple_formula sf x t).
Proof with auto.
  intros M σ sf x t v Ht. split.
  - destruct sf; simpl; intros H...
    + apply SFEval_True.
    + inversion H.
    + inversion H; subst. apply (teval_subst Ht) in H2, H3. apply SFEval_Eq with v0; assumption.
    + inversion H; subst. apply SFEval_Pred with vargs.
      * apply (teval_args_subst Ht). assumption.
      * assumption.
  - destruct sf; simpl; intros H...
    + apply SFEval_True.
    + inversion H.
    + inversion H; subst. apply (teval_subst Ht) in H2, H3. apply SFEval_Eq with v0; assumption.
    + inversion H; subst. apply SFEval_Pred with vargs.
      * apply (teval_args_subst Ht). assumption.
      * assumption.
Qed.

(* TODO: The other one should be called aux *)
Lemma subst_preserves_shape_aux : forall φ x a,
  shape_eq φ (φ[x \ a]) = true.
Proof with auto. intros. unfold subst_formula. apply subst_preserves_shape. Qed.

Lemma subst_preserves_shape_aux' : forall φ x a,
  shape_eq (φ[x \ a]) φ  = true.
Proof with auto. intros. apply shape_eq_sym. apply subst_preserves_shape_aux. Qed.

Lemma teval_delete_state_var : ∀ x {M σ t v},
    x ∉ term_fvars t ->
    teval M σ t v ↔ teval M (delete x σ) t v.
Proof with auto.
  intros x₀ M σ t v Hfree. split.
  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M σ t v -> x₀ ∉ term_fvars t -> teval M (delete x₀ σ) t v)
         (λ args vargs _, forallb (λ arg, bool_decide (x₀ ∉ term_fvars arg)) args ->
                              teval_args M σ args vargs -> teval_args M (delete x₀ σ) args vargs)).
    + intros. constructor.
    + intros x v H H' Hfree. constructor. simpl in Hfree.
      destruct (decide (x = x₀)); subst; simpl.
      * apply not_elem_of_singleton in Hfree. contradiction.
      * apply lookup_delete_Some. split...
    + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_Func with vargs...
      apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
      apply not_elem_of_union in Hfree as [H1 H2].
      simpl. apply andb_prop_intro. split...
    + constructor.
    + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
      apply andb_prop_elim in Hfree as [Hfree Hfrees]. apply bool_decide_unpack in Hfree.
      constructor.
      * apply IH...
      * apply IHargs...

  - intros H. revert Hfree. assert (H':=H). revert H H'.
    generalize dependent v. generalize dependent t.
    apply (teval_ind_mut _ _
         (λ t v _, teval M (delete x₀ σ) t v -> x₀ ∉ term_fvars t -> teval M σ t v)
         (λ args vargs _, forallb (λ arg, bool_decide (x₀ ∉ term_fvars arg)) args ->
                              teval_args M (delete x₀ σ) args vargs -> teval_args M σ args vargs)).
    + intros. constructor.
    + intros x v H H' Hfree. constructor. simpl in Hfree.
      destruct (decide (x = x₀)); subst; simpl.
      * apply not_elem_of_singleton in Hfree. contradiction.
      * apply lookup_delete_Some in H as [? ?]...
    + intros f args vargs v Hargs IHargs Hfn H Hfree. apply TEval_Func with vargs...
      apply IHargs... simpl in Hfree. clear Hfn IHargs Hargs H. induction args; subst; simpl in *...
      apply not_elem_of_union in Hfree as [? ?].
      simpl. apply andb_prop_intro. split...
    + constructor.
    + intros t ts v vs Ht IH Hargs IHargs Hfree H. simpl in *.
      apply andb_prop_elim in Hfree as [Hfree Hfrees]. apply bool_decide_unpack in Hfree.
      constructor.
      * apply IH...
      * apply IHargs...
Qed.


Lemma teval_args_delete_state_var : forall x {M σ args vargs},
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args ->
    teval_args M σ args vargs <->
    teval_args M (delete x σ) args vargs.
Proof with auto.
  intros x M σ args vargs Hfree. split.
  - induction 1.
    + constructor.
    + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
      constructor.
      * apply teval_delete_state_var...
      * apply IHteval_args...
  - induction 1.
    + constructor.
    + simpl in Hfree. apply andb_prop_elim in Hfree as [? ?]. apply bool_decide_unpack in H1.
      constructor.
      * apply teval_delete_state_var in H...
      * apply IHteval_args...
Qed.

Lemma sfeval_delete_state_var : ∀ x {M σ sf},
    x ∉ simple_formula_fvars sf -> sfeval M σ sf ↔ sfeval M (delete x σ) sf.
Proof with auto.
  intros x₀ M σ sf Hfree. intros. destruct sf; simpl.
  - split; constructor.
  - split; inversion 1.
  - simpl in Hfree. apply not_elem_of_union in Hfree as [? ?].
    split; inversion 1; subst.
    + apply SFEval_Eq with v; apply teval_delete_state_var...
    + apply SFEval_Eq with v;
        [apply teval_delete_state_var in H4 | apply teval_delete_state_var in H5]...
  - simpl in Hfree. split; inversion 1; subst.
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_state_var...
      clear H3 H2 vargs H symbol. induction args... simpl in *.
      apply not_elem_of_union in Hfree as [? ?].
      apply andb_prop_intro. split...
    + apply SFEval_Pred with vargs...
      apply teval_args_delete_state_var in H2...
      clear H0 H3 H2 vargs H symbol. induction args... simpl in *.
      apply not_elem_of_union in Hfree as [? ?].
      apply andb_prop_intro. split...
Qed.

Lemma feval_delete_state_var : forall x {M σ φ},
    x ∉ formula_fvars φ ->
    feval M σ φ <-> feval M (delete x σ) φ.
Proof with auto.
  intros x M σ φ. generalize dependent x. generalize dependent σ.
  induction φ using formula_ind; simpl; intros σ x₀ Hfree;
    try (apply not_elem_of_union in Hfree as [H₁ H₂]).
  - apply sfeval_delete_state_var...
  - split; intros H contra.
    + apply H. apply <- IHφ; [exact contra|]...
    + apply H. apply IHφ...
  - split; intros [? ?].
    + split.
      * apply (IHφ1 σ x₀)...
      * apply (IHφ2 σ x₀)...
    + split.
      * apply (IHφ1 σ x₀)...
      * apply (IHφ2 σ x₀)...
  - split; intros [?|?].
    + left. apply (IHφ1 σ x₀)...
    + right. apply (IHφ2 σ x₀)...
    + left. apply (IHφ1 σ x₀)...
    + right. apply (IHφ2 σ x₀)...
  - split; intros Himpl H.
    + apply (IHφ2 σ x₀)... apply Himpl. apply (IHφ1 σ x₀)...
    + apply (IHφ2 σ x₀)... apply Himpl. apply (IHφ1 σ x₀)...
  - destruct (decide (x₀ = x)); subst; simpl.
    + setoid_rewrite (insert_delete_insert σ)...
    + apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
      setoid_rewrite <- (delete_insert_ne σ)... destruct Hfree; try contradiction.
      split; intros [v Hv]; exists v.
      * apply H...
      * apply H in Hv...
  - destruct (decide (x₀ = x)); subst; simpl.
    + setoid_rewrite (insert_delete_insert σ)...
    + apply not_elem_of_difference in Hfree. rewrite elem_of_singleton in Hfree.
      setoid_rewrite <- (delete_insert_ne σ)... destruct Hfree; try contradiction.
      split; intros Hv v; specialize Hv with v.
      * apply H...
      * apply H in Hv...
Qed.

Lemma teval_delete_state_var_head : ∀ M σ t x₀ v₀ v,
    x₀ ∉ term_fvars t -> teval M (<[x₀:=v₀]> σ) t v ↔ teval M σ t v.
Proof with auto.
  intros. etrans.
  - apply teval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- teval_delete_state_var...
Qed.

Lemma teval_args_delete_state_var_head : forall M σ x (v : value) args vargs,
    forallb (λ arg, bool_decide (x ∉ term_fvars arg)) args ->
    teval_args M (<[x:=v]>σ) args vargs <->
    teval_args M σ args vargs.
Proof with auto.
  intros. etrans.
  - apply teval_args_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- teval_args_delete_state_var...
Qed.

Lemma sfeval_delete_state_var_head : ∀ M σ sf x₀ v₀,
    x₀ ∉ simple_formula_fvars sf -> sfeval M (<[x₀:=v₀]> σ) sf ↔ sfeval M σ sf.
Proof with auto.
  intros. etrans.
  - apply sfeval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- sfeval_delete_state_var...
Qed.

Theorem feval_delete_state_var_head : forall M σ φ x v,
    x ∉ formula_fvars φ ->
    feval M (<[x:=v]> σ) φ <-> feval M σ φ.
Proof with auto.
  intros. etrans.
  - apply feval_delete_state_var. exact H.
  - rewrite (delete_insert_delete σ). rewrite <- feval_delete_state_var...
Qed.

Theorem feval_subst : forall {M σ φ x t} {v : value},
    teval M σ t v ->
    feval M (<[x:=v]>σ) φ <-> feval M σ (φ[x \ t]).
Proof with auto.
  intros M σ φ. generalize dependent σ. induction φ using formula_ind; intros σ x₀ t v₀ Ht.
  - split; apply sfeval_subst...
  - rewrite simpl_subst_not. simpl. split;
      intros H contra; apply H; apply (IHφ _ _ _ _ Ht); assumption.
  - rewrite simpl_subst_and. split; intros [? ?];
      (split; [apply (IHφ1 _ _ _ _ Ht)|apply (IHφ2 _ _ _ _ Ht)]; assumption).
  - rewrite simpl_subst_or. split;
      (intros [?|?]; [left; apply (IHφ1 _ _ _ _ Ht) | right; apply (IHφ2 _ _ _ _ Ht)]; auto).
  - rewrite simpl_subst_implication. simpl. split;
      (intros; apply (IHφ2 _ _ _ _ Ht); apply H; apply (IHφ1 _ _ _ _ Ht); auto).
  - destruct (decide (x = x₀)).
    + rewrite simpl_subst_exists_skip... subst. simpl. setoid_rewrite (insert_insert σ)...
    + rename H into IH. destruct (decide (x₀ ∈ formula_fvars φ)).
      2: { rewrite simpl_subst_exists_skip... apply feval_delete_state_var_head...
           simpl. apply not_elem_of_difference... }
      pose proof (Hfresh := fresh_var_fresh x (quant_subst_fvars φ x₀ t))...
      apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3).
      rewrite simpl_subst_exists_propagate... simpl.
      remember (fresh_var x (quant_subst_fvars φ x₀ t)) as x'.
      enough (forall v, feval M (<[x:=v]> (<[x₀:=v₀]> σ)) φ
                   <-> feval M (<[x':=v]> σ) <! φ[x \ x'][x₀ \ t] !>) as H.
      { split; intros [v Hv]; exists v; apply H... }
      intros v. etrans.
      { apply (feval_delete_state_var x')... }
      symmetry. etrans.
      {
        rewrite <- IH.
        2: { apply subst_preserves_shape_aux'. }
        2: { apply teval_delete_state_var_head... apply Ht. }
        rewrite (insert_commute σ); [|auto].
        rewrite <- IH; [|auto|].
        2: { apply TEval_Var. apply lookup_insert. }
        rewrite feval_delete_state_var...
        exact H1.
      }
      destruct (decide (x = x')).
      * rewrite <- e0 in *. rewrite (delete_insert_delete (<[x:=v]> (<[x₀:=v₀]> σ)))...
      * rewrite (delete_insert_ne (<[x':=v]> (<[x₀:=v₀]> σ)))...
         rewrite (delete_insert_delete (<[x₀:=v₀]> σ)).
         rewrite (delete_insert_ne (<[x₀:=v₀]> σ))...
  - destruct (decide (x = x₀)).
    + rewrite simpl_subst_forall_skip... subst. simpl. setoid_rewrite (insert_insert σ)...
    + rename H into IH. destruct (decide (x₀ ∈ formula_fvars φ)).
      2: { rewrite simpl_subst_forall_skip... apply feval_delete_state_var_head...
           simpl. apply not_elem_of_difference... }
      pose proof (Hfresh := fresh_var_fresh x (quant_subst_fvars φ x₀ t))...
      apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3).
      rewrite simpl_subst_forall_propagate... simpl.
      remember (fresh_var x (quant_subst_fvars φ x₀ t)) as x'.
      enough (forall v, feval M (<[x:=v]> (<[x₀:=v₀]> σ)) φ
                   <-> feval M (<[x':=v]> σ) <! φ[x \ x'][x₀ \ t] !>) as H.
      { split; intros v Hv; apply H... }
      intros v. etrans.
      { apply (feval_delete_state_var x')... }
      symmetry. etrans.
      {
        rewrite <- IH.
        2: { apply subst_preserves_shape_aux'. }
        2: { apply teval_delete_state_var_head... apply Ht. }
        rewrite (insert_commute σ); [|auto].
        rewrite <- IH; [|auto|].
        2: { apply TEval_Var. apply lookup_insert. }
        rewrite feval_delete_state_var...
        exact H1.
      }
      destruct (decide (x = x')).
      * rewrite <- e0 in *. rewrite (delete_insert_delete (<[x:=v]> (<[x₀:=v₀]> σ)))...
      * rewrite (delete_insert_ne (<[x':=v]> (<[x₀:=v₀]> σ)))...
         rewrite (delete_insert_delete (<[x₀:=v₀]> σ)).
         rewrite (delete_insert_ne (<[x₀:=v₀]> σ))...
Qed.

Theorem feval_not_iff : forall M σ φ,
  feval M σ <! ~ φ !> <->
  ~ feval M σ <! φ !>.
Proof. auto. Qed.

Theorem feval_not_false_iff : forall M σ φ,
  ~ feval M σ <! ~ φ !> <->
  feval M σ <! φ !>.
Proof with auto.
  intros M σ φ. split... simpl. apply feval_dne.
Qed.

Theorem feval_and_iff : forall M σ φ ψ,
  feval M σ <! φ /\ ψ !> <->
  feval M σ φ /\ feval M σ ψ.
Proof with auto.
  intros. simpl. auto.
Qed.

Theorem feval_not_and_iff : forall M σ φ ψ,
  ~ feval M σ <! φ /\ ψ !> <->
  ~ feval M σ φ \/ ~ feval M σ ψ.
Proof with auto.
  intros. simpl. split...
  - intros H. destruct (feval_lem M σ φ); destruct (feval_lem M σ ψ)...
  - intros H. destruct H.
    + intros [contra _]...
    + intros [_ contra]...
Qed.

Theorem feval_or_true_iff : forall M σ φ ψ,
  feval M σ <! φ \/ ψ !> <->
  feval M σ φ \/ feval M σ ψ.
Proof with auto.
  intros. simpl. split...
Qed.

Theorem feval_not_or_iff : forall M σ φ ψ,
  ~ feval M σ <! φ \/ ψ !> <->
  ~ feval M σ φ /\ ~ feval M σ ψ.
Proof with auto.
  simpl. split... intros [H₁ H₂] [H|H]; contradiction.
Qed.

Theorem feval_implication_iff : forall M σ φ ψ,
  feval M σ <! φ => ψ !> <->
    ~ feval M σ <! φ !> \/
    feval M σ <! ψ !>.
Proof with auto.
  simpl. intros. split.
  - intros H. destruct (feval_lem M σ φ); destruct (feval_lem M σ ψ)...
  - intros [H|H] H'... contradiction.
Qed.

Theorem feval_not_implication_iff : forall M σ φ ψ,
  ~ feval M σ <! φ => ψ !> <->
    feval M σ <! φ !> /\
    ~ feval M σ <! ψ !>.
Proof with auto.
  intros. rewrite feval_implication_iff.
  rewrite (Decidable.not_or_iff (~ feval M σ φ) (feval M σ ψ)).
  split; intros [H₁ H₂]...
  rewrite (feval_dne M σ φ) in H₁...
Qed.

Theorem feval_iff_iff : forall M σ φ ψ,
  feval M σ <! φ <=> ψ !> <->
    (feval M σ <! φ !> /\
      feval M σ <! ψ !>) \/
    (~ feval M σ <! φ !> /\
      ~ feval M σ <! ψ !>).
Proof with auto.
  intros. simpl. split...
  - intros [H₁ H₂]. destruct (feval_lem M σ φ)...
    right...
  - intros [[H₁ H₂]|[H₁ H₂]]; split; auto; intros; contradiction.
Qed.

Theorem feval_iff_not_iff : forall M σ φ ψ,
  ~ feval M σ <! φ <=> ψ !> <->
    (feval M σ <! φ !> /\
      ~ feval M σ <! ψ !>) \/
    (~ feval M σ <! φ !> /\
      feval M σ <! ψ !>).
Proof with auto.
  intros. rewrite feval_iff_iff. split.
  - intros H. apply Decidable.not_or_iff in H. destruct H as [H₁ H₂].
    rewrite Decidable.not_and_iff in H₁, H₂.
    destruct (feval_lem M σ φ)... right. rewrite (feval_dne M σ ψ) in H₂...
  - intros [[H₁ H₂] | [H₁ H₂]].
    + intros [[? ?] | [? ?]]; contradiction.
    + intros [[? ?] | [? ?]]; contradiction.
Qed.

Theorem feval_exists_true_iff : forall M σ x φ,
  feval M σ <! exists x, φ !> true <->
  exists v, feval M σ (φ[x \ v]) true.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_exists_false_iff : forall M σ x φ,
  feval M σ <! exists x, φ !> false <->
  forall v, feval M σ (φ[x \ v]) false.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_forall_true_iff : forall M σ x φ,
  feval M σ <! forall x, φ !> true <->
  forall v, feval M σ (φ[x \ v]) true.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Theorem feval_forall_false_iff : forall M σ x φ,
  feval M σ <! forall x, φ !> false <->
  exists v, feval M σ (φ[x \ v]) false.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.


Theorem feval_inversion_false_true : forall M σ,
  ~ feval M σ <! false !> true.
Proof.
  intros st contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_inversion_true_false : forall {st},
  ~ feval M σ <! true !> false.
Proof.
  intros st contra. inversion contra; subst. inversion H0.
Qed.

Theorem feval_true_true : forall M σ,
  feval M σ <! true !> true.
Proof.
  intros st. apply FEval_Simple. apply SFEval_True.
Qed.

Theorem feval_false_false : forall M σ,
  feval M σ <! false !> false.
Proof.
  intros st. apply FEval_Simple. apply SFEval_False.
Qed.

Theorem feval_functional : forall φ st,
  feval M σ φ true ->
  feval M σ φ false ->
  False.
Proof with auto.
  intros φ st HT HF. induction φ.
  - induction sf.
    + inversion HF; subst. inversion H0.
    + inversion HT; subst. inversion H0.
    + inversion HT; subst. inversion HF; subst.
      inversion H0; subst. inversion H1; subst.
      inversion H5; subst. inversion H7; subst.
      subst pdef. inversion H3. subst.
      apply (pdef_functional (sym_pdef)) in H2.
      rewrite H4 in H3. inversion H3; subst.
      apply (Hfnal _ _ _ _ false) in H2... discriminate.
  - apply feval_not_true_iff in HT.
    apply feval_not_false_iff in HF.
    apply IHφ; assumption.
  - apply feval_and_true_iff in HT as [H0 H1].
    apply feval_and_false_iff in HF as [HF | HF]...
  - apply feval_or_false_iff in HF as [HF1 HF2].
    apply feval_or_true_iff in HT as [HT | HT]...
  - apply feval_implication_false_iff in HF as [HF1 HF2].
    apply feval_implication_true_iff in HT as [HT1 | HT1]...
  - apply feval_iff_true_iff in HT as [[HT1 HT2] | [HT1 HT2]];
    apply feval_iff_false_iff in HF as [[HF1 HF2] | [HF1 HF2]]...
  - inversion HT; subst. inversion HF; subst.
    destruct H1 as [v Hv]. specialize H2 with v.
    apply H with v...
  - inversion HT; subst. inversion HF; subst.
    destruct H2 as [v Hv]. specialize H1 with v.
    apply H with v...
Qed.

Theorem feval_eq_refl : forall t st,
  ~ feval M σ (F_Simple (φT_Pred "="%string [t; t])) false.
Proof with auto.
  intros t st contra. inversion contra; subst.
  inversion H0; subst.
  destruct (pctx_eq_semantics pctx) as [eq_pdef [Heqp1 Heqp2]].
  rewrite Heqp1 in H2. inversion H2. subst pdef.
  destruct (Heqp2 st fctx) as [Heqp_refl _].
  specialize (Heqp_refl t).
  assert (feval M σ fctx pctx <! t = t !> true).
  { apply FEval_Simple. apply SFEval_Pred with eq_pdef...
    destruct eq_pdef.
    apply Pred_Eval with n_params prel Hfnal... }
  destruct (feval_functional _ _ _ _ H contra).
Qed.
