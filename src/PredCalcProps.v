From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import Tactics PredCalc PredCalcSubst PredCalcEquiv.
From stdpp Require Import gmap fin_maps.

(* Lemma feval_subst_id : forall A x, *)
(*     <! A[x \ x] !> ≡ A. *)
(* Proof. *)
(*   intros A x M σ. destruct (decide (x ∈ formula_fvars A)). *)
(*   etrans. *)
(*   - erewrite <- feval_subst; [reflexivity|]. apply teval_id. *)
(* TODO: rename this *)
Lemma feval_subst_formula_id : forall A x,
    <! A[x \ x] !> ≡ A.
Proof with auto.
  intros A x. generalize dependent A.
  apply subst_formula_ind with (P:=λ A B, A ≡ B); intros...
  - rewrite subst_sf_id...
  - rewrite H. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
  - intros M σ. simpl.
    enough (forall v, feval M (<[y':=v]> σ) <! φ [y \ y'] [x \ x] !> <-> feval M (<[y:=v]> σ) φ).
    { split; intros [v Hv]; exists v; apply H2; apply Hv. }
    intros v.
    specialize H with (<! φ [y \ y'] !>). forward H by auto.
    pose proof (H M (<[y':=v]> σ)) as H. rewrite H. rewrite <- (feval_subst v).
    2: { apply TEval_Var. apply lookup_insert. }
    destruct (decide (y = y')).
    + unfold y' in *. rewrite <- e. rewrite (insert_insert σ)...
    + rewrite (insert_commute σ)...
      pose proof (fresh_var_fresh y (quant_subst_fvars φ x x)).
      apply quant_subst_fvars_inv in H2 as (?&?&?).
      rewrite (feval_delete_state_var_head y')...
  - intros M σ. simpl.
    enough (forall v, feval M (<[y':=v]> σ) <! φ [y \ y'] [x \ x] !> <-> feval M (<[y:=v]> σ) φ).
    { split; intros Hv v; apply H2... }
    intros v.
    specialize H with (<! φ [y \ y'] !>). forward H by auto.
    pose proof (H M (<[y':=v]> σ)) as H. rewrite H. rewrite <- (feval_subst v).
    2: { apply TEval_Var. apply lookup_insert. }
    destruct (decide (y = y')).
    + unfold y' in *. rewrite <- e. rewrite (insert_insert σ)...
    + rewrite (insert_commute σ)...
      pose proof (fresh_var_fresh y (quant_subst_fvars φ x x)).
      apply quant_subst_fvars_inv in H2 as (?&?&?).
      rewrite (feval_delete_state_var_head y')...
Qed.

(* HACK: subst_formula_not_free *)
(* HACK: subst_formula_commute *)

(* Lemma feval_subst_commute : forall M σ φ x₁ t₁ x₂ t₂, *)
(*     x₁ <> x₂ -> *)
(*     negb $ is_free_in_term x₁ t₂ -> *)
(*     negb $ is_free_in_term x₂ t₁ -> *)
(*     feval M σ <! φ[x₁ \ t₁][x₂ \ t₂] !> <-> feval M σ <! φ[x₂ \ t₂][x₁ \ t₁] !>. *)
(* Proof with auto. *)

(* Lemma subst_eq_congr : forall M σ φ x t u b, *)
(*   feval M σ <! t = u !> -> *)
(*   feval M σ <! φ[x\t] !> b <-> *)
(*   feval M σ <! φ[x\u] !> b. *)
(* Proof with auto. *)

Lemma feval_not_iff : forall M σ φ,
  feval M σ <! ~ φ !> <->
  ~ feval M σ <! φ !>.
Proof. auto. Qed.

Lemma feval_not_false_iff : forall M σ φ,
  ~ feval M σ <! ~ φ !> <->
  feval M σ <! φ !>.
Proof with auto.
  intros M σ φ. split... simpl. apply feval_dne.
Qed.

Lemma feval_and_iff : forall M σ φ ψ,
  feval M σ <! φ /\ ψ !> <->
  feval M σ φ /\ feval M σ ψ.
Proof with auto.
  intros. simpl. auto.
Qed.

Lemma feval_not_and_iff : forall M σ φ ψ,
  ~ feval M σ <! φ /\ ψ !> <->
  ~ feval M σ φ \/ ~ feval M σ ψ.
Proof with auto.
  intros. simpl. split...
  - intros H. destruct (feval_lem M σ φ); destruct (feval_lem M σ ψ)...
  - intros H. destruct H.
    + intros [contra _]...
    + intros [_ contra]...
Qed.

Lemma feval_or_true_iff : forall M σ φ ψ,
  feval M σ <! φ \/ ψ !> <->
  feval M σ φ \/ feval M σ ψ.
Proof with auto.
  intros. simpl. split...
Qed.

Lemma feval_not_or_iff : forall M σ φ ψ,
  ~ feval M σ <! φ \/ ψ !> <->
  ~ feval M σ φ /\ ~ feval M σ ψ.
Proof with auto.
  simpl. split... intros [H₁ H₂] [H|H]; contradiction.
Qed.

Lemma feval_implication_iff : forall M σ φ ψ,
  feval M σ <! φ => ψ !> <->
    ~ feval M σ <! φ !> \/
    feval M σ <! ψ !>.
Proof with auto.
  simpl. intros. split.
  - intros H. destruct (feval_lem M σ φ); destruct (feval_lem M σ ψ)...
  - intros [H|H] H'... contradiction.
Qed.

Lemma feval_not_implication_iff : forall M σ φ ψ,
  ~ feval M σ <! φ => ψ !> <->
    feval M σ <! φ !> /\
    ~ feval M σ <! ψ !>.
Proof with auto.
  intros. rewrite feval_implication_iff.
  rewrite (Decidable.not_or_iff (~ feval M σ φ) (feval M σ ψ)).
  split; intros [H₁ H₂]...
  rewrite (feval_dne M σ φ) in H₁...
Qed.

Lemma feval_iff_iff : forall M σ φ ψ,
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

Lemma feval_iff_not_iff : forall M σ φ ψ,
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

Lemma feval_exists_true_iff : forall M σ x φ,
  feval M σ <! exists x, φ !> true <->
  exists v, feval M σ (φ[x \ v]) true.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Lemma feval_exists_false_iff : forall M σ x φ,
  feval M σ <! exists x, φ !> false <->
  forall v, feval M σ (φ[x \ v]) false.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Lemma feval_forall_true_iff : forall M σ x φ,
  feval M σ <! forall x, φ !> true <->
  forall v, feval M σ (φ[x \ v]) true.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.

Lemma feval_forall_false_iff : forall M σ x φ,
  feval M σ <! forall x, φ !> false <->
  exists v, feval M σ (φ[x \ v]) false.
Proof with auto.
  intros st x φ. split.
  - intros H. inversion H; subst...
  - intros H...
Qed.


Lemma feval_inversion_false_true : forall M σ,
  ~ feval M σ <! false !> true.
Proof.
  intros st contra. inversion contra; subst. inversion H0.
Qed.

Lemma feval_inversion_true_false : forall {st},
  ~ feval M σ <! true !> false.
Proof.
  intros st contra. inversion contra; subst. inversion H0.
Qed.

Lemma feval_true_true : forall M σ,
  feval M σ <! true !> true.
Proof.
  intros st. apply FEval_Simple. apply SFEval_True.
Qed.

Lemma feval_false_false : forall M σ,
  feval M σ <! false !> false.
Proof.
  intros st. apply FEval_Simple. apply SFEval_False.
Qed.

Lemma feval_functional : forall φ st,
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

Lemma feval_eq_refl : forall t st,
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
