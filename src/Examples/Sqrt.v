From Stdlib Require Import Reals ZArith Sorting.
From Equations Require Import Equations.
From stdpp Require Import listset vector.
From MRC Require Import Prog Refinement.
From MRC Require Import SeqNotation.
From MRC Require Import Model.
From MRC.Examples Require Import Model Variables.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Notation Prog := (prog Model).
Notation Term := (term Model).
Notation Formula := (formula Model).

Definition final_var_to_term (x : Model.final_variable) : Term := TVar (Model.as_var x).
Coercion final_var_to_term : Model.final_variable >-> Term.

(* Notation "'|[' 'var*' xs ':' ty '⦁' y ']|' " := *)
(*   (PVarList xs y) *)
(*     (in custom prog at level 95, xs custom var_seq, ty custom term_ty, y custom prog) : refiney_scope. *)

(* Definition spec : Prog := <{ |[ var r s : ℕ ⦁ r := ⌊√ s⌋ ]| }>. *)
Definition spec : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r = ⌊√ s⌋⌝] ]| }>.
Definition prog2 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r ≤ √ s < r + 1⌝] ]| }>.

(* Lemma r1 : spec ≡ prog1. *)
(* Proof. unfold spec, prog1. by rewrite r_simple_spec. Qed. *)

Lemma list_to_vec_2_canon {A} (x1 x2 : A) H : list_to_vec_n [x1; x2] H = [#x1; x2].
Proof.
  unfold list_to_vec_n. simpl in *. assert (H = eq_refl).
  { apply Eqdep_dec.UIP_refl_nat. }
  subst. done.
Qed.

Definition is_num (v : Value) : bool :=
  match `v with
  | VNum r => true
  | _ => false
  end.

Ltac by_constructor := repeat constructor; auto.

Lemma term_le_same {σ}  {t1 t2 : Term} (v : Value) :
  is_num v →
  teval σ t1 v →
  teval σ t2 v →
  feval σ <! ⌜t1 ≤ t2⌝ !>.
Proof.
  intros. unfold term_le. simp feval. simpl. exists [v; v]. split.
  - by_constructor.
  - unfold peval. intros. rewrite list_to_vec_2_canon. simpl. destruct v.
    destruct x; simpl in *; try contradiction.
    + rewrite VNum_canon. constructor. done.
Qed.

From Stdlib Require Import Lra.

Notation ℝ := (TReal : Model.value_ty Model).
Notation ℤ := (TInt : Model.value_ty Model).

Lemma mkNum_eq x y : mkNum x = mkNum y ↔ x = y.
Proof.
  split; intros.
  - unfold mkNum in H. by inversion H. 
  - by subst.
Qed.

(* Lemma ffloor_spec {σ} x y : <! ⌜x = ⌊y⌋⌝ !> ≡_{σ} <! ⌜x ≤ y < x + 1⌝ !>. *)
(* Proof with auto. *)
(*   split; intros. *)
(*   - inversion H. destruct H0 as []. inversion H1. subst. inversion H4. subst. *)
(*     inversion H8. subst. clear H H1 H4 H8. inversion H6; clear H6. *)
(*     + simpl in *. subst. inversion H. clear H. subst. simp feval. split. *)
(*       * econstructor. Unshelve. 2: exact [mkInt i; mkNum r]. split; [by_constructor|]. *)
(*         unfold peval. intros. rewrite list_to_vec_2_canon. clear H. simpl. constructor. *)
(*         lra. *)
(*       * econstructor. Unshelve. 2: exact [mkNum r; mkNum (IZR i + 1)]. split. *)
(*         -- by_constructor. unfold term_sum. econstructor. Unshelve. 3: exact [mkInt i; mkInt 1]. *)
(*            ++ by_constructor. *)
(*            ++ by_constructor. *)
(*         -- simpl. unfold peval. intros. rewrite list_to_vec_2_canon. clear H. simpl. *)
(*            constructor. lra. *)
(*     + subst. simpl in H. exfalso. inversion Hy. simpl in H1. destruct H1. *)
(*       apply teval_det with (v1:=v) in H1... subst x0. inversion H2. subst v. eapply (H _). *)
(*       constructor. Unshelve. 2: exact (Zfloor r). apply Zfloor_bound. *)
(*   - simp feval in H. destruct H as []. simp feval. inversion H. destruct H1. inversion H1. *)
(*     clear H1; subst. inversion H7; subst. clear H7. inversion H8. subst. clear H8. *)
(*     unfold peval in H2. simpl in H2. specialize (H2 eq_refl). rewrite list_to_vec_2_canon in H2. *)
(*     inversion H2. subst. rename r2 into vx. rename r0 into vy. clear H. *)
(*     inversion H0; clear H0; subst. inversion H; clear H; subst. inversion H0; subst; clear H0. *)
(*     inversion H9; subst; clear H9. inversion H10; subst; clear H10. *)
(*     unfold term_sum in H6. inversion H6. subst. inversion H8; subst; clear H8. *)
(*     inversion H12; clear H12; subst. inversion H13; clear H13; subst. inversion H8. *)
(*     subst. clear H8. apply teval_det with (v1:=mkNum vx) in H9... subst v1. inversion H10. *)
(*     + subst. simpl in H. inversion H. subst. unfold peval in H1. simpl in H1. *)
(*       specialize (H1 eq_refl). inversion H1. subst. apply teval_det with (v1:=mkNum vy) in H7... *)
(*       apply mkNum_eq in H7. subst r2. econstructor. split; [exact H5|]. econstructor. *)
(*       Unshelve. 3: exact [mkNum vy]. 1: by_constructor. unfold fn_eval. simpl. *)
(*       constructor. *)
(*       inversion Hx. destruct H0. apply teval_det with (v1:=mkNum vx) in H0... subst x0. *)
(*       inversion H7. subst. rename n into vx.  *)
(*       assert (vx = Zfloor vy) as ->. *)
(*       * symmetry. apply Zfloor_eq. lra. *)
(*       * constructor. lra. *)
(*     + exfalso. subst. eapply H. simpl. constructor. *)
(* Qed. *)

Lemma ffloor_spec {σ} x y : feval σ <! ⌜x ∈ₜ ℤ⌝ ∧ ⌜y ∈ₜ ℝ⌝ !> → <! ⌜x = ⌊y⌋⌝ !> ≡_{σ} <! ⌜x ≤ y < x + 1⌝ !>.
Proof with auto.
  intros Hnum. simp feval in Hnum. destruct Hnum as [Hx Hy]. split; intros.
  - inversion H. destruct H0 as []. inversion H1. subst. inversion H4. subst.
    inversion H8. subst. clear H H1 H4 H8. inversion H6; clear H6.
    + simpl in *. subst. inversion H. clear H. subst. simp feval. split.
      * econstructor. Unshelve. 2: exact [mkInt i; mkNum r]. split; [by_constructor|].
        unfold peval. intros. rewrite list_to_vec_2_canon. clear H. simpl. constructor.
        lra.
      * econstructor. Unshelve. 2: exact [mkNum r; mkNum (IZR i + 1)]. split.
        -- by_constructor. unfold term_sum. econstructor. Unshelve. 3: exact [mkInt i; mkInt 1].
           ++ by_constructor.
           ++ by_constructor.
        -- simpl. unfold peval. intros. rewrite list_to_vec_2_canon. clear H. simpl.
           constructor. lra.
    + subst. simpl in H. exfalso. inversion Hy. simpl in H1. destruct H1.
      apply teval_det with (v1:=v) in H1... subst x0. inversion H2. subst v. eapply (H _).
      constructor. Unshelve. 2: exact (Zfloor r). apply Zfloor_bound.
  - simp feval in H. destruct H as []. simp feval. inversion H. destruct H1. inversion H1.
    clear H1; subst. inversion H7; subst. clear H7. inversion H8. subst. clear H8.
    unfold peval in H2. simpl in H2. specialize (H2 eq_refl). rewrite list_to_vec_2_canon in H2.
    inversion H2. subst. rename r2 into vy. rename r1 into vx. clear H.
    inversion H0; clear H0; subst. inversion H; clear H; subst. inversion H0; subst; clear H0.
    inversion H9; subst; clear H9. inversion H10; subst; clear H10.
    unfold term_sum in H6. inversion H6. subst. inversion H8; subst; clear H8.
    inversion H12; clear H12; subst. inversion H13; clear H13; subst. inversion H8.
    subst. clear H8. apply teval_det with (v1:=mkNum vx) in H9... subst v1. inversion H10.
    + subst. simpl in H. inversion H. subst. unfold peval in H1. simpl in H1.
      specialize (H1 eq_refl). inversion H1. subst. apply teval_det with (v1:=mkNum vy) in H7...
      apply mkNum_eq in H7. subst r1. econstructor. split; [exact H5|]. econstructor.
      Unshelve. 3: exact [mkNum vy]. 1: by_constructor. unfold fn_eval. simpl.
      constructor.
      inversion Hx. destruct H0. apply teval_det with (v1:=mkNum vx) in H0... subst x0.
      inversion H7. subst. rename n into vx.
      assert (vx = Zfloor vy) as ->.
      * symmetry. apply Zfloor_eq. lra.
      * constructor. lra.
    + exfalso. subst. eapply H. simpl. constructor.
Qed.

Lemma initial_var_of_eq {x y} :
  initial_var_of x = y → var_is_initial y.
Proof.
  intros. unfold var_is_initial. destruct y. destruct x. unfold initial_var_of in H.
  simpl in H. inversion H. done.
Qed.

Hint Extern 10 => match goal with A : final_formula _, H : ¬ formula_final _ |- _ => solve [destruct (H (final_formula_final A))] end : core.

Lemma IsNat_IsInt {σ} (t : Term) : afeval σ (AT_HasType t TNat) → afeval σ (AT_HasType t TInt).
Proof.
  inversion 1. destruct H0. inversion H1. subst. econstructor. split; [exact H0|].
  apply IsInt with (n:=Z.of_nat n). apply INR_IZR_INZ.
Qed.

Lemma IsInt_IsReal {σ} (t : Term) : afeval σ (AT_HasType t TInt) → afeval σ (AT_HasType t TReal).
Proof.
  inversion 1. destruct H0. inversion H1. subst. econstructor. split; [exact H0|].
  constructor.
Qed.

Lemma IsNat_IsReal {σ} (t : Term) : afeval σ (AT_HasType t TNat) → afeval σ (AT_HasType t TReal).
Proof.
  inversion 1. destruct H0. inversion H1. subst. econstructor. split; [exact H0|].
  constructor.
Qed.

Lemma term_floor_reducible_real {σ} (t : Term) (r : R) : teval σ t (mkNum r) → teval σ (term_floor t) (mkNum (IZR (Zfloor r))).
Proof.
  intros. unfold term_floor. econstructor. Unshelve. 3: exact [mkNum r].
  - by_constructor.
  - do 2 constructor. pose proof Zfloor_bound. apply H0.
Qed.

Lemma term_floor_inv {σ} (t : Term) v : teval σ (term_floor t) v → (∃ r, teval σ t (mkNum r) ∧ v = mkNum (IZR (Zfloor r))) ∨ v = ⊥.
Proof with auto.
  intros. unfold term_floor. inversion H. subst. inversion H4.
  - subst. inversion H0. subst. left. exists r. inversion H2. subst. split...
    do 2 f_equal. symmetry. apply Zfloor_eq...
  - right...
Qed.

Lemma term_floor_typing {σ} (t: Term) : afeval σ (AT_HasType t TReal) → afeval σ (AT_HasType (term_floor t) TInt).
Proof.
  inversion 1. destruct H0. inversion H1. subst. pose proof (@term_floor_reducible_real σ t r H0).
  econstructor. split; [exact H2|]. eapply IsInt. reflexivity.
Qed.

Lemma term_sqrt_reducible {σ} (t : Term) (r : R) : (0 <= r)%R → teval σ t (mkNum r) → teval σ (term_sqrt t) (mkNum (sqrt r)).
Proof.
  intros. econstructor. Unshelve. 3: exact [mkNum r].
  - by_constructor.
  - do 2 constructor.
    + apply sqrt_pos.
    + by apply pow2_sqrt.
Qed.

Lemma term_sqrt_typing_nat {σ} (t : Term) : afeval σ (AT_HasType t TNat) → afeval σ (AT_HasType (term_sqrt t) TReal).
Proof.
  inversion 1. destruct H0. inversion H1. subst. epose proof (@term_sqrt_reducible σ t (INR n) _ H0).
  econstructor. split; [exact H2|]. constructor.
  Unshelve. apply pos_INR.
Qed.

Global Instance set_unfold_simpl_initial_var_of_eq_final {x y} : SetUnfoldSimpl (initial_var_of x = as_var y) False.
Proof. do 2 constructor. done. Qed.

Global Instance set_unfold_elem_of_initial_var_of_final_formula_fvars {M} {x} {A : final_formula M}
  : SetUnfoldElemOf (initial_var_of x) (formula_fvars A) False.
Proof.
  constructor. split; [|done]. intros. apply initial_var_of_elem_of_formula_fvars in H.
  destruct (H (final_formula_final A)).
Qed.

(* Global Instance set_simpl_or_false {A B} : SetUnfold A B → SetUnfold (A ∨ False) B | 0. *)
(* Proof. firstorder. Qed. *)

Lemma simpl_feval_and {M σ} {A B : formula M} : feval σ <! A ∧ B !> ↔ feval σ A ∧ feval σ B.
Proof. simp feval. reflexivity. Qed.

Lemma r2 : spec ≡ prog2.
Proof with auto.
  unfold spec, prog2. intros A. simpl.
  rewrite f_subst_initials_no_initials.
  2:{ simpl. set_unfold. intros. destruct H... set_solver. }
  rewrite f_subst_initials_no_initials.
  2:{ simpl. set_unfold. intros. destruct H... set_solver. }
  intros σ. split; intros.
  - unfold FForallT in *. rewrite simpl_feval_fforall in H |- *. intros. specialize (H v).
    rewrite @feval_subst with (M:=Model) (v:=v) in H |- *...
    rewrite simpl_feval_fimpl in H |- *. intros. specialize (H H0).
    rewrite simpl_feval_fforall in H |- *. intros. specialize (H v0).
    rewrite @feval_subst with (M:=Model) (v:=v0) in H |- *...
    rewrite simpl_feval_fimpl in H |- *. intros. specialize (H H1).
    simp feval in *. split; [constructor|]. destruct H as [_ ?].
    rewrite simpl_feval_fforall in H |- *. intros. specialize (H v1).
    rewrite @feval_subst in H |- *...
    rewrite simpl_feval_fimpl in H |- *. intros. apply H.
    rewrite simpl_feval_and. simp feval in H2. destruct H2. split... apply ffloor_spec...
    simp feval. split.
    + apply IsNat_IsInt...
    + apply term_sqrt_typing_nat. apply afeval_delete_state_var_head; [set_solver|]...
  - unfold FForallT in *. rewrite simpl_feval_fforall in H |- *. intros. specialize (H v).
    rewrite @feval_subst with (M:=Model) (v:=v) in H |- *...
    rewrite simpl_feval_fimpl in H |- *. intros. specialize (H H0).
    rewrite simpl_feval_fforall in H |- *. intros. specialize (H v0).
    rewrite @feval_subst with (M:=Model) (v:=v0) in H |- *...
    rewrite simpl_feval_fimpl in H |- *. intros. specialize (H H1).
    simp feval in *. split; [constructor|]. destruct H as [_ ?].
    rewrite simpl_feval_fforall in H |- *. intros. specialize (H v1).
    rewrite @feval_subst in H |- *...
    rewrite simpl_feval_fimpl in H |- *. intros. apply H.
    rewrite simpl_feval_and. simp feval in H2. destruct H2. split... apply ffloor_spec...
    simp feval. split.
    + apply IsNat_IsInt...
    + apply term_sqrt_typing_nat. apply afeval_delete_state_var_head; [set_solver|]...
Qed.
