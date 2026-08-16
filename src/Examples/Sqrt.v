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
Definition prog1 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r ≤ √ s < r + 1⌝] ]| }>.
Definition prog2 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r ∈ₜ ℕ⌝ ∧ ⌜r² ≤ s < (r + 1)²⌝] ]| }>.

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

Ltac by_constructor := repeat (constructor; auto).

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

Lemma term_sqrt_reducible_nat {σ} (t : Term) (n : nat) : teval σ t (mkNat n) → teval σ (term_sqrt t) (mkNum (sqrt (INR n))).
Proof.
  apply term_sqrt_reducible. apply pos_INR.
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

Lemma r2 : spec ≡ prog1.
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

Lemma is_nat_iff {σ} {t : Term} :
  afeval σ (AT_HasType t TNat) ↔ ∃ n, teval σ t (mkNat n).
Proof.
  split; intros.
  - intros. simpl in H. destruct H as [v []]. inversion H0. subst. exists n. done.
  - destruct H as [n ?]. simpl. exists (mkNat n). split; try done. apply IsNat with (n:=n).
    reflexivity.
Qed.

Lemma pow2_le_inv {a b} : (0 <= a)%R → (a <= b)%R → (a ^ 2 <= b ^ 2)%R.
Proof with auto. intros. by apply pow_incr with (n:=2). Qed.

Lemma pow2_le {a b} : (0 <= a)%R → (0 <= b)%R → (a ^ 2 <= b ^ 2)%R → (a <= b)%R.
Proof with auto.
  intros. apply sqrt_le_1 in H1. 2-3: apply pow2_ge_0. do 2 rewrite sqrt_pow2 in H1...
Qed.

Lemma pow2_lt {a b} : (0 <= a)%R → (0 <= b)%R → (a ^ 2 < b ^ 2)%R → (a < b)%R.
Proof with auto.
  intros. apply sqrt_lt_1 in H1. 2-3: apply pow2_ge_0. do 2 rewrite sqrt_pow2 in H1...
Qed.

Hint Extern 0 (0 <= INR _)%R => apply pos_INR : core.
Hint Extern 0 (0 <= sqrt _)%R => apply sqrt_pos : core.

Lemma r3 : prog1 ⊑ prog2.
Proof with auto.
  unfold spec, prog2. intros A. simpl.
  rewrite f_subst_initials_no_initials.
  2:{ simpl. set_unfold. intros. destruct H... set_solver. }
  rewrite f_subst_initials_no_initials.
  2:{ simpl. set_unfold. intros. destruct H... set_solver. }
  intros σ. intros.
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
    rewrite simpl_feval_and. simp feval in H2. destruct H2. split...
    rewrite simpl_feval_and.
    rewrite <- @afeval_delete_state_var_head with (x:=as_var r) (v:=v1) in H1 by done.
    destruct (proj1 is_nat_iff H1) as [n Hn].
    remember (<[as_var r:=v1]> (<[as_var s:=v0]> (<[as_var r:=v]> σ))) as σ'.
    pose proof (@term_sqrt_reducible_nat σ' s n Hn).
    destruct (proj1 is_nat_iff H2) as [nr Hnr].
    split.
    + unfold term_le. simpl. econstructor. Unshelve. 2: exact [mkNat nr; mkNum (sqrt (INR n))].
      split; [by_constructor|]. unfold peval. intros. rewrite list_to_vec_2_canon. clear H5.
      constructor. rename n into ns. destruct H3 as [? _].
      inversion H3. clear H3. destruct H5. inversion H3. subst t ts x. clear H3.
      inversion H10. subst t ts vs. clear H10. inversion H11. subst vs0. clear H11.
      apply teval_det with (v1:=mkNat ns) in H7... subst v3.
      assert (teval σ' (term_pow2 r) (mkNum (pow (INR nr) 2))).
      { unfold term_pow2. econstructor. Unshelve. 3: exact [mkNat nr; mkNat 2].
        all: by_constructor. }
      apply teval_det with (v1:=v2) in H3... subst v2. unfold peval in H5.
      simpl in H5. specialize (H5 eq_refl). rewrite list_to_vec_2_canon in H5.
      inversion H5. subst r1 r3. apply pow2_le... rewrite pow2_sqrt...
    + unfold term_le. simpl. econstructor. Unshelve. 2: exact [mkNum (sqrt (INR n)); mkNat (nr + 1)].
      split; [by_constructor|].
      { unfold term_sum. econstructor. Unshelve. 3: exact [mkNat nr; mkNat 1]. 1: by_constructor.
        by_constructor. simpl. unfold mkNat. rewrite plus_INR. done. }
      unfold peval. intros. rewrite list_to_vec_2_canon. clear H5.
      constructor. rename n into ns. destruct H3 as [_ ?].
      inversion H3. clear H3. destruct H5. inversion H3. subst t ts x. clear H3.
      inversion H10. subst t ts vs. clear H10. inversion H11. subst vs0. clear H11.
      apply teval_det with (v1:=mkNat ((nr + 1) ^ 2)) in H7...
      2: { unfold term_sum. unfold term_pow2. simpl. econstructor. Unshelve.
           3: exact [mkNat (nr + 1); mkNat 2].
           - by_constructor. econstructor. Unshelve. 3: exact [mkNat nr; mkNat 1].
             + by_constructor.
             + by_constructor. simpl. unfold mkNat. rewrite plus_INR. done.
           - replace ((nr + 1) * ((nr + 1) * 1)) with ((nr + 1) ^ 2); try done.
             constructor. unfold mkNat. rewrite pow_INR... done. }
      subst v3. apply teval_det with (v1:=mkNat ns) in H8... subst v2. unfold peval in H5.
      simpl in H5. specialize (H5 eq_refl). rewrite list_to_vec_2_canon in H5.
      inversion H5. subst r1 r3. apply pow2_lt... rewrite pow2_sqrt... simpl.
      rewrite mult_INR in H6. rewrite mult_INR in H6. done.
Qed.
