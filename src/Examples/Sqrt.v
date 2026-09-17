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
Definition I : Formula := <! ⌜q ∈ₜ ℕ⌝ ∧ ⌜r ∈ₜ ℕ⌝ ∧ ⌜r² ≤ s < q²⌝ !>.
Definition prog3 : Prog :=
  <{ |[ var r s q : ℕ ⦁
                      q, r : [I ∧ ⌜r+1 = q⌝] ]| }>.
Definition prog4 : Prog :=
  <{ |[ var r s q : ℕ ⦁
                      q, r : [I];
                      q, r : [I, I ∧ ⌜r+1 = q⌝] ]| }>.
Definition prog5 : Prog :=
  <{ |[ var r s q : ℕ ⦁
                      q, r := s + 1, 0;
                      q, r : [I, I ∧ ⌜r+1 = q⌝] ]| }>.

Program Definition V : final_term Model := {| as_term := term_sub q r |}.
Next Obligation. unfold term_final. set_solver. Qed.

Definition prog6 : Prog :=
  <{ |[ var r s q : ℕ ⦁
          q, r := s + 1, 0;
          while ⌜r + 1 ≠ q⌝ invariant I variant V ⟶
            q, r : [⌜r + 1 ≠ q⌝ ∧ I, I ∧ ⌜0 ≤ q - r < ₀q - ₀r⌝]
          end
        ]| }>.

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

(* Definition I := <! ⌜r² ≤ s < q²⌝ !>. *)

  (* ∀ (v : value Model) (A : final_formula Model) (σ : state Model), *)
  (*   (<[x:=v]> σ ⊨ ⌜ x ∈ₜ ty ⌝ ⇒ (wp p1 A)) → <[x:=v]> σ ⊨ ⌜ x ∈ₜ ty ⌝ ⇒ (wp p2 A) *)
(* Lemma r_var (x : final_variable) τ p1 p2 : *)
(*   (∀ v σ A, *)
(*     feval (<[as_var x:=v]> σ) <! ⌜x ∈ₜ τ⌝ ⇒ $(wp p1 A) !> → *)
(*     feval (<[as_var x:=v]> σ) <! ⌜x ∈ₜ τ⌝ ⇒ $(wp p2 A) !>) → *)
(*   <{ |[ var x : τ ⦁ $p1 ]| }> ⊑ <{ |[ var x : τ ⦁ $p2 ]| }>. *)
(* Proof with auto. *)
(*   intros H0 A σ. simpl. intros. unfold FForallT in H |- *. *)
(*   rewrite simpl_feval_fforall in H |- *. intros. specialize (H v). *)
(*   rewrite feval_subst with (v:=v) in H... *)
(*   rewrite feval_subst with (v:=v)... *)
(* Qed. *)

Lemma r_var (x : final_variable) (τ : value_ty Model) p1 p2 A σ :
  (∀ v,
    HasType v τ →
    feval (<[as_var x:=v]> σ) <! $(wp p1 A) !> →
    feval (<[as_var x:=v]> σ) <! $(wp p2 A) !>) →
  feval σ (wp <{ |[ var x : τ ⦁ $p1 ]| }> A) → feval σ (wp <{ |[ var x : τ ⦁ $p2 ]| }> A).
Proof with auto.
  intros H0. simpl. intros. unfold FForallT in H |- *.
  rewrite simpl_feval_fforall in H |- *. intros. specialize (H v).
  rewrite feval_subst with (v:=v) in H... rewrite feval_subst with (v:=v)...
  rewrite simpl_feval_fimpl in H |- *. intros. specialize (H H1). apply H0...
  inversion H1. destruct H2. apply teval_det with (v1:=v) in H2.
  2:{ constructor. unfold state. apply fin_maps.lookup_total_insert. }
  subst...
Qed.

(* Lemma r_impl A p1 p2  *)

Hint Extern 0 (?A ⇚ ?A) => reflexivity : core.
Parameter q_free : ∀ (F : gmap.gset variable), as_var q ∉ F.

(* Axiom q_free_wp : ∀ p A, as_var q ∉ prog_fvars p → as_var q ∉ formula_fvars (wp p A). *)

Lemma r_add_var (x : final_variable) (τ : value_ty Model) {p} {σ A} :
  as_var x ∉ formula_fvars (wp p A) →
  feval σ (wp p A) → feval σ (wp <{ |[ var x : τ ⦁ $p ]| }> A).
Proof with auto.
  intros. simpl. unfold FForallT. rewrite simpl_feval_fforall. intros.
  rewrite feval_subst with (v:=v)... rewrite simpl_feval_fimpl. intros.
  rewrite feval_delete_state_var_head...
Qed.

Lemma r_add_frame (x : final_variable) (τ : value_ty Model) {σ y post} {A : final_formula Model} :
  x ≠ y →
  ₀x ∉ formula_fvars post →
  as_var x ∉ formula_fvars post →
  as_var x ∉ formula_fvars A →
  feval σ (wp <{ y : [post] }> A) → feval σ (wp <{ x, y : [⌜x ∈ₜ τ⌝ ∧ post] }> A).
Proof with auto.
  intros. simpl in *. simp feval in H3 |- *. destruct H3 as []. split...
  unfold subst_initials in *. simpl in H4 |- *.
  destruct (teval_total σ (y)) as [vy Hvy]. rewrite feval_subst with (v:=vy) in H4...
  destruct (teval_total σ (x)) as [vx Hvx]. rewrite feval_subst with (v:=vx)...
  destruct (teval_total (<[₀x:=vx]> σ) (y)) as [vy' Hvy']. rewrite feval_subst with (v:=vy')...
  rewrite teval_delete_state_var_head in Hvy' by set_solver.
  apply teval_det with (v1:=vy) in Hvy'... subst vy'.
  rewrite simpl_feval_fforall. intros. rewrite feval_subst with (v:=v)...
  rewrite simpl_feval_fforall in H4 |- *. intros. specialize (H4 v0).
  rewrite feval_subst with (v:=v0)... rewrite feval_subst with (v:=v0) in H4...
  rewrite simpl_feval_fimpl. intros. rewrite simpl_feval_fimpl in H4.
  rewrite simpl_feval_and in H5. destruct H5 as [_ ?].
  unfold state in *.
  rewrite (fin_maps.insert_commute _ (as_var y) (as_var x)) in H5 |- * by set_solver.
  rewrite feval_delete_state_var_head...
  rewrite feval_delete_state_var_head in H5 by set_solver...
  rewrite (fin_maps.insert_commute _ ₀y ₀x) in H5 |- * by set_solver.
  rewrite (fin_maps.insert_commute _ (as_var y) ₀x) in H5 |- * by set_solver.
  rewrite feval_delete_state_var_head by set_solver.
  rewrite feval_delete_state_var_head in H5 by set_solver...
Qed.

Global Instance PVar_proper_ref : Proper ((=) ==> (=) ==> (⊑) ==> (⊑)) PVar.
Proof. intros x ? <- ty ? <- A B ? C. simpl. rewrite (H C). reflexivity. Qed.

Global Instance PSeq_proper_ref : Proper ((⊑) ==> (⊑) ==> (⊑)) PSeq.
Proof.
  admit.
Admitted.

Lemma r4 : prog2 ⊑ prog3.
Proof with auto.
  unfold prog2, prog3, I. intros A σ. apply r_var. intros vr Hvr. apply r_var. intros vs Hvs.
  intros.
  opose proof (r_add_frame q ℕ _ _ _ _ H); try set_solver.
  { apply q_free. }
  simpl. apply simpl_feval_fforall. intros. rewrite simpl_subst_impl.
  apply simpl_feval_fimpl. intros. rewrite simpl_subst_and. apply simpl_feval_and.
  split.
  1: { constructor. }
  rewrite f_subst_initials_no_initials.
  2:{ simpl. set_unfold. intros. destruct_or! H2...
      + subst. set_solver.
      + subst. set_solver. }
  rewrite fequiv_subst_non_free.
  2: { simpl. set_solver. }
  simpl in H0. rewrite f_subst_initials_no_initials in H0.
  2:{ simpl. set_unfold. intros. destruct_or! H2...
      + subst. set_solver.
      + subst. set_solver. }
  simp feval in H0. destruct H0 as [_ ?]. rewrite simpl_feval_fforall in H0 |- *.
  intros. specialize (H0 v0).
  rewrite feval_subst with (v:=v0)...
  rewrite feval_subst with (v:=v0) in H0...
  rewrite simpl_feval_fforall in H0 |- *. intros. specialize (H0 v1).
  rewrite feval_subst with (v:=v1)...
  rewrite feval_subst with (v:=v1) in H0...
  rewrite simpl_feval_fimpl in H0 |- *. intros. apply H0.
  simp feval. simp feval in H2. destruct_and! H2. split_and!... simpl in H4.
  destruct H4 as (r1&?&?). unfold term_lt. simpl. simp feval. simpl. clear H0 H1 H3 H2 H5 H.
  destruct H7 as (vs'&?&?). inversion H. subst. inversion H7. subst. inversion H9; subst.
  clear H9 H7. rename v3 into q2. rename v2 into vs'. exists [vs'; q2].
  split... constructor... constructor. 2: constructor. clear H H3.
  unfold term_pow2 in *. simpl. simpl in H5. inversion H5. subst. inversion H2. subst.
  inversion H9. subst. inversion H11; subst. clear H11. inversion H8. subst.
  clear H9. clear H2. opose proof (teval_det _ _ _ H6 H3) as <-. clear H3.
  apply TEval_App with (vargs:=[r1; mkNum (1 + 1)])...
  by_constructor.
Qed.


Lemma r5 : prog3 ⊑ prog4.
Proof with auto.
  unfold prog3, prog4. repeat (apply PVar_proper_ref; auto). apply r_seq. unfold I...
Qed.

Lemma r_asgn_2 (x y : final_variable) (pre post : Formula) (t1 t2 : Term) `{!FormulaFinal pre} `{!TermFinal t1} `{!TermFinal t2} :
  x ≠ y →
  <! ⌜₀x = x⌝ ∧ ⌜₀y = y⌝ ∧ pre !> ⇛ <! post[[$(as_var x), $(as_var y) \ t1, t2]] !> ->
  <{ x, y : [pre, post] }> ⊑ <{ x, y := t1, t2 }>.
Proof with auto.
  intros.
  etransitivity.
  - apply r_assignment with (w:=[]) (ts:=[as_final_term t1; as_final_term t2])...
    + constructor; try set_solver. constructor; try set_solver. constructor.
    + intros σ ?. specialize (H0 σ). simp feval in H1, H0. simpl in H1. forward H0.
      * destruct H1 as (_&?&?). unfold FEqList in H1. simpl in H1.
        simp feval in H1. destruct_and! H1. split_and!...
      * simpl. apply H0.
  - simpl...
Qed.

(* Lemma r_asgn_2' σ (x y : final_variable) (pre post : Formula) (t1 t2 : Term) `{!FormulaFinal pre} `{!TermFinal t1} `{!TermFinal t2} : *)
(*   x ≠ y → *)
(*   (feval σ <! ⌜₀x = x⌝ ∧ ⌜₀y = y⌝ ∧ pre !> → feval σ <! post[[$(as_var x), $(as_var y) \ t1, t2]] !>) -> *)
(*   ∀ A, feval σ (wp <{ x, y : [pre, post] }> A) → feval σ (wp <{ x, y := t1, t2 }> A). *)
(* Proof with auto. *)
(*   intros. pose proof (r_asgn_2 x y pre post t1 t2 H). unfold sqsubseteq in H2. *)
(*   unfold refines in H2. forward H2. *)
(*   { intros σ'. } *)
(*   apply H2. *)
(*   intros. *)
(*   etransitivity. *)
(*   - apply r_assignment with (w:=[]) (ts:=[as_final_term t1; as_final_term t2])... *)
(*     + constructor; try set_solver. constructor; try set_solver. constructor. *)
(*     + intros σ ?. specialize (H0 σ). simp feval in H1, H0. simpl in H1. forward H0. *)
(*       * destruct H1 as (_&?&?). unfold FEqList in H1. simpl in H1. *)
(*         simp feval in H1. destruct_and! H1. split_and!... *)
(*       * simpl. apply H0. *)
(*   - simpl... *)
(* Qed. *)

Lemma r_asgn_1 (x : final_variable) (pre post : Formula) (t : Term) `{!FormulaFinal pre} `{!TermFinal t} :
  <! ⌜₀x = x⌝ ∧ pre !> ⇛ <! post[x \ t] !> ->
  <{ x : [pre, post] }> ⊑ <{ x := t }>.
Proof with auto.
  intros.
  etransitivity.
  - apply r_assignment with (w:=[]) (ts:=[as_final_term t])...
    + constructor; try set_solver. constructor; try set_solver.
    + intros σ ?. specialize (H σ). simpl. apply msubst_single. apply H. clear H.
      simp feval in H0. destruct_and! H0. unfold FEqList in H0. simpl in H0.
      simp feval in H0. destruct H0. simp feval. split...
  - simpl...
Qed.

Lemma pvar_ref (x : final_variable) t (p1 p2 : Prog) A σ :
  (∀ v, hastype Model v t → feval (<[as_var x:=v]> σ) (wp p1 A) → feval (<[as_var x:=v]> σ) (wp p2 A)) →
  (feval σ (wp <{ |[ var x : t ⦁ $p1 ]| }> A) → feval σ (wp <{ |[ var x : t ⦁ $p2 ]| }> A)).
Proof with auto.
  intros. simpl in *. unfold FForallT in *. rewrite simpl_feval_fforall in *.
  intros. specialize (H0 v). rewrite feval_subst with (v:=v)...
  rewrite feval_subst with (v:=v) in H0... rewrite simpl_feval_fimpl in *.
  intros. specialize (H0 H1). apply (H v)...
  simp feval in H1. simpl in H1. destruct H1 as (v'&?&?). enough (v = v') as -> by auto.
  inversion H1. subst. symmetry. unfold state. apply fin_maps.lookup_total_insert.
Qed.

Lemma r_var_spec (x : final_variable) ty (pre post : Formula) `{!FormulaFinal pre} w p2:
  <{ |[ var x : ty ⦁ *w : [pre, post]; $p2 ]| }> ≡ <{ |[ var x : ty ⦁ *w : [⌜x ∈ₜ ty⌝ ∧ pre, post]; $p2 ]| }>.
Proof with auto.
  intros A. simpl. simpl. apply fforall_proper... intros σ. split; intros.
  - rewrite simpl_feval_fimpl in *. intros. specialize (H H0). simp feval in *.
    destruct_and! H. split_and!...
  - rewrite simpl_feval_fimpl in *. intros. specialize (H H0). simp feval in *.
    destruct_and! H. split_and!...
Qed.

Lemma feval_forall_equiv_if {σ1 σ2 x1 x2} {A1 A2 : Formula}:
  (∀ v, feval σ1 (<! A1 [x1 \ $(TConst v) ] !>) ↔ feval σ2 (<! A2 [x2 \ $(TConst v) ] !>)) →
  feval σ1 <! ∀ x1, A1 !> ↔ feval σ2 <! ∀ x2, A2 !>.
Proof with auto.
  intros. unfold FForall. simp feval. f_equiv. repeat setoid_rewrite simpl_subst_not.
  split; intros [v Hv]; exists v.
  - simp feval in *. intros contra. apply H in contra. done.
  - simp feval in *. intros contra. apply H in contra. done.
Qed.

Lemma feval_forallt_equiv_if {σ1 σ2} {x1 x2 : variable} {A1 A2 : Formula} {ty}:
  (∀ v, feval σ1 (<! (⌜x1 ∈ₜ ty⌝ ⇒ A1) [x1 \ $(TConst v) ] !>) ↔ feval σ2 (<! (⌜x2 ∈ₜ ty⌝ ⇒ A2) [x2 \ $(TConst v) ] !>)) →
  feval σ1 <! ∀ x1 : ty, A1 !> ↔ feval σ2 <! ∀ x2 : ty, A2 !>.
Proof with auto.
  intros. unfold FForallT. apply feval_forall_equiv_if. intros.
  simp feval.
Qed.

Local Lemma r_var_permute_2_ref x y ty p :
  <{ |[ var x y : ty ⦁ $p ]| }> ⊑ <{ |[ var y x : ty ⦁ $p ]| }>.
Proof with auto.
  destruct (decide (x = y)); [subst; auto|].
  unfold equiv, pequiv. simpl. intros A. intros σ ?. simpl in *.
  unfold FForallT in *. rewrite simpl_feval_fforall in *. intros vy.
  rewrite feval_subst with (v:=vy)... rewrite simpl_feval_fimpl. intros.
  rewrite simpl_feval_fforall. intros vx. rewrite feval_subst with (v:=vx)...
  rewrite simpl_feval_fimpl. intros. unfold state in *.
  rewrite fin_maps.insert_commute...
  2: { intros contra. apply as_var_inj in contra. subst. done. }
  inversion H0. destruct H2 as []. inversion H2. subst.
  inversion H1. destruct H4 as []. inversion H4. subst.
  unfold state in *. rewrite fin_maps.lookup_total_insert in *.
  specialize (H vx). rewrite feval_subst with (v:=vx) in H...
  rewrite simpl_feval_fimpl in H. forward H.
  { simp feval. simpl. exists vx. split... constructor.
    unfold state in *. apply fin_maps.lookup_total_insert. }
  rewrite simpl_feval_fforall in H. specialize (H vy).
  rewrite feval_subst with (v:=vy) in H... rewrite simpl_feval_fimpl in H.
  forward H... simp feval. simpl. exists vy. split... constructor.
    unfold state in *. apply fin_maps.lookup_total_insert.
Qed.

Lemma r_var_permute_2 x y ty p :
  <{ |[ var x y : ty ⦁ $p ]| }> ≡ <{ |[ var y x : ty ⦁ $p ]| }>.
Proof with auto.
  unfold equiv, pequiv. intros. split; apply r_var_permute_2_ref.
Qed.

Lemma r6 : prog4 ⊑ prog5.
Proof with auto.
  unfold prog4, prog5. rewrite (r_var_permute_2 s q). rewrite (r_var_permute_2 s q).
  rewrite r_var_spec.
  rewrite r_asgn_2; [done|done|].
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

Lemma PWhile_equiv g1 g2 I1 I2 v p1 p2 :
  g1 ≡ g2 →
  I1 ≡ I2 →
  Δ p1 = Δ p2 →
  p1 ≡ p2 →
  PWhile g1 I1 v p1 ≡ PWhile g2 I2 v p2.
Proof with auto.
  (* intros. rewrite H. rewrite H0. clear H g1 H0 I1. intros A. simpl. rewrite H1.  *)
  (* f_equiv. f_equiv... *)
  (* - admit. *)
  (* - f_equiv. f_equiv. f_equiv. opose proof wp_proper_pequiv. *)
  (*   specialize (H p1 p2 H2). simpl in *. Unshelve. *)
  (*   2:{ exact <!! ⌜ v < $(to_initial_var (fresh_var String.EmptyString (Δ p2))) ⌝ !!>. } *)

  (* 2:{ repeat f_equiv. } *)
  (* repeat f_equiv. *)
  admit.
Admitted.

(* Global Instance PWhile_proper : Proper ((≡) ==> (≡@{final_formula}) ==> (=) ==> (=) ==> (≡)) PWhile. *)
(* Proof. *)
(*   intros g1 g2 ? I1 I2 ? v ? <- p ? <-. intros A. simpl. unfold equiv,ffequiv in H0. *)
(*   rewrite H0. unfold equiv,ffequiv in H. rewrite H. done. *)
(* Qed. *)
Lemma Rle_0_minus : forall (r1 r2 : R), (0 <= r2 - r1)%R ↔ (r1 <= r2)%R.
Proof.
  intros r1 r2; split.
  - intros. apply Rge_le. apply Rminus_ge. apply Rle_ge. assumption.
  - intros. apply Rge_le. apply Rge_minus. apply Rle_ge. assumption.
Qed.

Lemma r7 : prog5 ⊑ prog6.
Proof with auto.
  unfold prog5, prog6. repeat f_equiv. simpl.
  opose proof (r_iteration' [q; r] <!! ⌜r+1≠q⌝ !!> (as_final_formula I)
                                              <!! I ∧ ⌜q - r ∈ₜ TNat⌝ !!>
                                              <!! I ∧ ⌜r + 1 = q⌝ !!>
                                              V).
  simpl in H.
  etrans.
  - simpl. apply H.
    + by_constructor; try set_solver.
    + unfold I. unfold equiv, ffequiv. simpl. intros σ. simp feval. clear H.
      split; intros H; destruct_and! H; split_and!...

      simpl in *. destruct H0 as (vq&?&?). inversion H2. subst. rename n into nq.
      destruct H as (vr&?&?). inversion H4. subst. rename n into nr. exists (mkNat (nq - nr)).
      split.
      * unfold term_sub. apply TEval_App with (vargs:=[mkNat nq; mkNat nr]).
        -- by_constructor.
        -- unfold sub_sym. unfold fn_eval. constructor. simpl.
           assert (INR (nq - nr) = (INR nq - INR nr)%R).
           { rewrite minus_INR...  }
      * apply IsNat with (n:=nq-nr)...




      admit.
    + simpl. fSimpl.
  - unfold to_vtmap. simpl. rewrite fin_maps.lookup_insert.
    rewrite fin_maps.insert_commute... rewrite fin_maps.lookup_insert. simpl.
    apply pequiv_refines. apply PWhile_equiv...
    + unfold equiv, ffequiv. clear H. simpl. intros σ. simp feval.
      split; intros; destruct_and! H; split_and!...
    + clear H. f_equiv.
      * unfold equiv, ffequiv. simpl. fSimpl.
      * simpl. unfold term_sub at 5.
        intros σ. unfold I. simp feval. split; intros; destruct_and! H; split_and!...
        clear H2 H4 H5. inversion H3. clear H3. destruct H1 as [].
        inversion H1. clear H1. subst. inversion H7. subst. clear H7. inversion H8. clear H8.
        subst. inversion H5. subst. clear H5. unfold term_sub in *. unfold sub_sym in *.
        simpl. exists v0. split... inversion H4. subst. unfold fn_eval in H7. inversion H7.
        -- subst v0 args. inversion H5. subst; clear H5. inversion H10; subst; clear H10.
           inversion H11; subst; clear H11. simpl in H1. inversion H1. subst.
           rename r1 into vq, r7 into vr. clear H7 H1 H4. simpl in H2. unfold peval in H2.
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
