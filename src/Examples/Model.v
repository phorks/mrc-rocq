From Stdlib Require Import Reals ZArith Sorting.
From stdpp Require Import listset vector.
From MRC Require Export PredCalc Comparable ListBag Prelude Tactics Stdppp.

Notation compare := Comparable.compare.

Inductive ValueRaw :=
  | VUnit
  | VNum (r : R)
  | VStr (s : String.string)
  (* | VPair (v1 v2 : ValueRaw) *)
  | VSeq (l : list ValueRaw)
  | VBag (b : listbag ValueRaw)
  | VUnknown.

Fixpoint vraw_eq_dec (x y : ValueRaw) : {x = y} + {x <> y}.
Proof.
  decide equality; try solve_trivial_decision.
  - eapply list_eq_dec. Unshelve. unfold EqDecision, Decision. apply vraw_eq_dec.
  - destruct b as [l1], b0 as [l2]. assert (Decision (l1 = l2)).
    { eapply list_eq_dec. Unshelve. unfold EqDecision, Decision. apply vraw_eq_dec. }
    destruct H.
    + left. by f_equal.
    + right. intros contra. by inversion contra.
Defined.

Global Instance ValueRaw_EqDecision : EqDecision ValueRaw.
Proof.
  unfold EqDecision, Decision. apply vraw_eq_dec.
Qed.

Definition vraw_eqb (x y : ValueRaw) : bool := bool_decide (x = y).


Section vraw_compare.
  Local Definition vraw_constructor_idx (v : ValueRaw) : nat :=
    match v with
    | VUnit => 0
    | VNum _ => 1
    | VStr _ => 2
    | VSeq _ => 3
    | VBag _ => 4
    | VUnknown => 5
    end.

  Fixpoint vraw_compare (x y : ValueRaw) : comparison :=
    match x, y with
    | VUnit, VUnit => Eq
    | VNum x, VNum y => compare x y
    | VStr s1, VStr s2 => compare s1 s2
    | VSeq l1, VSeq l2 => list_compare vraw_compare l1 l2
    | VBag l1, VBag l2 => listbag_compare vraw_compare l1 l2
    | VUnknown, VUnknown => Eq
    | x, y => compare (vraw_constructor_idx x) (vraw_constructor_idx y)
    end.

  Local Lemma compare_nat_False (x y : nat) : x ≠ y → compare x y = Eq ↔ False.
  Proof.
    unfold compare, nat_comparable. intros. destruct (x ?= y) eqn:E; try done.
    apply Nat.compare_eq_iff in E. done.
  Qed.

  Local Lemma compare_nat_True (x : nat) : compare x x = Eq ↔ True.
  Proof.
    unfold compare, nat_comparable. intros. destruct (x ?= x) eqn:E; try done.
    - apply Nat.compare_lt_iff in E. lia.
    - apply Nat.compare_gt_iff in E. lia.
  Qed.

  Lemma compare_ne {A} `{CompareEq A} {x y : A} : x ≠ y → compare x y ≠ Eq.
  Proof. intros ? contra. by apply compare_eq_iff in contra. Qed.

  Fixpoint vraw_ind' (P : ValueRaw → Prop) :
    (P VUnit) →
    (∀ x, P (VNum x)) →
    (∀ s, P (VStr s)) →
    (∀ l, (∀ x, In x l → P x) → P (VSeq l)) →
    (∀ b, (∀ x, In x (listbag_car b) → P x) → P (VBag b)) →
    (P VUnknown) →
    (∀ x, P x).
  Proof.
    intros Hunit Hnum Hstr Hseq Hbag Hunknown. destruct x; try done.
    - apply Hseq. induction l; simpl; [done|]. intros. destruct H.
      + subst x. by apply vraw_ind'.
      + by apply IHl.
    - apply Hbag. induction (listbag_car b); simpl; [done|]. intros. destruct H.
      + subst x. by apply vraw_ind'.
      + by apply IHl.
  Qed.

  Ltac vauto_aux :=
  repeat lazymatch goal with
  | |- context[?x = ?y] =>
      try solve [rewrite compare_nat_False; done]
  end.

  Ltac vauto_aux2 :=
    let H := fresh "H" in
    symmetry; etrans; [split; [injection 1; intros HH; exact HH | intros; by f_equal] |];
    symmetry; apply compare_eq_iff
  .

  Ltac vauto y :=
    destruct y; simpl; intros; vauto_aux; try solve [vauto_aux2].

  Lemma vraw_compare_eq_iff x y :
    raw_compare_eq_iff vraw_compare x y.
  Proof.
    revert y. unfold raw_compare_eq_iff. induction x using vraw_ind'; simpl; vauto y; try done.
    - symmetry. etrans.
      + split; [injection 1; intros H1; exact H1| intros; by f_equal].
      + symmetry. apply raw_list_compare_eq_iff. intros x y ??. by apply H.
    - symmetry. etrans.
      + split; [injection 1; intros H1; exact H1| intros; by f_equal].
      + symmetry. apply raw_listbag_compare_eq_iff. intros x y ??. by apply H.
  Qed.

  Ltac vauto1 y :=
    destruct y; simpl; intros;
      try first [solve [simpl; unfold compare, nat_comparable; eauto; done]
                | apply compare_total].

  Lemma vraw_compare_total x y :
    raw_compare_total vraw_compare x y.
  Proof.
    revert y. unfold raw_compare_total. induction x using vraw_ind'; simpl; vauto1 y; try done.
    - apply raw_list_compare_total.
      + apply vraw_compare_eq_iff.
      + intros ????. by apply H.
    - apply raw_listbag_compare_total.
      + apply vraw_compare_eq_iff.
      + intros ????. by apply H.
  Qed.

  Ltac vauto2 y :=
    destruct y; simpl; intros;
      try first [solve [simpl; unfold compare, nat_comparable; eauto; done]
                | apply compare_antisym].

  Lemma vraw_compare_antisym x y :
    raw_compare_antisym vraw_compare x y.
  Proof.
    revert y. unfold raw_compare_antisym. induction x using vraw_ind'; simpl; vauto2 y; try done.
    - apply raw_list_compare_antisym.
      + apply vraw_compare_eq_iff.
      + intros ????. by apply H.
    - apply raw_listbag_compare_antisym.
      + apply vraw_compare_eq_iff.
      + intros ????. by apply H.
  Qed.

  Ltac vauto3 y z :=
    destruct y, z; simpl; intros;
      try first [solve [simpl; unfold compare, nat_comparable; simpl; subst; eauto; done]].

  Lemma vraw_compare_trans x y z :
    raw_compare_trans vraw_compare x y z.
  Proof.
    revert y z. unfold raw_compare_trans.
    induction x using vraw_ind'; simpl; vauto3 y z; try done.
    - eapply compare_trans; eauto.
    - eapply compare_trans; eauto.
    - apply raw_list_compare_trans with (ys:=l0); auto.
      + apply vraw_compare_eq_iff.
      + apply vraw_compare_antisym.
      + intros ???????. by apply H.
    - apply raw_listbag_compare_trans with (b2:=b0); auto.
      + apply vraw_compare_eq_iff.
      + apply vraw_compare_antisym.
      + intros ???????. by apply H.
  Qed.
End vraw_compare.

Definition vraw_le (x y : ValueRaw) := vraw_compare x y = Lt ∨ vraw_compare x y = Eq.

Global Instance vraw_le_dec : RelDecision vraw_le.
Proof. intros x y. solve_decision. Qed.

Global Instance vraw_comparable : Comparable ValueRaw := vraw_compare.

Fixpoint value_invariant (v : ValueRaw) : bool :=
  match v with
  | VUnit => true
  | VNum _ => true
  | VStr _ => true
  | VSeq l =>
      let fix list_value_invariant (l : list ValueRaw) : bool :=
        match l with
        | [] => true
        | x :: xs => value_invariant x && list_value_invariant xs
        end
      in
      list_value_invariant l
  | VBag b =>
      let fix list_value_invariant (l : list ValueRaw) : bool :=
        match l with
        | [] => true
        | x :: xs => value_invariant x && list_value_invariant xs
        end
      in
      sorted_b (listbag_car b) && list_value_invariant (listbag_car b)
  | VUnknown => true
  end.

Lemma value_invariant_seq_unfold {l} :
  value_invariant (VSeq l) = forallb value_invariant l.
Proof with auto. reflexivity. Qed.

Lemma value_invariant_bag_unfold {b} :
  value_invariant (VBag b) = sorted_b (listbag_car b) && forallb value_invariant (listbag_car b).
Proof with auto. reflexivity. Qed.

Definition Value := {v : ValueRaw | value_invariant v}.

Lemma value_invariant_pi : forall v (p q : value_invariant v), p = q.
Proof. intros v p q. apply Is_true_pi. Qed.

Lemma value_eq_iff {v1 v2 : Value} : v1 = v2 ↔ `v1 = `v2.
Proof with auto.
  destruct v1, v2. simpl. split; intros.
  - inversion H...
  - subst x0. f_equal. apply value_invariant_pi.
Qed.

Fixpoint value_eq_dec (x y : Value) : {x = y} + {x <> y}.
Proof.
  destruct x as [x i1]. destruct y as [y i2]. destruct (decide (x = y)).
  - subst. left. f_equal. apply value_invariant_pi.
  - right. intros contra. by inversion contra.
Qed.

Global Instance Value_EqDecision : EqDecision Value.
Proof.
  unfold EqDecision, Decision. apply value_eq_dec.
Qed.

Lemma value_invariant_value (v : Value) : value_invariant (`v).
Proof. by destruct v. Qed.

Section value_compare.
  Definition value_compare (v1 v2 : Value) := vraw_compare (`v1) (`v2).

  Global Instance value_comparable : Comparable Value := value_compare.

  Global Instance value_compare_eq : CompareEq Value.
  Proof.
    intros ??. unfold compare, value_comparable, value_compare. rewrite value_eq_iff.
    apply vraw_compare_eq_iff.
  Qed.

  Global Instance value_compare_total : CompareTotal Value.
  Proof.
    intros ??. unfold compare, value_comparable, value_compare. apply vraw_compare_total.
  Qed.

  Global Instance value_compare_antisym : CompareAntiSym Value.
  Proof.
    intros ??. unfold compare, value_comparable, value_compare. apply vraw_compare_antisym.
  Qed.

  Global Instance value_compare_trans : CompareTrans Value.
  Proof.
    intros ????. unfold compare, value_comparable, value_compare. apply vraw_compare_trans.
  Qed.

  Global Instance value_compare_lawful : LawfulCompare Value := {}.
End value_compare.

Notation "`* xs" := (map proj1_sig xs) (at level 10, format "`* xs") : stdpp_scope.

Definition mkUnknown : Value := VUnknown ↾ I.
Definition mkUnit : Value := VUnit ↾ I.
Definition mkNum (x : R) : Value := VNum x ↾ I.
Notation mkInt x := (mkNum (IZR x)).
Notation mkNat x := (mkNum (INR x)).
Definition mkStr (s : String.string) : Value := VStr s ↾ I.
Program Definition mkSeq (l : list Value) : Value := VSeq (`*l).
Next Obligation.
  epose proof value_invariant_seq_unfold. simpl in H. rewrite H. clear H.
  induction l; auto. simpl. rewrite Is_true_andb. split; auto. apply value_invariant_value.
Qed.
Program Definition mkBag (b : listbag Value) (H : sorted_b (`* (listbag_car b))) : Value
  := VBag (Listbag (`* (listbag_car b))).
Next Obligation.
  rewrite Is_true_andb. split; [assumption|]. clear H.
  epose proof value_invariant_seq_unfold. simpl in H. rewrite H. clear H.
  destruct b as [l]. induction l; auto. simpl. rewrite Is_true_andb. split; auto.
  apply value_invariant_value.
Qed.

Global Instance Value_Bottom : Bottom Value := mkUnknown.

Variant FSym :=
  | FSum
  | FSub
  | FMult
  | FPow
  | FSqrt
  | FFloor
  | FLen (* #as *)
  (* | FConcat (* as ++ bs *) *)
  (* | FIndex (* as[i] *) *)
  (* | FToBag (* bag as *) *)
  (* | FPrefix (* as↑n *) *)
  (* | FSuffix (* as↓n *) *)
.

Global Instance FSym_EqDecision : EqDecision FSym.
Proof. solve_decision. Qed.

Inductive PSym :=
  | PLt
  | PLe
  | PContains.
  (* | IsUnit *)
  (* | IsNat *)
  (* | IsInt *)
  (* | IsReal. *)

Global Instance PSym_EqDecision : EqDecision PSym.
Proof. solve_decision. Qed.

Definition Signature := Model.mkSignature FSym FSym_EqDecision PSym PSym_EqDecision.

Inductive Value_Ty :=
  | TEmpty
  | TUnit
  | TNat
  | TInt
  | TReal
  | TStr
  (* | TPair (τ1 τ2 : Value_Ty) *)
  | TSeq (τ : Value_Ty)
  | TBag (τ : Value_Ty)
  | TUnknown
  (* | TSet (τ : Value_Ty) *)
  (* | TRel (τ1 τ2 : Value_Ty) *)
  (* | TFun (τ1 τ2 : Value_Ty) *)
  (* | TFinSet (τ : Value_Ty) (* finite powerset *) *)
  (* | TSetComp (τ : Value_Ty) (P : Term → Formula) *)
  (* | TUnion (τ1 τ2 : Value_Ty) *)
  (* | TIntersection (τ1 τ2 : Value_Ty) *)
  (* | TSubtraction (τ1 τ2 : Value_Ty). *)
.


Variant FSum_rel : list Value → Value → Prop :=
  | FSum_RR : ∀ r1 r2, FSum_rel [mkNum r1; mkNum r2] (mkNum (r1 + r2))
.

Program Definition FSum_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSum_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: inversion H3; subst; done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FSub_rel : list Value → Value → Prop :=
  | FSub_RR : ∀ r1 r2, FSub_rel [mkNum r1; mkNum r2] (mkNum (r1 - r2)).

Program Definition FSub_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSub_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H5; subst; done).
  all: try (inversion H4; subst; done).
  all: try (inversion H3; subst; done).
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FMult_rel : list Value → Value → Prop :=
  | FMult_RR : ∀ r1 r2, FMult_rel [mkNum r1; mkNum r2] (mkNum (r1 * r2))
.

Program Definition FMult_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FMult_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FSqrt_rel : list Value → Value → Prop :=
  | FSqrt_R : ∀ r2 r, (0 <= r)%R → (r ^ 2)%R = r2 → FSqrt_rel [mkNum r2] (mkNum r)
.

Program Definition FSqrt_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSqrt_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst. inversion H7. f_equal.
  apply Rsqr_inj; try done. do 2 rewrite Rmult_1_r in H3. done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FPow_rel : list Value → Value → Prop :=
  | FPow_R : ∀ r n, FPow_rel [mkNum r; mkNat n] (mkNum (pow r n))
.

Program Definition FPow_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FPow_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst. inversion H3. subst r0.
  apply INR_eq in H4. subst n0. clear H3. f_equal.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FFloor_rel : list Value → Value → Prop :=
  | FFloor_R : ∀ r (i : Z), (IZR i <= r < IZR i + 1)%R → FFloor_rel [mkNum r] (mkNum (IZR i))
.

Program Definition FFloor_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FFloor_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst. inversion H5. subst r0.
  f_equal. apply Zfloor_eq in H1, H4. f_equal. lia.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FLen_rel : list Value → Value → Prop :=
  | FLen_Seq : ∀ l, FLen_rel [mkSeq l] (mkNat (length l))
  | FLen_Bag : ∀ b H, FLen_rel [mkBag b H] (mkNat (size b))
.

Program Definition FLen_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FLen_rel |}.
Next Obligation.
  inversion H; inversion H0; try congruence; subst; try (inversion H4; subst; done); do 2 f_equal.
  - inversion H3.
    assert (length l = length (`*l)) as -> by (symmetry; apply length_map).
    assert (length l0 = length (`*l0)) as -> by (symmetry; apply length_map).
    by rewrite H2.
  - inversion H5. unfold size, listbag_Size.
    destruct b0 as [l1], b as [l2]. simpl in *. clear H0 H H5.
    symmetry. destruct l1 as [|x0 xs].
    { simpl. simpl in H3. symmetry in H3. apply map_eq_nil in H3. by subst. }
    destruct l2 as [|y0 ys].
    { simpl. discriminate. }
    simpl. clear H1 H4. generalize dependent ys. generalize dependent y0.
    generalize dependent x0.
    induction xs as [|x xs]; intros.
    + simpl in H3. destruct ys as [|y ys]; simpl in H3; inversion H3. done.

    (* + simpl in H3. destruct ys as [|y ys]; simpl in H3; inversion H3. simpl. destruct x0, y0. *)
    (*   simpl in *. f_equal. *)
    (*   simpl. f_equal. *)
    + destruct ys as [|y ys]; simpl in H3; inversion H3. simpl.
      assert (x = y) as <- by (apply value_eq_iff; exact H1). clear H1.
      assert (x0 = y0) as <- by (apply value_eq_iff; exact H0). clear H0.
      destruct (decide (x0 = x)).
      * apply IHxs. simpl. by f_equal.
      * simpl. erewrite IHxs.
        -- reflexivity.
        -- simpl. by f_equal.
Qed.
Next Obligation.
  inversion H.
Qed.
  (* | FSum *)
  (* | FSub *)
  (* | FMul *)
  (* | FSqrt *)
  (* | FFloor *)
  (* | FLen (* #as *) *)
  (* | FConcat (* as ++ bs *) *)
  (* | FIndex (* as[i] *) *)
  (* | FToBag (* bag as *) *)
  (* | FPrefix (* as↑n *) *)
  (* | FSuffix (* as↓n *) *)

Definition Fdefs (fsym : FSym) : @Model.fdef Value _ :=
  match fsym with
  | FSum => FSum_fdef
  | FSub => FSub_fdef
  | FMult => FMult_fdef
  | FPow => FPow_fdef
  | FSqrt => FSqrt_fdef
  | FFloor => FFloor_fdef
  | FLen => FLen_fdef
  end.

Variant PLt_rel : vec Value 2 → Prop :=
  | PLt_RR : ∀ r1 r2, (r1 < r2)%R → PLt_rel [# mkNum r1; mkNum r2]
.

Definition PLt_pdef : @Model.pdef Value := {| Model.pdef_rel := PLt_rel |}.

Variant PLe_rel : vec Value 2 → Prop :=
  | PLe_RR : ∀ r1 r2, (r1 <= r2)%R → PLe_rel [# mkNum r1; mkNum r2]
.

Definition PLe_pdef : @Model.pdef Value := {| Model.pdef_rel := PLe_rel |}.

Variant PContains_rel : vec Value 2 → Prop :=
  | PContains_Seq : ∀ v l, v ∈ l → PContains_rel [# v; mkSeq l]
  | PContains_Bag : ∀ v b H, v ∈ b → PContains_rel [# v; mkBag b H]
.

Definition PContains_pdef : @Model.pdef Value := {| Model.pdef_rel := PContains_rel |}.

Definition Pdefs (psym : PSym) : @Model.pdef Value :=
  match psym with
  | PLt => PLt_pdef
  | PLe => PLe_pdef
  | PContains => PContains_pdef
  end.

Inductive HasType : Value → Value_Ty → Prop :=
  | IsUnit     : HasType mkUnit TUnit
  | IsNat      : ∀ x n, x = INR n → HasType (mkNum x) TNat
  | IsInt      : ∀ x n, x = IZR n → HasType (mkNum x) TInt
  | IsReal     : ∀ r, HasType (mkNum r) TReal
  | IsStr      : ∀ s, HasType (mkStr s) TStr
  | IsEmptySeq : ∀ l, HasType (mkSeq l) TEmpty
  | IsSeq      : ∀ l ty, Forall (λ x, HasType x ty) l → HasType (mkSeq l) (TSeq ty)
  | IsEmptyBag : ∀ l H, HasType (mkBag l H) TEmpty
  | IsBag      : ∀ b H ty, Forall (λ x, HasType x ty) (listbag_car b)
                           → HasType (mkBag b H) (TBag ty)
  | IsUnknown  : ∀ v, HasType v TUnknown.

Lemma HasType_Unknown v : HasType v TUnknown.
Proof. constructor. Qed.

Definition Model := Model.mkModel Value mkUnknown _ Value_Ty
                      HasType TUnknown HasType_Unknown Signature Fdefs Pdefs.

Notation Term := (term Model).
Notation Formula := (formula Model).

Definition term_length t : Term := @TApp Model FLen [t].

Notation "# t" := (term_length t)
                      (in custom term at level 40,
                          t custom term,
                          no associativity) : refiney_scope.

Definition term_pow2 t : Term := @TApp Model FPow [t; @TConst Model (mkNat 2)].

Notation "t '²'" := (term_pow2 t)
                      (in custom term at level 40,
                          t custom term,
                          no associativity) : refiney_scope.


Definition term_sqrt t : Term := @TApp Model FSqrt [t].

Notation "√ t" := (term_sqrt t)
                      (in custom term at level 40,
                          t custom term,
                          no associativity) : refiney_scope.

Definition term_floor t : Term := @TApp Model FFloor [t].

Notation "'⌊' t '⌋'" := (term_floor t)
                      (in custom term at level 40,
                          t custom term,
                          no associativity) : refiney_scope.

Definition value_to_term (v : Value) : Term := @TConst Model v.
Coercion value_to_term : Value >-> Term.

Definition nat_to_term_nat (n : nat) : Term := @TConst Model (mkNat n).

Coercion nat_to_term_nat : nat >-> Term.

Lemma VNum_canon x i : VNum x ↾ i = mkNum x.
Proof. simpl in i. by destruct i. Qed.

Definition R_to_int (r : R) : option Z :=
  if decide (frac_part r = 0%R) then Some (Int_part r) else None.
Definition R_to_nat (r : R) : option nat :=
  match R_to_int r with
  | None => None
  | Some z => if decide (0 ≤ z)%Z then Some (Z.to_nat z) else None
  end.

Lemma Int_part_IZR (z : Z) : Int_part (IZR z) = z.
Proof.
  unfold Int_part.
  replace (up (IZR z)) with (z + 1)%Z; [lia|]. apply tech_up.
  - rewrite plus_IZR. auto with real.
  - rewrite plus_IZR. auto with real.
Qed.

Lemma R_to_int_IZR z : R_to_int (IZR z) = Some z.
Proof.
  unfold R_to_int, frac_part. rewrite Int_part_IZR. rewrite <- minus_IZR.
  replace (z - z)%Z with 0%Z by lia. destruct (decide (0%R = 0%R)); done.
Qed.

Lemma R_to_nat_INR n : R_to_nat (INR n) = Some n.
Proof.
  unfold R_to_nat. rewrite INR_IZR_INZ. rewrite R_to_int_IZR.
  rewrite Nat2Z.id. destruct (decide (0 ≤ Z.of_nat _)%Z); try done.
  destruct (n0 (Nat2Z.is_nonneg n)).
Qed.

Lemma R_to_int_Some_inv x z : R_to_int x = Some z → x = IZR z.
Proof.
  unfold R_to_int. destruct (decide (frac_part x = 0%R)); try done.
  inversion 1. clear H. rename H1 into H. destruct (fp_nat x e) as [??]. subst x.
  f_equal. rewrite Int_part_IZR in H. subst. rewrite Int_part_IZR. done.
Qed.

Lemma R_to_nat_Some_inv x n : R_to_nat x = Some n → x = INR n.
Proof.
  unfold R_to_nat. intros. destruct (R_to_int x) eqn:E; try discriminate.
  apply R_to_int_Some_inv in E. subst x. destruct (decide (0 ≤ z)%Z); try discriminate.
  inversion H. clear H. rewrite INR_IZR_INZ. by rewrite Z2Nat.id.
Qed.

Program Definition Model_WithNat : ModelWithNat Model :=
  {|
    nat_to_value := λ n, mkNat n;
    nat_ty := TNat;
    value_to_nat :=
      λ v, match v with
             | VNum x => R_to_nat x
             | _ => None
           end;
    nat_with_sum := FSum;
    nat_with_sub := FSub;
    nat_with_mul := FMult;
    nat_with_order := {| lt_sym := PLt; lt_pdef_arity := eq_refl; le_sym := PLe; le_pdef_arity := eq_refl |}
  |}.
Next Obligation. apply IsNat with (n:=n). done. Qed.
Next Obligation.
  split; intros.
  - inversion H. subst. exists n. simpl. apply R_to_nat_INR.
  - destruct H as []. destruct v as [v]. simpl in H. destruct v; try discriminate.
    apply R_to_nat_Some_inv in H. subst. rewrite VNum_canon. eapply IsNat. reflexivity.
Qed.
Next Obligation. apply R_to_nat_INR. Qed.
Next Obligation.
  destruct v1 as [v1], v2 as [v2]. destruct v1, v2; try discriminate. simpl in H, H0.
  apply R_to_nat_Some_inv in H, H0. subst. unfold fn_eval. constructor. simpl.
  repeat rewrite VNum_canon. rewrite plus_INR. by constructor.
Qed.
Next Obligation.
  destruct v1 as [v1], v2 as [v2]. destruct v1, v2; try discriminate. simpl in H, H0.
  apply R_to_nat_Some_inv in H, H0. subst. unfold fn_eval. constructor. simpl.
  repeat rewrite VNum_canon. rewrite minus_INR; try constructor. lia.
Qed.
Next Obligation.
  destruct v1 as [v1], v2 as [v2]. destruct v1, v2; try discriminate. simpl in H, H0.
  apply R_to_nat_Some_inv in H, H0. subst. unfold fn_eval. constructor. simpl.
  repeat rewrite VNum_canon. rewrite mult_INR; try constructor.
Qed.
Next Obligation.
  destruct v1 as [v1], v2 as [v2]. destruct v1, v2; try discriminate. simpl in H, H0.
  apply R_to_nat_Some_inv in H, H0. subst. unfold lt_pdef_rel. simpl. repeat rewrite VNum_canon.
  split; intros.
  - inversion H. subst. by apply INR_lt in H1.
  - constructor. by apply lt_INR.
Qed.

Global Existing Instance Model_WithNat.
