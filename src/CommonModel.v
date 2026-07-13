From Stdlib Require Import Reals ZArith Sorting.
From stdpp Require Import listset vector.
From MRC Require Export PredCalc Comparable ListBag Prelude Tactics Stdppp.

Notation compare := Comparable.compare.

Inductive ValueRaw :=
  | VUnit
  | VNat (n : nat)
  | VInt (i : Z)
  | VReal (r : R)
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
    | VNat n => 1
    | VInt i => 2
    | VReal r => 3
    | VStr s => 4
    | VSeq l => 5
    | VBag l => 6
    | VUnknown => 7
    end.

  Fixpoint vraw_compare (x y : ValueRaw) : comparison :=
    match x, y with
    | VUnit, VUnit => Eq
    | VNat n1, VNat n2 => compare n1 n2
    | VInt i1, VInt i2 => compare i1 i2
    | VReal r1, VReal r2 => compare r1 r2
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
    (∀ n, P (VNat n)) →
    (∀ i, P (VInt i)) →
    (∀ r, P (VReal r)) →
    (∀ s, P (VStr s)) →
    (∀ l, (∀ x, In x l → P x) → P (VSeq l)) →
    (∀ b, (∀ x, In x (listbag_car b) → P x) → P (VBag b)) →
    (P VUnknown) →
    (∀ x, P x).
  Proof.
    intros Hunit Hnat Hint Hreal Hstr Hseq Hbag Hunknown. destruct x; try done.
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
  | VNat n => true
  | VInt i => true
  | VReal r => true
  | VStr s => true
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

Program Definition mkUnknown : Value := VUnknown.
Program Definition mkUnit : Value := VUnit.
Program Definition mkNat (n : nat) : Value := VNat n.
Program Definition mkInt (i : Z) : Value := VInt i.
Program Definition mkReal (r : R) : Value := VReal r.
Program Definition mkStr (s : String.string) : Value := VStr s.
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
  | FSqrt
  | FFloor
  | FToNat
  | FToInt
  | FToReal
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
  | PContains.
  (* | IsUnit *)
  (* | IsNat *)
  (* | IsInt *)
  (* | IsReal. *)

Global Instance PSym_EqDecision : EqDecision PSym.
Proof. solve_decision. Qed.

Definition Symbols := Model.mkSymbols FSym FSym_EqDecision PSym PSym_EqDecision.

Notation Term := (term Value Symbols).
Notation Formula := (formula Value Symbols).

Variant FSum_rel : list Value → Value → Prop :=
  | FSum_NN : ∀ n1 n2, FSum_rel [mkNat n1; mkNat n2] (mkNat (n1 + n2))
  | FSum_NZ : ∀ n i, FSum_rel [mkNat n; mkInt i] (mkInt (Z.of_nat n + i))
  | FSum_ZN : ∀ i n, FSum_rel [mkInt i; mkNat n] (mkInt (i + Z.of_nat n))
  | FSum_NR : ∀ n r, FSum_rel [mkNat n; mkReal r] (mkReal (INR n + r))
  | FSum_RN : ∀ r n, FSum_rel [mkReal r; mkNat n] (mkReal (r + INR n))
  | FSum_ZZ : ∀ i1 i2, FSum_rel [mkInt i1; mkInt i2] (mkInt (i1 + i2))
  | FSum_ZR : ∀ i r, FSum_rel [mkInt i; mkReal r] (mkReal (IZR i + r))
  | FSum_RZ : ∀ r i, FSum_rel [mkReal r; mkInt i] (mkReal (r + IZR i))
  | FSum_RR : ∀ r1 r2, FSum_rel [mkReal r1; mkReal r2] (mkReal (r1 + r2))
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
  | FSub_NN : ∀ n1 n2, n1 > n2 → FSub_rel [mkNat n1; mkNat n2] (mkNat (n1 - n2))
  | FSub_NZ : ∀ n i, FSub_rel [mkNat n; mkInt i] (mkInt (Z.of_nat n - i))
  | FSub_ZN : ∀ i n, FSub_rel [mkInt i; mkNat n] (mkInt (i - Z.of_nat n))
  | FSub_NR : ∀ n r, FSub_rel [mkNat n; mkReal r] (mkReal (INR n - r))
  | FSub_RN : ∀ r n, FSub_rel [mkReal r; mkNat n] (mkReal (r - INR n))
  | FSub_ZZ : ∀ i1 i2, FSub_rel [mkInt i1; mkInt i2] (mkInt (i1 - i2))
  | FSub_ZR : ∀ i r, FSub_rel [mkInt i; mkReal r] (mkReal (IZR i - r))
  | FSub_RZ : ∀ r i, FSub_rel [mkReal r; mkInt i] (mkReal (r - IZR i))
  | FSub_RR : ∀ r1 r2, FSub_rel [mkReal r1; mkReal r2] (mkReal (r1 - r2))
.

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
  | FMult_NN : ∀ n1 n2, FMult_rel [mkNat n1; mkNat n2] (mkNat (n1 * n2))
  | FMult_NZ : ∀ n i, FMult_rel [mkNat n; mkInt i] (mkInt (Z.of_nat n * i))
  | FMult_ZN : ∀ i n, FMult_rel [mkInt i; mkNat n] (mkInt (i * Z.of_nat n))
  | FMult_NR : ∀ n r, FMult_rel [mkNat n; mkReal r] (mkReal (INR n * r))
  | FMult_RN : ∀ r n, FMult_rel [mkReal r; mkNat n] (mkReal (r * INR n))
  | FMult_ZZ : ∀ i1 i2, FMult_rel [mkInt i1; mkInt i2] (mkInt (i1 * i2))
  | FMult_ZR : ∀ i r, FMult_rel [mkInt i; mkReal r] (mkReal (IZR i * r))
  | FMult_RZ : ∀ r i, FMult_rel [mkReal r; mkInt i] (mkReal (r * IZR i))
  | FMult_RR : ∀ r1 r2, FMult_rel [mkReal r1; mkReal r2] (mkReal (r1 * r2))
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
  | FSqrt_N : ∀ (r2 : nat) r, (0 <= r)%R → (r ^ 2)%R = INR r2 → FSqrt_rel [mkNat r2] (mkReal r)
  | FSqrt_Z : ∀ (r2 : Z) r, (0 <= r)%R → (r ^ 2)%R = IZR r2 → FSqrt_rel [mkInt r2] (mkReal r)
  | FSqrt_R : ∀ r2 r, (0 <= r)%R → (r ^ 2)%R = r2 → FSqrt_rel [mkReal r2] (mkReal r)
.

Program Definition FSqrt_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSqrt_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H7; subst; done).
  all: subst; inversion H7; subst; f_equal; apply Rsqr_inj; try done; unfold Rsqr; simpl in *.
  - rewrite Rmult_1_r in H2, H6. by rewrite H2.
  - rewrite Rmult_1_r in H2, H6. by rewrite H2.
  - do 2 rewrite Rmult_1_r in H3. done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FFloor_rel : list Value → Value → Prop :=
  | FFloor_N : ∀ n : nat, FFloor_rel [mkNat n] (mkNat n)
  | FFloor_Z : ∀ i : Z, FFloor_rel [mkInt i] (mkInt i)
  | FFloor_R : ∀ r (i : Z), (IZR i <= r < IZR i + 1)%R → FFloor_rel [mkReal r] (mkInt i)
.

Program Definition FFloor_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FFloor_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
  all: try (inversion H4; subst; done).
  inversion H5. subst r0. f_equal. apply Zfloor_eq in H1, H4. lia.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FToNat_rel : list Value → Value → Prop :=
  | FToNat_N : ∀ n : nat, FToNat_rel [mkNat n] (mkNat n)
  | FToNat_Z : ∀ i : Z, (0 ≤ i)%Z → FToNat_rel [mkInt i] (mkNat (Z.to_nat i))
  | FToNat_R : ∀ r n, r = INR n → FToNat_rel [mkReal r] (mkNat n)
.

Program Definition FToNat_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FToNat_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
  all: try (inversion H4; subst; done).
  all: try (inversion H5; subst; done).
  inversion H5; inversion H; inversion H0; subst. f_equal. apply INR_eq in H2. done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FToInt_rel : list Value → Value → Prop :=
  | FToInt_N : ∀ n : nat, FToInt_rel [mkNat n] (mkInt (Z.of_nat n))
  | FToInt_Z : ∀ i : Z, FToInt_rel [mkInt i] (mkInt i)
  | FToInt_R : ∀ r i, r = IZR i → FToInt_rel [mkReal r] (mkInt i)
.

Program Definition FToInt_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FToInt_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
  all: try (inversion H4; subst; done).
  inversion H5; inversion H; inversion H0; subst. apply eq_IZR in H2. f_equal. done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FToReal_rel : list Value → Value → Prop :=
  | FToReal_N : ∀ n : nat, FToReal_rel [mkNat n] (mkReal (INR n))
  | FToReal_Z : ∀ i : Z, FToReal_rel [mkInt i] (mkReal (IZR i))
  | FToReal_R : ∀ r, FToReal_rel [mkReal r] (mkReal r)
.

Program Definition FToReal_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FToReal_rel |}.
Next Obligation.
  apply value_eq_iff. inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
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
  inversion H; inversion H0; try congruence; subst.
  all: try (inversion H4; subst; done).
  - inversion H3. f_equal.
    assert (length l = length (`*l)) as -> by (symmetry; apply length_map).
    assert (length l0 = length (`*l0)) as -> by (symmetry; apply length_map).
    by f_equal.
  - inversion H5. f_equal. unfold size, listbag_Size.
    destruct b0 as [l1], b as [l2]. simpl in *. clear H0 H H5.
    f_equal. symmetry. destruct l1 as [|x0 xs].
    { simpl. simpl in H3. symmetry in H3. apply map_eq_nil in H3. by subst. }
    destruct l2 as [|y0 ys].
    { simpl. discriminate. }
    simpl. clear H1 H4. generalize dependent ys. generalize dependent y0.
    generalize dependent x0.
    induction xs as [|x xs]; intros.
    + simpl in H3. destruct ys as [|y ys]; simpl in H3; inversion H3.
      simpl. f_equal. by apply value_eq_iff.
    + destruct ys as [|y ys]; simpl in H3; inversion H3. simpl.
      assert (x = y) as <- by (apply value_eq_iff; exact H1). clear H1.
      assert (x0 = y0) as <- by (apply value_eq_iff; exact H0). clear H0.
      destruct (decide (x0 = x)).
      * apply IHxs. simpl. by f_equal.
      * f_equal. apply IHxs. simpl. by f_equal.
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
  | FSqrt => FSqrt_fdef
  | FFloor => FFloor_fdef
  | FToNat => FToNat_fdef
  | FToInt => FToInt_fdef
  | FToReal => FToReal_fdef
  | FLen => FLen_fdef
  end.

Variant PLt_rel : vec Value 2 → Prop :=
  | PLt_NN : ∀ n1 n2, n1 ≤ n2 → PLt_rel [# mkNat n1; mkNat n2]
  | PLt_NZ : ∀ n i, (Z.of_nat n ≤ i)%Z → PLt_rel [# mkNat n; mkInt i]
  | PLt_ZN : ∀ i n, (i ≤ Z.of_nat n)%Z → PLt_rel [# mkInt i; mkNat n]
  | PLt_NR : ∀ n r, (INR n <= r)%R → PLt_rel [# mkNat n; mkReal r]
  | PLt_RN : ∀ r n, (r <= INR n)%R → PLt_rel [# mkReal r; mkNat n]
  | PLt_ZZ : ∀ i1 i2, (i1 ≤ i2)%Z → PLt_rel [# mkInt i1; mkInt i2]
  | PLt_ZR : ∀ i r, (IZR i <= r)%R → PLt_rel [# mkInt i; mkReal r]
  | PLt_RZ : ∀ r i, (r <= IZR i)%R → PLt_rel [# mkReal r; mkInt i]
  | PLt_RR : ∀ r1 r2, (r1 <= r2)%R → PLt_rel [# mkReal r1; mkReal r2]
.

Definition PLt_pdef : @Model.pdef Value := {| Model.pdef_rel := PLt_rel |}.

Variant PContains_rel : vec Value 2 → Prop :=
  | PContains_Seq : ∀ v l, v ∈ l → PContains_rel [# v; mkSeq l]
  | PContains_Bag : ∀ v b H, v ∈ b → PContains_rel [# v; mkBag b H]
.

Definition PContains_pdef : @Model.pdef Value := {| Model.pdef_rel := PContains_rel |}.

Definition Pdefs (psym : PSym) : @Model.pdef Value :=
  match psym with
  | PLt => PLt_pdef
  | PContains => PContains_pdef
  end.

Definition Model := Model.mkModel Value mkUnknown Symbols Fdefs Pdefs.

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
  (* | TSet (τ : Value_Ty) *)
  (* | TRel (τ1 τ2 : Value_Ty) *)
  (* | TFun (τ1 τ2 : Value_Ty) *)
  (* | TFinSet (τ : Value_Ty) (* finite powerset *) *)
  (* | TSetComp (τ : Value_Ty) (P : Term → Formula) *)
  (* | TUnion (τ1 τ2 : Value_Ty) *)
  (* | TIntersection (τ1 τ2 : Value_Ty) *)
  (* | TSubtraction (τ1 τ2 : Value_Ty). *)
.

Definition term_length t : Term := @TApp Value Symbols FLen [t].

Notation "# t" := (term_length t)
                      (in custom term at level 40,
                          t custom term,
                          no associativity) : refiney_scope.

Definition value_to_term v : Term := TConst v.
Coercion value_to_term : Value >-> Term.

Definition nat_to_term_nat (n : nat) : Term := @TConst Value Symbols (mkNat n).

Coercion nat_to_term_nat : nat >-> Term.

(* Check ValueRaw_rec. *)
(* Fixpoint value_rec' {A} : *)
(*   A → *)
(*   (∀ n : nat, A) → *)
(*   (∀ i : Z, A) → *)
(*   (∀ r : R, A) → *)
(*   (∀ s : String.string, A) → *)
(*   (∀ l : list Value, A) → *)
(*   (∀ l : list Value, sorted_b l → A) → *)
(*   A → *)
(*   (∀ x : Value, A). *)
(* Proof. *)
(*   intros Funit Fnat Fint Freal Fstr Fseq Fbag Funknown ?. destruct x. destruct x. *)
(*   - exact Funit. *)
(*   - exact (Fnat n). *)
(*   - exact (Fint i0). *)
(*   - exact (Freal r). *)
(*   - exact (Fstr s). *)
(*   - clear Funit Fnat Fint Freal Fstr Fbag Funknown value_rec'. induction l. *)
(*     + exact (Fseq []). *)
(*     +  *)
(*   - apply Hseq. induction l; simpl; [done|]. intros. destruct H. *)
(*     + subst x. by apply vraw_ind'. *)
(*     + by apply IHl. *)
(*   - apply Hbag. induction (listbag_car b); simpl; [done|]. intros. destruct H. *)
(*     + subst x. by apply vraw_ind'. *)
(*     + by apply IHl. *)
(* Qed. *)
(* Fixpoint value_rec' {A : Type} : *)
(*   (VUnit → A) → *)
(*   (∀ n, VNat n → ) *)

Fixpoint value_hastype (v : Value) (τ : Value_Ty) : Formula :=
  match `v, τ with
  | VUnit, TUnit => <! true !>
  | VNat _, TNat => <! true !>
  | VInt _, TInt => <! true !>
  | VReal _, TReal => <! true !>
  | VStr _, TStr => <! true !>
  | VSeq _, TEmpty => <! ⌜# v = 0⌝ !>
  | VSeq l, TSeq τ => list_hastype l τ
  | _, TUnknown => <! true !>
  | _, _ => <! false !>
  (* | VPair v1 v2, TPair τ1 τ2 => <! $(hastype v1 τ2) ∧ $(hastype v2 τ2) !> *)
  (* | _, _ => <! false !> end. *)
  (* | VList l, TList τ => ∀ v, v ∈ l → hastype v τ (* define contains as a function symbol and ∈ notation for formula *) *)
  (* | VFinSet s, TFinSet τ =>  ∀ v, v ∈ l → hastype v τ (* define contains as a function symbol and ∈ notation for formula *) *)
  (* | VFinSet s, TFinRel τ1 τ2 => hastype v (TSet (τ1 * τ2)) *)
  (* | VFinSet s, TFun τ1 τ2 => hastype v (TRel τ1 τ2) ∧ ∀ a b1 b2, (a, b1) ∈ s → (a, b2) ∈ s → b1 = b2 *)
  (* | VFinSet s, TSet τ => ∀ v, v ∈ s → hastype v τ *)
  (* | _, TSetComp τ P => hastype v τ ∧ P v *)
  (* | _, TUnion τ1 τ2 => hastype v τ1 ∨ hastype v τ2 *)
  (* | _, TIntersection τ1 τ2 => hastype v τ1 ∧ hastype v τ2 *)
  (* | _, TSubtraction τ1 τ2 => hastype v τ1 ∧ ¬ hastype v τ2 *)
  (* | _, _ => false *)
  end
with list_hastype (l : list Value) (τ : Value_Ty) : Formula :=
  match l with
  | [] => <! true !>
  | x :: xs => <! $(value_hastype x τ) ∧ $(list_hastype xs τ) !>
  end
.

Inductive hastype : value → value_ty → Prop :=
  | VTUnit : hastype VUnit TUnit
  | VTNat n : hastype (VNat n) TNat
  | VTInt i : hastype (VInt i) TInt
  | VTReal r : hastype (VReal r) TReal
  | VTStr s : hastype (VStr s) TStr
  | VTPair v1 v2 τ1 τ2 : hastype v1 τ1 → hastype v2 τ2 → hastype (VPair v1 v2) (TPair τ1 τ2)
  | VTList (τ : value_ty)
  | VTSet (τ : value_ty)
  | VTRel (τ1 τ2 : value_ty)
  | VTFun (τ1 τ2 : value_ty)
  | VTPow (τ : value_ty)
  | VTSetComp (τ : value_ty) (P : variable → formula value)
  | VTUnion (τ1 τ2 : value_ty)
  | VTIntersection (τ1 τ2 : value_ty)
  | VTSubtraction (τ1 τ2 : value_ty).

Lemma value_hastype_det : ∀ (v : value) (τ1 τ2 : value_ty),
    v ∈ τ1 → v ∈ τ2 → τ1 = τ2.
Proof.
  intros v τ1 τ2 H1 H2. unfold elem_of, value_ty_elem_of, value_has_type.
  rewrite value_elem_of_iff_typeof_eq in H1, H2.
  apply bool_decide_unpack in H1, H2. subst. reflexivity.
Qed.
