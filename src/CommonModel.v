From Stdlib Require Import Reals ZArith Sorting.
From stdpp Require Import listset vector.
From MRC Require Export PredCalc Comparable ListBag Prelude Tactics Stdppp.

Notation compare := Comparable.compare.

Inductive Value :=
  | VUnit
  | VNat (n : nat)
  | VInt (i : Z)
  | VReal (r : R)
  | VStr (s : String.string)
  | VUnknown.

Global Instance Value_EqDecision : EqDecision Value.
Proof.
  hnf. intros. hnf. decide equality; try solve_trivial_decision.
Qed.


Global Instance Value_Bottom : Bottom Value := VUnknown.

Variant FSym :=
  | FSum
  | FSub
  | FMult
  | FSqrt
  | FFloor
  | FToNat
  | FToInt
  | FToReal
.

Global Instance FSym_EqDecision : EqDecision FSym.
Proof. solve_decision. Qed.

Variant PSym :=
  | PLt
  | PIsUnit
  | PIsNat
  | PIsInt
  | PIsReal
  | PIsStr.

Global Instance PSym_EqDecision : EqDecision PSym.
Proof. solve_decision. Qed.

Definition Symbols := Model.mkSymbols FSym FSym_EqDecision PSym PSym_EqDecision.

Notation Term := (term Value Symbols).
Notation Formula := (formula Value Symbols).

Variant FSum_rel : list Value → Value → Prop :=
  | FSum_NN : ∀ n1 n2, FSum_rel [VNat n1; VNat n2] (VNat (n1 + n2))
  | FSum_NZ : ∀ n i, FSum_rel [VNat n; VInt i] (VInt (Z.of_nat n + i))
  | FSum_ZN : ∀ i n, FSum_rel [VInt i; VNat n] (VInt (i + Z.of_nat n))
  | FSum_NR : ∀ n r, FSum_rel [VNat n; VReal r] (VReal (INR n + r))
  | FSum_RN : ∀ r n, FSum_rel [VReal r; VNat n] (VReal (r + INR n))
  | FSum_ZZ : ∀ i1 i2, FSum_rel [VInt i1; VInt i2] (VInt (i1 + i2))
  | FSum_ZR : ∀ i r, FSum_rel [VInt i; VReal r] (VReal (IZR i + r))
  | FSum_RZ : ∀ r i, FSum_rel [VReal r; VInt i] (VReal (r + IZR i))
  | FSum_RR : ∀ r1 r2, FSum_rel [VReal r1; VReal r2] (VReal (r1 + r2))
.

Program Definition FSum_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSum_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: inversion H3; subst; done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FSub_rel : list Value → Value → Prop :=
  | FSub_NN : ∀ n1 n2, n1 > n2 → FSub_rel [VNat n1; VNat n2] (VNat (n1 - n2))
  | FSub_NZ : ∀ n i, FSub_rel [VNat n; VInt i] (VInt (Z.of_nat n - i))
  | FSub_ZN : ∀ i n, FSub_rel [VInt i; VNat n] (VInt (i - Z.of_nat n))
  | FSub_NR : ∀ n r, FSub_rel [VNat n; VReal r] (VReal (INR n - r))
  | FSub_RN : ∀ r n, FSub_rel [VReal r; VNat n] (VReal (r - INR n))
  | FSub_ZZ : ∀ i1 i2, FSub_rel [VInt i1; VInt i2] (VInt (i1 - i2))
  | FSub_ZR : ∀ i r, FSub_rel [VInt i; VReal r] (VReal (IZR i - r))
  | FSub_RZ : ∀ r i, FSub_rel [VReal r; VInt i] (VReal (r - IZR i))
  | FSub_RR : ∀ r1 r2, FSub_rel [VReal r1; VReal r2] (VReal (r1 - r2))
.

Program Definition FSub_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSub_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: try (inversion H5; subst; done).
  all: try (inversion H4; subst; done).
  all: try (inversion H3; subst; done).
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FMult_rel : list Value → Value → Prop :=
  | FMult_NN : ∀ n1 n2, FMult_rel [VNat n1; VNat n2] (VNat (n1 * n2))
  | FMult_NZ : ∀ n i, FMult_rel [VNat n; VInt i] (VInt (Z.of_nat n * i))
  | FMult_ZN : ∀ i n, FMult_rel [VInt i; VNat n] (VInt (i * Z.of_nat n))
  | FMult_NR : ∀ n r, FMult_rel [VNat n; VReal r] (VReal (INR n * r))
  | FMult_RN : ∀ r n, FMult_rel [VReal r; VNat n] (VReal (r * INR n))
  | FMult_ZZ : ∀ i1 i2, FMult_rel [VInt i1; VInt i2] (VInt (i1 * i2))
  | FMult_ZR : ∀ i r, FMult_rel [VInt i; VReal r] (VReal (IZR i * r))
  | FMult_RZ : ∀ r i, FMult_rel [VReal r; VInt i] (VReal (r * IZR i))
  | FMult_RR : ∀ r1 r2, FMult_rel [VReal r1; VReal r2] (VReal (r1 * r2))
.

Program Definition FMult_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FMult_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FSqrt_rel : list Value → Value → Prop :=
  | FSqrt_N : ∀ (r2 : nat) r, (0 <= r)%R → (r ^ 2)%R = INR r2 → FSqrt_rel [VNat r2] (VReal r)
  | FSqrt_Z : ∀ (r2 : Z) r, (0 <= r)%R → (r ^ 2)%R = IZR r2 → FSqrt_rel [VInt r2] (VReal r)
  | FSqrt_R : ∀ r2 r, (0 <= r)%R → (r ^ 2)%R = r2 → FSqrt_rel [VReal r2] (VReal r)
.

Program Definition FSqrt_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FSqrt_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
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
  | FFloor_N : ∀ n : nat, FFloor_rel [VNat n] (VNat n)
  | FFloor_Z : ∀ i : Z, FFloor_rel [VInt i] (VInt i)
  | FFloor_R : ∀ r (i : Z), (IZR i <= r < IZR i + 1)%R → FFloor_rel [VReal r] (VInt i)
.

Program Definition FFloor_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FFloor_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
  all: try (inversion H4; subst; done).
  inversion H5. subst r0. f_equal. apply Zfloor_eq in H1, H4. lia.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FToNat_rel : list Value → Value → Prop :=
  | FToNat_N : ∀ n : nat, FToNat_rel [VNat n] (VNat n)
  | FToNat_Z : ∀ i : Z, (0 ≤ i)%Z → FToNat_rel [VInt i] (VNat (Z.to_nat i))
  | FToNat_R : ∀ r n, r = INR n → FToNat_rel [VReal r] (VNat n)
.

Program Definition FToNat_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FToNat_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
  all: try (inversion H4; subst; done).
  all: try (inversion H5; subst; done).
  inversion H5; inversion H; inversion H0; subst. f_equal. apply INR_eq in H2. done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FToInt_rel : list Value → Value → Prop :=
  | FToInt_N : ∀ n : nat, FToInt_rel [VNat n] (VInt (Z.of_nat n))
  | FToInt_Z : ∀ i : Z, FToInt_rel [VInt i] (VInt i)
  | FToInt_R : ∀ r i, r = IZR i → FToInt_rel [VReal r] (VInt i)
.

Program Definition FToInt_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FToInt_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
  all: try (inversion H4; subst; done).
  inversion H5; inversion H; inversion H0; subst. apply eq_IZR in H2. f_equal. done.
Qed.
Next Obligation.
  inversion H.
Qed.

Variant FToReal_rel : list Value → Value → Prop :=
  | FToReal_N : ∀ n : nat, FToReal_rel [VNat n] (VReal (INR n))
  | FToReal_Z : ∀ i : Z, FToReal_rel [VInt i] (VReal (IZR i))
  | FToReal_R : ∀ r, FToReal_rel [VReal r] (VReal r)
.

Program Definition FToReal_fdef : @Model.fdef Value _ := {| Model.fdef_rel := FToReal_rel |}.
Next Obligation.
  inversion H; inversion H0; simpl; subst.
  all: try (inversion H3; subst; done).
Qed.
Next Obligation.
  inversion H.
Qed.

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
  end.

Variant PLt_rel : vec Value 2 → Prop :=
  | PLt_NN : ∀ n1 n2, n1 < n2 → PLt_rel [# VNat n1; VNat n2]
  | PLt_NZ : ∀ n i, (Z.of_nat n < i)%Z → PLt_rel [# VNat n; VInt i]
  | PLt_ZN : ∀ i n, (i < Z.of_nat n)%Z → PLt_rel [# VInt i; VNat n]
  | PLt_NR : ∀ n r, (INR n < r)%R → PLt_rel [# VNat n; VReal r]
  | PLt_RN : ∀ r n, (r < INR n)%R → PLt_rel [# VReal r; VNat n]
  | PLt_ZZ : ∀ i1 i2, (i1 < i2)%Z → PLt_rel [# VInt i1; VInt i2]
  | PLt_ZR : ∀ i r, (IZR i < r)%R → PLt_rel [# VInt i; VReal r]
  | PLt_RZ : ∀ r i, (r < IZR i)%R → PLt_rel [# VReal r; VInt i]
  | PLt_RR : ∀ r1 r2, (r1 < r2)%R → PLt_rel [# VReal r1; VReal r2]
.

Definition PLt_pdef : @Model.pdef Value := {| Model.pdef_rel := PLt_rel |}.

Variant PIsUnit_rel : vec Value 1 → Prop :=
  | PIsUnit_unit : PIsUnit_rel [# VUnit]
.

Definition PIsUnit_pdef : @Model.pdef Value := {| Model.pdef_rel := PIsUnit_rel |}.

Variant PIsNat_rel : vec Value 1 → Prop :=
  | PIsNat_unit : ∀ n, PIsNat_rel [# (VNat n)]
.

Definition PIsNat_pdef : @Model.pdef Value := {| Model.pdef_rel := PIsNat_rel |}.

Variant PIsInt_rel : vec Value 1 → Prop :=
  | PIsInt_unit : ∀ i, PIsInt_rel [# (VInt i)]
.

Definition PIsInt_pdef : @Model.pdef Value := {| Model.pdef_rel := PIsInt_rel |}.

Variant PIsReal_rel : vec Value 1 → Prop :=
  | PIsReal_unit : ∀ r, PIsReal_rel [# (VReal r)]
.

Definition PIsReal_pdef : @Model.pdef Value := {| Model.pdef_rel := PIsReal_rel |}.

Variant PIsStr_rel : vec Value 1 → Prop :=
  | PIsStr_unit : ∀ r, PIsStr_rel [# (VStr r)]
.

Definition PIsStr_pdef : @Model.pdef Value := {| Model.pdef_rel := PIsStr_rel |}.

Definition Pdefs (psym : PSym) : @Model.pdef Value :=
  match psym with
  | PLt => PLt_pdef
  | PIsUnit => PIsUnit_pdef
  | PIsNat => PIsNat_pdef
  | PIsInt => PIsInt_pdef
  | PIsReal => PIsReal_pdef
  | PIsStr => PIsStr_pdef
  end.

Definition Model := Model.mkModel Value VUnknown Symbols Fdefs Pdefs.

Variant Value_Ty :=
  | TUnit
  | TNat
  | TInt
  | TReal
  | TStr
  | TUnknown
.

Fixpoint HasType (t : Term) (τ : Value_Ty) : Formula :=
  match τ with
  | TUnit => FAtom (@AT_Pred Value Symbols PIsUnit [t])
  | TNat => FAtom (@AT_Pred Value Symbols PIsNat [t])
  | TInt => FAtom (@AT_Pred Value Symbols PIsInt [t])
  | TReal => FAtom (@AT_Pred Value Symbols PIsReal [t])
  | TStr => FAtom (@AT_Pred Value Symbols PIsStr [t])
  | TUnknown => <! true !>
  end.

Program Definition Model_with_types : ModelWithTypes Model := {| value_ty := Value_Ty; hastype := HasType |}.
Next Obligation.
  unfold HasType in H. destruct ty; destruct t; simpl in *; set_solver.
Qed.

Global Existing Instance Model_with_types.

Lemma list_to_vec_1 {A} (x : A) (H : length [x] = 1) : list_to_vec_n [x] H = [# x].
Proof.
  unfold list_to_vec_n. unfold eq_rect. enough (H = eq_refl) as -> by reflexivity.
  apply Eqdep_dec.UIP_dec. intros. solve_decision.
Qed.

Program Definition Model_with_order : ModelWithOrder Model := {|
  lt_sym := PLt
|}.

Global Existing Instance Model_with_order.

Program Definition Model_with_nat : ModelWithNat Model := {|
  nat_with_types := Model_with_types;
  nat_to_value := VNat;
  nat_ty := TNat;
  value_to_nat := λ v,
    match v with
    | VNat n => Some n
    | _ => None
    end;
  nat_with_sum := FSum;
  nat_with_mul := FMult;
  nat_with_sub := FSub;
  nat_with_order := Model_with_order;
|}.
Next Obligation.
  econstructor. split; [constructor; constructor|].
  unfold peval. intros. simpl. rewrite list_to_vec_1. constructor.
Qed.
Next Obligation.
  split; intros.
  - unfold tautology in H. specialize (H ∅). inversion H. destruct H0 as []. unfold peval in H1.
    inversion H0. subst. inversion H4. subst v1. subst v0. inversion H6. subst.
    ospecialize (H1 _). inversion H1. rewrite list_to_vec_1 in H3. inversion H3.
    by exists n. Unshelve. done.
  - intros σ. econstructor. split; [constructor; constructor|]. unfold peval. intros.
    destruct H as [n ?]. destruct v; try discriminate. inversion H.
    simpl. rewrite list_to_vec_1.  subst n0. constructor.
Qed.
Next Obligation.
  unfold fn_eval. constructor. simpl. destruct v1; try discriminate. destruct v2; try discriminate.
  inversion H. subst n. inversion H0. subst n0. apply FSum_NN.
Qed.
Next Obligation.
  unfold fn_eval. constructor. simpl. destruct v1; try discriminate. destruct v2; try discriminate.
  inversion H. subst n. inversion H0. subst n0. by constructor.
Qed.
Next Obligation.
  unfold fn_eval. constructor. simpl. destruct v1; try discriminate. destruct v2; try discriminate.
  inversion H. subst n. inversion H0. subst n0. by constructor.
Qed.
Next Obligation.
  destruct v1; try discriminate; destruct v2; try discriminate. inversion H; inversion H0.
  subst n n0. unfold lt_pdef_rel. unfold eq_rect.
  assert (lt_pdef_arity = eq_refl) as ->.
  { apply Eqdep_dec.UIP_dec. solve_decision. }
  split; intros.
  - by inversion H1.
  - by constructor.
Qed.

Global Existing Instance Model_with_nat.

Definition value_to_term v : Term := TConst v.
Coercion value_to_term : Value >-> Term.

Definition nat_to_term_nat (n : nat) : Term := @TConst Value Symbols (VNat n).

Coercion nat_to_term_nat : nat >-> Term.
