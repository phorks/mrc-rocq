From Stdlib Require Import List String Reals.
From stdpp Require Import base tactics list.
From MRC Require Import Prelude Tactics.


Section raw_compare.
  Context {A : Type}.
  Context (comp : A → A → comparison).

  Definition raw_compare_eq_iff x y := comp x y = Eq ↔ x = y.
  Definition raw_compare_total x y := comp x y ≠ Gt ∨ comp y x ≠ Gt.
  Definition raw_compare_antisym x y := comp x y = CompOpp (comp y x).
  Definition raw_compare_trans x y z := ∀ c,
      comp x y = c → comp y z = c → comp x z = c.

  Lemma raw_compare_diag : (∀ x y, raw_compare_eq_iff x y) → ∀ x, comp x x = Eq.
  Proof.
    unfold raw_compare_eq_iff. intros. apply (H x x). done.
  Qed.
End raw_compare.

Class Comparable (A : Type) := compare : A → A → comparison.

Class CompareEq (A : Type) `{!Comparable A} := compare_eq_iff : ∀ x y, compare x y = Eq ↔ x = y.

Class CompareTotal (A : Type) `{!Comparable A}
  := compare_total : ∀ x y, compare x y ≠ Gt ∨ compare y x ≠ Gt.

Class CompareAntiSym (A : Type) `{Comparable A}
  := compare_antisym : ∀ x y, compare x y = CompOpp (compare y x).

Class CompareTrans (A : Type) `{!Comparable A}
  := compare_trans : ∀ x y z c, compare x y = c → compare y z = c → compare x z = c.

Class LawfulCompare (A : Type) `{Comparable A, !CompareEq A, !CompareTotal A, !CompareTrans A, !CompareAntiSym A}.

Lemma compare_diag {A} `{CompareEq A} {x} : compare x x = Eq.
Proof. assert (x = x) by reflexivity. apply compare_eq_iff in H0. done. Qed.

Lemma compare_trans_le {A} `{Comparable A, !CompareEq A, !CompareTrans A} x y z :
  compare x y ≠ Gt → compare y z ≠ Gt → compare x z ≠ Gt.
Proof.
  intros. intros contra. destruct (compare x y) eqn:E; [| |done].
  - destruct (compare y z) eqn:E'; [| |done].
    + pose proof (compare_trans _ _ _ _ E E'). congruence.
    + apply compare_eq_iff in E. subst. congruence.
  - destruct (compare y z) eqn:E'; [| |done].
    + apply compare_eq_iff in E'. subst. congruence.
    + pose proof (compare_trans _ _ _ _ E E'). congruence.
Qed.

Lemma compare_antisym_le {A} `{Comparable A, !CompareEq A, !CompareAntiSym A} x y :
  compare x y ≠ Gt → compare y x ≠ Gt → x = y.
Proof.
  intros. pose proof (compare_antisym x y).
  destruct (compare x y) eqn:E; [| |done].
  - apply compare_eq_iff in E. done.
  - destruct (compare y x) eqn:E1; [| |done].
    + by apply compare_eq_iff in E1.
    + by simpl in H2.
Qed.

Section nat_compare.
  Global Instance nat_comparable : Comparable nat := Nat.compare.

  Global Instance nat_compare_eq : CompareEq nat.
  Proof. unfold CompareEq. apply Nat.compare_eq_iff. Qed.

  Global Instance nat_compare_total : CompareTotal nat.
  Proof.
    intros x y. unfold compare, nat_comparable. destruct (x ?= y) eqn:E1; try (left; done).
    right. destruct (y ?= x) eqn:E2; try done. apply Nat.compare_gt_iff in E1, E2. lia.
  Qed.

  Global Instance nat_compare_antisym : CompareAntiSym nat.
  Proof. intros x y. unfold compare, nat_comparable. apply Nat.compare_antisym. Qed.

  Global Instance nat_compare_trans : CompareTrans nat.
  Proof.
    intros x y z c ??. unfold compare, nat_comparable in *. destruct (x ?= y) eqn:E1; subst c.
    - apply Nat.compare_eq_iff in E1, H0. subst. by apply Nat.compare_eq_iff.
    - apply Nat.compare_lt_iff in E1, H0. apply Nat.compare_lt_iff. by trans y.
    - apply Nat.compare_gt_iff in E1, H0. apply Nat.compare_gt_iff. by trans y.
  Qed.

  Global Instance nat_compare_lawful : LawfulCompare nat := {}.
End nat_compare.

Section Z_compare.
  Global Instance Z_comparable : Comparable Z := Z.compare.

  Global Instance Z_compare_eq : CompareEq Z.
  Proof. unfold CompareEq. apply Z.compare_eq_iff. Qed.

  Global Instance Z_compare_total : CompareTotal Z.
  Proof.
    intros x y. unfold compare, Z_comparable. destruct (x ?= y)%Z eqn:E1; try (left; done).
    right. destruct (y ?= x)%Z eqn:E2; try done. apply Z.compare_gt_iff in E1, E2. lia.
  Qed.

  Global Instance Z_compare_antisym : CompareAntiSym Z.
  Proof. intros x y. unfold compare, Z_comparable. apply Z.compare_antisym. Qed.

  Global Instance Z_compare_trans : CompareTrans Z.
  Proof.
    intros x y z c ??. unfold compare, Z_comparable in *. destruct (x ?= y)%Z eqn:E1; subst c.
    - apply Z.compare_eq_iff in E1, H0. subst. by apply Z.compare_eq_iff.
    - apply Z.compare_lt_iff in E1, H0. apply Z.compare_lt_iff. by trans y.
    - apply Z.compare_gt_iff in E1, H0. apply Z.compare_gt_iff. by trans y.
  Qed.

  Global Instance Z_compare_lawful : LawfulCompare Z := {}.
End Z_compare.

Section R_compare.
  Global Instance R_EqDecision : EqDecision R.
  Proof with auto.
    intros x y. apply Req_dec_T.
  Defined.

  Global Instance Rle_Decision {r1 r2} : Decision (Rle r1 r2) := Rle_dec r1 r2.
  Global Instance Rlt_Decision {r1 r2} : Decision (Rlt r1 r2) := Rlt_dec r1 r2.

  Definition R_leb (r1 r2 : R) := bool_decide (Rle r1 r2).
  Definition R_ltb (r1 r2 : R) := bool_decide (Rlt r1 r2).

  Definition R_compare (r1 r2 : R) : comparison :=
    if decide (r1 = r2) then Eq else if R_ltb r1 r2 then Lt else Gt.

  Global Instance R_comparable : Comparable R := R_compare.

  Global Instance R_compare_eq : CompareEq R.
  Proof.
    intros x y. unfold compare, R_comparable, R_compare. destruct (decide (x = y)).
    - by subst.
    - destruct (R_ltb x y); done.
  Qed.

  Global Instance R_compare_total : CompareTotal R.
  Proof.
    intros x y. unfold compare, R_comparable, R_compare. destruct (Rle_or_lt x y).
    - left. unfold R_ltb. apply Rle_lt_or_eq in H. destruct H.
      + pose proof (Rlt_not_eq _ _ H). destruct (decide (x = y)); [done|].
        destruct (bool_decide ((x < y)%R)) eqn:E.
        * apply bool_decide_eq_true in E. done.
        * apply bool_decide_eq_false in E. done.
      + subst. destruct (decide (y = y)); done.
    - right. unfold R_ltb. apply Rlt_le in H. apply Rle_lt_or_eq in H. destruct H.
      + pose proof (Rlt_not_eq _ _ H). destruct (decide (y = x)); [done|].
        destruct (bool_decide ((y < x)%R)) eqn:E.
        * apply bool_decide_eq_true in E. done.
        * apply bool_decide_eq_false in E. done.
      + subst. destruct (decide (x = x)); done.
  Qed.

  Global Instance R_compare_antisym : CompareAntiSym R.
  Proof.
    intros x y. unfold compare, R_comparable, R_compare. destruct (decide (x = y)).
    - subst. destruct (decide (y = y)); done.
    - destruct (decide (y = x)); [done|]. unfold R_ltb. destruct (bool_decide (x < y)%R) eqn:E1.
      + apply bool_decide_eq_true in E1. destruct (bool_decide (y < x)%R) eqn:E2; [|done].
        apply bool_decide_eq_true in E2. apply Rlt_asym in E2. done.
      + apply bool_decide_eq_false in E1. destruct (bool_decide (y < x)%R) eqn:E2; [done|].
        apply bool_decide_eq_false in E2. apply Rnot_lt_le in E1, E2.
        pose proof (Rle_antisym _ _ E1 E2). subst. contradiction.
  Qed.

  Global Instance R_compare_trans : CompareTrans R.
  Proof.
    intros x y z c ??. unfold compare, R_comparable, R_compare in *. destruct (decide (x = y)).
    - subst. destruct (decide (y = z)); done.
    - unfold R_ltb in *. destruct (decide (y = z)).
      + subst. destruct (bool_decide (x < z)%R); done.
      + subst c. destruct (bool_decide (x < y)%R) eqn:E1; destruct (bool_decide (y < z)%R) eqn:E2;
          try discriminate.
        * apply bool_decide_eq_true in E1, E2. destruct (decide (x = z)).
          -- subst. apply Rlt_asym in E1. contradiction.
          -- destruct (bool_decide (x < z)%R) eqn:E3; [reflexivity|].
            apply bool_decide_eq_false in E3. enough (x < z)%R by contradiction.
            apply Rlt_trans with (r2:=y); done.
        * apply bool_decide_eq_false in E1, E2. apply Rnot_lt_le in E1, E2.
          destruct (decide (x = z)).
          -- subst. pose proof (Rle_antisym _ _ E1 E2). done.
          -- destruct (bool_decide (x < z)%R) eqn:E3; [|reflexivity].
            apply bool_decide_eq_true in E3. enough (¬ (x < z)%R) by contradiction.
            apply Rlt_asym. pose proof (Rle_trans _ _ _ E2 E1).
            destruct (Rle_lt_or_eq _ _ H); done.
  Qed.

  Global Instance R_compare_lawful : LawfulCompare R := {}.

End R_compare.

Section string_compare.
  Lemma string_compare_eq_iff {s1 s2 : string} :
      String.compare s1 s2 = Eq ↔ s1 = s2.
  Proof.
    split; intros.
    - by apply String.compare_eq_iff.
    - subst. induction s2; simpl; auto. enough (Ascii.compare a a = Eq) by (rewrite H; done).
      clear IHs2. unfold Ascii.compare. by apply BinNat.N.compare_eq_iff.
  Qed.

  Lemma ascii_compare_eq_iff {x y} :
      Ascii.compare x y = Eq ↔ x = y.
  Proof.
    split; intros.
    - by apply Ascii.compare_eq_iff.
    - subst. unfold Ascii.compare. by apply BinNat.N.compare_eq_iff.
  Qed.

  Lemma ascii_compare_trans {x y z c} :
      Ascii.compare x y = c → Ascii.compare y z = c → Ascii.compare x z = c.
  Proof.
    unfold Ascii.compare. intros. destruct c.
    - rewrite BinNat.N.compare_eq_iff in *. congruence.
    - rewrite BinNat.N.compare_lt_iff in *. lia.
    - rewrite BinNat.N.compare_gt_iff in *. lia.
  Qed.

  Global Instance string_comparable : Comparable string := String.compare.

  Global Instance string_compare_eq : CompareEq string.
  Proof. intros x y. apply string_compare_eq_iff. Qed.

  Global Instance string_compare_total : CompareTotal string.
  Proof.
    intros x y. unfold compare, string_comparable.
    destruct (x ?= y)%string eqn:E1; try (left; done). right.
    destruct (y ?= x)%string eqn:E2; try done. exfalso. generalize dependent y.
    induction x; intros.
    - simpl in *. destruct y; simpl in *; discriminate.
    - simpl in *. destruct y; simpl in *; [discriminate|]. destruct (Ascii.compare a0 a) eqn:E3.
      + destruct (Ascii.compare a a0) eqn:E4.
        * apply IHx in E2; auto.
        * discriminate.
        * unfold Ascii.compare in E3, E4. rewrite BinNat.N.compare_eq_iff in E3.
          rewrite E3 in E4. by rewrite BinNat.N.compare_refl in E4.
      + discriminate.
      + destruct (Ascii.compare a a0) eqn:E4.
        * unfold Ascii.compare in E3, E4. rewrite BinNat.N.compare_eq_iff in E4.
          rewrite E4 in E3. by rewrite BinNat.N.compare_refl in E3.
        * discriminate.
        * apply BinNat.N.compare_gt_iff in E3. apply BinNat.N.compare_gt_iff in E4.
          lia.
  Qed.

  Global Instance string_compare_antisym : CompareAntiSym string.
  Proof. intros x y. apply String.compare_antisym. Qed.


  Global Instance string_compare_trans : CompareTrans string.
  Proof.
    intros x y z c ??. unfold compare, string_comparable in *.
    destruct (x ?= y)%string eqn:E1; subst c.
    - apply String.compare_eq_iff in E1, H0. subst. by apply string_compare_eq_iff.
    - generalize dependent z. generalize dependent y. induction x; intros; destruct y;
        try discriminate; destruct z; try discriminate; auto.
      simpl in *. destruct (Ascii.compare a a0) eqn:E2.
      + apply ascii_compare_eq_iff in E2. subst a0. destruct (Ascii.compare a a1); try done.
        apply IHx with (y:=y); done.
      + destruct (Ascii.compare a0 a1) eqn:E3; try done.
        * apply ascii_compare_eq_iff in E3. subst a1. by rewrite E2.
        * pose proof (ascii_compare_trans E2 E3). by rewrite H.
      + destruct (Ascii.compare a0 a1) eqn:E3; try done.
    - generalize dependent z. generalize dependent y. induction x; intros; destruct y;
        try discriminate; destruct z; try discriminate; auto.
      simpl in *. destruct (Ascii.compare a a0) eqn:E2.
      + apply ascii_compare_eq_iff in E2. subst a0. destruct (Ascii.compare a a1); try done.
        apply IHx with (y:=y); done.
      + destruct (Ascii.compare a0 a1) eqn:E3; try done.
      + destruct (Ascii.compare a0 a1) eqn:E3; try done.
        * apply ascii_compare_eq_iff in E3. subst a1. by rewrite E2.
        * pose proof (ascii_compare_trans E2 E3). by rewrite H.
  Qed.

  Global Instance string_compare_lawful : LawfulCompare string := {}.

End string_compare.

Section list_compare.
  Context {A : Type}.

  Ltac list_auto A Heq :=
  repeat lazymatch goal with
  | |- ?x = ?x =>
      reflexivity
  | H : ?xs = ?xs ++ _ |- _ =>
      rewrite <-(app_nil_r xs) in H at 1
  | H : ?xs ++ _ = ?xs |- _ =>
      symmetry in H
  | H : ?xs ++ _ = ?xs ++ _ |- _ =>
      apply app_inv_head in H
  | H : _ :: _ = _ :: _ |- _ =>
      injection H; intros; clear H; subst
  | H : [] = _ :: _ |- _ =>
      inversion H
  | H : compare ?x ?x = Lt |- _ =>
      rewrite (proj2 (Heq _ _) eq_refl) in H; discriminate
  | H : compare ?x ?x = Gt |- _ =>
      rewrite (proj2 (Heq _ _) eq_refl) in H; discriminate
  | H1 : ?p1 ++ _ :: _ = ?p2 ++ _ :: _,
    H2 : ?p2 ++ _ :: _ = ?p1 ++ _ :: _ |- _ =>
      symmetry in H2
  | H1 : ?p1 ++ ?x1 :: ?xs1 = ?p2 ++ ?x2 :: ?xs2,
    H2 : ?p1 ++ ?y1 :: ?ys1 = ?p2 ++ ?y2 :: ?ys2 |- _ =>
      assert (p1 = p2) as Hp;
      [ eapply (prefix_eq H1 H2); intros Heq; subst
      | subst; apply app_inv_head in H1, H2 ]
  | H : compare ?x ?x = _ |- _ =>
      rewrite (proj2 (Heq _ _) eq_refl) in H; try discriminate H
  | H1 : compare ?x1 ?x2 = _,
    H2 : compare ?x1 ?x2 = _ |- _ =>
      rewrite H1 in H2; discriminate H2
  | Htrans : forall (x y z : A) (c : comparison), compare x y = c -> compare y z = c -> compare x z = c,
    H1 : compare ?x1 ?x2 = ?c,
    H2 : compare ?x2 ?x3 = ?c |- _ =>
      pose proof (Htrans x1 x2 x3 c H1 H2); clear H1 H2
  | Hcmp_opp : (forall x y, compare y x = CompOpp (compare x y)),
    H1 : compare ?x1 ?x2 = ?c, H2 : compare ?x2 ?x1 = ?c |- _ =>
      rewrite Hcmp_opp, H2 in H1; simpl in H1; discriminate H1
  end.

  Section raw_list_compare.
    Context (comp : A → A → comparison).
    Definition raw_compare_eq_iff_In (l1 l2 : list A)
      := ∀ x y, In x l1 → In y l2 → comp x y = Eq ↔ x = y.

    Definition raw_compare_total_In (l1 l2 : list A)
      := ∀ x y, In x l1 → In y l2 → comp x y ≠ Gt ∨ comp y x ≠ Gt.

    Definition raw_compare_antisym_In (l1 l2 : list A)
      := ∀ x y, In x l1 → In y l2 → comp x y = CompOpp (comp y x).

    Definition raw_compare_trans_In (l1 l2 l3 : list A) := ∀ x y z c,
        In x l1 →
        In y l2 →
        In z l3 →
        comp x y = c →
        comp y z = c →
        comp x z = c.

    Local Lemma compare_diag_ne_lt (x : A) :
      (comp x x = Eq ↔ x = x) →
      comp x x ≠ Lt.
    Proof. intros. rewrite (proj2 H eq_refl). done. Qed.

    Local Lemma compare_diag_ne_gt (x : A) :
      (comp x x = Eq ↔ x = x) →
      comp x x ≠ Gt.
    Proof. intros. rewrite (proj2 H eq_refl). done. Qed.

    Lemma raw_list_compare_eq_iff {xs ys} :
      raw_compare_eq_iff_In xs ys →
      raw_compare_eq_iff (list_compare comp) xs ys.
    Proof.
      unfold raw_compare_eq_iff, raw_compare_eq_iff_In.
      generalize dependent ys. induction xs as [|x xs].
      - simpl in *. intros. destruct ys; done.
      - simpl in *. intros. destruct ys; [done|].
        destruct (comp x a) eqn:E.
        + rewrite IHxs.
          * split; intros.
            -- f_equal; auto. apply H; simpl; auto.
            -- by inversion H0.
          * intros. apply H; simpl; auto.
        + split; [discriminate|]. intros. inversion H0. subst a.
          apply compare_diag_ne_lt in E; [destruct E|]. apply H; simpl; auto.
        + split; [discriminate|]. intros. inversion H0. subst a.
          apply compare_diag_ne_gt in E; [destruct E|]. apply H; simpl; auto.
    Qed.

    Lemma raw_list_compare_total {xs ys} :
      (∀ x y, raw_compare_eq_iff comp x y) →
      raw_compare_total_In xs ys →
      raw_compare_total (list_compare comp) xs ys.
    Proof.
      intros Heq Htotal. generalize dependent ys. induction xs as [|x xs]; simpl in *; intros.
      1:{ unfold raw_compare_total. simpl. destruct ys; simpl; auto. }
      unfold raw_compare_total. simpl. destruct ys as [|y ys].
      1:{ right. auto. }
      simpl. destruct (comp x y) eqn:E.
      - simpl. apply Heq in E; simpl; auto. subst. pose proof (Heq y y).
        destruct (comp y y) eqn:E1; auto.
        + apply IHxs. intros ????. apply Htotal; simpl; auto.
        + apply compare_diag_ne_gt in E1; [destruct E1|]. apply Heq.
      - auto.
      - right. destruct (comp y x) eqn:E1; auto.
        + apply Heq in E1; simpl; auto. subst. apply compare_diag_ne_gt in E; auto.
          apply Heq; simpl; auto.
        + specialize (Htotal x y). do 2 forward Htotal by (simpl; auto). by destruct Htotal.
    Qed.

    Lemma raw_list_compare_antisym {xs ys} :
      (∀ x y, raw_compare_eq_iff comp x y) →
      raw_compare_antisym_In xs ys →
      raw_compare_antisym (list_compare comp) xs ys.
    Proof.
      intros Heq Hantisym. generalize dependent ys. induction xs as [|x xs]; simpl in *; intros.
      1:{ unfold raw_compare_antisym. simpl. destruct ys; auto. }
      unfold raw_compare_antisym. simpl. destruct ys as [|y ys]; auto.
      simpl. destruct (comp x y) eqn:E.
      - apply Heq in E; simpl; auto. subst y. destruct (comp x x) eqn:E1.
        2:{ apply compare_diag_ne_lt in E1; [destruct E1|]. apply Heq; simpl; auto. }
        2:{ apply compare_diag_ne_gt in E1; [destruct E1|]. apply Heq; simpl; auto. }
        clear E1. apply IHxs; auto.
        intros ????. apply Hantisym; simpl; auto.
      - destruct (comp y x) eqn:E1; simpl; auto.
        + opose proof (Hantisym x y _ _); simpl; auto. rewrite E in H. rewrite E1 in H. done.
        + opose proof (Hantisym x y _ _); simpl; auto. rewrite E in H. rewrite E1 in H. done.
      - destruct (comp y x) eqn:E1; simpl; auto.
        + opose proof (Hantisym x y _ _); simpl; auto. rewrite E in H. rewrite E1 in H. done.
        + opose proof (Hantisym x y _ _); simpl; auto. rewrite E in H. rewrite E1 in H. done.
    Qed.

    Lemma raw_list_compare_trans xs ys zs :
      (∀ x y, raw_compare_eq_iff comp x y) →
      (∀ x y, raw_compare_antisym comp x y) →
      raw_compare_trans_In xs ys zs →
      raw_compare_trans (list_compare comp) xs ys zs.
    Proof.
      intros Heq Hantisym Htrans c.
      generalize dependent zs. generalize dependent ys.
      induction xs as [|x xs].
      1:{ simpl. intros. destruct ys; destruct zs; simpl in *; subst; done. }
      destruct ys as [|y ys]; simpl; intros; subst; [destruct zs; done|].
      destruct zs as [|z zs]; [done|]. destruct (comp x y) eqn:E1.
      - apply Heq in E1. subst y. destruct (comp x z) eqn:E2; try done. apply Heq in E2.
        subst z. apply IHxs with (ys:=ys); try done. intros ???. intros.
        apply (Htrans x0 y z); simpl; auto.
      - destruct (comp y z) eqn:E2; try discriminate.
        + apply Heq in E2. subst z. rewrite E1. done.
        + destruct (comp x z) eqn:E3; auto.
          * opose proof (Htrans x y z _ _ _ _ E1 E2); simpl; auto. rewrite E3 in H. done.
          * opose proof (Htrans x y z _ _ _ _ E1 E2); simpl; auto. rewrite E3 in H. done.
      - destruct (comp y z) eqn:E2; try discriminate.
        + apply Heq in E2. subst z. rewrite E1. done.
        + destruct (comp x z) eqn:E3; auto.
          * opose proof (Htrans x y z _ _ _ _ E1 E2); simpl; auto. rewrite E3 in H. done.
          * opose proof (Htrans x y z _ _ _ _ E1 E2); simpl; auto. rewrite E3 in H. done.
    Qed.

  End raw_list_compare.


  Global Instance list_comparable `{Comparable A} : Comparable (list A) := list_compare compare.

  Global Instance list_compare_eq `{CompareEq A} : CompareEq (list A).
  Proof.
    unfold CompareEq. intros. apply raw_list_compare_eq_iff. intros ????. apply compare_eq_iff.
  Qed.

  Global Instance list_compare_total `{CompareEq A, !CompareTotal A} : CompareTotal (list A).
  Proof.
    unfold CompareTotal. intros. apply raw_list_compare_total.
    - apply compare_eq_iff.
    - intros x0 y0 ??. apply compare_total.
  Qed.

  Global Instance list_compare_antisym `{CompareEq A, !CompareAntiSym A} : CompareAntiSym (list A).
  Proof.
    unfold CompareAntiSym. intros. apply raw_list_compare_antisym.
    - apply compare_eq_iff.
    - intros x0 y0 ??. apply compare_antisym.
  Qed.

  Global Instance list_compare_trans `{CompareEq A, !CompareAntiSym A, !CompareTrans A} : CompareTrans (list A).
  Proof.
    unfold CompareTrans. intros. apply raw_list_compare_trans with (ys:=y).
    - apply compare_eq_iff.
    - apply compare_antisym.
    - intros x0 y0 z0 ????. apply compare_trans.
    - assumption.
    - assumption.
  Qed.

  Global Instance list_compare_lawful `{LawfulCompare A} : LawfulCompare (list A) := {}.

End list_compare.
