From Stdlib Require Import List Reals.
From stdpp Require Import base tactics.

Class Comparable (A : Type) := {
  compare : A → A → comparison;
  compare_eq : ∀ x y, compare x y = Eq ↔ x = y;
  compare_total : ∀ x y, compare x y ≠ Gt ∨ compare y x ≠ Gt;
  compare_trans : ∀ x y z c, compare x y = c → compare y z = c → compare x z = c;
  compare_antisym: ∀ x y, compare x y = CompOpp (compare y x);
}.

Lemma compare_diag {A} `{Comparable A} {x} : compare x x = Eq.
Proof. assert (x = x) by reflexivity. apply compare_eq in H0. done. Qed.

Lemma compare_trans_le {A} `{Comparable A} x y z :
  compare x y ≠ Gt → compare y z ≠ Gt → compare x z ≠ Gt.
Proof.
  intros. intros contra. destruct (compare x y) eqn:E; [| |done].
  - destruct (compare y z) eqn:E'; [| |done].
    + pose proof (compare_trans _ _ _ _ E E'). congruence.
    + apply compare_eq in E. subst. congruence.
  - destruct (compare y z) eqn:E'; [| |done].
    + apply compare_eq in E'. subst. congruence.
    + pose proof (compare_trans _ _ _ _ E E'). congruence.
Qed.

Lemma compare_antisym_le {A} `{Comparable A} x y :
  compare x y ≠ Gt → compare y x ≠ Gt → x = y.
Proof.
  intros. pose proof (compare_antisym x y).
  destruct (compare x y) eqn:E; [| |done].
  - apply compare_eq in E. done.
  - destruct (compare y x) eqn:E1; [| |done].
    + by apply compare_eq in E1.
    + by simpl in H2.
Qed.

Program Definition nat_comparable : Comparable nat := {| compare := Nat.compare |}.
Next Obligation. apply Nat.compare_eq_iff. Qed.
Next Obligation.
  intros. destruct (x ?= y) eqn:E1; try (left; done). right. destruct (y ?= x) eqn:E2; try done.
  apply Nat.compare_gt_iff in E1, E2. lia.
Qed.
Next Obligation.
  intros. destruct (x ?= y) eqn:E1; subst c.
  - apply Nat.compare_eq_iff in E1, H0. subst. by apply Nat.compare_eq_iff.
  - apply Nat.compare_lt_iff in E1, H0. apply Nat.compare_lt_iff. by trans y.
  - apply Nat.compare_gt_iff in E1, H0. apply Nat.compare_gt_iff. by trans y.
Qed.
Next Obligation. intros. apply Nat.compare_antisym. Qed.

Global Existing Instance nat_comparable.

Program Definition Z_comparable : Comparable Z := {| compare := Z.compare |}.
Next Obligation. apply Z.compare_eq_iff. Qed.
Next Obligation.
  intros. destruct (x ?= y)%Z eqn:E1; try (left; done). right. destruct (y ?= x)%Z eqn:E2; try done.
  apply Z.compare_gt_iff in E1, E2. lia.
Qed.
Next Obligation.
  intros. destruct (x ?= y)%Z eqn:E1; subst c.
  - apply Z.compare_eq_iff in E1, H0. subst. by apply Z.compare_eq_iff.
  - apply Z.compare_lt_iff in E1, H0. apply Z.compare_lt_iff. by trans y.
  - apply Z.compare_gt_iff in E1, H0. apply Z.compare_gt_iff. by trans y.
Qed.
Next Obligation. intros. apply Z.compare_antisym. Qed.

Global Existing Instance Z_comparable.

#[local] Ltac list_auto A Heq :=
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

Program Definition list_comparable {A} `{Comparable A} : Comparable (list A)
  := {| compare := list_compare compare |}.
Next Obligation.
  intros ?? xs ys.
  destruct (list_compareP compare compare_eq xs ys), (list_compareP compare compare_eq ys xs);
    subst; split; intros; first [list_auto A compare_eq; try discriminate].
  all: pose proof (compare_eq y y); epose proof (proj2 H0 eq_refl); congruence.
Qed.
Next Obligation.
  intros ?? xs ys.
  destruct (list_compareP compare compare_eq xs ys), (list_compareP compare compare_eq ys xs);
    subst; first [list_auto A compare_eq; try discriminate; try auto].
  all: repeat rewrite <-app_assoc in *; simpl in *; list_auto A compare_eq.
  assert (prefix = prefix0).
  { apply (prefix_eq H3 H4); intros contra; subst.
    - rewrite compare_diag in H2. discriminate.
    - rewrite compare_diag in H5. discriminate. }
  subst prefix0. assert (x :: xs' = y0 :: ys'0).
  { eapply app_inv_head. exact H4. }
  assert (y :: ys' = x0 :: xs'0).
  { eapply app_inv_head. exact H3. }
  inversion H0. inversion H1. subst x0 y0. destruct (compare_total x y); contradiction.
Qed.
Next Obligation.
  intros ?? xs ys zs c. apply (list_compare_trans).
  - apply compare_eq.
  - apply compare_trans.
  - intros. apply compare_antisym.
Qed.
Next Obligation.
  intros. apply list_compare_antisym.
  - apply compare_eq.
  - intros. apply compare_antisym.
Qed.

Global Existing Instance list_comparable.

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

Program Definition R_comparable {A} `{Comparable A} : Comparable R
  := {| compare := R_compare |}.
Next Obligation.
  intros. unfold R_compare. destruct (decide (x = y)).
  - by subst.
  - destruct (R_ltb x y); done.
Qed.
Next Obligation.
  intros. destruct (Rle_or_lt x y).
  - left. unfold R_compare, R_ltb. apply Rle_lt_or_eq in H0. destruct H0.
    + pose proof (Rlt_not_eq _ _ H0). destruct (decide (x = y)); [done|].
      destruct (bool_decide ((x < y)%R)) eqn:E.
      * apply bool_decide_eq_true in E. done.
      * apply bool_decide_eq_false in E. done.
    + subst. destruct (decide (y = y)); done.
  - right. unfold R_compare, R_ltb. apply Rlt_le in H0. apply Rle_lt_or_eq in H0. destruct H0.
    + pose proof (Rlt_not_eq _ _ H0). destruct (decide (y = x)); [done|].
      destruct (bool_decide ((y < x)%R)) eqn:E.
      * apply bool_decide_eq_true in E. done.
      * apply bool_decide_eq_false in E. done.
    + subst. destruct (decide (x = x)); done.
Qed.
Next Obligation.
  intros. unfold R_compare in *. destruct (decide (x = y)).
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
           destruct (Rle_lt_or_eq _ _ H0); done.
Qed.
Next Obligation.
  intros. unfold R_compare. destruct (decide (x = y)).
  - subst. destruct (decide (y = y)); done.
  - destruct (decide (y = x)); [done|]. unfold R_ltb. destruct (bool_decide (x < y)%R) eqn:E1.
    + apply bool_decide_eq_true in E1. destruct (bool_decide (y < x)%R) eqn:E2; [|done].
      apply bool_decide_eq_true in E2. apply Rlt_asym in E2. done.
    + apply bool_decide_eq_false in E1. destruct (bool_decide (y < x)%R) eqn:E2; [done|].
      apply bool_decide_eq_false in E2. apply Rnot_lt_le in E1, E2.
      pose proof (Rle_antisym _ _ E1 E2). subst. contradiction.
Qed.

Global Existing Instance R_comparable.
