From Stdlib Require Import List Reals.
From stdpp Require Import base tactics sorting.
From MRC Require Import Prelude Tactics Comparable.

Record listbag (A : Type) := Listbag {
  listbag_car : list A;
}.

Arguments listbag_car {_} _ : assert.
Arguments Listbag {_} _ : assert.

Lemma listbag_eq_iff {A} {b1 b2 : listbag A} :
  b1 = b2 ↔ listbag_car b1 = listbag_car b2.
Proof.
  destruct b1, b2. simpl. split; intros.
  - by inversion H.
  - by subst.
Qed.

Section listbag_compare.
  Context {A : Type}.

  Section raw_listbag_compare.
    Context (comp : A → A → comparison).

    Definition listbag_compare (b1 b2 : listbag A)
      := list_compare comp (listbag_car b1) (listbag_car b2).

    Lemma raw_listbag_compare_eq_iff {b1 b2} :
      raw_compare_eq_iff_In comp (listbag_car b1) (listbag_car b2) →
      raw_compare_eq_iff listbag_compare b1 b2.
    Proof.
      intros H. unfold listbag_compare, raw_compare_eq_iff. rewrite listbag_eq_iff.
      by apply raw_list_compare_eq_iff.
    Qed.

    Lemma raw_listbag_compare_total {b1 b2} :
      (∀ x y, raw_compare_eq_iff comp x y) →
      raw_compare_total_In comp (listbag_car b1) (listbag_car b2) →
      raw_compare_total listbag_compare b1 b2.
    Proof.
      intros Heq Htotal. unfold listbag_compare, raw_compare_total.
      by apply raw_list_compare_total.
    Qed.

    Lemma raw_listbag_compare_antisym {b1 b2} :
      (∀ x y, raw_compare_eq_iff comp x y) →
      raw_compare_antisym_In comp (listbag_car b1) (listbag_car b2) →
      raw_compare_antisym listbag_compare b1 b2.
    Proof.
      intros Heq Hantisym. unfold listbag_compare, raw_compare_antisym.
      by apply raw_list_compare_antisym.
    Qed.

    Lemma raw_listbag_compare_trans b1 b2 b3 :
      (∀ x y, raw_compare_eq_iff comp x y) →
      (∀ x y, raw_compare_antisym comp x y) →
      raw_compare_trans_In comp (listbag_car b1) (listbag_car b2) (listbag_car b3) →
      raw_compare_trans listbag_compare b1 b2 b3.
    Proof.
      intros Heq Hantisym Htrans. unfold listbag_compare, raw_compare_trans.
      by apply raw_list_compare_trans.
    Qed.
  End raw_listbag_compare.

  Global Instance listbag_comparable `{Comparable A} : Comparable (listbag A) := listbag_compare compare.

  Global Instance listbag_compare_eq `{CompareEq A} : CompareEq (listbag A).
  Proof.
    unfold CompareEq. intros. apply raw_listbag_compare_eq_iff. intros ????. apply compare_eq_iff.
  Qed.

  Global Instance listbag_compare_total `{CompareEq A, !CompareTotal A} : CompareTotal (listbag A).
  Proof.
    unfold CompareTotal. intros. apply raw_listbag_compare_total.
    - apply compare_eq_iff.
    - intros x0 y0 ??. apply compare_total.
  Qed.

  Global Instance listbag_compare_antisym `{CompareEq A, !CompareAntiSym A} : CompareAntiSym (listbag A).
  Proof.
    unfold CompareAntiSym. intros. apply raw_listbag_compare_antisym.
    - intros x0 y0. apply compare_eq_iff.
    - intros x0 y0 ??. apply compare_antisym.
  Qed.

  Global Instance listbag_compare_trans `{CompareEq A, !CompareAntiSym A, !CompareTrans A} : CompareTrans (listbag A).
  Proof.
    unfold CompareTrans. intros. apply raw_listbag_compare_trans with (b2:=y).
    - apply compare_eq_iff.
    - apply compare_antisym.
    - intros ???????. apply compare_trans.
    - exact H0.
    - exact H1.
  Qed.

  Global Instance listbag_compare_lawful `{LawfulCompare A} : LawfulCompare (listbag A) := {}.
End listbag_compare.

Section listbag.
  Context {A : Type}.
  Context `{Hlawful : LawfulCompare A}.
  Context `{!EqDecision A}.
  Implicit Types l : list A.

  Fixpoint sorted_b l : bool :=
    match l with
    | [] => true
    | x :: [] => true
    | x :: (y :: _) as rest =>
        match compare x y with
        | Gt => false
        | _ => sorted_b rest
        end
    end.

  Arguments sorted_b !_ : assert.

  Class SortedListBag (b : listbag A) := listbag_sorted : sorted_b (listbag_car b).

  Definition mkSortedListBag {b : listbag A} (H : sorted_b (listbag_car b))
                             : SortedListBag b
    := H.

  Definition sorted_listbag := {b : listbag A | SortedListBag b}.

  Lemma sorted_listbag_eq {b1 b2 : sorted_listbag} : b1 = b2 ↔ `b1 = `b2.
  Proof.
    destruct b1, b2. simpl. split; intros.
    - inversion H0. done.
    - unfold SortedListBag in s, s0. subst. f_equal. apply Is_true_pi.
  Qed.

  Definition comparable_lt := λ x y, compare x y ≠ Gt.

  Global Instance comparable_lt_total : Total comparable_lt.
  Proof using A Hlawful. unfold Total, comparable_lt. apply compare_total. Qed.

  Global Instance comparable_lt_trans : Transitive comparable_lt.
  Proof using A Hlawful. unfold Transitive, comparable_lt. apply compare_trans_le. Qed.

  Global Instance comparable_lt_antisymm : AntiSymm eq comparable_lt.
  Proof using A Hlawful. unfold AntiSymm, comparable_lt. apply compare_antisym_le. Qed.

  Global Instance comparable_lt_dec : RelDecision comparable_lt.
  Proof. solve_decision. Qed.

  Lemma sorted_b_sorted {l} : sorted_b l ↔ Sorted comparable_lt l.
  Proof with auto.
    induction l as [|x xs].
    - simpl. split...
    - simpl. destruct xs; split...
      + simpl in IHxs. destruct (compare x a) eqn:E; [| |done].
        all: simpl; intros; assert (H1:=proj1 IHxs H0); constructor; auto; constructor;
          intros contra; congruence.
      + intros. inversion H0. subst a0. rename a into y. subst l. simpl in *.
        assert (H5:=proj2 IHxs H3). clear IHxs. destruct (compare x y) eqn:E; try assumption.
        inversion H4. congruence.
  Qed.

  Global Instance listbag_EqDecision `{EqDecision A} : EqDecision (listbag A).
  Proof.
    intros b1 b2. unfold Decision, EqDecision. destruct b1 as [b1], b2 as [b2].
    destruct (list_eq_dec b1 b2).
    - subst. left. f_equal.
    - right. by inversion 1.
  Qed.

  Local Fixpoint dedup_aux (x : A) (xs : list A) `{EqDecision A} : list A :=
    match xs with
    | [] => [x]
    | x' :: xs => if (decide (x = x')) then dedup_aux x xs else x :: dedup_aux x' xs
    end.

  Definition dedup (l : list A) `{EqDecision A} : list A :=
    match l with
    | [] => []
    | h :: t => dedup_aux h t
    end.

  Global Instance listbag_Size `{EqDecision A} : Size (listbag A)
    := λ b, length (dedup (listbag_car b)).

  Lemma merge_sort_sorted_b l : sorted_b (merge_sort comparable_lt l).
  Proof using A Hlawful.
    apply sorted_b_sorted. apply Sorted_merge_sort. apply comparable_lt_total.
  Qed.

  Program Definition listbag_from_list (l : list A) : sorted_listbag
    := Listbag (merge_sort comparable_lt l).
  Next Obligation.
    simpl. intros. unfold SortedListBag. simpl. apply merge_sort_sorted_b.
  Qed.

  Local Fixpoint list_count (x : A) (l : list A) : nat :=
    match l with
    | [] => O
    | y :: ys => if decide (x = y) then S (list_count x ys) else (list_count x ys)
    end.

  Definition listbag_count (x : A) (b : listbag A) : nat :=
    list_count x (listbag_car b).

  Global Instance listbag_elem_of : ElemOf A (listbag A) := λ x b, elem_of x (listbag_car b).

  Program Definition listbag_union b1 b2 `{SortedListBag b1} `{SortedListBag b2} : sorted_listbag
    := Listbag (list_merge comparable_lt (listbag_car b1) (listbag_car b2)).
  Next Obligation.
    intros. unfold SortedListBag. simpl. apply sorted_b_sorted. apply Sorted_list_merge.
    - apply comparable_lt_total.
    - apply sorted_b_sorted. apply listbag_sorted.
    - apply sorted_b_sorted. apply listbag_sorted.
  Qed.

  Global Instance sorted_listbag_union : Union (sorted_listbag) :=
    λ b1 b2, @listbag_union (`b1) (`b2) (proj2_sig b1) (proj2_sig b2).

  Lemma listbag_union_comm b1 b2 `{SortedListBag b1} `{SortedListBag b2}
    : listbag_union b1 b2 = listbag_union b2 b1.
  Proof.
    unfold listbag_union. apply sorted_listbag_eq. simpl. f_equal.
    apply Sorted_unique with (R:=comparable_lt); try typeclasses eauto.
    - apply Sorted_list_merge; try typeclasses eauto.
      + apply sorted_b_sorted. apply listbag_sorted.
      + apply sorted_b_sorted. apply listbag_sorted.
    - apply Sorted_list_merge; try typeclasses eauto.
      + apply sorted_b_sorted. apply listbag_sorted.
      + apply sorted_b_sorted. apply listbag_sorted.
    - etrans.
      + apply merge_Permutation.
      + symmetry. rewrite Permutation_app_comm. apply merge_Permutation.
  Qed.

  Global Instance sorted_list_bag_union_comm : Comm (=) (@union sorted_listbag sorted_listbag_union).
  Proof.
    intros b1 b2. unfold union, sorted_listbag_union. apply listbag_union_comm.
  Qed.

  Definition listbag_map f (b : listbag A) := @Listbag A (map f (listbag_car b)).

End listbag.

Global Hint Extern 1 (SortedListBag ?b) =>
  match goal with
  | H : Is_true (sorted_b ?b) = true |- _ => exact (mkSortedListBag H)
  | _ => fail "No hypothesis n = 5 found"
  end : typeclass_instances.
