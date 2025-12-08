From stdpp Require Import sets vector gmap.
From MRC Require Import Prelude.
From MRC Require Import Tactics.

Lemma exists_iff_exists_weaken {V} (P Q : V → Prop) :
  (∀ v, P v ↔ Q v) →
  ((∃ v, P v) ↔ (∃ v, Q v)).
Proof.
  intros. split; intros [v Hv]; exists v; apply H; auto.
Qed.

Notation "x ∈? X" := (bool_decide (x ∈ X)) (at level 70) : stdpp_scope.
Notation "x ∉? X" := (bool_decide (x ∉ X)) (at level 70) : stdpp_scope.

Notation "x =? y" := (bool_decide (x = y)) (at level 70) : stdpp_scope.
Notation "x ≠? y" := (bool_decide (x ≠ y)) (at level 70) : stdpp_scope.

Lemma eq_dec_eq {A} {x y : A} `{EqDecision A} :
  x =? y ↔ x = y.
Proof with auto.
  destruct (x =? y) eqn:E.
  - rewrite bool_decide_eq_true in E. split...
  - rewrite bool_decide_eq_false in E. rewrite Is_true_true. split; intros.
    + discriminate.
    + contradiction.
Qed.

Lemma eq_dec_refl {A} {x : A} `{EqDecision A} :
  x =? x = true.
Proof with auto.
  destruct (x =? x) eqn:E.
  - rewrite bool_decide_eq_true in E. split...
  - rewrite bool_decide_eq_false in E. contradiction.
Qed.

Lemma Is_true_andb {b1 b2} :
  Is_true (b1 && b2) ↔ Is_true b1 ∧ Is_true b2.
Proof.
  rewrite Is_true_true. rewrite andb_true_iff. do 2 rewrite <- Is_true_true. reflexivity.
Qed.

Lemma Is_true_orb {b1 b2} :
  Is_true (b1 || b2) ↔ Is_true b1 ∨ Is_true b2.
Proof.
  rewrite Is_true_true. rewrite orb_true_iff. do 2 rewrite <- Is_true_true. reflexivity.
Qed.

Definition is_some {A} (opt : option A) : bool :=
  match opt with | Some x => true | None => false end.

Class InhabitedSigDecision {A} P := decide_inhabited_sig : {x : A | P x} + {∀ x : A, ¬ P x}.
Arguments InhabitedSigDecision (A P)%_type.
Notation "{ x ? P }" := (InhabitedSigDecision (fun x => P)) (x binder, at level 0) : type_scope.
Notation "{ x : A ? P }" := (InhabitedSigDecision (A:=A) (fun x => P)) (x binder, at level 0) : type_scope.

Lemma eq_iff : forall (P Q : Prop), P = Q -> (P <-> Q).
Proof. intros P Q H. rewrite H. apply iff_refl. Qed.

Definition list_to_vec_n {A n} (l : list A) (H : length l = n) : vec A n :=
  eq_rect _ (fun m => vec A m) (list_to_vec l) _ H.

Definition set_to_list {A} `{Countable A} `{EqDecision A} (s : gset A) : list A :=
  set_fold (λ i x, i :: x) [] s.

Lemma lookup_total_union_l' {K A M} `{FinMap K M} `{Inhabited A} (m1 m2 : M A) i x :
  m1 !! i = Some x →
  (m1 ∪ m2) !!! i = x.
Proof with auto.
  intros. unfold lookup_total, map_lookup_total. rewrite lookup_union_l'... rewrite H8...
Qed.

Lemma lookup_total_union_r {K A M} `{FinMap K M} `{Inhabited A} (m1 m2 : M A) i :
  m1 !! i = None →
  (m1 ∪ m2) !!! i = m2 !!! i.
Proof with auto.
  intros. unfold lookup_total, map_lookup_total. rewrite lookup_union_r...
Qed.



(** Facts about [list] *)
Lemma length_nonzero_iff_cons {A} (l : list A) n :
  length l = S n ↔ ∃ x xs, l = x :: xs ∧ length xs = n.
Proof with auto.
  intros. split; intros.
  - destruct l eqn:E; simpl in H; [discriminate|]. exists a, l0...
  - destruct H as (?&?&->&?). simpl. lia.
Qed.

Lemma length_nonzero_iff_snoc {A} (l : list A) n :
  length l = S n ↔ ∃ xs x, l = xs ++ [x] ∧ length xs = n.
Proof with auto.
  intros. split; intros.
  - destruct l eqn:E using rev_ind; simpl in H; [discriminate|]. exists l0, x. split...
    rewrite length_app in H. simpl in H. lia.
  - destruct H as (?&?&->&?). rewrite length_app. simpl. lia.
Qed.

Lemma list_lookup_None {A} (l : list A) i :
  l !! i = None ↔ length l ≤ i.
Proof with auto.
  generalize dependent i. induction l; intros.
  - rewrite lookup_nil. simpl. split... lia.
  - rewrite lookup_cons. destruct i.
    + simpl. split; intros; [discriminate | lia].
    + simpl. rewrite IHl. split; lia.
Qed.


(** [OfSameLength] type class provides a compositional way to limit pairs of lists
    to those of the same length. It uses the power of instance synthesization to
    deduce length equality of lists based on syntatic structure of lists.
    The main use case for this is in zip pairs. We can prove more intersting facts
    about the zipped result of two lists, if we know they are of the same length. *)
Class OfSameLength {A B} (l1 : list A) (l2 : list B) :=
  of_same_length : length l1 = length l2.


Instance OfSameLength_pi {A B} (l1 : list A) (l2 : list B) :
  ProofIrrel (OfSameLength l1 l2).
Proof. apply eq_pi. solve_decision. Qed.

Instance of_same_length_nil {A B} : @OfSameLength A B [] [].
Proof. reflexivity. Defined.

Instance of_same_length_id {A} {l : list A} : OfSameLength l l | 0.
Proof. reflexivity. Qed.

Instance of_same_length_cons {A B} {x1 : A} {l1 : list A} {x2 : B} {l2 : list B}
  `{OfSameLength A B l1 l2} : OfSameLength (x1::l1) (x2::l2).
Proof. unfold OfSameLength in *. do 2 rewrite length_cons. lia. Qed.

Instance of_same_length_singleton {A B} {x1 : A} {x2 : B} : OfSameLength [x1] [x2].
Proof. unfold OfSameLength in *. simpl. reflexivity. Qed.

Instance of_same_length_app {A B} {l1 l1' : list A} {l2 l2' : list B}
  `{OfSameLength A B l1 l2} `{OfSameLength A B l1' l2'} : OfSameLength (l1 ++ l1') (l2 ++ l2').
Proof. unfold OfSameLength in *. do 2 rewrite length_app. lia. Qed.

Instance of_same_length_fmap_l {A A' B} {l1 : list A} {l2 : list B} {f1 : A → A'}
  `{OfSameLength A B l1 l2} : OfSameLength (f1 <$> l1) l2.
Proof. unfold OfSameLength in *. rewrite length_fmap. assumption. Qed.

Instance of_same_length_fmap_r {A B B'} {l1 : list A} {l2 : list B} {f2 : B → B'}
  `{OfSameLength A B l1 l2} : OfSameLength l1 (f2 <$> l2).
Proof. unfold OfSameLength in *. rewrite length_fmap. assumption. Qed.

Instance of_same_length_fmap {A A' B B'} {l1 : list A} {l2 : list B} {f1 : A → A'} {f2 : B → B'}
  `{OfSameLength A B l1 l2} : OfSameLength (f1 <$> l1) (f2 <$> l2).
Proof. unfold OfSameLength in *. do 2 rewrite length_fmap. assumption. Qed.

Definition of_same_length_rest {A B} {x1 : A} {l1 : list A} {x2 : B} {l2 : list B}
                              (H : OfSameLength (x1::l1) (x2::l2)) : OfSameLength l1 l2.
Proof. unfold OfSameLength in *. simpl in H. lia. Defined.

Hint Extern 5 (OfSameLength ?xs1 ?xs2) =>
  match goal with
  | H : OfSameLength (?x1 :: xs1) (?x2 :: xs2) |- _ =>
      apply of_same_length_rest in H; exact H
  | _ => fail 1
  end : core.

Definition of_same_length_eq_l {A B} {l1 l1' : list A} {l2 : list B} (H : OfSameLength l1 l2) :
  l1 = l1' →
  OfSameLength l1' l2.
Proof. intros. subst. exact H. Qed.

Definition of_same_length_eq_r {A B} {l1 : list A} {l2 l2' : list B} (H : OfSameLength l1 l2) :
  l2 = l2' →
  OfSameLength l1 l2'.
Proof. intros. subst. exact H. Qed.

Definition of_same_length_eq {A B} {l1 l1' : list A} {l2 l2' : list B} (H : OfSameLength l1 l2) :
  l1 = l1' →
  l2 = l2' →
  OfSameLength l1' l2'.
Proof. intros. subst. exact H. Qed.


Instance of_same_length_rev {A B} {l1 : list A} {l2 : list B}
                              `{OfSameLength _ _ l1 l2} : OfSameLength (rev l1) (rev l2).
Proof. unfold OfSameLength in *. do 2 rewrite length_rev. assumption. Defined.

Definition of_same_length_rect {A B X Y} (f_nil : X → Y) (f_cons : (X → Y) → A → B → X → Y)
  (x : X)
  (l1 : list A) (l2 : list B)
  `{OfSameLength _ _ l1 l2} : Y.
Proof.
  generalize dependent x. generalize dependent l2.
  induction l1 as [|x1 l1' rec], l2 as [|x2 l2']; intros H.
  - exact f_nil.
  - inversion H.
  - inversion H.
  - apply of_same_length_rest in H. specialize (rec _ H). exact (f_cons rec x1 x2).
Defined.

Lemma of_same_length_nil_inv_l {N A} {l : list A} :
  @OfSameLength N A [] l → l = [].
Proof.
  intros. unfold OfSameLength in H. symmetry in H. simpl in H. apply length_zero_iff_nil in H.
  subst. reflexivity.
Qed.

Lemma of_same_length_nil_inv_r {N A} {l : list A} :
  @OfSameLength A N l [] → l = [].
Proof.
  intros. unfold OfSameLength in H. simpl in H. apply length_zero_iff_nil in H.
  subst. reflexivity.
Qed.

Lemma of_same_length_cons_inv_l {A B} {x1 : A} {l1 : list A} {l2 : list B} :
  OfSameLength (x1 :: l1) l2 → ∃ x2 l2', l2 = x2 :: l2' ∧ length l2' = length l1.
Proof.
  intros. unfold OfSameLength in H. symmetry in H. simpl in H. 
  apply length_nonzero_iff_cons in H. exact H.
Qed.

Lemma of_same_length_cons_inv_r {A B} {l1 : list A} {x2 : B} {l2 : list B} :
  OfSameLength l1 (x2 :: l2) → ∃ x1 l1', l1 = x1 :: l1' ∧ length l1' = length l2.
Proof.
  intros. unfold OfSameLength in H. simpl in H. 
  apply length_nonzero_iff_cons in H. exact H.
Qed.

Lemma of_same_length_snoc_inv_l {A B} {l1 : list A} {x1 : A} {l2 : list B} :
  OfSameLength (l1 ++ [x1]) l2 → ∃ l2' x2, l2 = l2' ++ [x2] ∧ length l2' = length l1.
Proof.
  intros. unfold OfSameLength in H. rewrite length_app in H. symmetry in H. simpl in H.
  rewrite Nat.add_1_r in H. apply length_nonzero_iff_snoc in H. exact H.
Qed.

Lemma of_same_length_snoc_inv_r {A B} {l1 : list A}  {l2 : list B} {x2 : B} :
  OfSameLength l1 (l2 ++ [x2]) → ∃ l1' x1, l1 = l1' ++ [x1] ∧ length l1' = length l2.
Proof.
  intros. unfold OfSameLength in H. rewrite length_app in H. simpl in H.
  rewrite Nat.add_1_r in H. apply length_nonzero_iff_snoc in H. exact H.
Qed.

Lemma of_same_length_ind {A B}
  (P : ∀ (xs1 : list A) (xs2 : list B), OfSameLength xs1 xs2 → Prop) :
  (∀ (H : OfSameLength [] []), P [] [] H) →
  (∀ x1 xs1 x2 xs2 (H' : OfSameLength (x1 :: xs1) (x2 :: xs2)),
      (∀ H : OfSameLength xs1 xs2, P xs1 xs2 H) → P (x1 :: xs1) (x2 :: xs2) H') →
  ∀ xs1 xs2 (H: OfSameLength xs1 xs2), P xs1 xs2 H.
Proof.
  intros Hnil Hcons. induction xs1 as [|x1 xs1 IH]; intros; assert (Hl:=H).
  - apply of_same_length_nil_inv_l in Hl as ->. apply Hnil.
  - apply of_same_length_cons_inv_l in Hl as (x2&xs2'&->&?). rename xs2' into xs2.
    eapply Hcons. apply IH.
Qed.

Tactic Notation "induction_same_length" hyp(xs1) hyp(xs2) "as" ident(x1) ident(x2) :=
  repeat match goal with
    | H : context[xs2], _ : OfSameLength xs1 xs2 |- _ => generalize dependent H
    | H : context[xs1], _ : OfSameLength xs1 xs2 |- _ => generalize dependent H
    end;
  generalize dependent xs2; generalize dependent xs1;
  match goal with
  | |- ∀ xs1, ∀ xs2, ∀ H, ?P => apply (of_same_length_ind (λ xs1 xs2 H, P))
  end;
  [intros | let IH := fresh "IH" in  intros x1 xs1 x2 xs2 ? IH].

Lemma lookup_of_same_length_l {A B} {i} {x1 : A} {xs1 : list A} (xs2 : list B)
    `{!OfSameLength xs1 xs2} :
  xs1 !! i = Some x1 → ∃ x2, xs2 !! i = Some x2.
Proof.
  intros. generalize dependent i.
  induction_same_length xs1 xs2 as x1' x2'; [set_solver|]. intros.
  apply lookup_cons_Some in H as [|[]]; [set_solver|].
  apply of_same_length_rest in H'. destruct (IH H' (i-1) H0) as (x2&?).
  exists x2. rewrite lookup_cons_ne_0; [| lia]. replace (Init.Nat.pred i) with (i-1) by lia.
  auto.
Qed.

Lemma lookup_of_same_length_r {A B} {i} {x2 : B} (xs1 : list A) {xs2 : list B}
    `{!OfSameLength xs1 xs2} :
  xs2 !! i = Some x2 → ∃ x1, xs1 !! i = Some x1.
Proof.
  intros. generalize dependent i.
  induction_same_length xs1 xs2 as x1' x2'; [set_solver|]. intros.
  apply lookup_cons_Some in H as [|[]]; [set_solver|].
  apply of_same_length_rest in H'. destruct (IH H' (i-1) H0) as (x1&?).
  exists x1. rewrite lookup_cons_ne_0; [| lia]. replace (Init.Nat.pred i) with (i-1) by lia.
  auto.
Qed.

Lemma elem_of_zip_with_indexed {A B C} (c : C) (xs : list A) (ys : list B) (f : A → B → C)
    `{OfSameLength _ _ xs ys} :
  c ∈ zip_with f xs ys ↔ ∃ i x y, xs !! i = Some x ∧ ys !! i = Some y ∧ c = f x y.
Proof with auto.
  split; intros.
  - induction_same_length xs ys as x y; [set_solver|]. simpl. intros.
    apply of_same_length_rest in H'. apply elem_of_cons in H0 as [].
    + exists 0, x, y. split_and!...
    + apply (IH H') in H as (i&x'&y'&?&?&?). exists (S i), x', y'. simpl.
      split_and!...
  - destruct H0 as (i&x&y&?&?&?). apply elem_of_list_split_length in H0 as (xs0&xs1&->&?).
    apply elem_of_list_split_length in H1 as (ys0&ys1&->&?). subst i. rewrite zip_with_app...
    apply elem_of_app. right. simpl. apply elem_of_cons. left...
Qed.

Lemma dom_list_to_map_zip_L {K A} `{Countable K} (ks : list K) (xs : list A)
    `{OfSameLength K A ks xs} :
  dom (list_to_map (zip ks xs) : gmap K A) = list_to_set ks.
Proof.
  remember (length ks) as n eqn:E. symmetry in E. generalize dependent xs.
  generalize dependent ks. induction n; intros.
  - simpl. apply length_zero_iff_nil in E. subst. simpl. apply dom_empty_L.
  - assert (E1:=E). rewrite of_same_length in E1.
    apply length_nonzero_iff_cons in E as (k'&ks'&->&?).
    apply length_nonzero_iff_cons in E1 as (x'&xs'&->&?). subst. simpl.
    rewrite dom_insert_L. apply set_eq. intros k. destruct (decide (k = k')); set_solver.
Qed.

Lemma lookup_list_to_map_zip_None {K A} `{Countable K}
    (ks : list K) (xs : list A) (k : K) `{OfSameLength K A ks xs} :
  (list_to_map (zip ks xs) : gmap K A) !! k = None ↔ k ∉ ks.
Proof with auto.
  induction_same_length ks xs as k' x'; [set_solver|]. simpl. destruct (decide (k' = k)).
  - subst. rewrite lookup_insert. rewrite not_elem_of_cons. naive_solver.
  - rewrite lookup_insert_ne... rewrite not_elem_of_cons. naive_solver.
Qed.

Lemma lookup_list_to_map_zip_Some {K A} `{Countable K}
    (ks : list K) (xs : list A) (k : K) (x : A) `{!OfSameLength ks xs} :
  (list_to_map (zip ks xs) : gmap K A) !! k = Some x ↔
    ∃ i, ks !! i = Some k ∧ xs !! i = Some x ∧ ∀ j, ks !! j = Some k → i ≤ j.
Proof with auto.
  induction_same_length ks xs as k' x'; [set_solver|].
  simpl. split.
  - intros. destruct (decide (k' = k)).
    + subst. rewrite lookup_insert in H0. exists 0. simpl. split_and!... lia.
    + apply of_same_length_rest in H'. specialize (IH H').
      rewrite lookup_insert_ne in H0... apply IH in H0 as (i&?&?&?).
      exists (S i). simpl. split_and!... intros. specialize (H2 (Init.Nat.pred j)).
      assert (j ≠ 0).
      { intros contra. subst. simpl in H3. inversion H3. contradiction. }
      forward H2.
      { rewrite lookup_cons_ne_0 in H3... }
      lia.
  - intros (i&?&?&?). destruct (decide (k' = k)).
    + subst. forward (H2 0) by reflexivity. assert (i = 0) by lia. subst.
      simpl in H1. inversion H1. subst. rewrite lookup_insert...
    + rewrite lookup_insert_ne... apply IH.
      { apply of_same_length_rest in H'... }
      assert (i ≠ 0).
      { intros contra. subst. simpl in H0. inversion H0. contradiction. }
      rewrite lookup_cons_ne_0 in H0... rewrite lookup_cons_ne_0 in H1...
      exists (Init.Nat.pred i). split_and!... intros. specialize (H2 (S j)).
      forward H2.
      { erewrite lookup_cons_ne_0... }
      lia.
Qed.

Definition universal_relation {A} (_ _ : A) := True.

Instance universal_relation_equivalence {A} : Equivalence (@universal_relation A).
Proof. split; hnf; naive_solver. Qed.

#[global] Hint Unfold universal_relation : core.

(** Zip pairs: A zip pair is a pair of two lists that are zipped together.
    In this section we define two notions of membership for zip pairs and
    prove some properties about them. *)
Instance zip_pair_elem_of_with_index {A B} : ElemOf (nat * (A * B)) (list A * list B) :=
  λ p1 p2, p2.1 !! p1.1 = Some p1.2.1 ∧ p2.2 !! p1.1 = Some p1.2.2.

Instance zip_pair_elem_of {A} {B} : ElemOf (A * B) (list A * list B) :=
  λ p1 p2, ∃ i, (i, p1) ∈ p2.

Lemma elem_of_zip_pair {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) ↔ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. reflexivity. Qed.

Lemma not_elem_of_zip_pair_inv {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∉ (xs, ys) → ¬ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. rewrite elem_of_zip_pair. auto. Qed.

Lemma not_elem_of_zip_pair {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (∀ i, xs !! i ≠ Some x ∨ ys !! i ≠ Some y) → (x, y) ∉ (xs, ys).
Proof.
  intros. intros contra. apply elem_of_zip_pair in contra as (i&?&?).
  destruct (H i) as []; contradiction.
Qed.

Lemma elem_of_zip_pair_indexed {A B} (i : nat) (x : A) (y : B) (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) ↔ xs !! i = Some x ∧ ys !! i = Some y.
Proof. reflexivity. Qed.


Lemma elem_of_zip_pair_hd_indexed {A B} x0 y0 x y (xs : list A) (ys : list B) :
  (0, (x0, y0)) ∈ (x :: xs, y :: ys) ↔ (x0 = x ∧ y0 = y).
Proof. rewrite elem_of_zip_pair_indexed. simpl. split; naive_solver. Qed.

Lemma elem_of_zip_pair_tl_indexed {A B} i x0 y0 x y (xs : list A) (ys : list B) :
  (S i, (x0, y0)) ∈ (x :: xs, y :: ys) ↔ (i, (x0, y0)) ∈ (xs, ys).
Proof.
  do 2 rewrite elem_of_zip_pair_indexed. simpl. naive_solver.
Qed.

Definition zip_pair_functional {A B} (xs : list A) (ys : list B) :=
  ∀ i j x y1 y2, i ≠ j → (i, (x, y1)) ∈ (xs, ys) → (j, (x, y2)) ∈ (xs, ys) → y1 = y2.

Lemma NoDup_zip_pair_functional {A B} (xs : list A) (ys : list B) :
  NoDup xs →
  zip_pair_functional xs ys.
Proof with auto.
  intros H i j ? ? ? ? ? ?. exfalso. apply H0. rewrite elem_of_zip_pair_indexed in H1.
  rewrite elem_of_zip_pair_indexed in H2. destruct H1 as [? _]. destruct H2 as [? _].
  eapply NoDup_lookup with (l:=xs) (x:=x)...
Qed.

Lemma zip_pair_functional_cons_inv {A B} x y (xs : list A) (ys : list B) :
  zip_pair_functional (x :: xs) (y :: ys) → zip_pair_functional xs ys.
Proof with auto.
  intros. intros i j x0 y1 y2 ? ? ?. unfold zip_pair_functional in H.
  apply (H (S i) (S j) x0); [lia| |]; apply elem_of_zip_pair_tl_indexed...
Qed.

Hint Resolve zip_pair_functional_cons_inv : core.

Lemma zip_pair_lookup_l' {A B} {l1 : list A} {l2 : list B} {i x1} :
  length l1 = length l2 →
  l1 !! i = Some x1 → ∃ x2, l2 !! i = Some x2.
Proof with auto.
  intros. apply elem_of_list_split_length in H0 as (l10&l11&->&?).
  destruct (l2 !! i) as [x2|] eqn:E.
  - exists x2...
  - exfalso. apply list_lookup_None in E. rewrite length_app in H. rewrite <- H in E.
    simpl in E. subst i. lia.
Qed.

Lemma zip_pair_lookup_l {A B} {l1 : list A} {l2 : list B} {x1} :
  length l1 = length l2 →
  x1 ∈ l1 → ∃ x2, (x1, x2) ∈ (l1, l2).
Proof with auto.
  intros. apply elem_of_list_lookup in H0 as [i ?].
  destruct (zip_pair_lookup_l' H H0) as [x2 ?]. exists x2. apply elem_of_zip_pair.
  exists i. split...
Qed.

Lemma list_to_map_zip_lookup_zip_pair_functional {A B} `{Countable A} {x y} {xs : list A} {ys : list B} :
  zip_pair_functional (x :: xs) (y :: ys) →
  length xs = length ys →
  x ∈ xs →
  (list_to_map (zip xs ys) : gmap A B) !! x = Some y.
Proof with auto.
  intros.
  destruct (list_to_map (zip xs ys) !! x) as [y'|] eqn:E.
  - apply lookup_list_to_map_zip_Some in E as (i&?&?&?)... enough (y = y') by (subst; auto).
    unfold zip_pair_functional in H0. apply (H0 0 (S i) x).
    + lia.
    + apply elem_of_zip_pair_hd_indexed. split...
    + apply elem_of_zip_pair_tl_indexed. apply elem_of_zip_pair_indexed...
  - exfalso. apply lookup_list_to_map_zip_None in E...
Qed.
