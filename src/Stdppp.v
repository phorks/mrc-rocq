From stdpp Require Import sets vector gmap.
From MRC Require Import Prelude.
From MRC Require Import Tactics.

Open Scope refiney_scope.

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

Lemma submseteq_NoDup {A} (l k : list A) :
  NoDup k →
  l ⊆+ k →
  NoDup l.
Proof with auto.
  intros. apply submseteq_Permutation in H0 as [k' ?]. apply Permutation_NoDup in H0...
  2:{ apply NoDup_ListNoDup... }
  apply NoDup_ListNoDup in H0. apply NoDup_app in H0 as [? _]...
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

Lemma lookup_app_l_Some_disjoint {A} (l1 l2 : list A) (x : A) i :
  l1 ## l2 →
  x ∈ l1 →
  (l1 ++ l2) !! i = Some x →
  l1 !! i = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (l1 !! i)... apply elem_of_list_lookup_2 in H1.
  exfalso. apply (H x)...
Qed.

Lemma lookup_app_l_Some_disjoint' {A} (l1 l2 : list A) (x : A) i :
  l1 ## l2 →
  x ∉ l2 →
  (l1 ++ l2) !! i = Some x →
  l1 !! i = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (l1 !! i)... apply elem_of_list_lookup_2 in H1.
  contradiction.
Qed.

Lemma lookup_app_r_Some_disjoint {A} (l1 l2 : list A) (x : A) i :
  l1 ## l2 →
  x ∈ l2 →
  (l1 ++ l2) !! i = Some x →
  length l1 ≤ i ∧ l2 !! (i - length l1) = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (l1 !! i) as [x'|] eqn:E...
  - inversion H1. subst. apply elem_of_list_lookup_2 in E. exfalso. apply (H x)...
  - split... destruct (decide (length l1 ≤ i))... apply not_le in n.
    apply list_lookup_None in E. lia.
Qed.

Lemma lookup_app_r_Some_disjoint' {A} (l1 l2 : list A) (x : A) i :
  l1 ## l2 →
  x ∉ l1 →
  (l1 ++ l2) !! i = Some x →
  length l1 ≤ i ∧ l2 !! (i - length l1) = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (l1 !! i) as [x'|] eqn:E...
  - inversion H1. subst. apply elem_of_list_lookup_2 in E. contradiction.
  - split... destruct (decide (length l1 ≤ i))... apply not_le in n.
    apply list_lookup_None in E. lia.
Qed.

(** [OfSameLength] type class provides a compositional way to limit pairs of lists
    to those of the same length. It uses the power of instance synthesization to
    deduce length equality of lists based on syntactic structures of lists.
    The main use case for this is in zip pairs. We can prove more intersting facts
    about the zipped result of two lists, if we know they are of the same length. *)
Class OfSameLength {A B} (l1 : list A) (l2 : list B) :=
  of_same_length : length l1 = length l2.

Instance OfSameLength_pi {A B} (l1 : list A) (l2 : list B) :
  ProofIrrel (OfSameLength l1 l2).
Proof. apply eq_pi. solve_decision. Qed.

Lemma rewrite_of_same_length {A B C} (xs xs' : list A) (ys ys' : list B)
    (f : ∀ (xs : list A) (ys : list B), OfSameLength xs ys → C)
    `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  xs = xs' →
  ys = ys' →
  f xs ys _ = f xs' ys' _.
Proof.
  intros. subst. f_equiv. apply OfSameLength_pi.
Qed.

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

Lemma elem_of_zip_pair_nil {A B} x y :
  (x, y) ∈ (([] : list A), ([] : list B)) → False.
Proof with auto.
  intros (i&?&?). simpl in *. apply elem_of_list_lookup_2 in H. set_solver.
Qed.

Lemma elem_of_zip_pair_hd_ne {A B} x0 y0 x y (xs : list A) (ys : list B) :
  x0 ≠ x →
  (x0, y0) ∈ (x :: xs, y :: ys) ↔ (x0, y0) ∈ (xs, ys).
Proof with auto.
  intros. split; intros (i&?).
  - destruct i.
    + apply elem_of_zip_pair_hd_indexed in H0 as []. subst. contradiction.
    + apply elem_of_zip_pair_tl_indexed in H0. exists i...
  - exists (S i). apply elem_of_zip_pair_tl_indexed...
Qed.

Lemma elem_of_zip_pair_hd {A B} y0 x y (xs : list A) (ys : list B) :
  x ∉ xs →
  (x, y0) ∈ (x :: xs, y :: ys) ↔ y0 = y.
Proof with auto.
  intros. split.
  - intros (i&?). destruct i.
    + apply elem_of_zip_pair_hd_indexed in H0 as []...
    + apply elem_of_zip_pair_tl_indexed in H0 as []. simpl in *. apply elem_of_list_lookup_2 in H0.
      done.
  - intros ->. exists 0. apply elem_of_zip_pair_hd_indexed...
Qed.

Lemma elem_of_zip_pair_app {A B} x y (xs1 : list A) (ys1 : list B)
  (xs2 : list A) (ys2 : list B) `{!OfSameLength xs1 ys1} :
  (x, y) ∈ (xs1 ++ xs2, ys1 ++ ys2) ↔ (x, y) ∈ (xs1, ys1) ∨ (x, y) ∈ (xs2, ys2).
Proof with auto.
  split.
  - intros (i&?&?). simpl in H, H0. destruct (decide (i < length xs1)).
    + left. rewrite lookup_app_l in H... rewrite OfSameLength0 in l. rewrite lookup_app_l in H0...
      exists i. split...
    + right. rewrite lookup_app_r in H by lia. rewrite OfSameLength0 in n.
      rewrite lookup_app_r in H0 by lia. rewrite OfSameLength0 in H. exists (i - length ys1).
      split...
  - intros [|]; destruct H as (i&?&?); simpl in H, H0.
    + exists i. split; simpl; apply lookup_app_l_Some...
    + exists (length xs1 + i). split; simpl.
      * rewrite lookup_app_r by lia. replace (length xs1 + i - length xs1) with i by lia...
      * rewrite OfSameLength0. rewrite lookup_app_r by lia.
        replace (length ys1 + i - length ys1) with i by lia...
Qed.

Lemma elem_of_zip_pair_indexed_inv {A B} i x y (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) → (x, y) ∈ (xs, ys).
Proof. intros. exists i. assumption. Qed.

Lemma lookup_list_to_map_zip_Some_inv {K A} `{Countable K}
    (ks : list K) (xs : list A) (k : K) (x : A) `{!OfSameLength ks xs} :
  (list_to_map (zip ks xs) : gmap K A) !! k = Some x →
                                                   (k, x) ∈ (ks, xs).
Proof with auto.
  intros. apply lookup_list_to_map_zip_Some in H0 as (i&?&?&?)... exists i. split...
Qed.

Lemma elem_of_zip_pair_fmap {A A' B B'} x' y' (xs : list A) (ys : list B)
    (f : A → A') (g : B → B')
    `{!OfSameLength xs ys} `{!OfSameLength (f <$> xs) (g <$> ys)} :
  (x', y') ∈ (f <$> xs, g <$> ys) ↔ ∃ x y, (x, y) ∈ (xs, ys) ∧ x' = f x ∧ y' = g y.
Proof with auto.
  split.
  - intros (i&?&?). simpl in H, H0. apply list_lookup_fmap_Some in H as (x&?&?).
    apply list_lookup_fmap_Some in H0 as (y&?&?). exists x, y. split_and!... exists i.
    split...
  - intros (x&y&(i&?&?)&?&?). simpl in H, H0. exists i. split; simpl; apply list_lookup_fmap_Some.
    + exists x. split...
    + exists y. split...
Qed.

Definition zip_pair_Permutation {A B} (p1 p2 : list A * list B) :=
  ∀ (x : A) (y : B), (x, y) ∈ p1 ↔ (x, y) ∈ p2.

Infix "≡ₚₚ" := (zip_pair_Permutation) (at level 70, no associativity) : refiney_scope.

Global Instance zip_pair_Permutation_refl {A B} : Reflexive (@zip_pair_Permutation A B).
Proof. intros p x y. reflexivity. Qed.

Hint Extern 0 (?p ≡ₚₚ ?p) => reflexivity : core.

Global Instance zip_pair_Permutation_sym {A B} : Symmetric (@zip_pair_Permutation A B).
Proof. intros p1 p2 H x y. specialize (H x y). naive_solver. Qed.

Global Instance zip_pair_Permutation_trans {A B} : Transitive (@zip_pair_Permutation A B).
Proof.
  intros p1 p2 p3 H12 H23. intros x y. specialize (H12 x y). specialize (H23 x y). naive_solver.
Qed.

Global Instance zip_pair_Permutation_equiv {A B} : Equivalence (@zip_pair_Permutation A B).
Proof.
  split; [exact zip_pair_Permutation_refl | exact zip_pair_Permutation_sym |
           exact zip_pair_Permutation_trans].
Qed.

Lemma zip_pair_Permutation_cons {A B} `{EqDecision A} (x : A) (y : B) (xs1 : list A)
  (ys1 : list B) (xs2 : list A) (ys2 : list B) `{!OfSameLength xs1 ys1} `{!OfSameLength xs2 ys2} :
  (xs1, ys1) ≡ₚₚ (xs2, ys2) →
  (x :: xs1, y :: ys1) ≡ₚₚ (x :: xs2, y :: ys2).
Proof with auto.
  unfold zip_pair_Permutation. intros. split; intros (i&?&?); simpl in H0, H1.
  - destruct i.
    + exists 0. split...
    + rewrite lookup_cons_ne_0 in H0 by lia. simpl in H0.
      rewrite lookup_cons_ne_0 in H1 by lia. simpl in H1. specialize (H x0 y0).
      pose proof (proj1 H). forward H2 by (exists i; split; auto).
      destruct H2 as (j&?&?). simpl in H2, H3.
      exists (S j). split...
  - destruct i.
    + exists 0. split...
    + rewrite lookup_cons_ne_0 in H0 by lia. simpl in H0.
      rewrite lookup_cons_ne_0 in H1 by lia. simpl in H1. specialize (H x0 y0).
      pose proof (proj2 H). forward H2 by (exists i; split; auto).
      destruct H2 as (j&?&?). simpl in H2, H3.
      exists (S j). split...
Qed.

Lemma zip_pair_Permutation_app_comm {A B} (xs1 : list A) (ys1 : list B) (xs2 : list A)
    (ys2 : list B) `{!OfSameLength xs1 ys1} `{!OfSameLength xs2 ys2} :
  (xs1 ++ xs2, ys1 ++ ys2) ≡ₚₚ (xs2 ++ xs1, ys2 ++ ys1).
Proof with auto.
  unfold zip_pair_Permutation. intros x y. repeat rewrite elem_of_zip_pair_app...
  naive_solver.
Qed.

Lemma zip_pair_Permutation_nil_inv_l {A B}
    (xs : list A) (ys : list B) `{!OfSameLength xs ys} :
  ([], []) ≡ₚₚ (xs, ys) →
  xs = [] ∧ ys = [].
Proof with auto.
  intros. unfold zip_pair_Permutation in H. induction_same_length xs ys as x y...
  - intros. clear IH. specialize (H x y). assert ((x, y) ∈ (x :: xs, y :: ys)).
    { exists 0. split... }
    rewrite <- H in H0. destruct H0 as (i&?&?). simpl in H0, H1. set_solver.
Qed.

Lemma zip_pair_Permutation_cons_inv_l {A B} `{EqDecision A}
    (x : A) (y : B) (xs : list A) (ys : list B)
    (xs' : list A) (ys' : list B) `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  (x :: xs, y :: ys) ≡ₚₚ (xs', ys') →
  x ∉ xs →
  NoDup xs →
  NoDup xs' →
  ∃ (xs'0 : list A) (ys'0 : list B) (xs'1 : list A) (ys'1 : list B) (Hl0 : OfSameLength xs'0 ys'0) (Hl1 : OfSameLength xs'1 ys'1),
    xs' = xs'0 ++ x :: xs'1 ∧ ys' = ys'0 ++ y :: ys'1 ∧ (xs, ys) ≡ₚₚ (xs'0 ++ xs'1, ys'0 ++ ys'1).
Proof with auto.
  intros ? Hnin Hnodup Hnodup'. pose proof (H x y). assert ((x, y) ∈ (xs', ys')) as (i&?&?).
  { apply H. exists 0. split... }
  simpl in H1, H2. apply elem_of_list_split_length in H1, H2. destruct H1 as (xs'0&xs'1&?&?).
  destruct H2 as (ys'0&ys'1&?&?). subst. exists xs'0, ys'0, xs'1, ys'1. eexists; [naive_solver|].
  eexists...
  { pose proof (@of_same_length _ _ _ _ OfSameLength1). unfold OfSameLength.
    repeat rewrite length_app in H1. simpl in H1. lia. }
  split_and!... intros x' y'. specialize (H x' y').
  apply NoDup_app in Hnodup' as (?&?&?). apply NoDup_cons in H3 as [].
  destruct (decide (x' = x)).
  - subst. split; intros (i&?&_); simpl in H6.
    + apply elem_of_list_lookup_2 in H6. contradiction.
    + apply elem_of_list_lookup_2 in H6. set_solver.
  - rewrite elem_of_zip_pair_hd_ne in H... rewrite H.
    rewrite elem_of_zip_pair_app... rewrite elem_of_zip_pair_hd_ne...
    rewrite elem_of_zip_pair_app...
Qed.

Lemma zip_pair_Permutation_list_to_map_zip {A B}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) `{Countable A} `{EqDecision A}
    `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  NoDup xs →
  NoDup xs' →
  (xs, ys) ≡ₚₚ (xs', ys') →
  (list_to_map (zip xs ys) : gmap A B) = list_to_map (zip xs' ys').
Proof with auto.
  intros. unfold zip_pair_Permutation in H. apply map_eq. intros x.
  destruct (list_to_map (zip xs ys) !! x) as [y|] eqn:E.
  - apply lookup_list_to_map_zip_Some_inv in E... apply H2 in E.
    symmetry. apply lookup_list_to_map_zip_Some... destruct E as (i&?&?). simpl in H3, H4.
    exists i. split_and!... intros. apply NoDup_lookup with (i:=i) in H5... lia.
  - apply lookup_list_to_map_zip_None in E... symmetry. apply lookup_list_to_map_zip_None...
    intros ?. apply elem_of_list_lookup in H3 as (i&?).
    destruct (lookup_of_same_length_l ys' H3) as (y&?)...
    assert ((x, y) ∈ (xs, ys)) as (?&?&_).
    { apply H2. exists i. split... }
    simpl in H5. apply elem_of_list_lookup_2 in H5. contradiction.
Qed.

Lemma zip_pair_Permutation_fmap {A A' B B'}
    (xs : list A) (ys : list B)
    (xs' : list A) (ys' : list B)
    (f : A → A') (g : B → B')
    `{!OfSameLength xs ys} `{!OfSameLength (f <$> xs) (g <$> ys)}
    `{!OfSameLength xs' ys'} `{!OfSameLength (f <$> xs') (g <$> ys')} :
  (xs, ys) ≡ₚₚ (xs', ys') →
  (f <$> xs, g <$> ys) ≡ₚₚ (f <$> xs', g <$> ys').
Proof with auto.
  intros. unfold zip_pair_Permutation. intros x' y'. rewrite elem_of_zip_pair_fmap...
  rewrite elem_of_zip_pair_fmap... split; intros (x&y&?&?&?);
    exists x, y; split; auto; apply H in H0...
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
