From stdpp Require Import sets vector gmap.
From MRC Require Import Prelude.
From MRC.Lib Require Import Tactics.

Open Scope refiney_scope.

Definition universal_relation {A} (_ _ : A) := True.

Instance universal_relation_equivalence {A} : Equivalence (@universal_relation A).
Proof. split; hnf; naive_solver. Qed.

#[global] Hint Unfold universal_relation : core.

Lemma equiv_eq {A} `{Equiv A} `{!Reflexive (≡@{A})} (x y : A) :
  x = y → x ≡ y.
Proof. intros. by subst. Qed.

Lemma exists_iff_exists_weaken {V} (P Q : V → Prop) :
  (∀ v, P v ↔ Q v) →
  ((∃ v, P v) ↔ (∃ v, Q v)).
Proof.
  intros. split; intros [v Hv]; exists v; apply H; auto.
Qed.

Lemma not_or P Q : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q.
Proof with auto.
  split; intros.
  - split; contradict H...
  - destruct H. intros []...
Qed.

Lemma not_not P `{Decision P} : ¬ ¬ P ↔ P.
Proof with auto.
  split; intros.
  - destruct (decide P)... contradict H0...
  - intros ?. apply H1...
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


Lemma eq_iff : forall (P Q : Prop), P = Q -> (P <-> Q).
Proof. intros P Q H. rewrite H. apply iff_refl. Qed.

Definition list_to_vec_n {A n} (l : list A) (H : length l = n) : vec A n :=
  eq_rect _ (fun m => vec A m) (list_to_vec l) _ H.

Lemma list_to_vec_2_canon {A} (x1 x2 : A) H : list_to_vec_n [x1; x2] H = [#x1; x2].
Proof.
  unfold list_to_vec_n. simpl in *. assert (H = eq_refl).
  { apply Eqdep_dec.UIP_refl_nat. }
  subst. done.
Qed.

(** converting sets to lists *)
Definition set_to_list {A} `{Countable A} (s : gset A) : list A :=
  set_fold cons [] s.

Lemma set_to_list_empty {A} `{Countable A} : set_to_list (∅ : gset A) = nil.
Proof. set_solver. Qed.

Lemma set_to_list_singleton {A} `{Countable A} (x : A) :
  set_to_list {[x]} = [x].
Proof. unfold set_to_list. by rewrite set_fold_singleton. Qed.

Lemma set_to_list_union_singleton_l_perm {A} `{Countable A} (x : A) (X : gset A) :
  x ∉ X →
  set_to_list ({[x]} ∪ X) ≡ₚ x :: set_to_list X.
Proof.
  intros. unfold set_to_list, set_fold, compose. by rewrite elements_union_singleton.
Qed.

Lemma set_to_list_union_singleton_r_perm {A} `{Countable A} (x : A) (X : gset A) :
  x ∉ X →
  set_to_list (X ∪ {[x]}) ≡ₚ x :: set_to_list X.
Proof.
  intros. rewrite union_comm_L. by apply set_to_list_union_singleton_l_perm.
Qed.

Lemma elem_of_set_to_list {A} `{Countable A} {x} {X : gset A} :
  x ∈ set_to_list X ↔ x ∈ X.
Proof with auto.
  unfold elem_of at 1. split; intros.
  - induction X using set_ind_L.
    + rewrite set_to_list_empty in H0. inversion H0.
    + rewrite set_to_list_union_singleton_l_perm in H0... set_solver.
  - induction X using set_ind_L.
    + set_solver.
    + rewrite set_to_list_union_singleton_l_perm... set_solver.
Qed.

Global Instance set_unfold_elem_of_set_to_list {A} `{Countable A} x (X : gset A) P :
  (∀ x, SetUnfoldElemOf x X (P x)) →
  SetUnfoldElemOf x
    (set_to_list X)
    (P x).
Proof. constructor. rewrite elem_of_set_to_list. apply H0. Qed.

Lemma set_to_list_union_perm {A} `{Countable A} (s1 s2 : gset A) :
  s1 ## s2 →
  set_to_list (s1 ∪ s2) ≡ₚ set_to_list s1 ++ set_to_list s2.
Proof with auto.
  generalize dependent s1. induction s2 using set_ind_L; intros.
  - rewrite union_empty_r_L. rewrite set_to_list_empty. rewrite app_nil_r...
  - rewrite union_assoc_L. rewrite IHs2 by set_solver. rewrite IHs2 by set_solver.
    rewrite set_to_list_union_singleton_r_perm by set_solver.
    rewrite set_to_list_singleton. rewrite app_assoc. by rewrite (Permutation_app_comm _ [x]).
Qed.

Lemma set_to_list_set_map_perm {A B} `{Countable A, Countable B}
    (s : gset A) (f : A → B) `{!Inj (=) (=) f} :
  set_to_list (set_map f s) ≡ₚ f <$> set_to_list s.
Proof with auto.
  induction s using set_ind_L; [set_solver|]. rewrite set_map_union_L.
  rewrite set_map_singleton_L. rewrite set_to_list_union_singleton_l_perm.
  2:{ set_unfold. intros (x0&?&?). apply Inj0 in H2. by subst x0. }
  rewrite set_to_list_union_singleton_l_perm... simpl. rewrite IHs...
Qed.

Lemma set_to_list_list_to_set {A} `{Countable A} (l : list A) :
  NoDup l →
  set_to_list (list_to_set l) ≡ₚ l.
Proof with auto.
  intros. induction l... rewrite list_to_set_cons. apply NoDup_cons in H0 as [].
  rewrite set_to_list_union_singleton_l_perm by set_solver. rewrite IHl...
Qed.

Lemma list_to_set_set_to_list {A} `{Countable A} (s : gset A) :
  list_to_set (set_to_list s) = s.
Proof with auto.
  intros. induction s using set_ind_L... rewrite set_to_list_union_singleton_l_perm...
  simpl. rewrite IHs...
Qed.

Global Instance set_to_list_proper {A} `{Countable A} :
  Proper ((≡) ==> (≡)) (@set_to_list A _ _).
Proof. intros X. induction X using set_ind_L; intros; set_solver. Qed.

Global Instance set_to_list_proper_perm {A} `{Countable A} :
  Proper ((≡) ==> (≡ₚ)) (@set_to_list A _ _).
Proof. intros X. induction X using set_ind_L; intros; set_solver. Qed.

Local Lemma filter_set_to_list_delete_union_singleton_l' {A} `{Countable A} {P : A → Prop}
    `{∀ x, Decision (P x)} {x : A} {X : gset A} :
  x ∉ X →
  ¬ P x →
  filter P (set_to_list ({[x]} ∪ X)) ≡ₚ filter P (set_to_list X).
Proof with auto.
  intros. rewrite set_to_list_union_singleton_l_perm... rewrite filter_cons.
  destruct (decide _)... contradiction.
Qed.

Lemma filter_set_to_list_delete_union_l {A} `{Countable A} {P : A → Prop}
    `{∀ x, Decision (P x)} (X Y : gset A) :
  (∀ x, x ∈ X → ¬ P x) →
  filter P (set_to_list (X ∪ Y)) ≡ₚ filter P (set_to_list Y).
Proof with auto.
  intros. generalize dependent Y. induction X using set_ind_L; intros.
  - rewrite union_empty_l_L...
  - destruct (decide (x ∈ Y)).
    + assert ({[x]} ∪ X ∪ Y = X ∪ Y) as -> by set_solver... apply IHX.
      intros. apply H1. set_solver.
    + rewrite <- union_assoc_L.
      rewrite filter_set_to_list_delete_union_singleton_l' by set_solver.
      apply IHX. intros. apply H1. set_solver.
Qed.

Lemma filter_set_to_list_delete_union_r {A} `{Countable A} {P : A → Prop}
    `{∀ x, Decision (P x)} (X Y : gset A) :
  (∀ x, x ∈ Y → ¬ P x) →
  filter P (set_to_list (X ∪ Y)) ≡ₚ filter P (set_to_list X).
Proof with auto.
  intros. rewrite union_comm_L. apply filter_set_to_list_delete_union_l...
Qed.

Lemma filter_set_to_list_delete_union_singleton_l {A} `{Countable A} {P : A → Prop}
    `{∀ x, Decision (P x)} (x : A) (X : gset A) :
  ¬ P x →
  filter P (set_to_list ({[x]} ∪ X)) ≡ₚ filter P (set_to_list X).
Proof with auto.
  intros. apply filter_set_to_list_delete_union_l. set_solver.
Qed.

Lemma filter_set_to_list_delete_difference {A} `{Countable A} {P : A → Prop}
    `{∀ x, Decision (P x)} (X Y : gset A) :
  (∀ x, x ∈ Y → ¬ P x) →
  filter P (set_to_list (X ∖ Y)) ≡ₚ filter P (set_to_list X).
Proof with auto.
  intros. rewrite <- filter_set_to_list_delete_union_r with (Y:=X ∩ Y) by set_solver.
  rewrite difference_union_intersection_L...
Qed.

Lemma set_to_list_list_to_set_eq_nil {A} `{Countable A} (xs : list A) :
  set_to_list (list_to_set xs) ≡ [] ↔ xs = [].
Proof. induction xs; set_solver. Qed.

Lemma set_to_list_union_singleton_l_dup {A} `{Countable A} (x : A) (xs : gset A) :
  x ∈ xs →
  set_to_list ({[x]} ∪ xs) ≡ set_to_list xs.
Proof. intros ? y. set_solver. Qed.

Lemma set_to_list_union_singleton_l_dup_perm {A} `{Countable A} (x : A) (xs : gset A) :
  x ∈ xs →
  set_to_list ({[x]} ∪ xs) ≡ₚ set_to_list xs.
Proof with auto.
  intros. induction xs using set_ind_L; [set_solver|].
  set_unfold in H0. destruct H0.
  - subst x0. f_equiv. set_solver.
  - rewrite union_comm_L with (y:=X). rewrite union_assoc_L.
    repeat rewrite union_comm_L with (y:={[x0]}).
    rewrite set_to_list_union_singleton_l_perm by set_solver.
    rewrite set_to_list_union_singleton_l_perm with (x:=x0) by set_solver.
    f_equiv. apply IHxs...
Qed.

Lemma set_to_list_NoDup {A} `{Countable A} (xs : gset A) :
  NoDup (set_to_list xs).
Proof with auto.
  induction xs using set_ind_L.
  - rewrite set_to_list_empty. constructor.
  - rewrite set_to_list_union_singleton_l_perm... constructor... set_solver.
Qed.

Lemma set_to_list_list_to_set_cons_inv {A} `{Countable A} (xs : list A) y ys :
  set_to_list (list_to_set xs) = y :: ys → y ∈ xs ∧ y ∉ ys.
Proof with auto.
  intros. assert (set_to_list (list_to_set xs) ≡ₚ y :: ys) by (by rewrite H0).
  assert (∃ k, set_to_list (list_to_set xs) ≡ₚ y :: k) by eauto.
  rewrite <- elem_of_Permutation in H2. split; [set_solver|].
  pose proof (set_to_list_NoDup (list_to_set xs)).
  rewrite H0 in H3. inversion H3. set_solver.
Qed.

(*** Facts and operations on lists *)
(** * Facts about [list] *)
Lemma cons_app {A} (x : A) (xs : list A) :
  x :: xs = [x] ++ xs.
Proof. reflexivity. Qed.

Lemma list_equiv_subseteq {A} (xs xs' : list A) :
  xs ≡ xs' ↔ xs ⊆ xs' ∧ xs' ⊆ xs.
Proof. set_solver. Qed.

Lemma submseteq_NoDup {A} (l k : list A) :
  NoDup k →
  l ⊆+ k →
  NoDup l.
Proof with auto.
  intros. apply submseteq_Permutation in H0 as [k' ?]. apply Permutation_NoDup in H0...
  2:{ apply NoDup_ListNoDup... }
  apply NoDup_ListNoDup in H0. apply NoDup_app in H0 as [? _]...
Qed.
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

Lemma lookup_app_l_Some_disjoint {A} (xs ys : list A) (x : A) i :
  xs ## ys →
  x ∈ xs →
  (xs ++ ys) !! i = Some x →
  xs !! i = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (xs !! i)... apply elem_of_list_lookup_2 in H1.
  exfalso. apply (H x)...
Qed.

Lemma lookup_app_l_Some_disjoint' {A} (xs ys : list A) (x : A) i :
  xs ## ys →
  x ∉ ys →
  (xs ++ ys) !! i = Some x →
  xs !! i = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (xs !! i)... apply elem_of_list_lookup_2 in H1.
  contradiction.
Qed.

Lemma lookup_app_r_Some_disjoint {A} (xs ys : list A) (x : A) i :
  xs ## ys →
  x ∈ ys →
  (xs ++ ys) !! i = Some x →
  length xs ≤ i ∧ ys !! (i - length xs) = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (xs !! i) as [x'|] eqn:E...
  - inversion H1. subst. apply elem_of_list_lookup_2 in E. exfalso. apply (H x)...
  - split... destruct (decide (length xs ≤ i))... apply not_le in n.
    apply list_lookup_None in E. lia.
Qed.

Lemma lookup_app_r_Some_disjoint' {A} (xs ys : list A) (x : A) i :
  xs ## ys →
  x ∉ xs →
  (xs ++ ys) !! i = Some x →
  length xs ≤ i ∧ ys !! (i - length xs) = Some x.
Proof with auto.
  intros. rewrite lookup_app in H1. destruct (xs !! i) as [x'|] eqn:E...
  - inversion H1. subst. apply elem_of_list_lookup_2 in E. contradiction.
  - split... destruct (decide (length xs ≤ i))... apply not_le in n.
    apply list_lookup_None in E. lia.
Qed.

Lemma Permutation_app_cons_r_comm {A} {x : A} {X Y : list A} :
  X ++ x :: Y ≡ₚ x :: X ++ Y.
Proof. rewrite Permutation_app_comm. simpl. by rewrite Permutation_app_comm. Qed.

Lemma subseteq_cons_not_in {A} {x : A} {X Y : list A} :
  x ∉ X →
  x ∉ Y →
  X ⊆ Y ↔ x :: X ⊆ x :: Y.
Proof. intros. set_solver. Qed.

Lemma list_equiv_nil {A} (xs : list A) :
  xs ≡ [] ↔ xs = nil.
Proof with auto.
  split; intros; [| subst]... induction xs... set_solver.
Qed.

Lemma list_equiv_cons_inl {A} (xs : list A) x ys :
  x ∈ xs →
  xs ≡ ys →
  xs ≡ x :: ys.
Proof. set_solver. Qed.

Global Instance cons_proper_eq' {A} : Proper ((=) ==> (≡) ==> (≡)) (@cons A).
Proof. intros x ? -> xs ys ?. intros z. set_solver. Qed.

Global Instance cons_proper_subseteq {A} : Proper ((=) ==> (⊆) ==> (⊆)) (@cons A).
Proof. intros x ? -> xs ys ?. intros z. set_solver. Qed.

Lemma equiv_cons_cons {A} (x y : A) (xs : list A) :
  x :: y :: xs ≡ y :: x :: xs.
Proof. set_solver. Qed.

Lemma take_all {A} (xs : list A) :
  take (length xs) xs = xs.
Proof. apply firstn_all. Qed.

Lemma Permutation_equiv_inv {A} (xs xs' : list A) :
  xs ≡ₚ xs' → xs ≡ xs'.
Proof with auto.
  intros. induction H...
  - f_equiv...
  - rewrite equiv_cons_cons...
  - rewrite IHPermutation1...
Qed.


(** * Lists with equal lengths  *)
(** [OfSameLength] type class provides a compositional way to limit pairs of lists
    to those of the same length. It uses the power of instance synthesization to
    deduce length equality of lists based on syntactic structures of lists.
    The main use case for this is in zpair. We can prove more intersting facts
    about the zipped result of two lists, if we know they are of the same length. *)
Class OfSameLength {A B} (xs : list A) (ys : list B) :=
  of_same_length : length xs = length ys.

Instance OfSameLength_pi {A B} (xs : list A) (ys : list B) :
  ProofIrrel (OfSameLength xs ys).
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

Lemma of_same_length_comm {A B} (l1 : list A) (l2 : list B) :
  OfSameLength l1 l2 → OfSameLength l2 l1.
Proof. naive_solver. Qed.

Instance of_same_length_nil {A B} : @OfSameLength A B [] [].
Proof. reflexivity. Qed.

Instance of_same_length_id {A} {l : list A} : OfSameLength l l | 0.
Proof. reflexivity. Qed.

Instance of_same_length_cons {A B} {x1 : A} {xs : list A} {x2 : B} {ys : list B}
  `{OfSameLength A B xs ys} : OfSameLength (x1::xs) (x2::ys).
Proof. unfold OfSameLength in *. do 2 rewrite length_cons. lia. Qed.

Instance of_same_length_singleton {A B} {x1 : A} {x2 : B} : OfSameLength [x1] [x2].
Proof. unfold OfSameLength in *. simpl. reflexivity. Qed.

Instance of_same_length_app {A B} {xs xs' : list A} {ys ys' : list B}
  `{OfSameLength A B xs ys} `{OfSameLength A B xs' ys'} : OfSameLength (xs ++ xs') (ys ++ ys').
Proof. unfold OfSameLength in *. do 2 rewrite length_app. lia. Qed.

Instance of_same_length_fmap_l {A A' B} {xs : list A} {ys : list B} {f1 : A → A'}
  `{OfSameLength A B xs ys} : OfSameLength (f1 <$> xs) ys.
Proof. unfold OfSameLength in *. rewrite length_fmap. assumption. Qed.

Instance of_same_length_fmap_r {A B B'} {xs : list A} {ys : list B} {f2 : B → B'}
  `{OfSameLength A B xs ys} : OfSameLength xs (f2 <$> ys).
Proof. unfold OfSameLength in *. rewrite length_fmap. assumption. Qed.

Instance of_same_length_fmap {A A' B B'} {xs : list A} {ys : list B} {f1 : A → A'} {f2 : B → B'}
  `{OfSameLength A B xs ys} : OfSameLength (f1 <$> xs) (f2 <$> ys).
Proof. unfold OfSameLength in *. do 2 rewrite length_fmap. assumption. Qed.

Lemma of_same_length_rest {A B} {x1 : A} {xs : list A} {x2 : B} {ys : list B} :
  OfSameLength (x1::xs) (x2::ys) → OfSameLength xs ys.
Proof. intros. unfold OfSameLength in *. simpl in H. lia. Qed.

Lemma of_same_length_cons_inv {A B} {x : A} {xs : list A} {y : B} {ys : list B} :
  OfSameLength ([x] ++ xs) ([y] ++ ys) →
  OfSameLength xs ys.
Proof. unfold OfSameLength in *. simpl. lia. Qed.


Global Hint Extern 0 (OfSameLength ?xs1 ?xs2) =>
  match goal with
  | H : OfSameLength (?x1 :: xs1) (?x2 :: xs2) |- _ =>
      apply of_same_length_rest in H; exact H
  | _ => fail 1
  end : core.

Definition of_same_length_eq_l {A B} {xs xs' : list A} {ys : list B} (H : OfSameLength xs ys) :
  xs = xs' →
  OfSameLength xs' ys.
Proof. intros. subst. exact H. Qed.

Definition of_same_length_eq_r {A B} {xs : list A} {ys ys' : list B} (H : OfSameLength xs ys) :
  ys = ys' →
  OfSameLength xs ys'.
Proof. intros. subst. exact H. Qed.

Definition of_same_length_eq {A B} {xs xs' : list A} {ys ys' : list B} (H : OfSameLength xs ys) :
  xs = xs' →
  ys = ys' →
  OfSameLength xs' ys'.
Proof. intros. subst. exact H. Qed.


Instance of_same_length_rev {A B} {xs : list A} {ys : list B}
                              `{OfSameLength _ _ xs ys} : OfSameLength (rev xs) (rev ys).
Proof. unfold OfSameLength in *. do 2 rewrite length_rev. assumption. Qed.

Definition of_same_length_rect {A B X Y} (f_nil : X → Y) (f_cons : (X → Y) → A → B → X → Y)
  (x : X)
  (xs : list A) (ys : list B)
  `{OfSameLength _ _ xs ys} : Y.
Proof.
  generalize dependent x. generalize dependent ys.
  induction xs as [|x1 xs' rec], ys as [|x2 ys']; intros H.
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

Lemma of_same_length_cons_inv_l {A B} {x1 : A} {xs : list A} {ys : list B} :
  OfSameLength (x1 :: xs) ys → ∃ x2 ys', ys = x2 :: ys' ∧ length ys' = length xs.
Proof.
  intros. unfold OfSameLength in H. symmetry in H. simpl in H. 
  apply length_nonzero_iff_cons in H. exact H.
Qed.

Lemma of_same_length_cons_inv_r {A B} {xs : list A} {x2 : B} {ys : list B} :
  OfSameLength xs (x2 :: ys) → ∃ x1 xs', xs = x1 :: xs' ∧ length xs' = length ys.
Proof.
  intros. unfold OfSameLength in H. simpl in H. 
  apply length_nonzero_iff_cons in H. exact H.
Qed.

Lemma of_same_length_snoc_inv_l {A B} {xs : list A} {x1 : A} {ys : list B} :
  OfSameLength (xs ++ [x1]) ys → ∃ ys' x2, ys = ys' ++ [x2] ∧ length ys' = length xs.
Proof.
  intros. unfold OfSameLength in H. rewrite length_app in H. symmetry in H. simpl in H.
  rewrite Nat.add_1_r in H. apply length_nonzero_iff_snoc in H. exact H.
Qed.

Lemma of_same_length_snoc_inv_r {A B} {xs : list A}  {ys : list B} {x2 : B} :
  OfSameLength xs (ys ++ [x2]) → ∃ xs' x1, xs = xs' ++ [x1] ∧ length xs' = length ys.
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


(** * Deleting elements of lists *)

Global Instance list_delete_elem {A} `{E : EqDecision A} : Delete A (list A)
  := λ x xs, remove (decide_rel _) x xs.

Global Instance list_delete_elem_proper {A} `{E : EqDecision A} {x : A}
  : Proper ((≡ₚ) ==> (≡ₚ@{A})) (delete x).
Proof with auto.
  intros xs ys ?. unfold delete, list_delete_elem. generalize dependent ys.
  induction xs as [|x' xs]; intros...
  - apply Permutation_nil_l in H. subst...
  - apply Permutation_cons_inv_l in H as (ys1&ys2&->&?). rewrite remove_app. simpl.
    destruct (decide_rel _).
    + rewrite <- remove_app...
    + rewrite <- Permutation_cons_app.
      2:{ rewrite <- remove_app. reflexivity. }
      f_equiv. apply IHxs...
Qed.

Lemma list_delete_elem_nil {A} {x : A} `{EqDecision A} :
  delete x [] = [].
Proof. reflexivity. Qed.

Lemma list_delete_elem_cons {A} {x : A} {xs} `{EqDecision A} :
  delete x (x :: xs) = delete x xs.
Proof. apply remove_cons. Qed.

Lemma elem_of_list_delete_elem_inv {A} (x y : A) (xs : list A) `{EqDecision A} :
  x ∈ delete y xs → x ≠ y.
Proof.
  induction xs.
  - rewrite list_delete_elem_nil. set_solver.
  - intros. unfold delete, list_delete_elem in H. simpl in H.
    destruct (decide_rel _).
    + subst. apply IHxs. done.
    + set_solver.
Qed.

Lemma list_delete_elem_id_alt {A} (x : A) (xs : list A) `{EqDecision A} :
  delete x xs = xs ↔ x ∉ xs.
Proof with auto.
  unfold delete, list_delete_elem. induction xs; [set_solver|].
  simpl. (destruct (decide_rel _)).
  - subst. split; [|set_solver]. intros.
    exfalso. pose proof (elem_of_list_delete_elem_inv a a xs).
    unfold delete, list_delete_elem in H0. apply H0... rewrite H. set_solver.
  - split; intros; [set_solver|]. f_equal. apply IHxs. set_solver.
Qed.

Lemma list_delete_elem_id {A} (x : A) (xs : list A) `{EqDecision A} :
  x ∉ xs →
  delete x xs = xs.
Proof. apply list_delete_elem_id_alt. Qed.

Global Instance set_unfold_elem_of_list_delete_elem {A} `{EqDecision A} (y x : A) (xs : list A) P :
  SetUnfoldElemOf y xs P →
  SetUnfoldElemOf y
    (delete x xs)
    (y ≠ x ∧ P).
Proof with auto.
  intros. constructor. destruct H. rewrite <- set_unfold_elem_of. clear set_unfold_elem_of.
  unfold delete, list_delete_elem. induction xs; [set_solver|].
  simpl. destruct (decide_rel _); set_solver.
Qed.


(** * Deduplication of lists *)
Definition dedup {A} (xs : list A) `{Countable A} : list A :=
  set_to_list ∘ list_to_set $ xs.

Lemma dedup_equiv {A} (xs : list A) `{Countable A} : xs ≡ dedup xs.
Proof. intros x. unfold dedup. simpl. set_solver. Qed.

Lemma elem_of_dedup {A} `{Countable A} x (xs : list A) :
  x ∈ xs ↔ x ∈ dedup xs.
Proof. intros. set_solver. Qed.

Global Instance set_unfold_elem_of_dedup {A} `{Countable A} x (xs : list A) P :
  SetUnfoldElemOf x xs P →
  SetUnfoldElemOf x (dedup xs) P.
Proof. constructor. rewrite <- dedup_equiv. apply H0. Qed.

Lemma dedup_nil {A} `{Countable A} :
  dedup [] = @nil A.
Proof.
  unfold dedup. simpl. rewrite <- list_equiv_nil. by rewrite set_to_list_empty.
Qed.

Lemma dedup_nil_iff {A} `{Countable A} (xs : list A) :
  dedup xs = [] ↔ xs = [].
Proof.
  unfold dedup. simpl. rewrite <- list_equiv_nil. by rewrite set_to_list_list_to_set_eq_nil.
Qed.

Lemma dedup_cons_inv {A} `{Countable A} (xs : list A) y ys :
  dedup xs = y :: ys → y ∈ xs ∧ y ∉ ys.
Proof.
  unfold dedup. simpl. intros. by apply set_to_list_list_to_set_cons_inv in H0.
Qed.

Lemma dedup_NoDup {A} (xs : list A) `{Countable A} :
  NoDup (dedup xs).
Proof. apply set_to_list_NoDup. Qed.

(** * Finding the first index of a particular element in a list *)

Definition first_index_of {A} (x : A) (xs : list A) `{EqDecision A} : option nat :=
  let fix go (xs : list A) i :=
    match xs with
    | [] => None
    | x' :: xs => if decide (x' = x) then Some i else go xs (S i)
    end in
  go xs 0.

Lemma first_index_of_nil {A} (x : A)  `{EqDecision A} :
  first_index_of x nil = None.
Proof. reflexivity. Qed.

Lemma first_index_of_cons {A} (x : A) (xs : list A) `{EqDecision A} :
  first_index_of x (x :: xs) = Some 0.
Proof. unfold first_index_of. destruct (decide _); done. Qed.

Lemma first_index_of_cons_ne {A} (x : A) (xs : list A) y `{EqDecision A} :
  x ≠ y →
  first_index_of x (y :: xs) = S <$> (first_index_of x xs).
Proof with auto.
  intros. unfold first_index_of. destruct (decide _); [done|].
  enough (∀ n,
    (fix go (xs0 : list A) (i : nat) {struct xs0} : option nat :=
      match xs0 with
      | [] => None
      | x' :: xs1 => if decide (x' = x) then Some i else go xs1 (S i)
      end)
      xs (S n) =
    S <$>
    (fix go (xs0 : list A) (i : nat) {struct xs0} : option nat :=
      match xs0 with
      | [] => None
      | x' :: xs1 => if decide (x' = x) then Some i else go xs1 (S i)
      end)
      xs n)...
  induction xs... intros. destruct (decide _)...
Qed.

Lemma first_index_of_cons_ne_Some_inv {A} (x : A) (xs : list A) y `{EqDecision A} i :
  x ≠ y →
  first_index_of x (y :: xs) = Some i → ∃ j, i = S j ∧ first_index_of x xs = Some j.
Proof with auto.
  intros. rewrite first_index_of_cons_ne in H0...
  destruct (first_index_of x xs) as [j|] eqn:E.
  - simpl in H0. inversion H0. exists j...
  - discriminate.
Qed.

Lemma first_index_of_None_inv {A} (y : A) (xs : list A) `{EqDecision A} :
  first_index_of y xs = None → y ∉ xs.
Proof with auto.
  intros. induction xs as [|x xs]; [set_solver|].
  destruct (decide (x = y)).
  - subst. rewrite first_index_of_cons in H. inversion H.
  - rewrite first_index_of_cons_ne in H... destruct (first_index_of y xs) as [j|] eqn:E.
    + simpl in H. discriminate.
    + set_solver.
Qed.

Lemma first_index_of_Some_inv {A} (y : A) (xs : list A) i `{EqDecision A} :
  first_index_of y xs = Some i → xs !! i = Some y ∧ ∀ j z, j < i → xs !! j = Some z → y ≠ z.
Proof with auto.
  intros. generalize dependent i. induction xs as [|x xs]; [discriminate|]; intros.
  destruct (decide (x = y)).
  - subst. rewrite first_index_of_cons in H. inversion H. subst. split; [set_solver|lia].
  - apply first_index_of_cons_ne_Some_inv in H as (j&?&?)...
    apply IHxs in H0 as []. subst i. simpl. split... intros.
    destruct (j0).
    + simpl in H2. inversion H2. subst...
    + assert (n0 < j) by lia. apply H1 with n0...
Qed.

Lemma first_index_of_Some_elem_of {A} (y : A) (xs : list A) `{EqDecision A} :
  y ∈ xs →
  ∃ i, first_index_of y xs = Some i.
Proof with auto.
  intros. induction xs as [|x xs]; [set_solver|]. set_unfold in H.
  destruct (decide (y = x)).
  - subst. exists 0. rewrite first_index_of_cons...
  - destruct H; [done|]. destruct (IHxs H) as (i&?). exists (S i).
    rewrite first_index_of_cons_ne... rewrite H0. reflexivity.
Qed.

(*** Z-Pairs *)
(** A zip pair or zpair for short is a conceptual pair of two lists in which elements at the same
index are somehow related to each other.

First, we define two notions of membership for zpair and prove some facts about them.

The most useful thing to do with zpairs is obviously to zip together and also to create a map
out of the zipped list. For this map to well-behave, the lists must "map" same item from the lhs
to the same item in the rhs. See [zpair_functional] below.

While most interesting facts about zpairs can be said when the two lists have the same length,
the general notion doesn't enforce this. *)

Instance zpair_elem_of_with_index {A B} : ElemOf (nat * (A * B)) (list A * list B) :=
  λ p1 p2, p2.1 !! p1.1 = Some p1.2.1 ∧ p2.2 !! p1.1 = Some p1.2.2.

Instance zpair_elem_of {A} {B} : ElemOf (A * B) (list A * list B) :=
  λ p1 p2, ∃ i, (i, p1) ∈ p2.

Lemma elem_of_zpair {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) ↔ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. reflexivity. Qed.


Global Hint Extern 0 =>
  match goal with
  | H1 : ?xs !! ?i = Some ?x, H2 : ?ys !! ?i = Some ?y |- (?x, ?y) ∈ (?xs, ?ys) =>
      exists i; split; assumption
  end : core.

Lemma not_elem_of_zpair_inv {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∉ (xs, ys) → ¬ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. rewrite elem_of_zpair. auto. Qed.

Lemma elem_of_zpair_indexed {A B} (i : nat) (x : A) (y : B) (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) ↔ xs !! i = Some x ∧ ys !! i = Some y.
Proof. reflexivity. Qed.

Lemma elem_of_zpair_indexed' {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) ↔ ∃ i, (i, (x, y)) ∈ (xs, ys).
Proof. reflexivity. Qed.

Global Hint Extern 0 =>
  match goal with
  | H1 : ?xs !! ?i = Some ?x,
    H2 : ?ys !! ?i = Some ?y |- (?i, (?x, ?y)) ∈ (?xs, ?ys) =>
      apply elem_of_zpair_indexed; split; [exact H1|exact H2]
  end : core.

Lemma not_elem_of_zpair {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (∀ i, xs !! i ≠ Some x ∨ ys !! i ≠ Some y) → (x, y) ∉ (xs, ys).
Proof.
  intros. intros contra. apply elem_of_zpair in contra as (i&?&?).
  destruct (H i) as []; contradiction.
Qed.

Lemma elem_of_zpair_diag {A} x x' (xs : list A) :
  (x, x') ∈ (xs, xs) → x' = x.
Proof. intros (i&?&?). simpl in *. naive_solver. Qed.

Lemma elem_of_zpair_indexed_diag {A} i x x' (xs : list A) :
  (i, (x, x')) ∈ (xs, xs) → x' = x.
Proof. intros (?&?). simpl in *. naive_solver. Qed.

Lemma elem_of_zpair_nil {A B} x y :
  ¬ (x, y) ∈ (([] : list A), ([] : list B)).
Proof with auto. intros (i&?&?). set_solver. Qed.

Lemma elem_of_zpair_nil_l {A B} x y (ys : list B) :
  ¬ (x, y) ∈ (([] : list A), ys).
Proof with auto. intros (i&?&?). set_solver. Qed.

Lemma elem_of_zpair_nil_r {A B} x y (xs : list A) :
  ¬ (x, y) ∈ (xs, ([] : list B)).
Proof with auto. intros (i&?&?). set_solver. Qed.

Global Hint Extern 0 =>
  match goal with
  | H : (_, _) ∈ ([], _) |- _ =>
      apply elem_of_zpair_nil_l in H as []
  | H : (_, _) ∈ (_, []) |- _ =>
      apply elem_of_zpair_nil_r in H as []
  end : core.

Lemma elem_of_zpair_cons_l {A B} y0 x y (xs : list A) (ys : list B) :
  y0 = y →
  (x, y0) ∈ (x :: xs, y :: ys).
Proof. intros. subst. apply elem_of_zpair. by exists 0. Qed.

Global Hint Extern 0 ((?x, ?y) ∈ (?x :: _, ?y :: _)) =>
  apply elem_of_zpair_cons_l; reflexivity : core.

Global Hint Extern 100 ((_, _) ∈ (_ :: _, _ :: _)) => apply elem_of_zpair_cons_l : core.

Lemma elem_of_zpair_cons_r {A B} x y x' y' (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) →
  (x, y) ∈ (x' :: xs, y' :: ys).
Proof. intros. destruct H as (i&?&?). simpl in *. apply elem_of_zpair. by exists (S i). Qed.

Global Hint Extern 100 ((_, _) ∈ (_ :: _, _ :: _)) => apply elem_of_zpair_cons_r : core.

Lemma elem_of_zpair_indexed_cons_l {A B} x0 y0 x y (xs : list A) (ys : list B) :
  (0, (x0, y0)) ∈ (x :: xs, y :: ys) ↔ (x0 = x ∧ y0 = y).
Proof. rewrite elem_of_zpair_indexed. simpl. split; naive_solver. Qed.

Lemma elem_of_zpair_indexed_cons_r {A B} i x0 y0 x y (xs : list A) (ys : list B) :
  (S i, (x0, y0)) ∈ (x :: xs, y :: ys) ↔ (i, (x0, y0)) ∈ (xs, ys).
Proof.
  do 2 rewrite elem_of_zpair_indexed. simpl. naive_solver.
Qed.

Global Hint Extern 0 =>
  match goal with
  | H : (?i, (?x, ?y) ∈ (?xs, ?ys)) |- (S ?i, (?x, ?y) ∈ (_ :: ?xs, _ :: ?ys)) =>
    rewrite elem_of_zpair_indexed_cons_r; exact H
  end : core.

Lemma elem_of_zpair_cons_ne {A B} x0 y0 x y (xs : list A) (ys : list B) :
  x0 ≠ x →
  (x0, y0) ∈ (x :: xs, y :: ys) ↔ (x0, y0) ∈ (xs, ys).
Proof with auto.
  intros. split; intros (i&?).
  - destruct i.
    + apply elem_of_zpair_indexed_cons_l in H0 as []. subst. contradiction.
    + apply elem_of_zpair_indexed_cons_r in H0. exists i...
  - exists (S i)...
Qed.

Lemma elem_of_zpair_cons_notin {A B} y0 x y (xs : list A) (ys : list B) :
  x ∉ xs →
  (x, y0) ∈ (x :: xs, y :: ys) ↔ y0 = y.
Proof with auto.
  intros. split.
  - intros (i&?). destruct i.
    + apply elem_of_zpair_indexed_cons_l in H0 as []...
    + apply elem_of_zpair_indexed_cons_r in H0 as []. simpl in *.
      by apply elem_of_list_lookup_2 in H0.
  - intros ->...
Qed.

Lemma elem_of_zpair_inv_l {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) →
  x ∈ xs.
Proof. intros (i&?&_). apply elem_of_list_lookup_2 in H. assumption. Qed.

Lemma elem_of_zpair_inv_r {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) →
  y ∈ ys.
Proof. intros (i&_&?). apply elem_of_list_lookup_2 in H. assumption. Qed.

Global Hint Extern 0 =>
  match goal with
  | H : (?x, ?y) ∈ (?xs, ?ys) |- ?x ∈ ?xs => apply elem_of_zpair_inv_l in H
  | H : (?x, ?y) ∈ (?xs, ?ys) |- ?y ∈ ?ys => apply elem_of_zpair_inv_l in H
  end : core.

Lemma elem_of_zpair_cons {A B} x0 y0 x y (xs : list A) (ys : list B) :
  (x0, y0) ∈ (x :: xs, y :: ys) ↔
  (x0 = x ∧ y0 = y) ∨ (x0, y0) ∈ (xs, ys).
Proof with auto.
  split; intros.
  - destruct H as (i&?&?). simpl in *. destruct i.
    + left. simpl in *... inversion H. inversion H0...
    + simpl in *. right...
  - destruct H... exists 0. split; naive_solver.
Qed.

Lemma elem_of_zpair_app {A B} x y (xs1 : list A) (ys1 : list B)
  (xs2 : list A) (ys2 : list B) `{!OfSameLength xs1 ys1} :
  (x, y) ∈ (xs1 ++ xs2, ys1 ++ ys2) ↔ (x, y) ∈ (xs1, ys1) ∨ (x, y) ∈ (xs2, ys2).
Proof with auto.
  split.
  - intros (i&?&?). simpl in H, H0. destruct (decide (i < length xs1)).
    + left. rewrite lookup_app_l in H... rewrite OfSameLength0 in l. rewrite lookup_app_l in H0...
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

Lemma elem_of_zpair_indexed_inv {A B} i x y (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) → (x, y) ∈ (xs, ys).
Proof. intros. exists i. assumption. Qed.

Global Hint Extern 0 =>
  match goal with
  | H : (?i, (?x, ?y)) ∈ (?xs, ?ys) |- ((?x, ?y) ∈ (?xs, ?ys)) =>
    apply elem_of_zpair_indexed_inv with (i:=i); exact H
  end : core.

Lemma lookup_list_to_map_zip_Some_inv {K A} `{Countable K}
    (ks : list K) (xs : list A) (k : K) (x : A) `{!OfSameLength ks xs} :
  (list_to_map (zip ks xs) : gmap K A) !! k = Some x →
                                                   (k, x) ∈ (ks, xs).
Proof with auto.
  intros. apply lookup_list_to_map_zip_Some in H0 as (i&?&?&?)...
Qed.

Lemma elem_of_zpair_fmap {A A' B B'} x' y' (xs : list A) (ys : list B)
    (f : A → A') (g : B → B') :
  (x', y') ∈ (f <$> xs, g <$> ys) ↔ ∃ x y, (x, y) ∈ (xs, ys) ∧ x' = f x ∧ y' = g y.
Proof with auto.
  split.
  - intros (i&?&?). simpl in H, H0. apply list_lookup_fmap_Some in H as (x&?&?).
    apply list_lookup_fmap_Some in H0 as (y&?&?). exists x, y. split_and!...
  - intros (x&y&(i&?&?)&?&?). simpl in H, H0. exists i. split; simpl; apply list_lookup_fmap_Some.
    + exists x. split...
    + exists y. split...
Qed.

Lemma elem_of_zpair_fmap_l {A A' B} x' y (xs : list A) (ys : list B)
    (f : A → A') :
  (x', y) ∈ (f <$> xs, ys) ↔ ∃ x, (x, y) ∈ (xs, ys) ∧ x' = f x.
Proof with auto.
  rewrite elem_of_zpair. split.
  - intros (i&?&?). apply list_lookup_fmap_Some in H as (x&?&?). exists x...
  - intros (x&(i&?&?)&?). simpl in H, H0. exists i. split... apply list_lookup_fmap_Some.
    exists x...
Qed.

Lemma elem_of_zpair_fmap_r {A B B'} x y' (xs : list A) (ys : list B)
    (g : B → B') :
  (x, y') ∈ (xs, g <$> ys) ↔ ∃ y, (x, y) ∈ (xs, ys) ∧ y' = g y.
Proof with auto.
  rewrite elem_of_zpair. split.
  - intros (i&?&?). apply list_lookup_fmap_Some in H0 as (y&?&?).
    exists y. split_and!...
  - intros (y&(i&?&?)&?). simpl in H, H0. exists i. split... apply list_lookup_fmap_Some.
    exists y...
Qed.

Lemma elem_of_zpair_indexed_flip {A B} (i : nat) (x : A) (y : B) (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) ↔ (i, (y, x)) ∈ (ys, xs).
Proof. do 2 rewrite elem_of_zpair_indexed. naive_solver. Qed.

Lemma elem_of_zpair_flip {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) ↔ (y, x) ∈ (ys, xs).
Proof.
  do 2 rewrite elem_of_zpair_indexed'. by setoid_rewrite elem_of_zpair_indexed_flip at 1.
Qed.

Lemma zpair_lookup_le {A B} {xs : list A} {ys : list B} {i x1} :
  length xs ≤ length ys →
  xs !! i = Some x1 → ∃ x2, ys !! i = Some x2.
Proof with auto.
  intros. apply elem_of_list_split_length in H0 as (xs0&xs1&->&?).
  destruct (ys !! i) as [x2|] eqn:E.
  - exists x2...
  - exfalso. apply list_lookup_None in E. rewrite length_app in H. rewrite <- H in E.
    simpl in E. subst i. lia.
Qed.

Lemma zpair_lookup_l' {A B} {xs : list A} {ys : list B} {i x1} :
  length xs = length ys →
  xs !! i = Some x1 → ∃ x2, ys !! i = Some x2.
Proof. intros H. apply zpair_lookup_le. lia. Qed.

Lemma zpair_lookup_l {A B} {xs : list A} {ys : list B} {x1} :
  length xs = length ys →
  x1 ∈ xs → ∃ x2, (x1, x2) ∈ (xs, ys).
Proof with auto.
  intros. apply elem_of_list_lookup in H0 as [i ?].
  destruct (zpair_lookup_l' H H0) as [x2 ?]. exists x2. apply elem_of_zpair.
  exists i. split...
Qed.

Lemma elem_of_zip {A B} (x : A) (xs : list A) (y : B) (ys : list B) :
  (x, y) ∈ zip xs ys ↔ (x, y) ∈ (xs, ys).
Proof with auto.
  rewrite elem_of_list_lookup at 1. rewrite elem_of_zpair. split; intros.
  - destruct H as (i&?). generalize dependent ys. revert i.
    induction xs; [set_solver|]. intros.
    destruct ys; [set_solver|]. destruct i.
    + simpl in H. inversion H. subst. exists 0...
    + simpl in H. apply IHxs in H as (j&?&?). exists (S j). simpl...
  - destruct H as (i&?). generalize dependent ys. revert i. induction xs; [set_solver|].
    intros. destruct H. destruct ys; [set_solver|]. destruct i.
    + simpl in H, H0. inversion H. inversion H0. subst. exists 0...
    + simpl in H, H0. ospecialize (IHxs i ys _); [auto|].
      destruct IHxs as (j&?). exists (S j). simpl...
Qed.

Lemma elem_of_zip' {A B} (x : A) (xs : list A) (y : B) (ys : list B) :
  (x, y) ∈ zip xs ys ↔ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. rewrite elem_of_zip. apply elem_of_zpair. Qed.

(** * Permutations of zpairs *)
(** We define a permutation relation for zpairs. This is an equivalence on zpairs.
Creating a map out of the zipping of two zpairs, is equivalent if they are zpair-permutation
of each other.

Intuitively, it describes shuffling the input and the output using the same algorithm. *)

Definition zpair_Permutation {A B} (p1 p2 : list A * list B) :=
  ∀ (x : A) (y : B), (x, y) ∈ p1 ↔ (x, y) ∈ p2.

Infix "≡ₚₚ" := (zpair_Permutation) (at level 70, no associativity) : refiney_scope.

Global Instance zpair_Permutation_refl {A B} : Reflexive (@zpair_Permutation A B).
Proof. intros p x y. reflexivity. Qed.

Global Hint Extern 0 (?p ≡ₚₚ ?p) => reflexivity : core.

Global Instance zpair_Permutation_sym {A B} : Symmetric (@zpair_Permutation A B).
Proof. intros p1 p2 H x y. specialize (H x y). naive_solver. Qed.

Global Instance zpair_Permutation_trans {A B} : Transitive (@zpair_Permutation A B).
Proof.
  intros p1 p2 p3 H12 H23. intros x y. specialize (H12 x y). specialize (H23 x y). naive_solver.
Qed.

Global Instance zpair_Permutation_equiv {A B} : Equivalence (@zpair_Permutation A B).
Proof.
  split; [exact zpair_Permutation_refl | exact zpair_Permutation_sym |
           exact zpair_Permutation_trans].
Qed.

Lemma zpair_Permutation_flip {A B}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) :
  (xs, ys) ≡ₚₚ (xs', ys') →
  (ys, xs) ≡ₚₚ (ys', xs').
Proof with auto.
  unfold zpair_Permutation. setoid_rewrite elem_of_zpair_flip at 1 2. naive_solver.
Qed.

Lemma zpair_Permutation_cons {A B} `{EqDecision A} (x : A) (y : B) (xs1 : list A)
  (ys1 : list B) (xs2 : list A) (ys2 : list B) `{!OfSameLength xs1 ys1} `{!OfSameLength xs2 ys2} :
  (xs1, ys1) ≡ₚₚ (xs2, ys2) →
  (x :: xs1, y :: ys1) ≡ₚₚ (x :: xs2, y :: ys2).
Proof with auto.
  unfold zpair_Permutation. intros. split; intros (i&?&?); simpl in H0, H1.
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

Lemma zpair_Permutation_app_comm {A B} (xs1 : list A) (ys1 : list B) (xs2 : list A)
    (ys2 : list B) `{!OfSameLength xs1 ys1} `{!OfSameLength xs2 ys2} :
  (xs1 ++ xs2, ys1 ++ ys2) ≡ₚₚ (xs2 ++ xs1, ys2 ++ ys1).
Proof with auto.
  unfold zpair_Permutation. intros x y. repeat rewrite elem_of_zpair_app...
  naive_solver.
Qed.

Lemma zpair_Permutation_nil_inv_l {A B}
    (xs : list A) (ys : list B) `{!OfSameLength xs ys} :
  ([], []) ≡ₚₚ (xs, ys) →
  xs = [] ∧ ys = [].
Proof with auto.
  intros. unfold zpair_Permutation in H. induction_same_length xs ys as x y...
  - intros. clear IH. specialize (H x y). assert ((x, y) ∈ (x :: xs, y :: ys)).
    { exists 0. split... }
    rewrite <- H in H0. destruct H0 as (i&?&?). simpl in H0, H1. set_solver.
Qed.

Lemma zpair_Permutation_cons_inv_l {A B} `{EqDecision A}
    (x : A) (y : B) (xs : list A) (ys : list B)
    (xs' : list A) (ys' : list B) `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  (x :: xs, y :: ys) ≡ₚₚ (xs', ys') →
  x ∉ xs →
  NoDup xs →
  NoDup xs' →
  ∃ (xs'0 : list A) (ys'0 : list B) (xs'1 : list A) (ys'1 : list B) (Hl0 : OfSameLength xs'0 ys'0) (Hxs : OfSameLength xs'1 ys'1),
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
  - rewrite elem_of_zpair_cons_ne in H... rewrite H.
    rewrite elem_of_zpair_app... rewrite elem_of_zpair_cons_ne...
    rewrite elem_of_zpair_app...
Qed.

Lemma zpair_Permutation_fmap {A A' B B'}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) (f : A → A') (g : B → B') :
  (xs, ys) ≡ₚₚ (xs', ys') →
  (f <$> xs, g <$> ys) ≡ₚₚ (f <$> xs', g <$> ys').
Proof with auto.
  intros. unfold zpair_Permutation. intros x' y'. rewrite elem_of_zpair_fmap...
  rewrite elem_of_zpair_fmap... split; intros (x&y&?&?&?);
    exists x, y; split; auto; apply H in H0...
Qed.

Lemma zpair_Permutation_fmap_l {A A' B}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) (f : A → A') :
  (xs, ys) ≡ₚₚ (xs', ys') →
  (f <$> xs, ys) ≡ₚₚ (f <$> xs', ys').
Proof with auto.
  intros. unfold zpair_Permutation. intros x' y. rewrite elem_of_zpair_fmap_l...
  rewrite elem_of_zpair_fmap_l... split; intros (x&?&?);
    exists x; split; auto; apply H in H0...
Qed.

Lemma zpair_Permutation_fmap_r {A B B'}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) (g : B → B') :
  (xs, ys) ≡ₚₚ (xs', ys') →
  (xs, g <$> ys) ≡ₚₚ (xs', g <$> ys').
Proof with auto.
  intros. unfold zpair_Permutation. intros x y'. rewrite elem_of_zpair_fmap_r...
  rewrite elem_of_zpair_fmap_r... split; intros (y&?&?);
    exists y; split; auto; apply H in H0...
Qed.

(** * Functional zpairs *)
(** A zpair is functional if it can uniquely be converted to a map. For this to happen, if
_x_ appears at indices _i_, and _j_ in the input list, the output list must have the same item
at these two indices. This way of defining the notion, assumes the output list's length is greater
of equal to the length of the input list. [zpair_functional] captures a weaker notion, by not
enforcing this. *)
Definition zpair_functional {A B} (xs : list A) (ys : list B) :=
  ∀ x y1 y2, (x, y1) ∈ (xs, ys) → (x, y2) ∈ (xs, ys) → y1 = y2.

Global Hint Extern 0 =>
  match goal with
  | H  : zpair_functional ?xs ?ys,
    H1 : (?x, ?y1) ∈ (?xs, ?ys),
    H2 : (?x, ?y2) ∈ (?xs, ?ys)
    |- ?y1 = ?y2 => apply (H x); [exact H1 | exact H2]
  end : core.

Lemma zpair_functional_inv {A B} x (xs : list A) y y' (ys : list B) i :
  zpair_functional xs ys →
  (x, y) ∈ (xs, ys) →
  xs !! i = Some x  →
  ys !! i = Some y' →
  y' = y.
Proof with auto. intros. apply (H x)... Qed.

Lemma NoDup_zpair_functional {A B} (xs : list A) (ys : list B) :
  NoDup xs →
  zpair_functional xs ys.
Proof with auto.
  intros H ? ? ? ? ?. apply elem_of_zpair in H0 as (i&?&?).
  apply elem_of_zpair in H1 as (j&?&?). pose proof (NoDup_lookup xs i j x H H0 H1).
  subst j. rewrite H2 in H3. inversion H3...
Qed.

Global Hint Extern 0 (zpair_functional ?xs _) =>
  match goal with
  | H : NoDup xs |- _ =>
    apply NoDup_zpair_functional; exact H
  end : core.
Global Hint Extern 0 (zpair_functional (dedup _) _) =>
  apply NoDup_zpair_functional; apply dedup_NoDup : core.

Lemma zpair_functional_nil {A B}  :
  zpair_functional (@nil A) (@nil B).
Proof. by intros x y1 y2 ??. Qed.

Global Hint Extern 0 (zpair_functional [] []) => apply zpair_functional_nil : core.

Lemma zpair_functional_cons_inv {A B} x y (xs : list A) (ys : list B) :
  zpair_functional (x :: xs) (y :: ys) → zpair_functional xs ys.
Proof with auto.
  intros. intros x0 y1 y2 ? ?. unfold zpair_functional in H.
  apply elem_of_zpair in H0 as (i&?&?). apply elem_of_zpair in H1 as (j&?&?).
  apply H with (x:=x0)...
Qed.

Lemma zpair_functional_cons {A B} x (xs : list A) y (ys : list B) :
  length xs = length ys →
  zpair_functional (x :: xs) (y :: ys) ↔
    (∀ y', (x, y') ∈ (xs, ys) → y' = y) ∧ zpair_functional xs ys.
Proof with auto.
  split; intros.
  - split; [|eapply zpair_functional_cons_inv; eauto]. intros.
    symmetry. apply (H0 x y y')...
  - destruct H0. intros u y1 y2 ??. apply elem_of_zpair_cons in H2 as [];
      apply elem_of_zpair_cons in H3 as []; naive_solver.
Qed.

Global Hint Resolve zpair_functional_cons_inv : core.

Global Hint Extern 0 =>
  match goal with
  | H : zpair_functional (_ :: ?a) (_ :: ?b) |- zpair_functional ?a ?b =>
      apply zpair_functional_cons_inv in H; exact H
  end : core.

Global Hint Extern 100 =>
  match goal with
  | H : zpair_functional (_ :: _) (_ :: _) |- _ => apply zpair_functional_cons_inv in H as ?
  end : core.

Lemma zpair_functional_cons_elem_of_tl {A B} (x : A) (xs : list A) (y : B) (ys : list B) :
  length xs = length ys →
  x ∈ xs →
  zpair_functional (x :: xs) (y :: ys) →
  y ∈ ys.
Proof with auto.
  intros. apply zpair_functional_cons in H1 as [? _]...
  apply elem_of_list_lookup_1 in H0 as (i&?).
  pose proof (zpair_lookup_l' H H0) as (y'&?).
  enough (y' = y) by (subst; apply elem_of_list_lookup_2 in H2; assumption)...
Qed.

Lemma zpair_functional_app_inv {A B} (xs1 xs2 : list A) (ys1 ys2 : list B) :
  length xs1 = length ys1 →
  zpair_functional (xs1 ++ xs2) (ys1 ++ ys2) →
  zpair_functional xs1 ys1 ∧ zpair_functional xs2 ys2.
Proof with auto.
  intros. split; intros x; intros; apply (H0 x); apply elem_of_zpair_app; auto.
Qed.

Lemma zpair_functional_app_comm {A B} (xs1 xs2 : list A) (ys1 ys2 : list B) :
  length xs1 = length ys1 →
  length xs2 = length ys2 →
  zpair_functional (xs1 ++ xs2) (ys1 ++ ys2) ↔ zpair_functional (xs2 ++ xs1) (ys2 ++ ys1).
Proof with auto.
  intros. unfold zpair_functional. setoid_rewrite elem_of_zpair_app... naive_solver.
Qed.

Lemma zpair_functional_app_cons_comm {A B} x (xs1 xs2 : list A) y (ys1 ys2 : list B) :
  length xs1 = length ys1 →
  length xs2 = length ys2 →
  zpair_functional (xs1 ++ x :: xs2) (ys1 ++ y :: ys2) ↔
    zpair_functional (x :: xs1 ++ xs2) (y :: ys1 ++ ys2).
Proof with auto.
  intros. unfold zpair_functional. setoid_rewrite elem_of_zpair_app... split; intros.
  - apply elem_of_zpair in H2 as (i&?&?). apply elem_of_zpair in H3 as (j&?&?).
    apply (H1 x0).
    + destruct i; simpl in *.
      * inversion H2. inversion H4. right...
      * apply lookup_app_Some in H2 as [| []]; apply lookup_app_Some in H4 as [| []].
        -- left. exists i...
        -- apply lookup_lt_Some in H2. lia.
        -- apply lookup_lt_Some in H4. lia.
        -- right. exists (S (i - length xs1)). apply elem_of_zpair_indexed_cons_r.
            split... replace (i - length xs1) with (i - length ys1) by lia...
    + destruct j; simpl in *.
      * inversion H3. inversion H5. right...
      * apply lookup_app_Some in H3 as [| []]; apply lookup_app_Some in H5 as [| []].
        -- left. exists j...
        -- apply lookup_lt_Some in H3. lia.
        -- apply lookup_lt_Some in H5. lia.
        -- right. exists (S (j - length xs1)). apply elem_of_zpair_indexed_cons_r.
            split... replace (j - length xs1) with (j - length ys1) by lia...
  - destruct H2; destruct H3; apply (H1 x0).
    all: try solve [apply elem_of_zpair_cons_r; auto; apply elem_of_zpair_app; auto].
    all: try solve [apply elem_of_zpair_cons in H2 as [[] |]; [subst; auto|];
        apply elem_of_zpair_cons_r; auto; apply elem_of_zpair_app; auto].
    all: try solve [apply elem_of_zpair_cons in H3 as [[] |]; [subst; auto|];
        apply elem_of_zpair_cons_r; auto; apply elem_of_zpair_app; auto].
Qed.


Lemma zpair_functional_fmap_l {A A' B} (f : A → A') (xs : list A) (ys : list B) `{!Inj (=) (=) f} :
  zpair_functional xs ys →
  zpair_functional (f <$> xs) ys.
Proof with auto.
  intros. intros x y1 y2 ??. apply elem_of_zpair_fmap_l in H0 as (x0&?&?).
  apply elem_of_zpair_fmap_l in H1 as (x0'&?&?). subst. apply Inj0 in H3 as ->...
Qed.

Lemma zpair_functional_fmap_r {A B B'} (f : B → B') (xs : list A) (ys : list B) `{!Inj (=) (=) f} :
  zpair_functional xs ys →
  zpair_functional xs (f <$> ys).
Proof with auto.
  intros. intros x y1 y2 ??. apply elem_of_zpair_fmap_r in H0 as (y0&?&?).
  apply elem_of_zpair_fmap_r in H1 as (y0'&?&?). subst. f_equal...
Qed.

Lemma list_to_map_zip_lookup_zpair_functional {A B} `{Countable A} {x y} {xs : list A} {ys : list B} :
  zpair_functional (x :: xs) (y :: ys) →
  length xs = length ys →
  x ∈ xs →
  (list_to_map (zip xs ys) : gmap A B) !! x = Some y.
Proof with auto.
  intros. destruct (list_to_map (zip xs ys) !! x) as [y'|] eqn:E.
  - apply lookup_list_to_map_zip_Some in E as (i&?&?&?)... f_equal. apply (H0 x)...
  - exfalso. apply lookup_list_to_map_zip_None in E...
Qed.

Lemma zpair_Permutation_list_to_map_zip' {A B}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) `{Countable A}
    `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  zpair_functional xs ys →
  zpair_functional xs' ys' →
  (xs, ys) ≡ₚₚ (xs', ys') →
  (list_to_map (zip xs ys) : gmap A B) = list_to_map (zip xs' ys').
Proof with auto.
  intros. unfold zpair_Permutation in H. apply map_eq. intros x.
  apply option_eq. intros y. rewrite <- elem_of_list_to_map'.
  2: { intros. apply elem_of_zip' in H3 as (?&?&?).
        apply elem_of_zip' in H4 as (?&?&?)... apply (H0 x)... }
  rewrite <- elem_of_list_to_map'.
  2: { intros. apply elem_of_zip' in H3 as (?&?&?).
        apply elem_of_zip' in H4 as (?&?&?)... apply (H1 x)... }
  do 2 rewrite elem_of_zip. specialize (H2 x y)...
Qed.

Lemma zpair_Permutation_list_to_map_zip {A B}
    (xs : list A) (ys : list B) (xs' : list A) (ys' : list B) `{Countable A}
    `{!OfSameLength xs ys} `{!OfSameLength xs' ys'} :
  NoDup xs →
  NoDup xs' →
  (xs, ys) ≡ₚₚ (xs', ys') →
  (list_to_map (zip xs ys) : gmap A B) = list_to_map (zip xs' ys').
Proof with auto.
  intros. apply zpair_Permutation_list_to_map_zip'...
  (* Direct proof: *)
  (* intros. unfold zpair_Permutation in H. apply map_eq. intros x. *)
  (* destruct (list_to_map (zip xs ys) !! x) as [y|] eqn:E. *)
  (* - apply lookup_list_to_map_zip_Some_inv in E... apply H2 in E. *)
  (*   symmetry. apply lookup_list_to_map_zip_Some... destruct E as (i&?&?). simpl in H3, H4. *)
  (*   exists i. split_and!... intros. apply NoDup_lookup with (i:=i) in H5... lia. *)
  (* - apply lookup_list_to_map_zip_None in E... symmetry. apply lookup_list_to_map_zip_None... *)
  (*   intros ?. apply elem_of_list_lookup in H3 as (i&?). *)
  (*   destruct (lookup_of_same_length_l ys' H3) as (y&?)... *)
  (*   assert ((x, y) ∈ (xs, ys)) as (?&?&_). *)
  (*   { apply H2. exists i. split... } *)
  (*   simpl in H5. apply elem_of_list_lookup_2 in H5. contradiction. *)
Qed.

(** * Injective zpairs *)
(** The dual concept of functional zpairs. If a zpair is injective, creating an inverse map out
of it is well-defined. *)
Definition zpair_injective {A B} (xs : list A) (ys : list B) :=
  ∀ x1 x2 y, (x1, y) ∈ (xs, ys) → (x2, y) ∈ (xs, ys) → x1 = x2.

Global Hint Extern 0 =>
  match goal with
  | H  : zpair_injective ?xs ?ys,
    H1 : (?x1, ?y) ∈ (?xs, ?ys),
    H2 : (?x2, ?y) ∈ (?xs, ?ys)
    |- ?x1 = ?x2 => apply (H _ _ y); [exact H1 | exact H2]
  end : core.

Lemma zpair_injective_flip {A B} (xs : list A) (ys : list B) :
  zpair_injective xs ys ↔ zpair_functional ys xs.
Proof.
  unfold zpair_injective, zpair_functional. split.
  - intros H x1 x2 y ??. apply elem_of_zpair_flip in H0, H1. naive_solver.
  - intros H x1 x2 y ??. apply elem_of_zpair_flip in H0, H1. naive_solver.
Qed.

Lemma NoDup_zpair_injective {A B} (xs : list A) (ys : list B) :
  NoDup ys →
  zpair_injective xs ys.
Proof. intros. apply zpair_injective_flip. by apply NoDup_zpair_functional. Qed.

Global Hint Extern 0 (zpair_injective _ ?ys) =>
  match goal with
  | H : NoDup ys |- _ =>
    apply NoDup_zpair_injective; exact H
  end : core.
Global Hint Extern 0 (zpair_injective _ (dedup _) ) =>
  apply NoDup_zpair_injective; apply dedup_NoDup : core.

Lemma zpair_injective_cons_inv {A B} x y (xs : list A) (ys : list B) :
  zpair_injective (x :: xs) (y :: ys) → zpair_injective xs ys.
Proof with auto. do 2 rewrite zpair_injective_flip... Qed.

Global Hint Extern 1 =>
  match goal with
  | H : zpair_injective (_ :: ?a) (_ :: ?b) |- zpair_injective ?a ?b =>
      apply zpair_injective_cons_inv in H; exact H
  end : core.

Lemma zpair_injective_cons_elem_of_tl {A B} (x : A) (xs : list A) (y : B) (ys : list B) :
  length xs = length ys →
  y ∈ ys →
  zpair_injective (x :: xs) (y :: ys) →
  x ∈ xs.
Proof with auto.
  intros. rewrite zpair_injective_flip in H1.
  apply zpair_functional_cons_elem_of_tl with (x:=y) (xs:=ys)...
Qed.

(** * The image of a zpair under a list *)
(** Given a zpair xs, ys and a list xs' of the same type as xs, [zpair_image xs ys xs'] is
a list ys' that is a sublist of ys and for each zipped pair (x, y), ys' contains y only
iff x ∈ xs'.

Conceptually, and ideally (i.e., xs and ys are of same length, and the zpair is functional),
if we consider a zpair as a function f: xs → ys, [zpair_image xs ys xs'] is the image of f
under xs': [f(xs') ⊆ ys].

Note that the output is not intended to form zpair with xs'. That's because the output
is in the same order as ys. For filtering ys to form a zpair with xs', see [zpair_permute]
below. *)

(* HACK: Should we return a set instead of a list since the output isn't supposed to be
zpair with xs'? *)
Fixpoint zpair_image {A B} `{EqDecision A} (xs : list A) (ys : list B) (xs' : list A) :=
  match xs, ys with
  | x :: xs, y :: ys =>
      if decide (x ∈ xs') then
        y :: zpair_image xs ys xs'
      else
        zpair_image xs ys xs'
  | _, _ => []
  end.

Global Instance zpair_image_proper {A B} `{EqDecision A} :
  Proper ((=) ==> (=) ==> (≡) ==> (=)) (@zpair_image A B _).
Proof with auto.
  intros xs ? <- ys ? <- xs'1 xs'2 H . generalize dependent ys. induction xs as [|x xs]...
  intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _)...
  - f_equal. apply IHxs.
  - apply H in e. contradiction.
  - apply H in e. contradiction.
Qed.

Lemma zpair_image_cons_pair {A B} `{EqDecision A}
    (xs' : list A) x (xs : list A) y (ys : list B) :
  x ∈ xs' →
  zpair_image (x :: xs) (y :: ys) xs' = y :: zpair_image xs ys xs'.
Proof. intros. simpl. by destruct (decide _). Qed.

Lemma zpair_image_cons_pair_notin {A B} `{EqDecision A}
    (xs' : list A) x (xs : list A) y (ys : list B) :
  x ∉ xs' →
  zpair_image (x :: xs) (y :: ys) xs' = zpair_image xs ys xs'.
Proof. intros. simpl. by destruct (decide _). Qed.

Lemma zpair_image_nil_1 {A B} `{EqDecision A} (xs : list A) (ys : list B) :
  zpair_image xs ys [] = [].
Proof with auto.
  generalize dependent ys. induction xs as [|x xs]... destruct ys as [|y ys]... simpl...
Qed.
Lemma zpair_image_nil_2 {A B} `{EqDecision A} (xs' : list A) (ys : list B) :
  zpair_image [] ys xs' = [].
Proof with auto. induction ys... Qed.
Lemma zpair_image_nil_3 {A B} `{EqDecision A} (xs' xs : list A) :
  zpair_image xs (@nil B) xs' = [].
Proof with auto. induction xs... Qed.

Lemma zpair_image_delete_1 {A B} `{EqDecision A} (x : A) (xs' xs : list A) (ys : list B) :
  x ∉ xs →
  zpair_image xs ys xs' = zpair_image xs ys (delete x xs').
Proof with auto.
  intros. generalize dependent ys. induction xs as [|x' xs]...
  intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _).
  2-4: set_solver.
  f_equal. apply IHxs. set_solver.
Qed.

Lemma zpair_image_delete_1_head {A B} `{EqDecision A} (x : A) (xs' xs : list A) (ys : list B) :
  x ∉ xs →
  zpair_image xs ys (x :: xs') = zpair_image xs ys xs'.
Proof with auto.
  intros. generalize dependent ys. induction xs as [|x' xs]...
  intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _).
  2-4: set_solver.
  f_equal. apply IHxs. set_solver.
Qed.

Lemma zpair_image_diag_1 {A B} `{EqDecision A} (xs : list A) (ys : list B) :
  zpair_image xs ys xs = take (length xs) ys.
Proof with auto.
  generalize dependent xs. induction ys as [|y ys].
  - intros. rewrite take_nil. rewrite zpair_image_nil_3...
  - destruct xs as [|x xs]... simpl. destruct (decide _); [|set_solver].
    destruct (decide (x ∈ xs)).
    + assert (xs ≡ x :: xs) by set_solver. f_equiv. rewrite <- IHys.
      apply zpair_image_proper...
    + rewrite zpair_image_delete_1_head... f_equal. apply IHys.
Qed.

Lemma zpair_image_sub_1 {A B} `{EqDecision A} (xs' xs : list A) (ys : list B) :
  xs ⊆ xs' →
  zpair_image xs ys xs' = zpair_image xs ys xs.
Proof with auto.
  intros. generalize dependent ys. generalize dependent xs'. induction xs as [|x xs]...
  intros. destruct ys as [|y ys]... simpl. destruct (decide _); destruct (decide _).
  2-4: set_solver.
  - f_equal. rewrite IHxs; [|set_solver].
    destruct (decide (x ∈ xs)).
    + apply zpair_image_proper... set_solver.
    + rewrite <- zpair_image_delete_1_head with (x:=x)...
Qed.

Lemma zpair_image_cons_1 {A B} `{EqDecision A} (x : A) (y : B)
    (xs' xs : list A) (ys : list B) :
  length xs ≤ length ys →
  zpair_functional xs ys →
  x ∉ xs' →
  (x, y) ∈ (xs, ys) →
  zpair_image xs ys (x :: xs') ≡ y :: zpair_image xs ys xs'.
Proof with auto.
  intros Hlen. intros. generalize dependent ys. induction xs as [|x1 xs1]; intros.
  { apply elem_of_zpair in H1 as (i&?&?). discriminate. }
  destruct ys as [|y1 ys1].
  { apply elem_of_zpair in H1 as (i&?&?). discriminate. }
  destruct (decide (x = x1)).
  - subst. simpl in *. destruct (decide _); [|set_solver]. destruct (decide _); [set_solver|].
    apply zpair_functional_cons_inv in H as ?. apply Nat.succ_le_mono in Hlen.
    specialize (IHxs1 ys1 Hlen H2). assert (y = y1).
    {
      apply elem_of_zpair in H1 as (i&?&?). destruct (decide (i = 0)).
      - subst. simpl in *. inversion H3...
      - apply (H x1)...
    }
    subst. destruct (decide (x1 ∈ xs1)).
    + apply elem_of_list_lookup in e0 as (i&?).
      pose proof (zpair_lookup_le Hlen H3) as (y1'&?).
      assert (y1 = y1') by (apply (H x1); auto).
      subst y1'. forward IHxs1 by (apply elem_of_zpair; eauto).
      unfold equiv, set_equiv_instance in IHxs1.
      set_solver.
    + rewrite zpair_image_delete_1_head...
  - simpl in Hlen. apply Nat.succ_le_mono in Hlen. simpl. destruct decide.
    + destruct decide; [| set_solver]. clear e. rewrite equiv_cons_cons.
      simpl in Hlen.
      rewrite IHxs1... apply elem_of_zpair_cons_ne in H1...
    + destruct decide; [set_solver|].
      apply IHxs1... apply elem_of_zpair_cons_ne in H1...
Qed.

(** * Permutating a zpair *)
(** Does the same thing as [zpair_image], while ensuring the output forms a zpair with xs'. *)
Fixpoint zpair_permute {A B} (xs : list A) (ys : list B) (xs' : list A) `{!EqDecision A} `{!Inhabited B} : list B :=
  match xs' with
  | [] => []
  | x' :: xs' =>
      match first_index_of x' xs with
      | None => inhabitant :: zpair_permute xs ys xs'
      | Some i => ys !!! i :: zpair_permute xs ys xs'
      end
  end.

Lemma zpair_permute_length {A B} (xs : list A) (ys : list B) (xs' : list A) `{!EqDecision A} `{!Inhabited B} :
  length (zpair_permute xs ys xs') = length xs'.
Proof with auto.
  induction xs'... simpl. destruct (first_index_of _ _); simpl; lia.
Qed.

Lemma zpair_permute_subset {A B} (xs : list A) (ys : list B) (xs' : list A) `{!EqDecision A} `{!Inhabited B} :
  length xs ≤ length ys →
  xs' ⊆ xs →
  zpair_permute xs ys xs' ⊆ ys.
Proof with auto.
  induction xs' as [|x' xs']; intros.
  - set_solver.
  - simpl. destruct (first_index_of x' xs) as [i|] eqn:E.
    + apply first_index_of_Some_inv in E as [E' _]. destruct (zpair_lookup_le H E') as [y ?].
      apply list_lookup_total_correct in H1 as H2. rewrite H2.
      apply elem_of_list_lookup_2 in H1.
      apply list_subseteq_cons_iff. split... apply IHxs'... set_solver.
    + apply first_index_of_None_inv in E. set_solver.
Qed.

Lemma zpair_permute_elem_inv {A B} (xs : list A) (ys : list B) (xs' : list A)
    x y `{!EqDecision A} `{!Inhabited B} :
  length xs ≤ length ys →
  xs' ⊆ xs →
  (x, y) ∈ (xs', zpair_permute xs ys xs') →
  (x, y) ∈ (xs, ys).
Proof with auto.
  intros H. induction xs' as [|x' xs']; intros.
  { rewrite elem_of_zpair in H1. naive_solver. }
  simpl in *. destruct (first_index_of x' xs) as [k|] eqn:E.
  - apply first_index_of_Some_inv in E as [? _]. pose proof (zpair_lookup_le H H2) as (y'&?).
    apply elem_of_zpair_indexed' in H1 as (i&?&?). simpl in *. destruct i.
    + simpl in *. inversion H1. inversion H4. subst x'.
      apply list_lookup_total_correct in H3 as H5. subst y'. rewrite H7 in *.
      apply elem_of_zpair. exists k...
    + simpl in H1, H4. apply IHxs'; [set_solver|]. exists i...
  - apply first_index_of_None_inv in E. set_solver.
Qed.

Lemma zpair_permute_image  {A B} (xs : list A) (ys : list B) (xs' : list A)
    `{!EqDecision A} `{!Inhabited B} :
  length xs ≤ length ys →
  zpair_functional xs ys →
  xs' ⊆ xs →
  zpair_image xs ys xs' ⊆ zpair_permute xs ys xs'.
Proof with auto.
  induction xs' as [|x' xs']; intros.
  - rewrite zpair_image_nil_1...
  - simpl. destruct (first_index_of x' xs) as [i|] eqn:E.
    + apply list_subseteq_cons_iff in H1 as [? ?]. destruct (decide (x' ∈ xs')).
      * assert (x' :: xs' ≡ xs') by set_solver. rewrite H3. apply list_subseteq_cons...
      * apply first_index_of_Some_inv in E as [? _].
        pose proof (zpair_lookup_le H H3) as [y ?]. eapply subseteq_proper.
        -- apply zpair_image_cons_1... apply elem_of_zpair. eauto.
        -- reflexivity.
        -- apply list_lookup_total_correct in H4. rewrite H4. apply cons_proper_subseteq...
    + apply first_index_of_None_inv in E. set_solver.
Qed.

(* The requirements cannot be weakened. For example [xs ⊆ xs'] and [length ys ≤ length xs] *)
(* is not enough: [xs:=[a; a; b]], [ys:=[c; c]], [xs':=[a; b]] permutes to [[c; ⊥]]        *)
Lemma zpair_permute_superset {A B} (xs : list A) (ys : list B) (xs' : list A)
    `{!EqDecision A} `{!Inhabited B} :
  length xs = length ys →
  zpair_functional xs ys →
  xs ≡ xs' →
  ys ⊆ zpair_permute xs ys xs'.
Proof with auto.
  intros. apply list_equiv_subseteq in H1 as [].
  intros. opose proof (zpair_permute_image xs ys xs' _ H0 H2); [lia|].
  rewrite zpair_image_sub_1 in H3... rewrite zpair_image_diag_1 in H3.
  rewrite take_ge in H3... lia.
Qed.

Lemma zpair_permute_equiv {A B} (xs : list A) (ys : list B) (xs' : list A)
    `{!EqDecision A} `{!Inhabited B} :
  length xs = length ys →
  zpair_functional xs ys →
  xs ≡ xs' →
  zpair_permute xs ys xs' ≡ ys.
Proof with auto.
  intros. apply list_equiv_subseteq. apply list_equiv_subseteq in H1 as []. split.
  - apply zpair_permute_subset... lia.
  - apply zpair_permute_superset... set_solver.
Qed.

Lemma zpair_permute_functional {A B} (xs : list A) (ys : list B) (xs' : list A)
    `{!EqDecision A} `{!Inhabited B} :
  length xs ≤ length ys →
  zpair_functional xs ys →
  xs' ⊆ xs →
  zpair_functional xs' (zpair_permute xs ys xs').
Proof with auto.
  intros. intros x y1 y2 ??. pose proof (zpair_permute_elem_inv xs ys xs').
  apply H4 in H2... apply H4 in H3...
Qed.

Lemma zpair_permute_injective {A B} (xs : list A) (ys : list B) (xs' : list A)
    `{!EqDecision A} `{!Inhabited B} :
  length xs ≤ length ys →
  zpair_injective xs ys →
  xs' ⊆ xs →
  zpair_injective xs' (zpair_permute xs ys xs').
Proof with auto.
  intros. intros x1 x2 y ??. pose proof (zpair_permute_elem_inv xs ys xs').
  apply H4 in H2... apply H4 in H3...
Qed.

Lemma zpair_permute_elem {A B} (xs : list A) (ys : list B) (xs' : list A)
    x y `{!EqDecision A} `{!Inhabited B} :
  zpair_functional xs ys →
  length xs = length ys →
  (x, y) ∈ (xs, ys) →
  x ∈ xs' →
  (x, y) ∈ (xs', zpair_permute xs ys xs').
Proof with auto.
  intros. generalize dependent ys. generalize dependent xs.
  induction xs' as [|x' xs']; [set_solver|]. intros.
  simpl. destruct (first_index_of x' xs) as [k|] eqn:E.
  - apply first_index_of_Some_inv in E as [? _]. destruct (zpair_lookup_l' H0 H3) as (y'&?).
    apply list_lookup_total_correct in H4 as H5. rewrite H5. clear H5.
    destruct (decide (x = x')).
    + subst. apply elem_of_zpair_cons_l... apply (H x')...
    + set_unfold in H2. destruct H2; [contradiction|].
      apply elem_of_zpair_cons_r...
  - apply first_index_of_None_inv in E. apply elem_of_zpair_cons_r.
    apply elem_of_cons in H2 as [|].
    + subst x'. assert (x ∈ xs)... done.
    + apply IHxs'...
Qed.

Lemma zpair_permute_Permutation {A B} (xs : list A) (ys : list B) (xs' : list A)
    `{!EqDecision A} `{!Inhabited B} :
  xs ≡ₚ xs' →
  length xs = length ys →
  zpair_functional xs ys →
  (xs, ys) ≡ₚₚ (xs', zpair_permute xs ys xs').
Proof with auto.
  intros. unfold zpair_Permutation. intros. split.
  2:{
    intros. apply zpair_permute_elem_inv in H2...
    - lia.
    - apply Permutation_equiv_inv in H. apply list_equiv_subseteq in H. naive_solver.
  }
  generalize dependent ys. generalize dependent xs.
  induction xs' as [|x' xs']; intros.
  - apply Permutation_equiv_inv in H. apply list_equiv_nil in H. subst.
    apply elem_of_zpair in H2 as (i&?&_). set_solver.
  - simpl. destruct (first_index_of x' xs) as [i|] eqn:E.
    2:{
      apply first_index_of_None_inv in E. apply Permutation_equiv_inv in H.
      specialize (H x'). set_solver.
    }
    apply first_index_of_Some_inv in E as (?&E). destruct (zpair_lookup_l' H0 H3) as (y'&?).
    apply list_lookup_total_correct in H4 as H5. rewrite H5 in *. clear H5.
    destruct (decide (x = x')).
    + subst. assert (y = y') by (apply (H1 x'); auto). subst...
    + apply elem_of_zpair_cons_r.
      apply elem_of_list_split_length in H3 as H5. destruct H5 as (xs1&xs2&->&?).
      rewrite Permutation_app_cons_r_comm in H. apply Permutation_cons_inv in H.
      apply elem_of_list_split_length in H4 as H6. destruct H6 as (ys1&ys2&->&?).
      rewrite H5 in H6. do 2 rewrite length_app in H0. simpl in H0.
      assert (length xs2 = length ys2) by lia. assert (Hf:=H1).
      apply zpair_functional_app_cons_comm in H1... apply zpair_functional_cons_inv in H1.
      ospecialize (IHxs' (xs1 ++ xs2) H (ys1 ++ ys2) _ _ _)...
      { simpl in *. do 2 rewrite length_app. lia. }
      { apply elem_of_zpair_app in H2 as []...
        + apply elem_of_zpair_app...
        + apply elem_of_zpair_cons in H2 as [[] |]; [contradiction|].
          apply elem_of_zpair_app... }
      rename IHxs' into Helem. assert (x ∈ xs')...
      apply zpair_permute_elem_inv in Helem.
      2: do 2 rewrite length_app; lia.
      2:{ apply list_equiv_subseteq. apply Permutation_equiv_inv... }
      subst. apply zpair_permute_elem... do 2 rewrite length_app. simpl. lia.
Qed.
