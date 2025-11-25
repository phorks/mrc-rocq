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

Lemma length_nonzero_iff_cons {A} (l : list A) n :
  length l = S n ↔ ∃ x xs, l = x :: xs ∧ length xs = n.
Proof with auto.
  intros. split; intros.
  - destruct l eqn:E; simpl in H; [discriminate|]. exists a, l0...
  - destruct H as (?&?&->&?). simpl. lia.
Qed.





Class OfSameLength {A B} (l1 : list A) (l2 : list B) :=
  of_same_length : length l1 = length l2.

Instance of_same_length_nil {A B} : @OfSameLength A B [] [].
Proof. reflexivity. Defined.

Instance of_same_length_id {A} {l : list A} : OfSameLength l l | 0.
Proof. reflexivity. Qed.

Instance of_same_length_cons {A B} {x1 : A} {x2 : B} {l1 : list A} {l2 : list B}
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

Instance of_same_length_fmap {A A' B B'} {l1 : list A} {l2 : list B} (f1 : A → A') {f2 : B → B'}
  `{OfSameLength A B l1 l2} : OfSameLength (f1 <$> l1) (f2 <$> l2).
Proof. unfold OfSameLength in *. do 2 rewrite length_fmap. assumption. Qed.

Definition of_same_length_rest {A B} {x1 : A} {l1 : list A} {x2 : B} {l2 : list B}
                              (H : OfSameLength (x1::l1) (x2::l2)) : OfSameLength l1 l2.
Proof. unfold OfSameLength in *. simpl in H. lia. Defined.

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
  remember (length ks) as n eqn:E. symmetry in E. generalize dependent xs.
  generalize dependent ks. induction n; intros.
  - simpl. apply length_zero_iff_nil in E. subst. simpl. rewrite lookup_empty.
    rewrite elem_of_nil. split...
  - assert (E1:=E). rewrite of_same_length in E1.
    apply length_nonzero_iff_cons in E as (k'&ks'&->&?).
    apply length_nonzero_iff_cons in E1 as (x'&xs'&->&?). subst. simpl.
    destruct (decide (k' = k)).
    + subst. rewrite lookup_insert. rewrite not_elem_of_cons. naive_solver.
    + rewrite lookup_insert_ne... rewrite not_elem_of_cons. naive_solver.
Qed.

Lemma lookup_list_to_map_zip_Some {K A} `{Countable K}
    (ks : list K) (xs : list A) (k : K) (x : A) `{OfSameLength K A ks xs} :
  (list_to_map (zip ks xs) : gmap K A) !! k = Some x → ∃ i, ks !! i = Some k ∧ xs !! i = Some x.
Proof with auto.
  remember (length ks) as n eqn:E. symmetry in E. generalize dependent xs.
  generalize dependent ks. induction n; intros.
  - simpl. apply length_zero_iff_nil in E. subst. simpl in H1. rewrite lookup_empty in H1.
    discriminate.
  - assert (E1:=E). rewrite of_same_length in E1.
    apply length_nonzero_iff_cons in E as (k'&ks'&->&?).
    apply length_nonzero_iff_cons in E1 as (x'&xs'&->&?). subst. simpl in H1.
    destruct (decide (k' = k)).
    + subst. rewrite lookup_insert in H1. exists 0. simpl. split...
    + forward (IHn ks') by reflexivity. forward (IHn xs').
      { unfold OfSameLength... }
      rewrite lookup_insert_ne in H1... destruct (IHn H1) as (i&?&?).
      exists (S i). simpl. split...
Qed.

(* HACK: These are not currently used. I will keep them as reference.
   I should delete them at some point. *)
(* Section sets. *)
(*   Context `{Set_ A C}. *)
(*   Implicit Types x y : A. *)
(*   Implicit Types X Y : C. *)

(*   Lemma difference_singleton_not_elem_of : forall X x, *)
(*     x ∉ X → *)
(*     X ∖ {[x]} ≡ X. *)
(*   Proof. set_solver. Qed. *)

(*   Section leibniz. *)
(*     Context `{!LeibnizEquiv C}. *)

(*     Lemma difference_singleton_not_elem_of_L : forall X x, *)
(*       x ∉ X → *)
(*       X ∖ {[x]} = X. *)
(*     Proof. set_solver. Qed. *)
(*   End leibniz. *)
(* End sets. *)
