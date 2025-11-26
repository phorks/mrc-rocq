From Equations Require Import Equations.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From stdpp Require Import base list_monad sets gmap.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import SeqNotation.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SyntacticFacts.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.EquivLemmas.
From MRC Require Import PredCalc.NAry.

(* TODO: move them *)
Notation "(¬)ₗ" := FNot (only parsing) : refiney_scope.
Notation "(∧)ₗ" := FAnd (only parsing) : refiney_scope.
Notation "( X ∧.)ₗ" := (FAnd X) (only parsing) : refiney_scope.
Notation "(.∧ X )ₗ" := (λ Y, FAnd X Y) (only parsing) : refiney_scope.
Notation "(∨)ₗ" := FAnd (only parsing) : refiney_scope.
Notation "( X ∨.)ₗ" := (FOr X) (only parsing) : refiney_scope.
Notation "(.∨ X )ₗ" := (λ Y, FOr X Y) (only parsing) : refiney_scope.
Notation "(⇒)ₗ" := FImpl (only parsing) : refiney_scope.
Notation "( X ⇒.)ₗ" := (FImpl X) (only parsing) : refiney_scope.
Notation "(.⇒ X )ₗ" := (λ Y, FImpl X Y) (only parsing) : refiney_scope.
Notation "(⇔)ₗ" := FIff (only parsing) : refiney_scope.
Notation "( X ⇔.)ₗ" := (FIff X) (only parsing) : refiney_scope.
Notation "(.⇔ X )ₗ" := (λ Y, FIff X Y) (only parsing) : refiney_scope.



Instance list_pair_indexed_elem_of {A B} : ElemOf (nat * (A * B)) (list A * list B) :=
  λ p1 p2, p2.1 !! p1.1 = Some p1.2.1 ∧ p2.2 !! p1.1 = Some p1.2.2.

Instance list_pair_elem_of {A} {B} : ElemOf (A * B) (list A * list B) :=
  λ p1 p2, ∃ i, (i, p1) ∈ p2.

Lemma elem_of_list_pair {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∈ (xs, ys) ↔ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. reflexivity. Qed.

Lemma not_elem_of_list_pair_inv {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (x, y) ∉ (xs, ys) → ¬ ∃ i, xs !! i = Some x ∧ ys !! i = Some y.
Proof. rewrite elem_of_list_pair. auto. Qed.

Lemma not_elem_of_list_pair {A B} (x : A) (y : B) (xs : list A) (ys : list B) :
  (∀ i, xs !! i ≠ Some x ∨ ys !! i ≠ Some y) → (x, y) ∉ (xs, ys).
Proof.
  intros. intros contra. apply elem_of_list_pair in contra as (i&?&?).
  destruct (H i) as []; contradiction.
Qed.

Lemma elem_of_list_pair_indexed {A B} (i : nat) (x : A) (y : B) (xs : list A) (ys : list B) :
  (i, (x, y)) ∈ (xs, ys) ↔ xs !! i = Some x ∧ ys !! i = Some y.
Proof. reflexivity. Qed.

Lemma elem_of_zip_with_same_length {A B C} (c : C) (xs : list A) (ys : list B) (f : A → B → C)
    `{OfSameLength _ _ xs ys} :
  c ∈ zip_with f xs ys ↔ ∃ i x y, xs !! i = Some x ∧ ys !! i = Some y ∧ c = f x y.
Proof with auto.
  split; intros.
  - generalize dependent ys. induction xs as [| x xs IH]; simpl; intros.
    + apply of_same_length_nil_inv_l in H as ->. apply elem_of_nil in H0 as [].
    + assert (Hl:=H). apply of_same_length_cons_inv_l in H as (y&ys'&->&?).
      rename ys' into ys. apply of_same_length_rest in Hl. apply elem_of_cons in H0 as [].
      * exists 0, x, y. split_and!...
      * apply (IH _ Hl) in H0 as (i&x'&y'&?&?&?). exists (S i), x', y'. simpl.
        split_and!...
  - destruct H0 as (i&x&y&?&?&?). apply elem_of_list_split_length in H0 as (xs0&xs1&->&?).
    apply elem_of_list_split_length in H1 as (ys0&ys1&->&?). subst i. rewrite zip_with_app...
    apply elem_of_app. right. simpl. apply elem_of_cons. left...
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

Lemma elem_of_list_pair_indexed_hd {A B} x0 y0 x y (xs : list A) (ys : list B) :
  (0, (x0, y0)) ∈ (x :: xs, y :: ys) ↔ (x0 = x ∧ y0 = y).
Proof. rewrite elem_of_list_pair_indexed. simpl. split; naive_solver. Qed.

Lemma elem_of_list_pair_indexed_tl {A B} i x0 y0 x y (xs : list A) (ys : list B) :
  (S i, (x0, y0)) ∈ (x :: xs, y :: ys) ↔ (i, (x0, y0)) ∈ (xs, ys).
Proof.
  do 2 rewrite elem_of_list_pair_indexed. simpl. naive_solver.
Qed.

Section n_ary_lemmas.
  Context {M : model}.

  Local Notation value := (value M).
  Local Notation term := (term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A B : formula.
  Implicit Types xs : list variable.
  Implicit Types ts : list term.
  Implicit Types Bs Cs Ds : list formula.
  Implicit Types vs : list value.

  Lemma f_eqlist_nil :
    <! ⌜[] =* []⌝ !> ≡@{formula} <! true !>.
  Proof. unfold FEqList. reflexivity. Qed.

  Lemma f_eqlist_cons t1 t2 ts1 ts2
    {H1 : OfSameLength ts1 ts2}
    {H2 : OfSameLength (t1 :: ts1) (t2 :: ts2)} :
    <! ⌜$(t1 :: ts1) =* $(t2 :: ts2)⌝ !> ≡ <! ⌜t1 = t2⌝ ∧ ⌜ts1 =* ts2⌝ !>.
  Proof. unfold FEqList. simpl. reflexivity. Qed.

  Lemma f_andlist_elim_andlist' Bs' Bs :
    Bs' ⊆+ Bs →
    <! ∧* Bs !> ⇛ <! ∧* Bs' !>.
  Proof.
    intros. intros σ Hand. rewrite simpl_feval_andlist. intros.
    rewrite simpl_feval_andlist in Hand. apply Hand. eapply elem_of_submseteq.
    - apply H0.
    - apply H.
  Qed.

  Lemma f_orlist_elim_andlist' Bs' Bs :
    Bs' ⊆+ Bs →
    <! ∨* Bs' !> ⇛ <! ∨* Bs !>.
  Proof with auto.
    intros. intros σ Hor. rewrite simpl_feval_orlist.
    apply simpl_feval_orlist in Hor as (B&?&?). exists B. split...
    eapply elem_of_submseteq.
    - apply H0.
    - apply H.
  Qed.

  Lemma f_andlist_elim' B Bs :
    B ∈ Bs →
    <! ∧* Bs !> ⇛ B.
  Proof with auto.
    intros. intros σ Hand. rewrite simpl_feval_andlist in Hand. apply Hand...
  Qed.

  Lemma f_orlist_intro' B Bs :
    B ∈ Bs →
    B ⇛ <! ∨* Bs !>.
  Proof with auto.
    intros. intros σ HB. apply simpl_feval_orlist. exists B. split...
  Qed.

  Lemma f_andlist_elim B Bs B' :
    B ⇛ B' →
    B ∈ Bs →
    <! ∧* Bs !> ⇛ B'.
  Proof with auto.
    intros. trans B.
    - apply f_andlist_elim'...
    - rewrite H. reflexivity.
  Qed.

  Lemma f_orlist_intro B Bs B' :
    B' ⇛ B →
    B ∈ Bs →
    B' ⇛ <! ∨* Bs !>.
  Proof with auto.
    intros. trans B.
    - rewrite H. reflexivity.
    - apply f_orlist_intro'...
  Qed.

  (* TODO: move these *)
  Lemma f_and_elim_l A B :
    <! A ∧ B !> ⇛ A.
  Proof with auto. intros σ. simp feval. intros [? _]... Qed.

  Lemma f_and_elim_r A B :
    <! A ∧ B !> ⇛ B.
  Proof with auto. intros σ. simp feval. intros [_ ?]... Qed.

  Lemma f_or_intro_l A B :
    A ⇛ <! A ∨ B !>.
  Proof with auto. intros σ. simp feval. intros... Qed.

  Lemma f_or_intro_r A B :
    B ⇛ <! A ∨ B !>.
  Proof with auto. intros σ. simp feval. intros... Qed.

  Lemma f_and_andlist_distr_l A Bs :
    length Bs ≠ 0 →
    <! A ∧ (∧* Bs) !> ≡ <! ∧* $((A∧.)ₗ <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - intros. contradiction.
    - intros. rewrite <- f_and_assoc. destruct (decide (length Bs = 0)).
      + apply length_zero_iff_nil in e. subst. simpl...
      + rewrite f_and_assoc. rewrite <- (f_and_redundant_r (<! A ∧ B !>) A).
        2: { apply f_and_elim_l. }
        rewrite <- f_and_assoc. rewrite IH... rewrite f_and_assoc. f_equiv.
        reflexivity.
  Qed.

  Lemma f_and_andlist_distr_r A Bs :
    length Bs ≠ 0 →
    <! (∧* Bs) ∧ A !> ≡ <! ∧* $((.∧A)ₗ <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - intros. contradiction.
    - intros. rewrite <- f_and_assoc. destruct (decide (length Bs = 0)).
      + apply length_zero_iff_nil in e. subst. simpl. rewrite (f_and_comm _ A).
        repeat rewrite f_and_true. apply f_and_comm.
      + rewrite (f_and_comm _ A). rewrite f_and_assoc.
        rewrite <- (f_and_redundant_r (<! B ∧ A !>) A).
        2: { apply f_and_elim_r. }
        rewrite <- f_and_assoc. rewrite (f_and_comm A). rewrite IH...
        f_equiv.
        * apply f_and_comm.
        * reflexivity.
  Qed.

  Lemma f_or_orlist_distr_l A Bs :
    length Bs ≠ 0 →
    <! A ∨ (∨* Bs) !> ≡ <! ∨* $((A∨.)ₗ <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - intros. contradiction.
    - intros. rewrite <- f_or_assoc. destruct (decide (length Bs = 0)).
      + apply length_zero_iff_nil in e. subst. simpl...
      + rewrite f_or_assoc. rewrite <- (f_or_redundant_r (<! A ∨ B !>) A).
        2: { apply f_or_intro_l. }
        rewrite <- f_or_assoc. rewrite IH... rewrite f_or_assoc. f_equiv.
        reflexivity.
  Qed.

  Lemma f_or_orlist_distr_r A Bs :
    length Bs ≠ 0 →
    <! (∨* Bs) ∨ A !> ≡ <! ∨* $((.∨A)ₗ <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - intros. contradiction.
    - intros. rewrite <- f_or_assoc. destruct (decide (length Bs = 0)).
      + apply length_zero_iff_nil in e. subst. simpl. rewrite (f_or_comm _ A).
        repeat rewrite f_or_false. apply f_or_comm.
      + rewrite (f_or_comm _ A). rewrite f_or_assoc.
        rewrite <- (f_or_redundant_r (<! B ∨ A !>) A).
        2: { apply f_or_intro_r. }
        rewrite <- f_or_assoc. rewrite (f_or_comm A). rewrite IH...
        f_equiv.
        * apply f_or_comm.
        * reflexivity.
  Qed.

  Lemma f_and_andlist_comm A Bs :
    <! A ∧ ∧* Bs !> ≡ <! (∧* Bs) ∧ A !>.
  Proof with auto.
    intros. destruct Bs as [| B Bs].
    - simpl. rewrite f_and_comm...
    - simpl. rewrite f_and_comm. reflexivity.
  Qed.

  Lemma f_or_orlist_comm A Bs :
    <! A ∨ ∨* Bs !> ≡ <! (∨* Bs) ∨ A !>.
  Proof with auto.
    intros. destruct Bs as [| B Bs].
    - simpl. rewrite f_or_comm...
    - simpl. rewrite f_or_comm. reflexivity.
  Qed.

  Lemma f_andlist_app Bs Cs :
    <! ∧* $(Bs ++ Cs) !> ≡ <! (∧* Bs) ∧ (∧* Cs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; intros.
    - simpl. rewrite f_and_comm. rewrite f_and_true...
    - simpl. rewrite IH. rewrite f_and_assoc...
  Qed.

  Lemma f_orlist_app Bs Cs :
    <! ∨* $(Bs ++ Cs) !> ≡ <! (∨* Bs) ∨ (∨* Cs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; intros.
    - simpl. rewrite f_or_comm. rewrite f_or_false...
    - simpl. rewrite IH. rewrite f_or_assoc...
  Qed.

  Lemma f_andlist_comm Bs Bs' :
    Bs ≡ₚ Bs' →
    <! ∧* Bs !> ≡ <! ∧* Bs' !>.
  Proof with auto.
    intros. generalize dependent Bs'. induction Bs as [|B Bs IH]; intros.
    - apply Permutation_nil_l in H. subst...
    - apply Permutation_cons_inv_l in H as (Bs'0&Bs'1&?&?). simpl. subst Bs'.
      rewrite f_andlist_app. simpl. rewrite f_and_assoc. rewrite (f_and_comm _ B).
      rewrite <- f_and_assoc. rewrite <- f_andlist_app. rewrite IH.
      + reflexivity.
      + assumption.
  Qed.

  Lemma f_orlist_comm Bs Bs' :
    Bs ≡ₚ Bs' →
    <! ∨* Bs !> ≡ <! ∨* Bs' !>.
  Proof with auto.
    intros. generalize dependent Bs'. induction Bs as [|B Bs IH]; intros.
    - apply Permutation_nil_l in H. subst...
    - apply Permutation_cons_inv_l in H as (Bs'0&Bs'1&?&?). simpl. subst Bs'.
      rewrite f_orlist_app. simpl. rewrite f_or_assoc. rewrite (f_or_comm _ B).
      rewrite <- f_or_assoc. rewrite <- f_orlist_app. rewrite IH.
      + reflexivity.
      + assumption.
  Qed.

  (* HACK: it might more sense to make formula_list_equiv also respect permutations *)
  Lemma f_andlist_equiv_comm Bs Bs' Cs :
    formula_list_equiv Bs Bs' →
    Bs ≡ₚ Cs →
    <! ∧* Cs !> ≡ <! ∧* Bs' !>.
  Proof with auto.
    intros. rewrite (f_andlist_comm Cs Bs).
    - rewrite H...
    - symmetry. assumption.
  Qed.

  Lemma f_orlist_equiv_comm Bs Bs' Cs :
    formula_list_equiv Bs Bs' →
    Bs ≡ₚ Cs →
    <! ∨* Cs !> ≡ <! ∨* Bs' !>.
  Proof with auto.
    intros. rewrite (f_orlist_comm Cs Bs).
    - rewrite H...
    - symmetry. assumption.
  Qed.

  (** Dup lemmas for n-ary and/or, corresponding to idemp lemmas of normal and/or **)
  Lemma f_andlist_dup_keep_l Bs0 B1 Bs2 B2 Bs3 :
    B1 ≡ B2 →
    <! ∧* $(Bs0 ++ [B1] ++ Bs2 ++ [B2] ++ Bs3) !> ≡ <! ∧* $(Bs0 ++ [B1] ++ Bs2 ++ Bs3) !>.
  Proof with auto.
    intros. repeat rewrite f_andlist_app. simpl. repeat rewrite f_and_true.
    rewrite f_and_assoc. rewrite (f_and_comm _ B1). rewrite (f_and_assoc <! ∧* Bs2!> _).
    rewrite (f_and_comm _ B2). rewrite <- f_and_assoc. do 2 rewrite (f_and_assoc <! ∧* Bs0 !>).
    rewrite (f_and_comm _ B2). rewrite (f_and_assoc <! ∧* Bs0 !>). rewrite (f_and_comm _ B1).
    repeat rewrite <- f_and_assoc. rewrite f_and_assoc. rewrite <- H. rewrite f_and_idemp...
  Qed.

  Lemma f_andlist_dup_keep_r Bs0 B1 Bs2 B2 Bs3 :
    B1 ≡ B2 →
    <! ∧* $(Bs0 ++ [B1] ++ Bs2 ++ [B2] ++ Bs3) !> ≡ <! ∧* $(Bs0 ++ Bs2 ++ [B2] ++ Bs3) !>.
  Proof with auto.
    intros. repeat rewrite f_andlist_app. simpl. repeat rewrite f_and_true.
    rewrite f_and_assoc. rewrite (f_and_comm _ B1). rewrite (f_and_assoc <! ∧* Bs2!> _).
    rewrite (f_and_comm _ B2). rewrite <- f_and_assoc. do 2 rewrite (f_and_assoc <! ∧* Bs0 !>).
    rewrite (f_and_comm _ B2). repeat rewrite <- f_and_assoc. rewrite f_and_assoc.
    rewrite H. rewrite f_and_idemp...
  Qed.

  Lemma f_andlist_dup_head B1 B2 Bs :
    B1 ≡ B2 →
    <! ∧* $(B1 :: B2 :: Bs) !> ≡ <! ∧* $(B2 :: Bs) !>.
  Proof with auto.
    intros. replace (B1 :: B2 :: Bs) with ([] ++ [B1] ++ [] ++ [B2] ++ Bs) by reflexivity.
    rewrite (f_andlist_dup_keep_r [] B1 [] B2 Bs)...
  Qed.

  Lemma f_andlist_dup_tail B1 B2 Bs :
    B1 ≡ B2 →
    <! ∧* $(Bs ++ [B1] ++ [B2]) !> ≡ <! ∧* $(Bs ++ [B2]) !>.
  Proof with auto.
    intros. replace (Bs ++ [B1] ++ [B2]) with (Bs ++ [B1] ++ [] ++ [B2] ++ []) by reflexivity.
    rewrite (f_andlist_dup_keep_r Bs B1 [] B2 [])...
  Qed.

  Lemma f_orlist_dup_keep_l Bs0 B1 Bs2 B2 Bs3 :
    B1 ≡ B2 →
    <! ∨* $(Bs0 ++ [B1] ++ Bs2 ++ [B2] ++ Bs3) !> ≡ <! ∨* $(Bs0 ++ [B1] ++ Bs2 ++ Bs3) !>.
  Proof with auto.
    intros. repeat rewrite f_orlist_app. simpl. repeat rewrite f_or_false.
    rewrite f_or_assoc. rewrite (f_or_comm _ B1). rewrite (f_or_assoc <! ∨* Bs2!> _).
    rewrite (f_or_comm _ B2). rewrite <- f_or_assoc. do 2 rewrite (f_or_assoc <! ∨* Bs0 !>).
    rewrite (f_or_comm _ B2). rewrite (f_or_assoc <! ∨* Bs0 !>). rewrite (f_or_comm _ B1).
    repeat rewrite <- f_or_assoc. rewrite f_or_assoc. rewrite <- H. rewrite f_or_idemp...
  Qed.

  Lemma f_orlist_dup_keep_r Bs0 B1 Bs2 B2 Bs3 :
    B1 ≡ B2 →
    <! ∨* $(Bs0 ++ [B1] ++ Bs2 ++ [B2] ++ Bs3) !> ≡ <! ∨* $(Bs0 ++ Bs2 ++ [B2] ++ Bs3) !>.
  Proof with auto.
    intros. repeat rewrite f_orlist_app. simpl. repeat rewrite f_or_false.
    rewrite f_or_assoc. rewrite (f_or_comm _ B1). rewrite (f_or_assoc <! ∨* Bs2!> _).
    rewrite (f_or_comm _ B2). rewrite <- f_or_assoc. do 2 rewrite (f_or_assoc <! ∨* Bs0 !>).
    rewrite (f_or_comm _ B2). repeat rewrite <- f_or_assoc. rewrite f_or_assoc.
    rewrite H. rewrite f_or_idemp...
  Qed.

  Lemma f_orlist_dup_head B1 B2 Bs :
    B1 ≡ B2 →
    <! ∨* $(B1 :: B2 :: Bs) !> ≡ <! ∨* $(B2 :: Bs) !>.
  Proof with auto.
    intros. replace (B1 :: B2 :: Bs) with ([] ++ [B1] ++ [] ++ [B2] ++ Bs) by reflexivity.
    rewrite (f_orlist_dup_keep_r [] B1 [] B2 Bs)...
  Qed.

  Lemma f_orlist_dup_tail B1 B2 Bs :
    B1 ≡ B2 →
    <! ∨* $(Bs ++ [B1] ++ [B2]) !> ≡ <! ∨* $(Bs ++ [B2]) !>.
  Proof with auto.
    intros. replace (Bs ++ [B1] ++ [B2]) with (Bs ++ [B1] ++ [] ++ [B2] ++ []) by reflexivity.
    rewrite (f_orlist_dup_keep_r Bs B1 [] B2 [])...
  Qed.

  Lemma f_and_andlist_redundant_l B Bs B' :
    B ⇛ B' →
    B ∈ Bs →
    <! B' ∧ (∧* Bs) !> ≡ <! ∧* Bs !>.
  Proof with auto.
    intros. apply f_and_redundant_l. apply f_andlist_elim with (B:=B)...
  Qed.

  Lemma f_and_andlist_redundant_r B Bs B' :
    B ⇛ B' →
    B ∈ Bs →
    <! (∧* Bs) ∧ B' !> ≡ <! ∧* Bs !>.
  Proof with auto.
    intros. apply f_and_redundant_r. apply f_andlist_elim with (B:=B)...
  Qed.

  Lemma f_and_andlist_redundant_l' B Bs :
    B ∈ Bs →
    <! B ∧ (∧* Bs) !> ≡ <! ∧* Bs !>.
  Proof with auto.
    intros. apply f_and_andlist_redundant_l with (B:=B)... reflexivity.
  Qed.

  Lemma f_and_andlist_redundant_r' B Bs :
    B ∈ Bs →
    <! (∧* Bs) ∧ B !> ≡ <! ∧* Bs !>.
  Proof with auto.
    intros. apply f_and_andlist_redundant_r with (B:=B)... reflexivity.
  Qed.

  Lemma f_or_orlist_redundant_l B Bs B' :
    B' ⇛ B →
    B ∈ Bs →
    <! B' ∨ (∨* Bs) !> ≡ <! ∨* Bs !>.
  Proof with auto.
    intros. apply f_or_redundant_l. apply f_orlist_intro with (B:=B)...
  Qed.

  Lemma f_or_orlist_redundant_r B Bs B' :
    B' ⇛ B →
    B ∈ Bs →
    <! (∨* Bs) ∨ B' !> ≡ <! ∨* Bs !>.
  Proof with auto.
    intros. apply f_or_redundant_r. apply f_orlist_intro with (B:=B)...
  Qed.

  Lemma f_or_orlist_redundant_l' B Bs :
    B ∈ Bs →
    <! B ∨ (∨* Bs) !> ≡ <! ∨* Bs !>.
  Proof with auto.
    intros. apply f_or_orlist_redundant_l with (B:=B)... reflexivity.
  Qed.

  Lemma f_or_orlist_redundant_r' B Bs :
    B ∈ Bs →
    <! (∨* Bs) ∨ B !> ≡ <! ∨* Bs !>.
  Proof with auto.
    intros. apply f_or_orlist_redundant_r with (B:=B)... reflexivity.
  Qed.

  (* FEq comm *)

  Lemma f_eqlist_redundant_l t1 t2 ts1 ts2 `{OfSameLength _ _ ts1 ts2} :
    (t1, t2) ∈ (ts1, ts2) →
    <! ⌜t1 = t2⌝ ∧ ⌜ts1 =* ts2⌝ !> ≡ <! ⌜ts1 =* ts2⌝ !>.
  Proof with auto.
    intros. apply elem_of_list_pair in H0 as (i&?&?). unfold FEqList.
    rewrite f_and_andlist_redundant_l'... apply elem_of_zip_with_same_length...
    exists i, t1, t2. split_and!...
  Qed.

  Lemma f_eqlist_redundant_r t1 t2 ts1 ts2 `{OfSameLength _ _ ts1 ts2} :
    (t1, t2) ∈ (ts1, ts2) →
    <! ⌜ts1 =* ts2⌝ ∧  ⌜t1 = t2⌝ !> ≡ <! ⌜ts1 =* ts2⌝ !>.
  Proof with auto.
    intros. apply elem_of_list_pair in H0 as (i&?&?). unfold FEqList.
    rewrite f_and_andlist_redundant_r'... apply elem_of_zip_with_same_length...
    exists i, t1, t2. split_and!...
  Qed.

  Lemma f_and_andlist_andlist Bs Cs `{OfSameLength _ _ Bs Cs} :
    <! (∧* Bs) ∧ (∧* Cs) !> ≡ <! ∧* $(zip_with FAnd Bs Cs) !>.
  Proof with auto.
    generalize dependent Cs. induction Bs as [|B Bs IH]; intros.
    - apply of_same_length_nil_inv_l in H. subst. simpl. rewrite f_and_idemp...
    - apply of_same_length_cons_inv_l in H as (C&Cs'&->&?). rename Cs' into Cs.
      simpl. rewrite f_and_assoc at 1. rewrite (f_and_comm _ C). rewrite (f_and_assoc C).
      rewrite (f_and_comm C). repeat rewrite <- f_and_assoc. do 2 f_equiv.
      apply IH. unfold OfSameLength...
  Qed.

  Lemma f_or_orlist_andlist Bs Cs `{OfSameLength _ _ Bs Cs} :
    <! (∨* Bs) ∨ (∨* Cs) !> ≡ <! ∨* $(zip_with FOr Bs Cs) !>.
  Proof with auto.
    generalize dependent Cs. induction Bs as [|B Bs IH]; intros.
    - apply of_same_length_nil_inv_l in H. subst. simpl. rewrite f_or_idemp...
    - apply of_same_length_cons_inv_l in H as (C&Cs'&->&?). rename Cs' into Cs.
      simpl. rewrite f_or_assoc at 1. rewrite (f_or_comm _ C). rewrite (f_or_assoc C).
      rewrite (f_or_comm C). repeat rewrite <- f_or_assoc. do 2 f_equiv.
      apply IH. unfold OfSameLength...
  Qed.


  (* TODO: [f_and_or_absorb] and the rest of equiv lemmas are not ported  *)

  Lemma f_andlist_or_absorb A Bs :
    <! A ∧ ∧* $(FOr A <$> Bs) !> ≡ A.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - apply f_and_true.
    - rewrite f_and_assoc. rewrite f_and_or_absorb. rewrite IH...
  Qed.

  Lemma f_orlist_and_absorb A Bs :
    <! A ∨ ∨* $(FAnd A <$> Bs) !> ≡ A.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - apply f_or_false.
    - rewrite f_or_assoc. rewrite f_or_and_absorb. rewrite IH...
  Qed.

  Lemma f_or_andlist_distr A Bs :
    <! A ∨ (∧* Bs) !> ≡ <! ∧* $(FOr A <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - apply f_or_true.
    - rewrite f_or_and_distr. rewrite IH. f_equiv...
  Qed.

  Lemma f_and_orlist_distr A Bs :
    <! A ∧ (∨* Bs) !> ≡ <! ∨* $(FAnd A <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - apply f_and_false.
    - rewrite f_and_or_distr. rewrite IH. f_equiv...
  Qed.


  Lemma f_not_andlist Bs :
    <! ¬ (∧* Bs) !> ≡ <! ∨* $(FNot <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - apply f_not_true.
    - rewrite f_not_and. f_equiv...
  Qed.

  Lemma f_not_orlist Bs :
    <! ¬ (∨* Bs) !> ≡ <! ∧* $(FNot <$> Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl.
    - apply f_not_false.
    - rewrite f_not_or. f_equiv...
  Qed.

  Lemma f_or_andlist_absorb' A Bs :
    <! A ∨ (∧* $(FAnd (FNot A) <$> Bs)) !> ≡ <! A ∨ (∧* Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl...
    rewrite f_or_and_distr. rewrite f_or_and_absorb'.
    rewrite IH. rewrite f_or_and_distr. f_equiv...
  Qed.

  Lemma f_and_orlist_absorb' A Bs :
    <! A ∧ (∨* $(FOr (FNot A) <$> Bs)) !> ≡ <! A ∧ (∨* Bs) !>.
  Proof with auto.
    induction Bs as [|B Bs IH]; simpl...
    rewrite f_and_or_distr. rewrite f_and_or_absorb'.
    rewrite IH. rewrite f_and_or_distr. f_equiv...
  Qed.

  (* A.33 *)
  (* Lemma f_impl_and_r A B C : *)
  (*     <! C ⇒ (A ∧ B) !> ≡ <! (C ⇒ A) ∧ (C ⇒ B) !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.34 *)
  (* Lemma f_impl_or_l A B C : *)
  (*   <! (A ∨ B) ⇒ C !> ≡ <! (A ⇒ C) ∧ (B ⇒ C) !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.35 *)
  (* Lemma f_impl_or_r A B C : *)
  (*   <! C ⇒ (A ∨ B) !> ≡ <! (C ⇒ A) ∨ (C ⇒ B) !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.36 *)
  (* Lemma f_impl_and_l A B C : *)
  (*   <! (A ∧ B) ⇒ C !> ≡ <! (A ⇒ C) ∨ (B ⇒ C) !>. *)
  (* Proof with auto. *)
  (*   unfold FImpl. intros σ. simp feval. split; [| naive_solver]. *)
  (*   intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec. *)
  (* Qed. *)

  (* A.37 *)
  (* Lemma f_impl_curry A B C : *)
  (*   <! A ⇒ (B ⇒ C) !> ≡ <! (A ∧ B) ⇒ C !>. *)
  (* Proof with auto. *)
  (*   unfold FImpl. intros σ. simp feval. split; [naive_solver |]. *)
  (*   intros [|]... apply Decidable.not_and in H as [|]... apply feval_dec. *)
  (* Qed. *)

  (* A.38 *)
  (* Lemma f_cases_as_or A B C : *)
  (*   <! (A ⇒ B) ∧ (¬A ⇒ C) !> ≡ <! (A ∧ B) ∨ (¬A ∧ C) !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.39 *)
  (* Lemma f_iff_as_and A B C : *)
  (*   <! A ⇔ B !> ≡ <! (A ⇒ B) ∧ (B ⇒ A) !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.40 *)
  (* Lemma f_iff_as_or A B : *)
  (*   <! A ⇔ B !> ≡ <! (A ∧ B) ∨ ¬(A ∨ B) !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.41 *)
  (* Lemma f_iff_negate A B : *)
  (*   <! A ⇔ B !> ≡ <! ¬A ⇔ ¬B !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.42 *)
  (* Lemma f_iff_self A : *)
  (*   <! A ⇔ A !> ≡ <! true !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.43 *)
  (* Lemma f_iff_not_self A : *)
  (*   <! A ⇔ ¬ A !> ≡ <! false !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.44 *)
  (* Lemma f_iff_true A : *)
  (*   <! A ⇔ true !> ≡ <! A !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.45 *)
  (* Lemma f_iff_false A : *)
  (*   <! A ⇔ false !> ≡ <! ¬ A !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.46 *)
  (* Lemma f_iff_and_absorb A B : *)
  (*   <! A ⇔ (A ∧ B) !> ≡ <! A ⇒ B !>. *)
  (* Proof. prove_equiv. Qed. *)

  (* A.47 *)
  (* Lemma f_iff_or_absorb A B : *)
  (*   <! A ⇔ (A ∨ B) !> ≡ <! B ⇒ A !>. *)
  (* Proof with auto. *)
  (*   intros σ. unfold FIff, FImpl. simp feval. split. *)
  (*   - intros []. destruct_or! H; naive_solver. *)
  (*   - intros [|]; [|naive_solver]. split. *)
  (*     + pose proof (feval_lem σ A). destruct H0 as [|]... *)
  (*     + pose proof (feval_lem σ A) as [|]; naive_solver. *)
  (* Qed. *)

  (* A.48 *)
  (* Lemma f_or_iff A B C : *)
  (*   <! A ∨ (B ⇔ C) !> ≡ <! (A ∨ B) ⇔ (A ∨ C) !>. *)
  (* Proof with auto. *)
  (*   intros σ. unfold FIff, FImpl. simp feval. split; [|naive_solver]. *)
  (*   intros [|[]]; [naive_solver|]. split; destruct (feval_lem σ A); naive_solver. *)
  (* Qed. *)

  (* A.61 *)
  Lemma f_not_foralllist xs A :
    <! ¬ ∀* xs, A !> ≡ <! ∃* xs, ¬ A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl... rewrite f_not_forall. rewrite IH...
  Qed.

  (* A.62 *)
  Lemma f_not_existslist xs A :
    <! ¬ ∃* xs, A !> ≡ <! ∀* xs, ¬ A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl... rewrite f_not_exists. rewrite IH...
  Qed.

  Lemma f_foralllist_as_existslist xs A :
    <! ∀* xs, A !> ≡ <! ¬ ∃* xs, ¬ A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl...
    - rewrite f_not_stable...
    - intros σ. unfold FForall. rewrite IH... rewrite f_not_stable...
  Qed.

  (* A.76 *)
  Lemma f_existslist_and_unused_l xs A B :
    list_to_set xs ∩ formula_fvars A = ∅ →
    <! ∃* xs, A ∧ B !> ≡ <! A ∧ (∃* xs, B) !>.
  Proof with auto.
    intros. induction xs as [|x xs IH]... simpl. rewrite IH; [rewrite f_exists_and_unused_l|];
      set_solver.
  Qed.

  (* A.78 *)
  Lemma f_foralllist_impl_unused_l xs A B :
    list_to_set xs ∩ formula_fvars A = ∅ →
    <! ∀* xs, A ⇒ B !> ≡ <! A ⇒ (∀* xs, B) !>.
  Proof with auto.
    intros. induction xs as [|x xs IH]... simpl. rewrite IH; [rewrite f_forall_impl_unused_l|];
      set_solver.
  Qed.

  (* TODO: Move these somewhere *)
  Definition seqsubst_lists_unique xs ts :=
    ∀ i j x t1 t2, i ≠ j → (i, (x, t1)) ∈ (xs, ts) → (j, (x, t2)) ∈ (xs, ts) → t1 = t2.

  Lemma NoDup_seqsubst_lists_unique xs ts :
    NoDup xs →
    seqsubst_lists_unique xs ts.
  Proof with auto.
    intros H i j ? ? ? ? ? ?. exfalso. apply H0. rewrite elem_of_list_pair_indexed in H1.
    rewrite elem_of_list_pair_indexed in H2. destruct H1 as [? _]. destruct H2 as [? _].
    eapply NoDup_lookup with (l:=xs) (x:=x)...
  Qed.

  Lemma seqsubst_lists_unique_cons_inv x t xs ts :
    seqsubst_lists_unique (x :: xs) (t :: ts) → seqsubst_lists_unique xs ts.
  Proof with auto.
    intros. intros i j x0 t1 t2 ? ? ?. unfold seqsubst_lists_unique in H.
    apply (H (S i) (S j) x0); [lia| |]; apply elem_of_list_pair_indexed_tl...
  Qed.

  (* Lemma fequiv_subst_non_free A x t : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! A[x \ t] !> ≡ A. *)
  (* Proof with auto. *)
  (*   apply subst_formula_ind with (P:=λ A B, x ∉ formula_fvars B → A ≡ B); intros. *)
  (*   - rewrite subst_af_non_free... *)
  (*   - f_equiv... *)
  (*   - simpl in H1. apply not_elem_of_union in H1 as [? ?]. *)
  (*     f_equiv; [apply H|apply H0]... *)
  (*   - simpl in H1. apply not_elem_of_union in H1 as [? ?]. *)
  (*     f_equiv; [apply H|apply H0]... *)
  (*   - reflexivity. *)
  (*   - simpl in H2. apply not_elem_of_difference in H2. rewrite elem_of_singleton in H2. *)
  (*     destruct H2; subst; contradiction. *)
  (* Qed. *)

  (* A.64 *)
  Lemma f_exists_existslist_comm x xs A :
    <! ∃ x, ∃* xs, A !> ≡ <! ∃* xs, ∃ x, A !>.
  Proof with auto.
    induction xs as [|x' xs IH]; simpl... rewrite f_exists_comm. rewrite IH...
  Qed.

  (* A.64 *)
  Lemma f_existslist_comm xs1 xs2 A :
    <! ∃* xs1, ∃* xs2, A !> ≡ <! ∃* xs2, ∃* xs1, A !>.
  Proof with auto.
    induction xs1 as [|x1 xs1 IH]; simpl... rewrite IH. rewrite f_exists_existslist_comm...
  Qed.

  (* A.63 *)
  Lemma f_forall_foralllist_comm x xs A :
    <! ∀ x, ∀* xs, A !> ≡ <! ∀* xs, ∀ x, A !>.
  Proof with auto.
    induction xs as [|x' xs IH]; simpl... rewrite f_forall_comm. rewrite IH...
  Qed.

  (* A.63 *)
  Lemma f_foralllist_comm xs1 xs2 A :
    <! ∀* xs1, ∀* xs2, A !> ≡ <! ∀* xs2, ∀* xs1, A !>.
  Proof with auto.
    induction xs1 as [|x1 xs1 IH]; simpl... rewrite IH. rewrite f_forall_foralllist_comm...
  Qed.

  (* A.60 *)
  Lemma f_exists_existslist_idemp x xs A :
    x ∈ xs →
    <! ∃ x, ∃* xs, A !> ≡ <! ∃* xs, A !>.
  Proof with auto.
    intros. induction xs as [|x' xs IH].
    - apply elem_of_nil in H as [].
    - simpl. set_unfold. destruct H.
      + subst. rewrite f_exists_idemp...
      + rewrite f_exists_comm. rewrite IH...
  Qed.

  (* A.60 *)
  Lemma f_existslist_exists_idemp x xs A :
    x ∈ xs →
    <! ∃* xs, ∃ x, A !> ≡ <! ∃* xs, A !>.
  Proof with auto.
    rewrite <- f_exists_existslist_comm. apply f_exists_existslist_idemp.
  Qed.

  (* A.60 *)
  Lemma f_existslist_idemp xs A :
    <! ∃* xs, ∃* xs, A !> ≡ <! ∃* xs, A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl... rewrite f_exists_existslist_comm.
    rewrite f_exists_idemp. rewrite <- f_exists_existslist_comm. rewrite IH...
  Qed.

  (* A.60 *)
  Lemma f_forall_foralllist_idemp x xs A :
    x ∈ xs →
    <! ∀ x, ∀* xs, A !> ≡ <! ∀* xs, A !>.
  Proof with auto.
    intros. induction xs as [|x' xs IH].
    - apply elem_of_nil in H as [].
    - simpl. set_unfold. destruct H.
      + subst. rewrite f_forall_idemp...
      + rewrite f_forall_comm. rewrite IH...
  Qed.

  (* A.60 *)
  Lemma f_foralllist_forall_idemp x xs A :
    x ∈ xs →
    <! ∀* xs, ∀ x, A !> ≡ <! ∀* xs, A !>.
  Proof with auto.
    rewrite <- f_forall_foralllist_comm. apply f_forall_foralllist_idemp.
  Qed.

  (* A.60 *)
  Lemma f_foralllist_idemp xs A :
    <! ∀* xs, ∀* xs, A !> ≡ <! ∀* xs, A !>.
  Proof with auto.
    induction xs as [|x xs IH]; simpl... rewrite f_forall_foralllist_comm.
    rewrite f_forall_idemp. rewrite <- f_forall_foralllist_comm. rewrite IH...
  Qed.

  (* A.56 *)
  Lemma f_existslist_one_point xs ts A `{OfSameLength _ _ xs ts} :
    seqsubst_lists_unique xs ts →
    (list_to_set xs) ∩ ⋃ (term_fvars <$> ts) = ∅ →
    <! ∃* xs, ⌜@*xs =* ts⌝ ∧ A !> ≡ <! A[; *xs \ *ts ;] !>.
  Proof with auto.
    intros Hunique Hfree. generalize dependent ts.
    induction xs as [|x xs IH]; simpl in *; intros.
    - inversion H. assert (H':=H). apply of_same_length_nil_inv_l in H' as ->.
      simpl. unfold FEqList. simpl. rewrite f_and_comm. apply f_and_true.
    - inversion H. assert (H':=H). apply of_same_length_cons_inv_l in H' as (t&ts'&?&?).
      subst ts. rename ts' into ts. simpl. rewrite f_eqlist_cons.
      apply seqsubst_lists_unique_cons_inv in Hunique as Hunique'.
      destruct (decide (x ∈ xs)).
      + assert (e':=e). apply elem_of_list_lookup_1 in e' as [i Hi].
        rewrite f_eqlist_redundant_l.
        2:{ apply elem_of_list_pair. exists i. split...
            - apply list_lookup_fmap_Some. exists x...
            - assert (∃ t', ts !! i = Some t') as (t'&?).
              { apply elem_of_list_split_length in Hi as (xs0&xs1&->&?).
                simpl in H1. inversion H1. destruct (ts !! i) eqn:E.
                + exists t0. subst...
                + exfalso. apply list_lookup_None in E. rewrite length_app in H4.
                  rewrite <- H0 in H4. simpl in H4. lia. }
              specialize (Hunique 0 (S i) x t t').
              enough (t = t') by (subst t'; apply H0).
              apply Hunique.
              + lia.
              + apply elem_of_list_pair_indexed_hd. split...
              + apply elem_of_list_pair_indexed_tl. apply elem_of_list_pair_indexed.
                split... }
        rewrite f_exists_existslist_idemp... rewrite fequiv_subst_non_free.
        * apply IH; [| set_solver]...
        * intros contra.
          apply fvars_seqsubst_vars_not_free_in_terms_superset in contra; set_solver.
      + rewrite <- f_and_assoc. rewrite f_existslist_and_unused_l by set_solver.
        rewrite IH by set_solver. rewrite f_exists_one_point by set_solver...
  Qed.

  Lemma f_foralllist_one_point xs ts A `{OfSameLength _ _ xs ts} :
    seqsubst_lists_unique xs ts →
    (list_to_set xs) ∩ ⋃ (term_fvars <$> ts) = ∅ →
    <! ∀* xs, ⌜@*xs =* ts⌝ ⇒ A !> ≡ <! A[; *xs \ *ts ;] !>.
  Proof with auto.
    intros. rewrite f_foralllist_as_existslist. rewrite f_not_impl.
    rewrite f_existslist_one_point... rewrite simpl_seqsubst_not. rewrite f_not_stable...
  Qed.

  (* A.60 *)
  (* Lemma f_exists_idemp x A : *)
  (*   <! ∃ x x, A !> ≡ <! ∃ x, A !>. *)
  (* Proof with auto. rewrite fexists_unused... simpl. set_solver. Qed. *)

  (* A.59 *)
  (* Lemma f_forall_idemp x A : *)
  (*   <! ∀ x x, A !> ≡ <! ∀ x, A !>. *)
  (* Proof with auto. unfold FForall. rewrite f_not_stable. rewrite f_exists_idemp... Qed. *)


  (* A.64 *)
  (* Lemma f_exists_comm x y A : *)
  (*   <! ∃ x y, A !> ≡ <! ∃ y x, A !>. *)
  (* Proof with auto. *)
  (*   intros σ. destruct (decide (x = y)). 1:{ subst... } *)
  (*   destruct (decide (x ∈ formula_fvars A)). *)
  (*   2:{ rewrite fexists_unused. *)
  (*       - rewrite (fexists_unused x)... *)
  (*       - simpl. set_solver. } *)
  (*   destruct (decide (y ∈ formula_fvars A)). *)
  (*   2:{ rewrite (fexists_unused y)... *)
  (*       rewrite (fexists_unused y)... simpl. set_solver. } *)
  (*   simp feval. split. *)
  (*   - intros [vx H]. rewrite (feval_subst vx) in H... simp feval in H. destruct H as [vy H]. *)
  (*     rewrite (feval_subst vy) in H... exists vy. rewrite (feval_subst vy)... *)
  (*     simp feval. exists vx. rewrite (feval_subst vx)... rewrite (insert_commute σ)... *)
  (*   - intros [vy H]. rewrite (feval_subst vy) in H... simp feval in H. destruct H as [vx H]. *)
  (*     rewrite (feval_subst vx) in H... exists vx. rewrite (feval_subst vx)... *)
  (*     simp feval. exists vy. rewrite (feval_subst vy)... rewrite (insert_commute σ)... *)
  (* Qed. *)

  (* A.63 *)
  (* Lemma f_forall_comm x y A : *)
  (*   <! ∀ x y, A !> ≡ <! ∀ y x, A !>. *)
  (* Proof. unfold FForall. do 2 rewrite f_not_stable. rewrite f_exists_comm. reflexivity. Qed. *)

  (* A.66 *)
  (* Lemma f_exists_or x A B : *)
  (*   <! ∃ x, A ∨ B !> ≡ <! (∃ x, A) ∨ (∃ x, B) !>. *)
  (* Proof with auto. *)
  (*   intros σ. simp feval. setoid_rewrite simpl_subst_or. split. *)
  (*   - intros [v H]. simp feval in H. destruct H as [|]; [left|right]; exists v... *)
  (*   - intros [[v H] | [v H]]; exists v; simp feval... *)
  (* Qed. *)

  (* A.65 *)
  (* Lemma f_forall_and x A B : *)
  (*   <! ∀ x, A ∧ B !> ≡ <! (∀ x, A) ∧ (∀ x, B) !>. *)
  (* Proof. unfold FForall. rewrite f_not_and. rewrite f_exists_or. rewrite f_not_or; auto. Qed. *)

  (* A.67 *)
  (* Lemma f_exists_impl x A B : *)
  (*   <! ∃ x, A ⇒ B !> ≡ <! (∀ x, A) ⇒ (∃ x, B) !>. *)
  (* Proof with auto. *)
  (*   intros σ. unfold FImpl. rewrite f_exists_or. unfold FForall. rewrite f_not_stable... *)
  (* Qed. *)

  (* A.68 *)
  (* Lemma f_forall_ent_exists x A : *)
  (*   <! ∀ x, A !> ⇛ <! ∃ x, A !>. *)
  (* Proof. *)
  (*   intros σ. rewrite simpl_feval_fforall. intros. simp feval. *)
  (*   exists ⊥. apply H. *)
  (* Qed. *)

  (* A.69 *)
  (* Lemma f_or_forall x A B : *)
  (*   <! (∀ x, A) ∨ (∀ x, B) !> ⇛ <! ∀ x, A ∨ B !>. *)
  (* Proof. *)
  (*   intros σ. simp feval. do 3 rewrite simpl_feval_fforall. *)
  (*   setoid_rewrite simpl_subst_or. *)
  (*   intros [|]; intros; simp feval; naive_solver. *)
  (* Qed. *)

  (* A.70 *)
  (* Lemma f_forall_impl x A B : *)
  (*   <! ∀ x, A ⇒ B !> ⇛ <! (∀ x, A) ⇒ (∀ x, B) !>. *)
  (* Proof. *)
  (*   intros σ. rewrite simpl_feval_fimpl. do 3 rewrite simpl_feval_fforall. *)
  (*   intros. specialize (H v). rewrite simpl_subst_impl in H. rewrite simpl_feval_fimpl in H. *)
  (*   naive_solver. *)
  (* Qed. *)

  (* A.71 *)
  (* Lemma f_exists_and x A B : *)
  (*   <! ∃ x, A ∧ B !> ⇛ <! (∃ x, A) ∧ (∃ x, B) !>. *)
  (* Proof with auto. *)
  (*   intros σ. simp feval. intros [v H]. rewrite simpl_subst_and in H. simp feval in H. *)
  (*   destruct H as []. split; exists v... *)
  (* Qed. *)

  (* A.72 *)
  (* Lemma f_impl_exists x A B : *)
  (*   <! (∃ x, A) ⇒ (∃ x, B) !> ⇛ <! ∃ x, A ⇒ B !>. *)
  (* Proof with auto. *)
  (*   intros σ. rewrite simpl_feval_fimpl. intros. simp feval. *)
  (*   setoid_rewrite simpl_subst_impl. setoid_rewrite simpl_feval_fimpl. *)
  (*   destruct (feval_lem σ <! ∃ x, A !>). *)
  (*   - apply H in H0. simp feval in H0. destruct H0 as [v Hv]. exists v. intros... *)
  (*   - exists ⊥. intros. simp feval in H0. exfalso. apply H0. exists ⊥... *)
  (* Qed. *)

  (* A.73 *)
  (* Lemma f_exists_forall x y A : *)
  (*   <! ∃ x, (∀ y, A) !> ⇛ <! ∀ y, (∃ x, A) !>. *)
  (* Proof with auto. *)
  (*   intros σ. simp feval. rewrite simpl_feval_fforall. intros [vx H] vy. *)
  (*   destruct (decide (x = y)). *)
  (*   1:{ subst y. rewrite simpl_subst_forall_skip in H... rewrite simpl_subst_exists_skip... *)
  (*       apply f_forall_ent_exists in H... } *)
  (*   rewrite (feval_subst vx) in H... rewrite simpl_feval_fforall in H. *)
  (*   specialize (H vy). rewrite (feval_subst vy) in H... *)
  (*   rewrite (feval_subst vy)... simp feval. exists vx. rewrite (feval_subst vx)... *)
  (*   rewrite (insert_commute σ)... *)
  (* Qed. *)

  (* A.74: fforall_unused *)
  (* A.75: fexists_unused *)

  (* A.76 *)
  (* Lemma f_forall_and_unused_l x A B : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∀ x, A ∧ B !> ≡ <! A ∧ (∀ x, B) !>. *)
  (* Proof with auto. intros. rewrite f_forall_and. rewrite fforall_unused... Qed. *)

  (* A.76' *)
  (* Lemma f_forall_and_unused_r x A B : *)
  (*   x ∉ formula_fvars B → *)
  (*   <! ∀ x, A ∧ B !> ≡ <! (∀ x, A) ∧ B !>. *)
  (* Proof with auto. intros. rewrite f_forall_and. rewrite (fforall_unused x B)... Qed. *)

  (* A.77 *)
  (* Lemma f_forall_or_unused_l x A B : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∀ x, A ∨ B !> ≡ <! A ∨ (∀ x, B) !>. *)
  (* Proof with auto. *)
  (*   intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_or. *)
  (*   split; intros. *)
  (*   - simp feval. destruct (feval_lem σ A)... right. rewrite simpl_feval_fforall. *)
  (*     intros. specialize (H0 v). simp feval in H0. destruct H0... *)
  (*     rewrite (feval_subst v) in H0... apply feval_delete_state_var_head in H0... *)
  (*     contradiction. *)
  (*   - simp feval in *. rewrite (feval_subst v)... rewrite feval_delete_state_var_head... *)
  (*     destruct H0... right. rewrite simpl_feval_fforall in H0. apply H0. *)
  (* Qed. *)

  (* A.77' *)
  (* Lemma f_forall_or_unused_r x A B : *)
  (*   x ∉ formula_fvars B → *)
  (*   <! ∀ x, A ∨ B !> ≡ <! (∀ x, A) ∨ B !>. *)
  (* Proof with auto. *)
  (*   intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_or. *)
  (*   split; intros. *)
  (*   - simp feval. destruct (feval_lem σ B)... left. rewrite simpl_feval_fforall. *)
  (*     intros. specialize (H0 v). simp feval in H0. destruct H0... *)
  (*     rewrite (feval_subst v) in H0... apply feval_delete_state_var_head in H0... *)
  (*     contradiction. *)
  (*   - simp feval in *. destruct H0. *)
  (*     + left. rewrite simpl_feval_fforall in H0. apply H0... *)
  (*     + right. rewrite (feval_subst v)... rewrite feval_delete_state_var_head... *)
  (* Qed. *)

  (* A.78 *)
  (* Lemma f_forall_impl_unused_l x A B : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∀ x, A ⇒ B !> ≡ <! A ⇒ (∀ x, B) !>. *)
  (* Proof with auto. *)
  (*   intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_impl. *)
  (*   rewrite simpl_feval_fimpl. *)
  (*   split; intros. *)
  (*   - rewrite simpl_feval_fforall. intros. specialize (H0 v). rewrite simpl_feval_fimpl in H0. *)
  (*     rewrite (feval_subst v) in H0... rewrite feval_delete_state_var_head in H0... *)
  (*   - rewrite simpl_feval_fimpl. intros. rewrite (feval_subst v) in H1... *)
  (*     rewrite feval_delete_state_var_head in H1... apply H0 in H1. *)
  (*     rewrite simpl_feval_fforall in H1... *)
  (* Qed. *)

  (* A.79 *)
  (* Lemma f_forall_impl_unused_r x A B : *)
  (*   x ∉ formula_fvars B → *)
  (*   <! ∀ x, A ⇒ B !> ≡ <! (∃ x, A) ⇒ B !>. *)
  (* Proof with auto. *)
  (*   intros. intros σ. rewrite simpl_feval_fforall. setoid_rewrite simpl_subst_impl. *)
  (*   setoid_rewrite simpl_feval_fimpl. simp feval. *)
  (*   split; intros. *)
  (*   - destruct H1 as [v Hv]. apply H0 in Hv. apply (feval_subst v) in Hv... *)
  (*     apply feval_delete_state_var_head in Hv... *)
  (*   - forward H0 by (exists v)... apply (feval_subst v)... apply feval_delete_state_var_head... *)
  (* Qed. *)

  (* A.80 *)
  (* Lemma f_exists_and_unused_l x A B : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∃ x, A ∧ B !> ≡ <! A ∧ (∃ x, B) !>. *)
  (* Proof with auto. *)
  (*   intros. rewrite <- (f_not_stable A). rewrite <- (f_not_stable B). rewrite <- (f_not_or). *)
  (*   rewrite <- (f_not_forall). rewrite f_forall_or_unused_l by (simpl; auto). *)
  (*   rewrite f_not_or. rewrite f_not_forall... *)
  (* Qed. *)

  (* A.80' *)
  (* Lemma f_exists_and_unused_r x A B : *)
  (*   x ∉ formula_fvars B → *)
  (*   <! ∃ x, A ∧ B !> ≡ <! (∃ x, A) ∧ B !>. *)
  (* Proof with auto. *)
  (*   intros. rewrite <- (f_not_stable A). rewrite <- (f_not_stable B). rewrite <- (f_not_or). *)
  (*   rewrite <- (f_not_forall). rewrite f_forall_or_unused_r by (simpl; auto). *)
  (*   rewrite f_not_or. rewrite f_not_forall... *)
  (* Qed. *)

  (* A.81 *)
  (* Lemma f_exists_or_unused_l x A B : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∃ x, A ∨ B !> ≡ <! A ∨ (∃ x, B) !>. *)
  (* Proof with auto. intros. rewrite f_exists_or. rewrite fexists_unused... Qed. *)

  (* A.81' *)
  (* Lemma f_exists_or_unused_r x A B : *)
  (*   x ∉ formula_fvars B → *)
  (*   <! ∃ x, A ∨ B !> ≡ <! (∃ x, A) ∨ B !>. *)
  (* Proof with auto. intros. rewrite f_exists_or. rewrite (fexists_unused _ B)... Qed. *)

  (* A.82 *)
  (* Lemma f_exists_impl_unused_l x A B : *)
  (*   x ∉ formula_fvars A → *)
  (*   <! ∃ x, A ⇒ B !> ≡ <! A ⇒ (∃ x, B) !>. *)
  (* Proof with auto. intros. rewrite f_exists_impl. rewrite fforall_unused... Qed. *)

  (* A.83 *)
  (* Lemma f_exists_impl_unused_r x A B : *)
  (*   x ∉ formula_fvars B → *)
  (*   <! ∃ x, A ⇒ B !> ≡ <! (∀ x, A) ⇒ B !>. *)
  (* Proof with auto. intros. rewrite f_exists_impl. rewrite fexists_unused... Qed. *)

  (* A.84: fforall_alpha_equiv *)
  (* A.85: fexists_alpha_equiv *)

  (* A.86 *)
  (* Lemma f_forall_elim t x A : *)
  (*   <! ∀ x, A !> ⇛ <! A[x \ t] !>. *)
  (* Proof with auto. *)
  (*   intros σ. rewrite simpl_feval_fforall. intros. pose proof (teval_total σ t) as [v Hv]. *)
  (*   specialize (H v). rewrite (feval_subst v) in H... rewrite (feval_subst v)... *)
  (* Qed. *)

  (* A.86 *)
  (* Lemma f_exists_intro t x A : *)
  (*   <! A[x \ t] !> ⇛ <! ∃ x, A !>. *)
  (* Proof with auto. *)
  (*   intros σ. simp feval. intros. pose proof (teval_total σ t) as [v Hv]. *)
  (*   exists v. rewrite (feval_subst v) in H... rewrite (feval_subst v)... *)
  (* Qed. *)

  (* Lemma f_impl_elim A B : *)
  (*   <! A ∧ (A ⇒ B) !> ⇛ B. *)
  (* Proof with auto. *)
  (*   intros σ. simp feval. rewrite simpl_feval_fimpl. naive_solver. *)
  (* Qed. *)

  (* some lemmas for proving equivalences and entailments *)

  (* Lemma f_and_cancel_l A B C : *)
  (*   B ≡ C → <! A ∧ B !> ≡ <! A ∧ C !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_and_cancel_r A B C : *)
  (*   B ≡ C → <! B ∧ A !> ≡ <! C ∧ A !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_or_cancel_l A B C : *)
  (*   B ≡ C → <! A ∨ B !> ≡ <! A ∨ C !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_or_cancel_r A B C : *)
  (*   B ≡ C → <! B ∨ A !> ≡ <! C ∨ A !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_impl_cancel_l A B C : *)
  (*   B ≡ C → <! A ⇒ B !> ≡ <! A ⇒ C !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_impl_cancel_r A B C : *)
  (*   B ≡ C → <! B ⇒ A !> ≡ <! C ⇒ A !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_subst_cancel A B x t : *)
  (*   A ≡ B → <! A[x \ t] !> ≡ <! B[x \ t] !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_subst_cancel_term A x t1 t2 : *)
  (*   t1 ≡ t2 → <! A[x \ t1] !> ≡ <! A[x \ t2] !>. *)
  (* Proof. intros. rewrite H. reflexivity. Qed. *)

  (* Lemma f_exists_equiv A B y1 y2 : *)
  (*   (∀ t, <! A[y1 \ t] !> ≡ <! B[y2 \ t] !>) → *)
  (*   <! ∃ y1, A !> ≡ <! ∃ y2, B !>. *)
  (* Proof. intros Hequiv σ. apply feval_exists_equiv_if. naive_solver. Qed. *)

  (* Lemma f_forall_equiv A B y1 y2 : *)
  (*   (∀ t, <! A[y1 \ t] !> ≡ <! B[y2 \ t] !>) → *)
  (*   <! ∀ y1, A !> ≡ <! ∀ y2, B !>. *)
  (* Proof. intros Hequiv σ. do 2 rewrite simpl_feval_fforall. naive_solver. Qed. *)

  (* Lemma f_ent_and_cancel_l A B C : *)
  (*   B ⇛ C → <! A ∧ B !> ⇛ <! A ∧ C !>. *)
  (* Proof. intros H σ. simp feval. specialize (H σ). naive_solver. Qed. *)

  (* Lemma f_ent_and_cancel_r A B C : *)
  (*   B ⇛ C → <! B ∧ A !> ⇛ <! C ∧ A !>. *)
  (* Proof. intros H σ. simp feval. specialize (H σ). naive_solver. Qed. *)

  (* Lemma f_ent_or_cancel_l A B C : *)
  (*   B ⇛ C → <! A ∨ B !> ⇛ <! A ∨ C !>. *)
  (* Proof. intros H σ. simp feval. specialize (H σ). naive_solver. Qed. *)

  (* Lemma f_ent_or_cancel_r A B C : *)
  (*   B ⇛ C → <! B ∨ A !> ⇛ <! C ∨ A !>. *)
  (* Proof. intros H σ. simp feval. specialize (H σ). naive_solver. Qed. *)

  (* Lemma f_ent_subst_cancel A B x t : *)
  (*   A ⇛ B → <! A[x \ t] !> ⇛ <! B[x \ t] !>. *)
  (* Proof with auto. *)
  (*   intros Hent σ H. pose proof (teval_total σ t) as [v Hv]. rewrite (feval_subst v) in H... *)
  (*   apply Hent in H. rewrite (feval_subst v)... *)
  (* Qed. *)

  (* Lemma f_ent_impl_cancel_l A B C : *)
  (*   B ⇛ C → <! A ⇒ B !> ⇛ <! A ⇒ C !>. *)
  (* Proof. intros H σ. do 2 rewrite simpl_feval_fimpl. naive_solver. Qed. *)

  (* Lemma f_ent_impl_cancel_r A B C : *)
  (*   C ⇛ B → <! B ⇒ A !> ⇛ <! C ⇒ A !>. *)
  (* Proof. intros H σ. do 2 rewrite simpl_feval_fimpl. naive_solver. Qed. *)

  (* Lemma f_exists_ent A B y1 y2 : *)
  (*   (∀ t, <! A[y1 \ t] !> ⇛ <! B[y2 \ t] !>) → *)
  (*   <! ∃ y1, A !> ⇛ <! ∃ y2, B !>. *)
  (* Proof. *)
  (*   intros Hequiv σ. simp feval. intros [v Hv]. exists v. naive_solver. *)
  (* Qed. *)

  (* Lemma f_forall_ent A B y1 y2 : *)
  (*   (∀ t, <! A[y1 \ t] !> ⇛ <! B[y2 \ t] !>) → *)
  (*   <! ∀ y1, A !> ⇛ <! ∀ y2, B !>. *)
  (* Proof. *)
  (*   intros Hequiv σ. do 2 rewrite simpl_feval_fforall. intros. naive_solver. *)
  (* Qed. *)

  (* Lemma f_ent_elim σ A B : *)
  (*   feval σ A → *)
  (*   A ⇛ B → *)
  (*   feval σ B. *)
  (* Proof. naive_solver. Qed. *)

  (* Lemma f_ent_intro A B : *)
  (*   (∀ σ, feval σ A → feval σ B) → *)
  (*   A ⇛ B. *)
  (* Proof. naive_solver. Qed. *)

  (* Lemma f_eq_refl t : *)
  (*   <! ⌜t = t⌝ !> ≡ <! true !>. *)
  (* Proof. *)
  (*   prove_equiv. intros. destruct (teval_total σ t) as [v Hv]. econstructor. split; exact Hv. *)
  (* Qed. *)

  (* Lemma f_neq_irrefl t : *)
  (*   <! ⌜t ≠ t⌝ !> ≡ <! false !>. *)
  (* Proof. *)
  (*   rewrite f_eq_refl. rewrite f_not_true. reflexivity. *)
  (* Qed. *)
End n_ary_lemmas.
