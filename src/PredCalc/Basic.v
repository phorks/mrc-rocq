From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia.
From stdpp Require Import gmap vector.
From Equations Require Import Equations.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import Tactics.
From MRC Require Import SeqNotation.
Open Scope bool_scope.

Section pred_calc_syntax.
  Context {V : Type}.

  Unset Elimination Schemes.
  Inductive term : Type :=
  | TConst (v : V)
  | TVar (x : variable)
  | TApp (symbol : string) (args : list term).
  Set Elimination Schemes.

  Fixpoint term_rank (t : term) :=
    match t with
    | TConst _ => 0
    | TVar _ => 0
    | TApp f args => 1 + max_list_with term_rank args
    end.

  Lemma term_rank_app_gt_args fsym (arg : term) (args : list term) :
    In arg args →
    term_rank arg < term_rank (TApp fsym args).
  Proof with auto.
    intros HIn. simpl. unfold In in HIn. induction args.
    - destruct HIn.
    - destruct HIn as [HIn | HIn].
      + rewrite HIn in *. simpl. lia.
      + simpl in *. remember (max_list_with term_rank args) as rest.
        destruct (Nat.max_spec (term_rank a) (rest)) as [[_ H] | [_ H]]; rewrite H; try lia...
        forward IHargs... lia.
  Qed.

  Lemma term_formula_rank_ind P :
    (forall n,
        (forall m, m < n →
                   forall u, term_rank u = m → P u) →
        (forall t, term_rank t = n → P t)) →
    forall n t, term_rank t < n → P t.
  Proof with auto.
    intros Hind n. induction n; intros t Hrank.
    - lia.
    - apply Hind with (term_rank t)...
      intros m Hlt u Hu. apply IHn. lia.
  Qed.

  Lemma term_ind P :
    (forall v, P (TConst v)) →
    (forall x, P (TVar x)) →
    (forall f args,
        (forall arg, In arg args → P arg) → P (TApp f args)) →
    (forall t, P t).
  Proof with auto.
    intros Hconst Hvar Hfunc t.
    apply (term_formula_rank_ind P) with (term_rank t + 1); try lia...
    clear t. intros n IH t Htr. destruct t...
    apply Hfunc. intros arg HIn.
    apply term_rank_app_gt_args with (fsym:=symbol) in HIn.
    apply IH with (term_rank arg); lia.
  Qed.

  Inductive atomic_formula : Type :=
  | AT_True
  | AT_False
  | AT_Eq (t1 t2 : term)
  | AT_Pred (symbol : string) (args : list (term)).

  Unset Elimination Schemes.
  Inductive formula : Type :=
  | FAtom (af : atomic_formula)
  | FNot (A : formula)
  | FAnd (A B : formula)
  | FOr (A B : formula)
  | FExists (x : variable) (A : formula).
  Set Elimination Schemes.
  Scheme formula_ind_naive := Induction for formula Sort Type.

  Set Warnings "-uniform-inheritance".
  Global Coercion TVar : variable >-> term.
  Set Warnings "+uniform-inheritance".
  Global Coercion FAtom : atomic_formula >-> formula.

  Definition FImpl A B := FOr (FNot A) B.
  Definition FIff A B := FAnd (FImpl A B) (FImpl B A).
  Definition FForall x A := FNot (FExists x (FNot A)).

  Fixpoint subst_term t x a : term :=
    match t with
    | TConst v => TConst v
    | TVar y => if decide (y = x) then a else TVar y
    | TApp sym args => TApp sym (map (fun arg => subst_term arg x a) args)
    end.

  Definition subst_af af x a :=
    match af with
    | AT_Eq t₁ t₂ => AT_Eq (subst_term t₁ x a) (subst_term t₂ x a)
    | AT_Pred sym args => AT_Pred sym (map (fun arg => subst_term arg x a) args)
    | _ => af
    end.

  Fixpoint term_fvars t : gset variable :=
    match t with
    | TConst v => ∅
    | TVar y => {[y]}
    | TApp sym args => ⋃ (term_fvars <$> args)
    end.

  Definition af_fvars af : gset variable :=
    match af with
    | AT_Eq t₁ t₂ => term_fvars t₁ ∪ term_fvars t₂
    | AT_Pred _ args => ⋃ (term_fvars <$> args)
    | _ => ∅
    end.

  Fixpoint formula_fvars A : gset variable :=
    match A with
    | FAtom af => af_fvars af
    | FNot A => formula_fvars A
    | FAnd A B => formula_fvars A ∪ formula_fvars B
    | FOr A B => formula_fvars A ∪ formula_fvars B
    | FExists x A => formula_fvars A ∖ {[x]}
    end.

  Fixpoint formula_rank A :=
    match A with
    | FAtom af => 1
    | FNot A => 1 + formula_rank A
    | FAnd A B => 1 + max (formula_rank A) (formula_rank B)
    | FOr A B => 1 + max (formula_rank A) (formula_rank B)
    | FExists _ A => 1 + (formula_rank A)
    end.

  Fixpoint quantifier_rank A :=
    match A with
    | FAtom af => 0
    | FNot A => quantifier_rank A
    | FAnd A B => max (quantifier_rank A) (quantifier_rank B)
    | FOr A B => max (quantifier_rank A) (quantifier_rank B)
    | FExists _ A => 1 + (quantifier_rank A)
    end.

  Notation rank A := (formula_rank A + quantifier_rank A).

  Definition quant_subst_fvars y A x t :=
    (formula_fvars A ∖ {[y]}) ∪ term_fvars t ∪ {[x]}.

  Lemma quant_subst_fvars_inv y' y A x t :
    y' ∉ quant_subst_fvars y A x t → (y = y' ∨ y' ∉ formula_fvars A) ∧ y' ∉ term_fvars t ∧ y' ≠ x.
  Proof with auto.
    intros. unfold quant_subst_fvars in H. apply not_elem_of_union in H as [H H1].
    apply not_elem_of_union in H as [H H2]. apply not_elem_of_difference in H.
    apply not_elem_of_singleton in H1. rewrite elem_of_singleton in H...
    split... destruct H...
  Qed.

  Lemma fresh_var_ne_inv y A x t :
    fresh_var y (quant_subst_fvars y A x t) ≠ y →
    y ∈ term_fvars t ∨ y = x.
  Proof with auto.
    intros. unfold fresh_var, fresh_var_aux in H.
    destruct (size (quant_subst_fvars y A x t)); destruct (decide (y ∈ quant_subst_fvars y A x t)).
    - unfold quant_subst_fvars in e. do 2 rewrite elem_of_union in e. rewrite elem_of_singleton in e.
      destruct e... destruct H0... set_solver.
    - contradiction.
    - unfold quant_subst_fvars in e. do 2 rewrite elem_of_union in e. rewrite elem_of_singleton in e.
      destruct e... destruct H0... set_solver.
    - contradiction.
  Qed.

  Inductive sum_quant_subst_skip_cond y A x :=
  | SumQuantSubstSkipCond_True (H : x = y ∨ x ∉ formula_fvars A)
  | SumQuantSubstSkipCond_False (H1 : x ≠ y) (H2: x ∈ formula_fvars A).

  Definition quant_subst_skip_cond y A x : sum_quant_subst_skip_cond y A x.
  Proof with auto.
    destruct (decide (x = y ∨ x ∉ formula_fvars A)).
    - apply SumQuantSubstSkipCond_True...
    - apply Decidable.not_or in n as [H1 H2]. destruct (decide (x ∈ formula_fvars A)).
      + apply SumQuantSubstSkipCond_False...
      + contradiction.
  Defined.

  (*
For (Qy. A)[x \ t] (where Q ∈ {∃, ∀}), when x ≠ y and y ∈ FV(t),
we need to pick a fresh quantifier y'. But there are two limitations:
1. y' ∉ FV(A): or else we will incorrectly capture
2. y' ∉ FV(t): Let's assume (Qy. y = x)[x \ z],
  If y' = c:
    (Qy. y = x)[x \ c + y] ≡ (Qc. (c = x)[x \ c + y]) ≡ (Qc. c = c + y)
  If y' = z a universally fresh quantifier:
    (Qy. y = x)[x \ c + y] ≡ (Qz. (z = x)[x \ c + y]) ≡ (Qz. z = c + y)
  These two are not α-equivalent.


The following is not a limitation; however we enforce it to make proofs easier
1. y' can be x but we don't allow it:
  (Qy. A)[x \ t] ≡ (Qx. A[y \ x][x \ t]) ≡ (Qx. A[y \ x])
  This discards the substition; picking a universally fresh quantifier z, yields:
  (Qz. A)[x \ t] ≡ (Qz. A[y \ z][x \ t])
  It seems like these two are not α-equivalent; but:
  Since y' = x, we must have x ∉ FV(A) which means (Qz. A[y \ z][x \ t]) ≡ (Qz. A[y \ z])
   *)
  Fixpoint subst_formula_aux qrank :=
    fix subst_aux A x t :=
      match A with
      | FAtom af => FAtom (subst_af af x t)
      | FNot A => FNot (subst_aux A x t)
      | FAnd A₁ A₂ => FAnd
                        (subst_aux A₁ x t)
                        (subst_aux A₂ x t)
      | FOr A₁ A₂ => FOr
                       (subst_aux A₁ x t)
                       (subst_aux A₂ x t)
      | FExists y A =>
          if quant_subst_skip_cond y A x then FExists y A else
            let y' := fresh_var y (quant_subst_fvars y A x t) in
            match qrank with
            | 0 => FExists y A
            | S qrank => FExists y' (subst_formula_aux qrank (subst_aux A y (TVar y')) x t)
            end
      end.

  Definition subst_formula A x t :=
    subst_formula_aux (quantifier_rank A) A x t.

  Ltac fold_qrank_subst n A x t :=
    let R := fresh in
    let H := fresh in
    let H' := fresh in
    remember (subst_formula_aux n A x t) as R eqn:H;
    assert (H' := H); simpl in H'; rewrite H in H'; rewrite <- H' in *;
    clear H'; clear H; clear R.

  Ltac fold_qrank_subst_fresh n A x x' t :=
    fold_qrank_subst n A x (fresh_var x (quant_subst_fvars x A x' t)).

  Lemma formula_rank_gt_zero : forall A, formula_rank A > 0.
  Proof.
    intros A. destruct A; simpl; lia.
  Qed.

  Lemma formula_rank_nonzero : forall A,
      formula_rank A <> 0.
  Proof.
    intros A. assert (formula_rank A > 0) by apply formula_rank_gt_zero.
    lia.
  Qed.

  Hint Resolve formula_rank_nonzero : core.

  Hint Extern 2 =>
         match goal with [H : formula_rank _ = 0 |- _] =>
                           apply formula_rank_nonzero in H; destruct H end : core.

  Hint Extern 2 =>
         match goal with [H : 0 = formula_rank _ |- _] =>
                           apply eq_sym in H; apply formula_rank_nonzero in H;
  destruct H end : core.

  Lemma formula_rank_one_is_simple : forall A,
      formula_rank A = 1 →
      ∃ af, A = FAtom af.
  Proof with auto.
    intros A Hr. destruct A;
      try solve [inversion Hr; auto];
      try solve [inversion Hr;
                 destruct (Nat.max_spec (formula_rank A1) (formula_rank A2))
                   as [[_ H] | [_ H]]; rewrite H0 in *; auto].
    - exists af...
  Qed.

  Lemma formula_rank_ind : forall P,
      (forall n,
          (forall m, m < n →
                     forall B, rank B = m → P B) →
          (forall A, rank A = n → P A)) →
      forall A, P A.
  Proof with auto.
    intros P Hind.
    assert (H : forall n A, rank A < n → P A).
    {
      induction n; intros A Hrank.
      - lia.
      - apply Hind with (formula_rank A + quantifier_rank A)...
        intros m Hlt B HB. apply IHn. lia.
    }
    intros A. apply H with (S (rank A)). lia.
  Qed.

  Definition is_quantifier P :=
    match P with
    | FExists _ _ => true
    | _ => false
    end.

  Definition ctor_eq A B :=
    match A, B with
    | FAtom _, FAtom _ => true
    | FNot _, FNot _ => true
    | FAnd _ _, FAnd _ _  => true
    | FOr _ _, FOr _ _ => true
    | FExists _ _, FExists _ _ => true
    | _, _ => false
    end.

  Fixpoint shape_eq A B :=
    match A, B with
    | FAtom _, FAtom _ => true
    | FNot A, FNot B => shape_eq A B
    | FAnd A1 A2, FAnd B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
    | FOr A1 A2, FOr B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
    | FExists _ A, FExists _ B => shape_eq A B
    | _, _ => false
    end.

  Lemma shape_eq__ctor_eq A B :
    shape_eq A B = true →
    ctor_eq A B = true.
  Proof with auto.
    intros. destruct A; destruct B; try discriminate...
  Qed.

  Lemma ctor_eq_atomic af B :
    ctor_eq (FAtom af) B = true →
    ∃ af', B = FAtom af'.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists af0...
  Qed.

  Lemma shape_eq_simple af B :
    shape_eq (FAtom af) B = true →
    ∃ af', B = FAtom af'.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists af0...
  Qed.

  Lemma ctor_eq_not A1 B :
    ctor_eq (FNot A1) B = true →
    ∃ B1, B = FNot B1.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists B...
  Qed.

  Lemma shape_eq_not A1 B :
    shape_eq (FNot A1) B = true →
    ∃ B1, B = FNot B1 ∧ shape_eq A1 B1 = true.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists B...
  Qed.

  Lemma ctor_eq_and A1 A2 B :
    ctor_eq (FAnd A1 A2) B = true →
    ∃ B1 B2, B = (FAnd B1 B2).
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists B1, B2...
  Qed.

  Lemma shape_eq_and A1 A2 B :
    shape_eq (FAnd A1 A2) B = true →
    ∃ B1 B2, B = FAnd B1 B2 ∧
               shape_eq A1 B1 = true ∧
               shape_eq A2 B2 = true.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate.
    apply Bool.andb_true_iff in H. exists B1, B2...
  Qed.

  Lemma ctor_eq_or A1 A2 B :
    ctor_eq (FOr A1 A2) B = true →
    ∃ B1 B2, B = FOr B1 B2.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists B1, B2...
  Qed.

  Lemma shape_eq_or A1 A2 B :
    shape_eq (FOr A1 A2) B = true →
    ∃ B1 B2, B = FOr B1 B2 ∧
               shape_eq A1 B1 = true ∧
               shape_eq A2 B2 = true.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate.
    apply Bool.andb_true_iff in H. exists B1, B2...
  Qed.

  Lemma ctor_eq_exists x A1 B :
    ctor_eq (FExists x A1) B = true →
    ∃ x' B1, B = FExists x' B1.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists x0, B...
  Qed.

  Lemma shape_eq_exists x A1 B :
    shape_eq (FExists x A1) B = true →
    ∃ x' B1, B = FExists x' B1 ∧ shape_eq A1 B1 = true.
  Proof with auto.
    intros. simpl in H. destruct B; try discriminate. exists x0, B...
  Qed.

  Lemma shape_eq_refl A : shape_eq A A = true.
  Proof with auto.
    intros. induction A using formula_ind_naive; simpl; auto; apply Bool.andb_true_iff...
  Qed.

  Lemma shape_eq_sym A B :
    shape_eq A B = true →
    shape_eq B A = true.
  Proof with auto.
    generalize dependent B.
    induction A using formula_ind_naive; destruct B; try discriminate; simpl; auto;
      try repeat rewrite Bool.andb_true_iff; intros [H1 H2]...
  Qed.

  Lemma shape_eq_trans A B C :
    shape_eq A B = true →
    shape_eq B C = true →
    shape_eq A C = true.
  Proof with auto.
    generalize dependent C. generalize dependent B.
    induction A using formula_ind_naive; intros B C HAB HBC; destruct B; try discriminate;
      destruct C; try discriminate; simpl;
      try solve [inversion HAB; inversion HBC;
                 apply Bool.andb_true_iff in H0 as [H2 H3];
                 apply Bool.andb_true_iff in H1 as [H0 H1];
                 rewrite IHA1 with B1 C1; auto;
                 rewrite IHA2 with B2 C2; auto];
      try solve [apply IHA with B; auto]...
  Qed.

  Lemma ranks_equal_if_shape_eq : forall A B,
      shape_eq A B = true →
      formula_rank A = formula_rank B ∧
        quantifier_rank A = quantifier_rank B.
  Proof with auto.
    assert (Hfr: forall A B, shape_eq A B = true →
                             formula_rank A = formula_rank B). {
      intros A; induction A using formula_ind_naive; destruct B; try discriminate;
        intros H; simpl; auto;
        try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2];
             auto). }
    assert (Hqr: forall A B, shape_eq A B = true →
                             quantifier_rank A = quantifier_rank B). {
      intros A. induction A using formula_ind_naive; destruct B; try discriminate;
        intros H; simpl; auto;
        try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2];
             auto).
    }
    auto.
  Qed.

  Lemma rank_eq_if_shape_eq A B :
    shape_eq A B = true →
    rank A = rank B.
  Proof. intros. apply ranks_equal_if_shape_eq in H. lia. Qed.

  Ltac deduce_rank_eq Hsame :=
    let Htemp := fresh in
    let Hfr := fresh "Hfr" in
    let Hqr := fresh "Hqr" in
    apply ranks_equal_if_shape_eq in Hsame as Htemp;
    destruct Htemp as [Hfr Hqr].

  Hint Resolve shape_eq_refl : core.

  Lemma subst_preserves_shape_aux A x a r :
    shape_eq A (subst_formula_aux r A x a) = true.
  Proof with auto.
    revert x a r.
    apply (formula_rank_ind (fun P => forall x a r,
                                 shape_eq P (subst_formula_aux r P x a) = true))...
    clear A. intros n IH. destruct A;
      intros Hr x' a r.
    - destruct r; simpl in *...
    - specialize IH with (m:=rank A) (B:=A).
      destruct r; simpl in *...
      + fold_qrank_subst 0 A x' a. apply IH; try lia...
      + fold_qrank_subst (S r) A x' a. apply IH; try lia...
    - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1.
      specialize IH with (m:=rank A2) (B:=A2) as IH2.
      assert (HMax :=
                (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
      + destruct r; simpl in *; rewrite H2 in *.
        * fold_qrank_subst 0 A2 x' a. fold_qrank_subst 0 A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
        * fold_qrank_subst (S r) A2 x' a.
          fold_qrank_subst (S r) A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
      + destruct r; simpl in *; rewrite H2 in *.
        * fold_qrank_subst 0 A2 x' a. fold_qrank_subst 0 A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
        * fold_qrank_subst (S r) A2 x' a.
          fold_qrank_subst (S r) A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
    - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1.
      specialize IH with (m:=rank A2) (B:=A2) as IH2.
      assert (HMax :=
                (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))).
      destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
      + destruct r; simpl in *; rewrite H2 in *.
        * fold_qrank_subst 0 A2 x' a. fold_qrank_subst 0 A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
        * fold_qrank_subst (S r) A2 x' a.
          fold_qrank_subst (S r) A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
      + destruct r; simpl in *; rewrite H2 in *.
        * fold_qrank_subst 0 A2 x' a. fold_qrank_subst 0 A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
        * fold_qrank_subst (S r) A2 x' a.
          fold_qrank_subst (S r) A1 x' a.
          apply Bool.andb_true_iff. split;
            [apply IH1|apply IH2]; lia...
    - subst. destruct r; simpl in *.
      + destruct (quant_subst_skip_cond x A x')...
      + fold_qrank_subst_fresh (S r) A x x' a.
        destruct (quant_subst_skip_cond x A x'); try lia...
        remember (subst_formula_aux (S r) A x (fresh_var x (quant_subst_fvars x A x' a)))
          as A₁. (* the first substitution *)
        remember (subst_formula_aux r A₁ x' a)
          as A₂. (* the second substituion *)
        specialize IH with (m:=rank A) (B:=A) as IHA.
        specialize IH with (m:=rank A₁) (B:=A₁) as IHA₁.
        forward IHA by lia. forward IHA by auto.
        specialize (IHA x (fresh_var x (quant_subst_fvars x A x' a)) (S r)). (* A₁ *)
        forward IHA₁. { deduce_rank_eq IHA. rewrite HeqA₁. lia. }
        forward IHA₁ by reflexivity. specialize (IHA₁ x' a r).
        rewrite <- HeqA₁ in *. rewrite <- HeqA₂ in *.
        apply shape_eq_trans with A₁...
  Qed.

  Lemma subst_preserves_shape A x a :
    shape_eq (subst_formula A x a) A  = true.
  Proof with auto.
    unfold subst_formula. apply shape_eq_sym. apply subst_preserves_shape_aux.
  Qed.

  Hint Resolve subst_preserves_shape : core.

  Lemma formula_ind P :
    (∀ af, P (FAtom af)) →
    (∀ A, P A → P (FNot A)) →
    (∀ A1 A2, P A1 → P A2 → P (FAnd A1 A2)) →
    (∀ A1 A2, P A1 → P A2 → P (FOr A1 A2)) →
    (∀ x A, (∀ B, shape_eq B A = true → P B) → P (FExists x A)) →
    ∀ A, P A.
  Proof with auto.
    intros Haf Hnot Hand Hor Hexists A.
    induction A using formula_rank_ind. destruct A; subst; simpl in *.
    - apply Haf.
    - apply Hnot. apply X with (rank A); lia.
    - apply Hand; [apply X with (rank A1) | apply X with (rank A2)]; lia.
    - apply Hor; [apply X with (rank A1) | apply X with (rank A2)]; lia.
    - apply Hexists. intros. apply X with (rank B); auto.
      apply rank_eq_if_shape_eq in H. lia.
  Qed.

End pred_calc_syntax.

Notation rank A := (formula_rank A + quantifier_rank A).

Open Scope refiney_scope.

Declare Custom Entry term.
Declare Custom Entry formula.
Declare Custom Entry term_relation.
Declare Custom Entry atomic_formula.

Notation "e" := e (in custom term at level 0, e constr at level 0) : refiney_scope.
Notation "$( e )" := e (in custom term at level 0, only parsing,
                          e constr at level 200) : refiney_scope.
Notation "( e )" := e (in custom term, e custom term at level 200) : refiney_scope.
Notation "₀ x" := (initial_var_of x) (in custom term at level 5).
Notation "t + u" := (TApp "+" (@cons term t (@cons term u nil)))
                      (in custom term at level 50,
                          t custom term,
                          u custom term,
                          left associativity) : refiney_scope.
Notation "t - u" := (TApp "-" (@cons term t (@cons term u nil)))
                      (in custom term at level 50,
                          t custom term,
                          u custom term,
                          left associativity) : refiney_scope.
Notation "t * u" := (TApp "*" (@cons term t (@cons term u nil)))
                      (in custom term at level 50,
                          t custom term,
                          u custom term,
                          left associativity) : refiney_scope.
Notation "t [ x \ t' ]" := (subst_term t x t')
                            (in custom term at level 10, left associativity,
                              x at next level) : refiney_scope.

Notation "t = u" := (FAtom (AT_Eq t u))
                      (in custom term_relation at level 60,
                          t custom term at level 60,
                          u custom term at level 60,
                          no associativity) : refiney_scope.
Notation "t '≠' u" := (FNot (FAtom (AT_Eq t u)))
                       (in custom term_relation at level 60,
                           t custom term at level 60,
                           u custom term at level 60,
                           no associativity) : refiney_scope.

(* Notation "f '(' x ',' .. ',' y ')'" := (TApp f (@cons term x .. (@cons term y nil) ..)) *)
(*                                          (in custom term at level 40, *)
(*                                              x custom term, y custom term) : refiney_scope. *)

(* Declare Custom Entry aformula. *)

(* Notation "x < y" := (AT_Pred "<" (@cons term x (@cons term y nil)))
                              (in custom formula at level 70, no associativity). *)
(* Notation "x <= y" := (AT_Pred "<=" (@cons term x (@cons term y nil)))
                              (in custom formula at level 70, no associativity). *)
(* Notation "x > y" := (AT_Pred ">" (@cons term x (@cons term y nil)))
                              (in custom formula at level 70, no associativity). *)
(* Notation "x >= y" := (AT_Pred ">=" (@cons term x (@cons term y nil)))
                              (in custom formula at level 70, no associativity). *)

Notation "<! e !>" := e (e custom formula) : refiney_scope.

Notation "e" := e (in custom formula at level 0, e constr at level 0) : refiney_scope.
Notation "$( e )" := e (in custom formula at level 0, only parsing,
                           e constr at level 200) : refiney_scope.
Notation "( e )" := e (in custom formula, e at level 200) : refiney_scope.
Notation "⌜ r ⌝" := r (in custom formula, r custom term_relation) : refiney_scope.
Notation "'true'" := (FAtom AT_True) (in custom formula at level 0).
Notation "'false'" := (FAtom AT_False) (in custom formula at level 0).
Notation "¬ A" := (FNot A) (in custom formula at level 70, right associativity) : refiney_scope.
Notation "A ∧ B" := (FAnd A B) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "A ∨ B" := (FOr A B) (in custom formula at level 80, right associativity) : refiney_scope.
Notation "A ⇒ B" := (FImpl A B) (in custom formula at level 95, right associativity) : refiney_scope.
Notation "A ⇔ B" := (FIff A B) (in custom formula at level 90, no associativity) : refiney_scope.
Notation "∃ x .. y , A" := (FExists x .. (FExists y A) ..)
                                      (in custom formula at level 99, only parsing) : refiney_scope.
Notation "∃ x .. y ● A" := (FExists x .. (FExists y A) ..)
                                 (in custom formula at level 99, only printing) : refiney_scope.
Notation "∀ x .. y , A" := (FForall x .. (FForall y A) ..)
                                 (in custom formula at level 99, only parsing) : refiney_scope.
Notation "∀ x .. y ● A" := (FForall x .. (FForall y A) ..)
                                 (in custom formula at level 99, only printing) : refiney_scope.


Notation "A [! x \ t !]" := (subst_formula A x t)
                            (at level 10, left associativity,
                              x at next level) : refiney_scope.

Notation "A [ x \ t ]" := (subst_formula A x t)
                            (in custom formula at level 74, left associativity,
                                A custom formula,
                                x constr at level 0, t custom formula) : refiney_scope.

Declare Custom Entry term_seq_notation.
Declare Custom Entry term_seq_elem.

Notation "xs" := (xs) (in custom term_seq_notation at level 0,
                       xs custom term_seq_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom term_seq_notation at level 0)
    : refiney_scope.

Notation "x" := ([x]) (in custom term_seq_elem at level 0, x custom term at level 200)
    : refiney_scope.
Notation "* x" := x (in custom term_seq_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "*$( x )" := x (in custom term_seq_elem at level 5, x constr at level 200)
    : refiney_scope.
Infix "," := app (in custom term_seq_elem at level 10, right associativity) : refiney_scope.

Ltac fold_qrank_subst n A x t :=
  let R := fresh in
  let H := fresh in
  let H' := fresh in
  remember (subst_formula_aux n A x t) as R eqn:H;
  assert (H' := H); simpl in H'; rewrite H in H'; rewrite <- H' in *;
  clear H'; clear H; clear R.

Ltac fold_qrank_subst_fresh n A x x' t :=
  fold_qrank_subst n A x (fresh_var x (quant_subst_fvars x A x' t)).

Ltac deduce_rank_eq Hsame :=
  let Htemp := fresh in
  let Hfr := fresh "Hfr" in
  let Hqr := fresh "Hqr" in
  apply ranks_equal_if_shape_eq in Hsame as Htemp;
  destruct Htemp as [Hfr Hqr].

Hint Resolve shape_eq_refl : core.
Hint Resolve subst_preserves_shape : core.

Section pred_calc_semantics.
  Context {M : model}.
  Let V := value M.

  Definition state := gmap variable V.

  Inductive fn_eval fSym vargs : V → Prop :=
  | FnEval : ∀ fdef v,
      (fdefs M) !! fSym = Some fdef →
      fdef_rel fdef vargs v →
      fn_eval fSym vargs v
  | FnEvalBottom : (fdefs M) !! fSym = None → fn_eval fSym vargs ⊥.

  Inductive teval (σ : state) : term → V → Prop :=
  | TEval_Const : ∀ v, teval σ (TConst v) v
  | TEval_Var : ∀ x v, σ !!! x = v → teval σ (TVar x) v
  | TEval_App : ∀ f args vargs fval,
      teval_list σ args vargs →
      fn_eval f vargs fval →
      teval σ (TApp f args) (fval)
  with teval_list (σ : state) : list term → list V → Prop :=
  | TEvalArgs_Nil : teval_list σ [] []
  | TEvalArgs_Cons : ∀ t ts v vs,
      teval σ t v →
      teval_list σ ts vs →
      teval_list σ (t::ts) (v::vs).

  Scheme teval_ind_mut := Induction for teval Sort Prop
      with teval_list_ind_mut := Induction for teval_list Sort Prop.

  Lemma teval_det {σ} t v1 v2 :
    teval σ t v1 → teval σ t v2 → v1 = v2.
  Proof with auto.
    intros H1 H2. generalize dependent v2.
    generalize dependent v1. generalize dependent t.
    apply (teval_ind_mut σ (λ t v1 _, forall v2, teval σ t v2 → v1 = v2)
             (λ args vargs1 _, forall vargs2, teval_list σ args vargs2 → vargs1 = vargs2)).
    - intros. inversion H...
    - intros. inversion H; subst...
    - intros. inversion H0; subst. inversion H5; subst; inversion f0; subst...
      + apply H in H3. subst vargs0. rewrite H1 in H4. inversion H4; subst.
        eapply fdef_det; [exact H6 | exact H2].
      + setoid_rewrite H1 in H4. discriminate.
      + setoid_rewrite H1 in H2. discriminate.
    - inversion 1...
    - intros. destruct vargs2.
      + inversion H1.
      + inversion H1; subst. f_equal.
        * apply H...
        * apply H0...
  Qed.

  Lemma teval_total σ t : ∃ v, teval σ t v.
  Proof with auto.
    induction t.
    - exists v. constructor.
    - exists (σ !!! x). constructor...
    - assert (∃ vargs, teval_list σ args vargs) as [vargs Hvargs].
      { induction args.
        + exists []. constructor.
        + forward IHargs. { intros. apply H. right... }
          destruct IHargs as [vargs ?]. destruct (H a) as [v Hv]; [left; auto|].
          exists (v :: vargs). constructor... }
      destruct (fdefs M !! f) eqn:Hdef.
      + rename f0 into fdef. pose proof (fdef_total fdef vargs) as [v Hv]. exists v.
        econstructor.
        * exact Hvargs.
        * apply FnEval with (fdef:=fdef)...
      + exists ⊥. econstructor.
        * exact Hvargs.
        * apply FnEvalBottom...
  Qed.

  Lemma teval_list_det {σ} args vargs1 vargs2 :
    teval_list σ args vargs1 → teval_list σ args vargs2 →
    vargs1 = vargs2.
  Proof with auto.
    generalize dependent vargs2. generalize dependent vargs1.
    induction args; intros vargs₁ vargs₂ H1 H2.
    - inversion H1. inversion H2...
    - inversion H1; subst. inversion H2; subst. f_equal.
      + eapply teval_det; [apply H3 | apply H4].
      + apply IHargs...
  Qed.

  Definition peval (pSym : string) (vargs : list V) : Prop :=
    ∃ pdef, (pdefs M !! pSym = Some pdef ∧
               ∀ H : length vargs = pdef_arity pdef,
                 pdef_rel pdef (list_to_vec_n vargs H)).

  Definition afeval (σ : state) (af : atomic_formula) :=
    match af with
    | AT_True => True
    | AT_False => False
    | AT_Eq t1 t2 => ∃ v, teval σ t1 v ∧ teval σ t2 v
    | AT_Pred symbol args => ∃ vargs, teval_list σ args vargs ∧ peval symbol vargs
  end.

  Equations? feval (σ : state) (A : formula) : Prop by wf (rank A) lt :=
    feval σ (FAtom af) => afeval σ af;
    feval σ (FNot A) => ¬ feval σ A;
    feval σ (FAnd A B) => feval σ A ∧ feval σ B;
    feval σ (FOr A B) => feval σ A ∨ feval σ B;
    feval σ (FExists x A) => ∃ v : V, feval σ (<! A[x \ $(TConst v)] !>).
  Proof.
    all: try (unfold rank; simpl; fold Nat.add; lia).
    unfold rank. simpl. fold Nat.add. pose proof (subst_preserves_shape A x (TConst v)).
    deduce_rank_eq H. rewrite Hfr. rewrite Hqr. lia.
  Qed.

  (* ******************************************************************* *)
  (* LEM and decidability of feval                                       *)
  (* ******************************************************************* *)
  Axiom feval_lem : ∀ σ A, feval σ A ∨ ¬ feval σ A.

  Lemma feval_dec : ∀ σ A, Decidable.decidable (feval σ A).
  Proof. exact feval_lem. Qed.

  Lemma feval_stable σ A :
    ¬ ¬ feval σ A ↔ feval σ A.
  Proof with auto. intros. apply (Decidable.not_not_iff _ (feval_dec σ A)). Qed.

  (* ******************************************************************* *)
  (* some useful lemmas                                                  *)
  (* ******************************************************************* *)
  Lemma feval_exists_equiv_if {σ1 σ2 x1 x2} {A1 A2 : formula}:
    (∀ v, feval σ1 (<! A1 [x1 \ $(TConst v) ] !>) ↔ feval σ2 (<! A2 [x2 \ $(TConst v) ] !>)) →
    feval σ1 <! ∃ x1, A1 !> ↔ feval σ2 <! ∃ x2, A2 !>.
  Proof with auto.
    intros. simp feval. split; intros [v Hv]; exists v; apply H...
  Qed.
End pred_calc_semantics.

Arguments term V : clear implicits.
Arguments atomic_formula : clear implicits.
Arguments formula V : clear implicits.

Hint Constructors teval : core.

Notation "σ '⊨' A" := (feval σ A) (at level 100, only printing, A custom formula).

Tactic Notation "generalize_fresh_var" ident(y) constr(A) ident(x) constr(t) "as" ident(y') :=
  let Hfresh := fresh in
  let Heq := fresh in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in
  pose proof (Hfresh := fresh_var_fresh y (quant_subst_fvars y A x t));
  apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3);
  remember (fresh_var y (quant_subst_fvars y A x t)) as y' eqn:Heq;
  clear Heq.
