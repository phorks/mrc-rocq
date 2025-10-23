From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia.
From stdpp Require Import gmap vector.
From MRC Require Import Options.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import Tactics.
Open Scope bool_scope.

Definition list_to_vec_n {A n} (l : list A) (H : length l = n) : vec A n :=
  eq_rect _ (fun m => vec A m) (list_to_vec l) _ H.


Unset Elimination Schemes.
Inductive term  : Type :=
| TConst (v : value)
| TVar (x : variable)
| TApp (symbol : string) (args : list term).
Set Elimination Schemes.

Fixpoint term_rank t :=
  match t with
  | TConst _ => 0
  | TVar _ => 0
  | TApp f args => 1 + max_list_with term_rank args
  end.

Lemma term_rank_app_gt_args : forall f args arg,
    In arg args →
    term_rank arg < term_rank (TApp f args).
Proof with auto.
  intros f args arg HIn.
  simpl. unfold In in HIn. induction args.
  - destruct HIn.
  - destruct HIn as [HIn | HIn].
    + rewrite HIn in *. simpl. lia.
    + simpl in *. remember (max_list_with term_rank args) as rest.
      destruct (Nat.max_spec (term_rank a) (rest)) as [[_ H] | [_ H]]; rewrite H; try lia...
      forward IHargs... lia.
Qed.

Lemma term_formula_rank_ind : forall P,
    (forall n,
        (forall m, m < n →
              forall u, term_rank u = m → P u) →
        (forall t, term_rank t = n → P t)) →
    forall n t, term_rank t < n → P t.
Proof with auto.
  intros P Hind n. induction n; intros t Hrank.
  - lia.
  - apply Hind with (term_rank t)...
    intros m Hlt u Hu. apply IHn. lia.
Qed.

Lemma term_ind : forall P,
    (forall v, P (TConst v)) →
    (forall x, P (TVar x)) →
    (forall f args,
        (forall arg, In arg args → P arg) → P (TApp f args)) →
    (forall t, P t).
Proof with auto.
  intros P Hconst Hvar Hfunc t.
  apply (term_formula_rank_ind P) with (term_rank t + 1); try lia...
  clear t. intros n IH t Htr. destruct t...
  apply Hfunc. intros arg HIn.
  apply term_rank_app_gt_args with (f:=symbol) in HIn.
  apply IH with (term_rank arg); lia.
Qed.

Inductive simple_formula : Type :=
| AT_True
| AT_False
| AT_Eq (t1 t2 : term)
| AT_Pred (symbol : string) (args : list term).

Unset Elimination Schemes.
Inductive formula : Type :=
| FSimple (sf : simple_formula)
| FNot (A : formula)
| FAnd (A B : formula)
| FOr (A B : formula)
| FExists (x : variable) (τ : value_ty) (A : formula).
Set Elimination Schemes.
Scheme formula_ind_naive := Induction for formula Sort Type.

Coercion TConst : value >-> term.
Coercion TVar : variable >-> term.
Coercion FSimple : simple_formula >-> formula.


Declare Custom Entry formula.
Declare Scope formula_scope.
Declare Custom Entry formula_aux.
Bind Scope formula_scope with simple_formula.
Delimit Scope formula_scope with formula.

Definition FImpl A B := FOr (FNot A) B.
Definition FIff A B := FAnd (FImpl A B) (FImpl B A).
Definition FForall x τ A := FNot (FExists x τ (FNot A)).


Notation "<! e !>" := e (e custom formula_aux) : formula_scope.
Notation "e" := e (in custom formula_aux at level 0, e custom formula) : formula_scope.

Notation "( x )" := x (in custom formula, x at level 99) : formula_scope.
Notation "'`' f x .. y '`'" := (.. (f x) .. y)
                                  (in custom formula at level 0, only parsing,
                                      f constr at level 0, x constr at level 9,
                                      y constr at level 9) : formula_scope.
Notation "x" := x (in custom formula at level 0, x constr at level 0) : formula_scope.

Notation "x + y" := (TApp "+" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "x - y" := (TApp "-" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "x * y" := (TApp "*" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "f '(' x ',' .. ',' y ')'" := (TApp f (@cons term x .. (@cons term y nil) ..)) (in custom formula at level 40).

Notation "'true'"  := true (at level 1).
Notation "'true'" := (AT_True) (in custom formula at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := (AT_False) (in custom formula at level 0).
Notation "x = y" := (AT_Eq x y) (in custom formula at level 70, no associativity).
Notation "x <> y" := (FNot (FSimple (AT_Eq x y))) (in custom formula at level 70, no associativity, only parsing).
Notation "x ≠ y" := (FNot (FSimple (AT_Eq x y))) (in custom formula at level 70, no associativity, only printing).
Notation "x < y" := (AT_Pred "<" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <= y" := (AT_Pred "<=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x > y" := (AT_Pred ">" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x >= y" := (AT_Pred ">=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "'~' x" := (FNot x) (in custom formula at level 75, only parsing).
Notation "'¬' x" := (FNot x) (in custom formula at level 75, only printing).
Notation "x ∧ y" := (FAnd x y) (in custom formula at level 80, only parsing, left associativity).
Notation "x ∧ y" := (FAnd x y) (in custom formula at level 80, only printing, left associativity).
Notation "x ∨ y" := (FOr x y) (in custom formula at level 80, left associativity, only parsing).
Notation "x ∨ y" := (FOr x y) (in custom formula at level 80, left associativity, only printing).
Notation "x => y" := (FImpl x y) (in custom formula at level 80, only parsing).
Notation "x ⇒ y" := (FImpl x y) (in custom formula at level 80, only printing).
Notation "x <=> y" := (FIff x y) (in custom formula at level 80, only parsing).
Notation "x ⇔ y" := (FIff x y) (in custom formula at level 80, only printing).
Notation "'exists' x .. y ':' k ',' f" := (FExists x k .. (FExists y k f) ..) (in custom formula at level 85, only parsing).
Notation "'∃' x .. y ':' k '●' f" := (FExists x k .. (FExists y k f) ..) (in custom formula at level 85, only printing).
Notation "'forall' x .. y ':' k ',' f" := (FForall x k .. (FForall y k f) ..) (in custom formula at level 85).
Notation "'∀' x .. y ':' k '●' f" := (FForall x k .. (FForall y k f) ..) (in custom formula at level 85).

Open Scope formula_scope.

Fixpoint subst_term t x a :=
  match t with
  | TConst v => TConst v
  | TVar y => if decide (y = x) then a else TVar y
  | TApp sym args => TApp sym (map (fun arg => subst_term arg x a) args)
  end.

Definition subst_sf sf x a :=
  match sf with
  | AT_Eq t₁ t₂ => AT_Eq (subst_term t₁ x a) (subst_term t₂ x a)
  | AT_Pred sym args => AT_Pred sym (map (fun arg => subst_term arg x a) args)
  | _ => sf
  end.

Fixpoint term_fvars t : gset variable :=
  match t with
  | TConst v => ∅
  | TVar y => {[y]}
  | TApp sym args => ⋃ (map term_fvars args)
  end.

Definition sf_fvars sf : gset variable :=
  match sf with
  | AT_Eq t₁ t₂ => term_fvars t₁ ∪ term_fvars t₂
  | AT_Pred _ args => ⋃ (map term_fvars args)
  | _ => ∅
  end.

Fixpoint formula_fvars (A : formula) : gset variable :=
  match A with
  | FSimple sf => sf_fvars sf
  | FNot A => formula_fvars A
  | FAnd A B => formula_fvars A ∪ formula_fvars B
  | FOr A B => formula_fvars A ∪ formula_fvars B
  | FExists x _ A => formula_fvars A ∖ {[x]}
  end.

Fixpoint formula_rank f :=
  match f with
  | FSimple sf => 1
  | FNot A => 1 + formula_rank A
  | FAnd A B => 1 + max (formula_rank A) (formula_rank B)
  | FOr A B => 1 + max (formula_rank A) (formula_rank B)
  | FExists _ _ A => 1 + (formula_rank A)
  end.

Fixpoint quantifier_rank A :=
  match A with
  | FSimple sf => 0
  | FNot A => quantifier_rank A
  | FAnd A B => max (quantifier_rank A) (quantifier_rank B)
  | FOr A B => max (quantifier_rank A) (quantifier_rank B)
  | FExists _ _ A => 1 + (quantifier_rank A)
  end.

Notation rank A := (formula_rank A + quantifier_rank A).

Definition quant_subst_fvars y A x t := (formula_fvars A ∖ {[y]}) ∪ term_fvars t ∪ {[x]}.
Lemma quant_subst_fvars_inv : forall y' y A x t,
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
| SumQuantSubstSkipCond_False (H : x = y ∨ x ∉ formula_fvars A)
| SumQuantSubstSkipCond_True (H1 : x ≠ y) (H2: x ∈ formula_fvars A).

Definition quant_subst_skip_cond y A x : sum_quant_subst_skip_cond y A x.
Proof with auto.
  destruct (decide (x = y ∨ x ∉ formula_fvars A)).
  - apply SumQuantSubstSkipCond_False...
  - apply Decidable.not_or in n as [H1 H2]. destruct (decide (x ∈ formula_fvars A)).
    + apply SumQuantSubstSkipCond_True...
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
    | FSimple sf => FSimple (subst_sf sf x t)
    | FNot A => FNot (subst_aux A x t)
    | FAnd A₁ A₂ => FAnd
                      (subst_aux A₁ x t)
                      (subst_aux A₂ x t)
    | FOr A₁ A₂ => FOr
                      (subst_aux A₁ x t)
                      (subst_aux A₂ x t)
    | FExists y k A =>
        if quant_subst_skip_cond y A x then FExists y k A else
          let y' := fresh_var y (quant_subst_fvars y A x t) in
          match qrank with
          | 0 => FExists y k A
          | S qrank => FExists y' k
                        (subst_formula_aux qrank (subst_aux A y (TVar y')) x t)
          end
    end.

Definition subst_formula A x t :=
  subst_formula_aux (quantifier_rank A) A x t.

Notation "f [ x \ a ]" := (subst_formula f x a)
                            (at level 10, left associativity,
                              x at next level) : formula_scope.

Notation "f [ x \ a ]" := (subst_formula f x a)
                            (in custom formula at level 74, left associativity,
                                f custom formula,
                                x constr at level 0, a custom formula) : formula_scope.

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
    exists sf, A = FSimple sf.
Proof with auto.
  intros A Hr. destruct A;
    try solve [inversion Hr; auto];
    try solve [inversion Hr;
                destruct (Nat.max_spec (formula_rank A1) (formula_rank A2))
                  as [[_ H] | [_ H]]; rewrite H0 in *; auto].
  - exists sf...
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
  | FExists _ _ _ => true
  | _ => false
  end.

Definition ctor_eq A B :=
  match A, B with
  | FSimple _, FSimple _ => true
  | FNot _, FNot _ => true
  | FAnd _ _, FAnd _ _  => true
  | FOr _ _, FOr _ _ => true
  | FExists _ _ _, FExists _ _ _ => true
  | _, _ => false
  end.

Fixpoint shape_eq A B :=
  match A, B with
  | FSimple _, FSimple _ => true
  | FNot A, FNot B => shape_eq A B
  | FAnd A1 A2, FAnd B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
  | FOr A1 A2, FOr B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
  | FExists _ _ A, FExists _ _ B => shape_eq A B
  | _, _ => false
  end.

Lemma shape_eq__ctor_eq : forall A B,
    shape_eq A B = true →
    ctor_eq A B = true.
Proof with auto.
  intros. destruct A; destruct B; try discriminate...
Qed.

Lemma ctor_eq_simple : forall sf B,
    ctor_eq (FSimple sf) B = true →
    exists sf', B = FSimple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Lemma shape_eq_simple : forall sf B,
    shape_eq (FSimple sf) B = true →
    exists sf', B = FSimple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Lemma ctor_eq_not : forall A1 B,
    ctor_eq <! ~ A1 !> B = true →
    exists B1, B = <! ~ B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Lemma shape_eq_not : forall A1 B,
    shape_eq <! ~ A1 !> B = true →
    exists B1, B = <! ~ B1 !> ∧ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Lemma ctor_eq_and : forall A1 A2 B,
    ctor_eq <! A1 ∧ A2 !> B = true →
    exists B1 B2, B = <! B1 ∧ B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Lemma shape_eq_and : forall A1 A2 B,
    shape_eq <! A1 ∧ A2 !> B = true →
    exists B1 B2, B = <! B1 ∧ B2 !> ∧
                shape_eq A1 B1 = true ∧
                shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Lemma ctor_eq_or : forall A1 A2 B,
    ctor_eq <! A1 ∨ A2 !> B = true →
    exists B1 B2, B = <! B1 ∨ B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Lemma shape_eq_or : forall A1 A2 B,
    shape_eq <! A1 ∨ A2 !> B = true →
    exists B1 B2, B = <! B1 ∨ B2 !> ∧
                            shape_eq A1 B1 = true ∧
                            shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Lemma ctor_eq_exists : forall x τ A1 B,
    ctor_eq <! exists x : τ, A1 !> B = true →
                    exists x' τ' B1, B = <! exists x' : τ', B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, τ0, B...
Qed.

Lemma shape_eq_exists : forall x τ A1 B,
    shape_eq <! exists x : τ, A1 !> B = true →
                      exists x' τ' B1, B = <! exists x' : τ', B1 !> ∧ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, τ0, B...
Qed.

Lemma shape_eq_refl : forall A,
    shape_eq A A = true.
Proof with auto.
  intros. induction A using formula_ind_naive; simpl; auto; apply Bool.andb_true_iff...
Qed.

Lemma shape_eq_sym : forall A B,
    shape_eq A B = true →
    shape_eq B A = true.
Proof with auto.
  induction A using formula_ind_naive; destruct B; try discriminate; simpl; auto;
    try repeat rewrite Bool.andb_true_iff; intros [H1 H2]...
Qed.

Lemma shape_eq_trans : forall A B C,
    shape_eq A B = true →
    shape_eq B C = true →
    shape_eq A C = true.
Proof with auto.
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

Lemma rank_eq_if_shape_eq : forall A B,
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

Lemma subst_preserves_shape_aux : forall A x a r,
    shape_eq A (subst_formula_aux r A x a) = true.
Proof with auto.
  intros A.
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

Lemma subst_preserves_shape : forall A x a,
    shape_eq (A[x \ a]) A  = true.
Proof with auto.
  intros. unfold subst_formula. apply shape_eq_sym. apply subst_preserves_shape_aux. Qed.

Hint Resolve subst_preserves_shape : core.

Lemma formula_ind : forall P,
    (forall sf, P (FSimple sf)) →
    (forall A, P A → P <! ~ A !>) →
    (forall A₁ A₂, P A₁ → P A₂ → P <! A₁ ∧ A₂ !>) →
    (forall A₁ A₂, P A₁ → P A₂ → P <! A₁ ∨ A₂ !>) →
    (forall x τ A, (forall B, shape_eq B A = true → P B) → P <! exists x : τ, A !>) →
    forall A, P A.
Proof with auto.
  intros P Hsf Hnot Hand Hor Hexists A.
  induction A using formula_rank_ind. destruct A; subst; simpl in *.
  - apply Hsf.
  - apply Hnot. apply X with (rank A); lia.
  - apply Hand; [apply X with (rank A1) | apply X with (rank A2)]; lia.
  - apply Hor; [apply X with (rank A1) | apply X with (rank A2)]; lia.
  - apply Hexists. intros. apply X with (rank B); auto.
    apply rank_eq_if_shape_eq in H. lia.
Qed.


Section semantics.
  Context (M : model).

  Definition state := gmap variable (value).
  Definition state_covers_term (σ : state) (t : term) := term_fvars t ⊆ dom σ.
  Definition state_covers_sf (σ : state) (sf : simple_formula) := sf_fvars sf ⊆ dom σ.
  Definition state_covers (σ : state) (A : formula) := formula_fvars A ⊆ dom σ.

  Definition state_typing := gmap variable value_ty.
  Definition state_types (σ : state) := value_typeof <$> σ.

  Lemma state_types_insert {σ x v} :
    state_types (<[x:=v]> σ) = <[x:=value_typeof v]> (state_types σ).
  Proof. unfold state_types. rewrite (fmap_insert _ σ). reflexivity. Qed.


  Fixpoint args_wf_aux (arg_kinds : list (option value_ty)) (sig : list value_ty) : bool :=
    match arg_kinds, sig with
    | [], [] => true
    | (Some arg) :: args, param :: params =>
        if arg =? param
        then args_wf_aux args params
        else false
    | _, _ => false
    end.

  Fixpoint term_ty (Γ : state_typing) (t : term) : option value_ty :=
    match t with
    | TConst v => Some (value_typeof v)
    | TVar x => Γ !! x
    | TApp symbol args =>
        match (model_fdefs M !! symbol) with
        | Some fdef =>
            let sig := fdef_sig fdef in
            if args_wf_aux (term_ty Γ <$> args) (sig.1) then Some (sig.2) else None
        | None => None
        end
    end.

  Definition term_has_type Γ t τ :=
    term_ty Γ t = Some τ.

  Definition term_wf_aux (Γ : state_typing) (t : term) : bool :=
    match term_ty Γ t with | Some _ => true | None => false end.

  Definition term_args_match_sig (Γ : state_typing) (args : list term) (sig : list value_ty) :=
    args_wf_aux (term_ty Γ <$> args) sig.

  Definition sf_wf_aux (Γ : state_typing) (sf : simple_formula) : bool :=
    match sf with
    | AT_True => true
    | AT_False => true
    | AT_Eq t₁ t₂ => term_wf_aux Γ t₁ && term_wf_aux Γ t₂
    | AT_Pred symbol args =>
        match (model_pdefs M !! symbol) with
        | Some pdef => term_args_match_sig Γ args (pdef_sig pdef)
        | None => false
        end
    end.

  Fixpoint formula_wf_aux (Γ : state_typing) (A : formula) : bool :=
    match A with
    | FSimple sf => sf_wf_aux Γ sf
    | FNot A => formula_wf_aux Γ A
    | FAnd A B => formula_wf_aux Γ A && formula_wf_aux Γ B
    | FOr A B => formula_wf_aux Γ A && formula_wf_aux Γ B
    | FExists x τ A => formula_wf_aux (<[x:=τ]> Γ) A
    end.

  (*
      wf implies that:
      1. All functions and predicates are invoked with the correct number and
          types of arguments.
      2. Every free variable has a value in the state
   *)
  Notation term_wf σ := (term_wf_aux (state_types σ)).
  Notation term_args_wf σ := (forallb (term_wf σ)).
  Notation sf_wf σ := (sf_wf_aux (state_types σ)).
  Notation formula_wf σ := (formula_wf_aux (state_types σ)).

  Inductive fn_eval (fSym : string) (vargs : list value) : value → Prop :=
  | FnEval : ∀ v fdef,
      (model_fdefs M) !! fSym = Some fdef →
      ∀ Hsig : args_match_sig vargs (fdef_sig fdef).1,
      ∀ Hret : v ∈ (fdef_sig fdef).2,
        fdef_rel fdef vargs Hsig v Hret →
        fn_eval fSym vargs v.

  Inductive teval (σ : state) : term → value → Prop :=
  | TEval_Const : forall v, teval σ (TConst v) v
  | TEval_Var : forall x v, σ !! x = Some v → teval σ (TVar x) v
  | TEval_App : forall f args vargs fval,
      teval_args σ args vargs →
      fn_eval f vargs fval →
      teval σ (TApp f args) (fval)
  with teval_args (σ : state) : list term → list value → Prop :=
  | TEvalArgs_Nil : teval_args σ [] []
  | TEvalArgs_Cons : forall t ts v vs,
      teval σ t v →
      teval_args σ ts vs →
      teval_args σ (t::ts) (v::vs).

  Scheme teval_ind_mut := Induction for teval Sort Prop
      with teval_args_ind_mut := Induction for teval_args Sort Prop.

  Lemma teval_det : forall {σ t v₁ v₂},
      teval σ t v₁ → teval σ t v₂ → v₁ = v₂.
  Proof with auto.
    intros σ t v₁ v₂ H1 H2. generalize dependent v₂.
    generalize dependent v₁. generalize dependent t.
    apply (teval_ind_mut σ (λ t v₁ _, forall v₂, teval σ t v₂ → v₁ = v₂)
             (λ args vargs₁ _, forall vargs₂, teval_args σ args vargs₂ → vargs₁ = vargs₂)).
    - intros. inversion H...
    - intros. inversion H; subst. rewrite e in H1. inversion H1...
    - intros. inversion H0; subst. inversion H5; subst. inversion f0; subst.
      apply H in H3. subst vargs0. rewrite H1 in H4. inversion H4; subst.
      eapply fdef_det.
      + exact H6.
      + exact H2.
    - inversion 1...
    - intros. destruct vargs₂.
      + inversion H1.
      + inversion H1; subst. f_equal.
        * apply H...
        * apply H0...
  Qed.


  Lemma teval_args_det : ∀ {σ args vargs₁ vargs₂},
      teval_args σ args vargs₁ → teval_args σ args vargs₂ →
      vargs₁ = vargs₂.
  Proof with auto.
    intros σ. induction args; intros vargs₁ vargs₂ H1 H2.
    - inversion H1. inversion H2...
    - inversion H1; subst. inversion H2; subst. f_equal.
      + eapply teval_det; [apply H3 | apply H4].
      + apply IHargs...
  Qed.

  Inductive peval (pSym : string) (vargs : list value) : bool → Prop :=
  | PEval_True : ∀ pdef,
      model_pdefs M !! pSym = Some pdef →
      ∀ Hsig : args_match_sig vargs (pdef_sig pdef),
        pdef_rel pdef vargs Hsig →
        peval pSym vargs true
  | PEval_False : ∀ pdef,
      model_pdefs M !! pSym = Some pdef →
      ∀ Hsig : args_match_sig vargs (pdef_sig pdef),
        ¬ pdef_rel pdef vargs Hsig →
        peval pSym vargs false.

  Inductive sfeval (σ : state) : simple_formula → bool → Prop :=
  | SFEval_True : sfeval σ AT_True true
  | SFEval_False : sfeval σ AT_False false
  | SFEval_Eq_True : ∀ t1 t2 v,
      teval σ t1 v →
      teval σ t2 v →
      sfeval σ (AT_Eq t1 t2) true
  | SFEval_Eq_False : ∀ t1 t2 v1 v2,
      teval σ t1 v1 →
      teval σ t2 v2 →
      v1 ≠ v2 →
      sfeval σ (AT_Eq t1 t2) false
  | SFEval_Pred : ∀ pSym args vargs b,
      teval_args σ args vargs →
      peval pSym vargs b →
      sfeval σ (AT_Pred pSym args) b.

  Inductive feval (σ : state) : formula → bool → Prop :=
  | FEval_Simple : ∀ sf b, sfeval σ sf b → feval σ (FSimple sf) b
  | FEval_Not : ∀ A b, feval σ A b → feval σ (FNot A) (negb b)
  | FEval_And : ∀ A B b1 b2, feval σ A b1 → feval σ B b2 → feval σ (FAnd A B) (b1 && b2)
  | FEval_Or : ∀ A B b1 b2, feval σ A b1 → feval σ B b2 → feval σ (FOr A B) (b1 || b2)
  | FEval_Exists_True : ∀ x τ A,
      (∃ v, v ∈ τ ∧ feval (<[x:=v]> σ) A true) →
      feval σ (FExists x τ A) true
  | FEval_Exists_False : ∀ x τ A,
      (∃ v, v ∈ τ) →
      (∀ v, v ∈ τ → feval (<[x:=v]> σ) A false) →
      feval σ (FExists x τ A) false
  | FEval_Exists_False_Empty : ∀ x τ A,
      value_ty_is_empty τ →
      formula_wf_aux (<[x:=τ]> (state_types σ)) A →
      feval σ (FExists x τ A) false.


  (* ******************************************************************* *)
  (* wf and state_covers facts                                           *)
  (* ******************************************************************* *)
  Lemma term_wf_insert_state x v τ σ t :
    v ∈ τ →
    term_wf (<[x:=v]> σ) t ↔ term_wf_aux (<[x:=τ]> (state_types σ)) t.
  Proof.
    intros. unfold state_types. unfold state.
    rewrite fmap_insert. rewrite value_elem_of_iff_typeof_eq in H.
    apply eq_dec_eq in H. rewrite H. reflexivity.
  Qed.

  Lemma sf_wf_insert_state x v τ σ sf :
    v ∈ τ →
    sf_wf (<[x:=v]> σ) sf ↔ sf_wf_aux (<[x:=τ]> (state_types σ)) sf.
  Proof.
    intros. unfold state_types. unfold state.
    rewrite fmap_insert. rewrite value_elem_of_iff_typeof_eq in H.
    apply eq_dec_eq in H. rewrite H. reflexivity.
  Qed.

  Lemma formula_wf_insert_state x v τ σ A :
    v ∈ τ →
    formula_wf (<[x:=v]> σ) A ↔ formula_wf_aux (<[x:=τ]> (state_types σ)) A.
  Proof.
    intros. unfold state_types. unfold state.
    rewrite fmap_insert. rewrite value_elem_of_iff_typeof_eq in H.
    apply eq_dec_eq in H. rewrite H. reflexivity.
  Qed.

  Lemma term_ty_delete_state_var x {Γ t} :
    x ∉ term_fvars t →
    term_ty Γ t = term_ty (delete x Γ) t.
  Proof with auto.
    intros. induction t; simpl...
    - simpl in H. rewrite not_elem_of_singleton in H. rewrite (lookup_delete_ne Γ)...
    - simpl in H. destruct (model_fdefs M !! f)...
      enough (term_ty Γ <$> args = term_ty (delete x Γ) <$> args).
      { rewrite H1.  reflexivity. }
      induction args... simpl. simpl in H. apply not_elem_of_union in H as []. f_equal.
      + apply H0... left...
      + apply IHargs... intros. apply H0... right...
  Qed.

  Lemma term_wf_delete_state_var x t Γ :
    x ∉ term_fvars t →
    term_wf_aux Γ t = term_wf_aux (delete x Γ) t.
  Proof with auto.
    intros. unfold term_wf_aux. rewrite (term_ty_delete_state_var x)...
  Qed.

  Lemma sf_wf_delete_state_var x Γ sf :
    x ∉ sf_fvars sf →
    sf_wf_aux Γ sf = sf_wf_aux (delete x Γ) sf.
  Proof with auto.
    destruct sf; intros...
    - simpl in *. apply not_elem_of_union in H as [].
      rewrite <- term_wf_delete_state_var...
      rewrite <- term_wf_delete_state_var...
    - simpl in *. destruct (model_pdefs M !! symbol)... remember (pdef_sig p) as sig.
      clear Heqsig. generalize dependent sig. induction args; simpl in *...
      intros. apply not_elem_of_union in H as []. unfold term_args_match_sig.
      destruct sig; simpl; rewrite <- term_ty_delete_state_var...
      unfold term_args_match_sig in IHargs. rewrite IHargs...
  Qed.

  Lemma formula_wf_delete_state_var x Γ A :
    x ∉ formula_fvars A →
    formula_wf_aux Γ A = formula_wf_aux (delete x Γ) A.
  Proof with auto.
    generalize dependent Γ. induction A; simpl; intros...
    - apply sf_wf_delete_state_var...
    - apply not_elem_of_union in H as []. f_equal; [apply IHA1 | apply IHA2]...
    - apply not_elem_of_union in H as []. f_equal; [apply IHA1 | apply IHA2]...
    - apply not_elem_of_difference in H0 as [].
      + destruct (decide (x = x0)).
        * f_equal. subst. rewrite (insert_delete_insert Γ)...
        * rewrite H... f_equal. rewrite (delete_insert_ne Γ)...
      + rewrite elem_of_singleton in H0. subst. rewrite (insert_delete_insert Γ)...
  Qed.

  Lemma term_ty_delete_state_var_head x τ Γ t :
    x ∉ term_fvars t →
    term_ty (<[x:=τ]> Γ) t = term_ty Γ t.
  Proof with auto.
    intros. etrans.
    - apply term_ty_delete_state_var. exact H.
    - rewrite (delete_insert_delete Γ). rewrite <- term_ty_delete_state_var...
  Qed.

  Lemma term_wf_delete_state_var_head x τ Γ t :
    x ∉ term_fvars t →
    term_wf_aux (<[x:=τ]> Γ) t = term_wf_aux Γ t.
  Proof with auto.
    intros. etrans.
    - apply term_wf_delete_state_var. exact H.
    - rewrite (delete_insert_delete Γ). rewrite <- term_wf_delete_state_var...
  Qed.

  Lemma formula_wf_delete_state_var_head x τ Γ A :
    x ∉ formula_fvars A →
    formula_wf_aux (<[x:=τ]> Γ) A = formula_wf_aux Γ A.
  Proof with auto.
    intros. etrans.
    - apply formula_wf_delete_state_var. exact H.
    - rewrite (delete_insert_delete Γ). rewrite <- formula_wf_delete_state_var...
  Qed.

  Lemma teval_term_ty' σ t v τ :
    teval σ t v →
    v ∈ τ ↔ term_ty (state_types σ) t = Some τ.
  Proof with auto.
    intros H. generalize dependent v. generalize dependent τ. induction t; intros v0; intros.
    - simpl in *. setoid_rewrite value_elem_of_iff_typeof_eq.
      inversion H; subst. rewrite eq_dec_eq. split; intros.
      + f_equal...
      + inversion H0...
    - simpl in *. inversion H; subst.
      setoid_rewrite value_elem_of_iff_typeof_eq. unfold state_types. unfold state_typing.
      rewrite lookup_fmap. setoid_rewrite H1. simpl. rewrite eq_dec_eq.
      split; intros.
      + f_equal...
      + inversion H0...
    - inversion H0; subst. inversion H5; subst. unfold term_ty. rewrite H1. fold term_ty.
      enough (args_wf_aux (term_ty (state_types σ) <$> args) (fdef_sig fdef).1).
      { apply Is_true_eq_true in H4. rewrite H4. split; intros.
        - f_equal. apply value_elem_of_det with v...
        - inversion H6... }
      unfold args_match_sig in Hsig. unfold args_wf_aux. clear H0. clear H5 H2.
      fold args_wf_aux. fold args_match_sig in *.
      remember ((fdef_sig fdef).1) as sig. clear Heqsig.
      generalize dependent sig.
      generalize dependent vargs. induction args; intros.
      + inversion H3; subst. simpl in *. assumption.
      + inversion H3; subst. simpl in *. pose proof (IH:=H). forward (H a) by (left; auto).
        destruct sig; try contradiction.
        apply (H v2) in H4.
        forward IHargs. { intros. apply IH; [right|]... }
        forward (IHargs vs) by auto.
        destruct (v1 ∈? v2) eqn:E; [| contradiction].
        apply IHargs in Hsig. apply bool_decide_eq_true in E. apply H4 in E. rewrite E.
        rewrite eq_dec_refl. assumption.
    Qed.

  Lemma teval_term_ty {σ t v} :
    teval σ t v →
    term_ty (state_types σ) t = Some (value_typeof v).
  Proof with auto.
    intros. apply teval_term_ty' with (τ:=value_typeof v) in H. apply H.
    apply value_elem_of_iff_typeof_eq...
  Qed.

  Lemma teval_term_has_type {σ t v} :
    teval σ t v →
    term_has_type (state_types σ) t (value_typeof v).
  Proof with auto. intros. apply teval_term_ty in H... Qed.

  Lemma args_match_sig_args_wf σ args vargs sig :
    teval_args σ args vargs →
    args_match_sig vargs sig ↔ args_wf_aux (term_ty (state_types σ) <$> args) sig.
  Proof with auto.
    intros H. generalize dependent vargs. generalize dependent sig.
    induction args; intros.
    - inversion H; subst. simpl. reflexivity.
    - inversion H; subst. clear H. simpl in *. split; intros.
      + destruct sig; try contradiction. apply teval_term_ty' with (τ:=v0) in H2.
        destruct (v ∈? v0) eqn:E; [|contradiction].
        rewrite bool_decide_eq_true in E. apply H2 in E. rewrite E. rewrite eq_dec_refl.
        apply (IHargs sig) in H4. rewrite <- H4...
      + destruct sig.
        1:{ destruct (term_ty (state_types σ) a); try contradiction. }
        apply teval_term_ty' with (τ:=v0) in H2.
        destruct (term_ty (state_types σ) a); [|contradiction].
        destruct (v1 =? v0) eqn:Heq; [|contradiction].
        rewrite bool_decide_eq_true in Heq. subst.
        destruct (v ∈? v0) eqn:E.
        2:{ rewrite bool_decide_eq_false in E. apply E. apply H2. reflexivity. }
        apply IHargs...
    Qed.

  Lemma teval_wf {σ} t v :
      teval σ t v → term_wf σ t.
  Proof with auto.
    induction t; intros; simpl...
    - inversion H; subst. unfold term_wf_aux, term_ty, state_types, state_typing.
      rewrite lookup_fmap. setoid_rewrite H1. simpl...
    - inversion H0; subst. unfold term_wf_aux. simpl. inversion H5; subst.
      rewrite H1. clear H2. rewrite args_match_sig_args_wf in Hsig.
      2: { exact H3. } apply Is_true_true in Hsig. rewrite Hsig...
  Qed.

  Lemma term_wf_teval {σ} t :
    term_wf σ t → ∃ v, teval σ t v.
  Proof with auto.
    intros. unfold term_wf in H. destruct (term_ty (state_types σ) t) eqn:E; [| contradiction].
    rename v into τ. generalize dependent τ.
    induction t; intros; simpl...
    - exists v. constructor.
    - unfold term_ty, state_types in E. apply lookup_fmap_Some in E.
      destruct E as [v [_ Hv]]. exists v. constructor...
    - simpl in E. destruct (model_fdefs M !! f) eqn:E1; [| discriminate].
      rename f0 into fdef.
      destruct (args_wf_aux (term_ty (state_types σ) <$> args) (fdef_sig fdef).1) eqn:E2;
        [| discriminate].
      assert (∃ vargs, teval_args σ args vargs ∧ args_match_sig vargs ((fdef_sig fdef).1)).
      + clear E. remember ((fdef_sig fdef).1) as sig; clear Heqsig. generalize dependent sig.
        induction args; intros.
        * exists []. split... apply TEvalArgs_Nil.
        * unfold args_wf_aux in E2. destruct sig.
          { simpl in E2. destruct (term_ty (state_types σ) a); discriminate. }
          rewrite fmap_cons in E2. destruct (term_ty (state_types σ) a) eqn:E3; [| discriminate].
          destruct (v0 =? v) eqn:E4; [| discriminate]. fold args_wf_aux in E2.
          apply Is_true_true in E4. apply eq_dec_eq in E4. subst. forward IHargs.
          { intros. eapply H0; [right | apply E]... }
          rename v into τ1.
          apply IHargs in E2. destruct E2 as [vargs []].
          apply (H0 a) in E3 as ?; [| left]... destruct H3 as [v Hv].
          exists (v :: vargs). split.
          -- apply TEvalArgs_Cons...
          -- simpl. destruct (v ∈? τ1) eqn:E... apply teval_term_ty' with (τ:=τ1) in Hv.
             apply Hv in E3. apply Is_true_false in E. set_solver.
      + destruct H1 as [vargs []]. pose proof (fdef_total fdef vargs H2).
        destruct H3 as (v&Hret&?). exists v. apply TEval_App with vargs...
        eapply FnEval.
        * apply E1.
        * apply H3.
  Qed.

  Lemma sfeval_wf : ∀ {σ sf b},
      sfeval σ sf b → sf_wf σ sf.
  Proof with auto.
    intros. destruct sf; simpl in *...
    - inversion H; subst; (apply Is_true_andb; split; eapply teval_wf; [apply H2 |]).
      + apply H4.
      + apply H3.
    - inversion H; subst. inversion H4; subst.
      + rewrite H0. unfold term_args_match_sig. clear H1.
        rewrite args_match_sig_args_wf in Hsig. 2: { apply H2. } assumption.
      + rewrite H0. unfold term_args_match_sig. clear H1.
        rewrite args_match_sig_args_wf in Hsig. 2: { apply H2. } assumption.
  Qed.

  Lemma feval_wf : ∀ {σ A b},
      feval σ A b → formula_wf σ A.
  Proof with auto.
    intros. generalize dependent σ. generalize dependent b. induction A; simpl; intros.
    - eapply sfeval_wf. inversion H; subst. exact H1.
    - inversion H; subst. apply IHA in H1...
    - inversion H; subst. apply Is_true_andb. apply IHA1 in H2. apply IHA2 in H4. split...
    - inversion H; subst. apply Is_true_andb. apply IHA1 in H2. apply IHA2 in H4. split...
    - inversion H0; subst...
      + destruct H5 as [v []]. apply H in H2; [| apply shape_eq_refl].
        apply formula_wf_insert_state with (v:=v)...
      + destruct H5 as [v Hv]. apply H6 in Hv as H1. apply H in H1; [| apply shape_eq_refl].
        apply formula_wf_insert_state with (v:=v)...
  Qed.

  Lemma term_wf_aux_state_covers : ∀ {Γ t},
      term_wf_aux Γ t → term_fvars t ⊆ dom Γ.
  Proof with auto.
    unfold state_covers_term. induction t; simpl; intros.
    - apply empty_subseteq.
    - unfold term_wf_aux in H. destruct (term_ty Γ x) eqn:E; [|contradiction].
      simpl in E. apply singleton_subseteq_l. apply elem_of_dom. unfold is_Some. exists v...
    - unfold term_wf_aux in H0. simpl in H0. destruct (model_fdefs M !! f); [|contradiction].
      destruct (args_wf_aux (term_ty Γ <$> args) (fdef_sig f0).1) eqn:E;
        [|contradiction]. remember ((fdef_sig f0).1) as sig. clear Heqsig.
      generalize dependent sig. induction args; [set_solver|]. intros. simpl.
      pose proof (IH:=H). forward (H a) by (left; auto). simpl in E.
      destruct (term_ty Γ a) eqn:E1; [|discriminate].
      destruct sig eqn:E2; [discriminate|]. destruct (v =? v0) eqn:E3; [|discriminate].
      rewrite <- Is_true_true in E3. apply eq_dec_eq in E3. subst.
      forward IHargs. { intros. apply IH... right... } clear IH. forward (IHargs l) by apply E.
      forward H. { unfold term_wf. rewrite E1... } set_solver.
  Qed.

  Lemma term_wf_state_covers : ∀ {σ t},
      term_wf σ t → state_covers_term σ t.
  Proof. intros. apply term_wf_aux_state_covers in H. set_solver. Qed.

  Lemma teval_state_covers {σ t v} : teval σ t v → state_covers_term σ t.
  Proof. intros. apply term_wf_state_covers. apply teval_wf in H. assumption. Qed.

  Lemma sf_wf_aux_state_covers : ∀ {Γ sf},
      sf_wf_aux Γ sf → sf_fvars sf ⊆ dom Γ.
  Proof with auto.
    unfold state_covers_sf. destruct sf; simpl; try set_solver; intros.
    - apply Is_true_andb in H as []. apply term_wf_aux_state_covers in H, H0.
      unfold state_covers_term in H, H0. set_solver.
    - destruct (model_pdefs M !! symbol); [|contradiction].
      remember (pdef_sig p) as sig. clear Heqsig. generalize dependent sig.
      induction args; [set_solver|]. intros. unfold term_args_match_sig in H.
      simpl in H. destruct (term_ty Γ a) eqn:E1; [|contradiction].
      destruct sig eqn:E2; [contradiction|]. destruct (v =? v0) eqn:E3; [|contradiction].
      rewrite <- Is_true_true in E3. apply eq_dec_eq in E3. subst.
      forward (IHargs l) by apply H. simpl.
      enough (term_fvars a ⊆ dom Γ) by set_solver. apply term_wf_aux_state_covers.
      unfold term_wf. rewrite E1...
  Qed.

  Lemma sf_wf_state_covers : ∀ {σ sf},
      sf_wf σ sf → state_covers_sf σ sf.
  Proof. intros. apply sf_wf_aux_state_covers in H. set_solver. Qed.

  Lemma sfeval_state_covers {σ sf b} : sfeval σ sf b → state_covers_sf σ sf.
  Proof. intros. apply sf_wf_state_covers. apply sfeval_wf in H. assumption. Qed.

  Lemma formula_wf_aux_state_covers : ∀ {Γ A},
      formula_wf_aux Γ A → formula_fvars A ⊆ dom Γ.
  Proof with auto.
    intros. generalize dependent Γ. induction A; simpl; intros.
    - apply sf_wf_aux_state_covers...
    - apply IHA...
    - simpl. apply Is_true_andb in H as []. apply IHA1 in H. apply IHA2 in H0. set_solver.
    - simpl. apply Is_true_andb in H as []. apply IHA1 in H. apply IHA2 in H0. set_solver.
    - apply H in H0; [|apply shape_eq_refl]. set_solver.
  Qed.

  Lemma formula_wf_state_covers : ∀ {σ A},
      formula_wf σ A → state_covers σ A.
  Proof. intros. apply formula_wf_aux_state_covers in H. set_solver. Qed.

  Lemma feval_state_covers {σ A b} : feval σ A b → state_covers σ A.
  Proof. intros. apply formula_wf_state_covers. apply feval_wf in H. assumption. Qed.

  (* ******************************************************************* *)
  (* LEM                                                                 *)
  (* ******************************************************************* *)
  Axiom feval_lem : ∀ σ A, formula_wf σ A → ∃ b, feval σ A b.

  Lemma feval_lem' : forall σ A, formula_wf σ A → feval σ A true ∨ feval σ A false.
  Proof. intros. apply feval_lem in H as [[] H]; auto. Qed.


  (* ******************************************************************* *)
  (* some equiv lemmas                                                   *)
  (* ******************************************************************* *)
  Lemma feval_exists_equiv {σ1 σ2 x1 x2 τ A1 A2} b:
    ((∃ v, v ∈ τ) →
     ∀ v b', v ∈ τ →
          feval (<[x1:=v]> σ1) A1 b' ↔ feval (<[x2:=v]> σ2) A2 b') →
    (value_ty_is_empty τ →
     formula_wf_aux (<[x1:=τ]> (state_types σ1)) A1 =
       formula_wf_aux (<[x2:=τ]> (state_types σ2)) A2) →
    feval σ1 <! exists x1 : τ, A1 !> b ↔ feval σ2 <! exists x2 : τ, A2 !> b.
  Proof with eauto.
    intros. split; inversion 1; subst.
    - apply FEval_Exists_True. destruct H6 as [v []]. forward H... apply (H v true) in H3...
    - apply FEval_Exists_False... intros. apply H...
    - apply FEval_Exists_False_Empty... rewrite <- H0...
    - apply FEval_Exists_True. destruct H6 as [v []]. forward H... apply (H v true) in H3...
    - apply FEval_Exists_False... intros. apply H...
    - apply FEval_Exists_False_Empty... rewrite H0...
  Qed.
End semantics.

(* (* if x ∈ FV(A) and y is a variable, then FV(A[x \ y]) = FV(A) ∪ {[y]} \ {[x]}  *) *)
(* TODO: remove this *)
(* (* if x ∈ FV(A) and y is a variable, then FV(A[x \ y]) = FV(A) ∪ {[y]} \ {[x]}  *) *)
(* (* if (Qy. A)[x \ t] = (Qx. A[x \ t]), then x ∉ FV(A) hence ≡ (Qx. A) *) *)
(* Lemma temp : forall (x y : variable) A, *)
(*     x ∈ formula_fvars A → *)
(*     formula_fvars (<! A[x \ y] !>) = formula_fvars A ∪ {[y]} ∖ {[x]}. *)
(* Proof. *)

Notation term_wf M σ := (term_wf_aux M (state_types σ)).
Notation term_args_wf M σ := (forallb (term_wf M σ)).
Notation sf_wf M σ := (sf_wf_aux M (state_types σ)).
Notation formula_wf M σ := (formula_wf_aux M (state_types σ)).
Hint Constructors teval : core.
Hint Constructors sfeval : core.
Hint Constructors feval : core.

Tactic Notation "generalize_fresh_var" ident(y) constr(A) ident(x) ident(t) "as" ident(y') :=
  let Hfres := fresh in
  let Heq := fresh in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in
  pose proof (Hfresh := fresh_var_fresh y (quant_subst_fvars y A x t));
  apply quant_subst_fvars_inv in Hfresh as (H1&H2&H3);
  remember (fresh_var y (quant_subst_fvars y A x t)) as y' eqn:Heq;
  clear Heq.
