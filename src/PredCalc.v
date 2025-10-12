From Stdlib Require Import Strings.String.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From stdpp Require Import gmap vector.
From MRC Require Import Tactics.
Open Scope bool_scope.

Definition list_to_vec_n {A n} (l : list A) (H : length l = n) : vec A n :=
  eq_rect _ (fun m => vec A m) (list_to_vec l) _ H.


Definition value := {t : Type & t}.

Record variable := mkVar {
  var_name : string;
  var_sub : nat;
  var_is_initial : bool;
}.

Global Instance variable_eq_dec : EqDecision variable. Proof. solve_decision. Defined.
Global Instance variable_countable : Countable variable.
Proof.
  refine (
    {| encode v := encode (var_name v, var_sub v, var_is_initial v);
       decode t :=
         match decode t with
         | Some (n, s, i) => Some (mkVar n s i)
         | None => None
         end
    |}).
  intros [n s i]. simpl. rewrite decode_encode. reflexivity.
Defined.

Definition simple_var name := mkVar name 0 false.
Definition var_with_sub x i :=
  mkVar (var_name x) (i) (var_is_initial x).
Definition var_increase_sub x i :=
  var_with_sub x (var_sub x + i).

Lemma var_with_sub_var_sub_id : forall x,
    var_with_sub x (var_sub x) = x.
Proof. intros. unfold var_with_sub. destruct x. reflexivity. Qed.
Lemma var_with_sub_idemp : forall x i j,
  var_with_sub (var_with_sub x j) i = var_with_sub x i.
Proof. intros. unfold var_with_sub. reflexivity. Qed.
Lemma var_sub_of_var_with_sub : forall x i,
    var_sub (var_with_sub x i) = i.
Proof. reflexivity. Qed.
(* Lemma var_with_sub_var_sub_id : forall x, *)
(*     var_with_sub x (var_sub x) = x. *)
(* Proof. intros. unfold var_with_sub. destruct x. reflexivity. Qed. *)

Hint Rewrite var_with_sub_var_sub_id : core.
Hint Rewrite var_with_sub_idemp : core.
(* Lemma var_with_sub_eq_increase_sub : forall x n, *)
(*     var_sub x <= n -> *)
(*     var_with_sub x (n) = var_increase_sub x (n - var_sub x). *)
(* Proof. *)

Coercion simple_var : string >-> variable.

Unset Elimination Schemes.
Inductive term : Type :=
  | TConst (v : value)
  | TVar (x : variable)
  | TApp (symbol : string) (args : list term).
Set Elimination Schemes.

Fixpoint term_rank t :=
  match t with
  | TConst _ => 0
  | TVar _ => 0
  | TApp f args => 1
    + fold_right max 0 (map (fun arg => term_rank arg) args)
  end.

Lemma term_rank_app_gt_args : forall f args arg,
  In arg args ->
  term_rank arg < term_rank (TApp f args).
Proof with auto.
  intros f args arg HIn.
  simpl. unfold In in HIn. induction args.
  - destruct HIn.
  - destruct HIn as [HIn | HIn].
    + rewrite HIn in *. simpl. lia.
    + simpl in *. remember (fold_right Init.Nat.max 0
        (map (fun arg0 : term => term_rank arg0) args)) as others.
      assert (HMax :=
        (Nat.max_spec (term_rank a) (others))).
      destruct HMax as [[H1 H2] | [H1 H2]]; rewrite H2; try lia...
      * forward IHargs... lia.
Qed. (* TODO: I did this proof blindly, maybe it can be simplified *)

Lemma term_formula_rank_ind : forall P,
  (forall n,
    (forall m, m < n ->
      forall u, term_rank u = m -> P u) ->
    (forall t, term_rank t = n -> P t)) ->
  forall n t, term_rank t < n -> P t.
Proof with auto.
  intros P Hind n. induction n; intros t Hrank.
  - lia.
  - apply Hind with (term_rank t)...
    intros m Hlt u Hu. apply IHn. lia.
Qed.

Lemma term_ind : forall P,
  (forall v, P (TConst v)) ->
  (forall x, P (TVar x)) ->
  (forall f args,
    (forall arg, In arg args -> P arg) -> P (TApp f args)) ->
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
  | AT_Eq (t₁ t₂ : term)
  | AT_Pred (symbol : string) (args : list term).

Unset Elimination Schemes.
Inductive formula : Type :=
  | F_Simple (sf : simple_formula)
  | F_Not (f : formula)
  | F_And (f₁ f₂ : formula)
  | F_Or (f₁ f₂ : formula)
  | F_Implies (f₁ f₂ : formula)
  | F_Exists (x : variable) (f : formula)
  | F_Forall (x : variable) (f : formula).
Set Elimination Schemes.
Scheme formula_ind_naive := Induction for formula Sort Type.

Definition to_value {A : Type} (x : A) : value := @existT Type _ A x.
Definition N_to_value (n : nat) : value := to_value n.
Definition Z_to_value (z : Z) : value := to_value z.
Definition R_to_value (r : R) : value := to_value r.
Coercion N_to_value : nat >-> value.
Coercion Z_to_value : Z >-> value.
Coercion R_to_value : R >-> value.

Coercion TConst : value >-> term.
Coercion TVar : variable >-> term.
Coercion F_Simple : simple_formula >-> formula.


Declare Custom Entry formula.
Declare Scope formula_scope.
Declare Custom Entry formula_aux.
Bind Scope formula_scope with simple_formula.
Delimit Scope formula_scope with formula.


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
Notation "x <> y" := (F_Not (F_Simple (AT_Eq x y))) (in custom formula at level 70, no associativity, only parsing).
Notation "x ≠ y" := (F_Not (F_Simple (AT_Eq x y))) (in custom formula at level 70, no associativity, only printing).
Notation "x < y" := (AT_Pred "<" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <= y" := (AT_Pred "<=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x > y" := (AT_Pred ">" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x >= y" := (AT_Pred ">=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "'~' x" := (F_Not x) (in custom formula at level 75, only parsing).
Notation "'¬' x" := (F_Not x) (in custom formula at level 75, only printing).
Notation "x /\ y" := (F_And x y) (in custom formula at level 80, only parsing, left associativity).
Notation "x ∧ y" := (F_And x y) (in custom formula at level 80, only printing, left associativity).
Notation "x \/ y" := (F_Or x y) (in custom formula at level 80, left associativity, only parsing).
Notation "x ∨ y" := (F_Or x y) (in custom formula at level 80, left associativity, only printing).
Notation "x => y" := (F_Implies x y) (in custom formula at level 80, only parsing).
Notation "x ⇒ y" := (F_Implies x y) (in custom formula at level 80, only printing).
Notation "x <=> y" := (F_And (F_Implies x y) (F_Implies y x)) (in custom formula at level 80, only parsing).
Notation "x ⇔ y" := (F_And (F_Implies x y) (F_Implies y x)) (in custom formula at level 80, only printing).
Notation "'exists' x .. y ',' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only parsing).
Notation "'∃' x .. y '●' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only printing).
Notation "'forall' x .. y ',' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).
Notation "'∀' x .. y '●' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).

Open Scope formula_scope.

Fixpoint is_free_in_term x t :=
  match t with
  | TConst v => false
  | TVar y => if decide (y = x) then true else false
  | TApp sym args => foldr orb false (map (fun arg => is_free_in_term x arg) args)
  end.

Definition is_free_in_sf x sf :=
  match sf with
  | AT_Eq t₁ t₂ => is_free_in_term x t₁ || is_free_in_term x t₂
  | AT_Pred sym args =>
    fold_right orb false (map (fun arg => is_free_in_term x arg) args)
  | _ => false
  end.

Fixpoint is_free_in (x : variable) f :=
  match f with
  | F_Simple sf => is_free_in_sf x sf
  | F_Not f₁ => is_free_in x f₁
  | F_And f₁ f₂ => is_free_in x f₁ ||  is_free_in x f₂
  | F_Or f₁ f₂ => is_free_in x f₁ || is_free_in x f₂
  | F_Implies f₁ f₂ => is_free_in x f₁ || is_free_in x f₂
  | F_Exists y f₁ => if decide (y = x) then false else (is_free_in x f₁)
  | F_Forall y f₁ => if decide (y = x) then false else (is_free_in x f₁)
  end.

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
  | TApp sym args =>
    foldr (∪) ∅ (map (fun arg => term_fvars arg) args)
  end.

Definition simple_formula_fvars sf : gset variable :=
  match sf with
  | AT_Eq t₁ t₂ => term_fvars t₁ ∪ term_fvars t₂
  | AT_Pred _ args =>
    foldr (∪) ∅ (map (fun arg => term_fvars arg) args)
  | _ => ∅
  end.

Fixpoint formula_fvars (f : formula) : gset variable :=
  match f with
  | F_Simple sf => simple_formula_fvars sf
  | F_Not f => formula_fvars f
  | F_And f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Or f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Implies f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Exists x f => formula_fvars f ∖ {[x]}
  | F_Forall x f => formula_fvars f ∖ {[x]}
  end.

Fixpoint fresh_var_aux x (fvars : gset variable) fuel :=
  match fuel with
  | O => x
  | S fuel =>
      if decide (x ∈ fvars) then fresh_var_aux (var_increase_sub x 1) fvars fuel else x
  end.

Definition fresh_var (x : variable) (fvars : gset variable) : variable :=
  fresh_var_aux x fvars (S (size fvars)).

Fixpoint formula_rank f :=
  match f with
  | F_Simple sf => 1
  | F_Not f => 1 + formula_rank f
  | F_And f₁ f₂ => 1 + max (formula_rank f₁) (formula_rank f₂)
  | F_Or f₁ f₂ => 1 + max (formula_rank f₁) (formula_rank f₂)
  | F_Implies f₁ f₂ => 1 + max (formula_rank f₁) (formula_rank f₂)
  | F_Exists y f => 1 + (formula_rank f)
  | F_Forall y f => 1 + (formula_rank f)
  end.

Fixpoint quantifier_rank f :=
  match f with
  | F_Simple sf => 0
  | F_Not f => quantifier_rank f
  | F_And f₁ f₂ => max (quantifier_rank f₁) (quantifier_rank f₂)
  | F_Or f₁ f₂ => max (quantifier_rank f₁) (quantifier_rank f₂)
  | F_Implies f₁ f₂ => max (quantifier_rank f₁) (quantifier_rank f₂)
  | F_Exists y f => 1 + (quantifier_rank f)
  | F_Forall y f => 1 + (quantifier_rank f)
  end.      

Declare Scope formula_props.
Open Scope formula_props.

Notation "'rank' A" := (formula_rank A + quantifier_rank A)
  (at level 20) : formula_props.

Definition quant_subst_fvars φ x t := formula_fvars φ ∪ term_fvars t ∪ {[x]}.
Lemma quant_subst_fvars_inv : forall y φ x t,
    y ∉ quant_subst_fvars φ x t -> y ∉ formula_fvars φ /\ y ∉ term_fvars t /\ y ≠ x.
Proof with auto.
  intros. unfold quant_subst_fvars in H.
  apply not_elem_of_union in H as [H H1]. apply not_elem_of_singleton in H1.
  apply not_elem_of_union in H as [H2 H3]...
Qed.

Inductive sum_quant_subst_skip_cond y φ x :=
  | SumQuantSubstSkipCond_False (H : y = x \/ x ∉ formula_fvars φ)
  | SumQuantSubstSkipCond_True (H1 : y <> x) (H2: x ∈ formula_fvars φ).

Definition quant_subst_skip_cond y φ x : sum_quant_subst_skip_cond y φ x.
Proof with auto.
  destruct (decide (y = x \/ x ∉ formula_fvars φ)).
  - apply SumQuantSubstSkipCond_False...
  - apply Decidable.not_or in n as [H1 H2]. destruct (decide (x ∈ formula_fvars φ)).
    + apply SumQuantSubstSkipCond_True...
    + contradiction.
Defined.

(*
  For (Qy. φ)[x \ t] (where Q ∈ {∃, ∀}), when x ≠ y and y ∈ FV(t),
  we need to pick a fresh quantifier y'. But there are two limitations:
  1. y' ∉ FV(φ): or else we will incorrectly capture
  2. y' ∉ FV(t): Let's assume (Qy. y = x)[x \ z],
    If y' = c:
      (Qy. y = x)[x \ c + y] ≡ (Qc. (c = x)[x \ c + y]) ≡ (Qc. c = c + y)
    If y' = z a universally fresh quantifier:
      (Qy. y = x)[x \ c + y] ≡ (Qz. (z = x)[x \ c + y]) ≡ (Qz. z = c + y)
    These two are not α-equivalent.


  The following is not a limitation; however we envforce it to make proofs easier
  1. y' can be x but we don't allow it:
    (Qy. φ)[x \ t] ≡ (Qx. φ[y \ x][x \ t]) ≡ (Qx. φ[y \ x])
    This discards the substition; picking a universally fresh quantifier z, yields:
    (Qz. φ)[x \ t] ≡ (Qz. φ[y \ z][x \ t])
    It seems like these two are not α-equivalent; but:
    Since y' = x, we must have x ∉ FV(φ) which means (Qz. φ[y \ z][x \ t]) ≡ (Qz. φ[y \ z])
 *)
Fixpoint subst_formula_aux qrank :=
  fix subst_aux φ x t :=
    match φ with
    | F_Simple sf => F_Simple (subst_sf sf x t)
    | F_Not φ => F_Not (subst_aux φ x t)
    | F_And φ₁ φ₂ => F_And
      (subst_aux φ₁ x t)
      (subst_aux φ₂ x t)
    | F_Or φ₁ φ₂ => F_Or
      (subst_aux φ₁ x t)
      (subst_aux φ₂ x t)
    | F_Implies φ₁ φ₂ => F_Implies
      (subst_aux φ₁ x t)
      (subst_aux φ₂ x t)
    | F_Exists y φ =>
        if quant_subst_skip_cond y φ x then F_Exists y φ else
          let y' := fresh_var y (quant_subst_fvars φ x t) in
          match qrank with
          | 0 => F_Exists y φ
          | S qrank => F_Exists y'
                        (subst_formula_aux qrank (subst_aux φ y (TVar y')) x t)
          end
    | F_Forall y φ =>
        if quant_subst_skip_cond y φ x then F_Forall y φ else
          let y' := fresh_var y (quant_subst_fvars φ x t) in
          match qrank with
          | 0 => F_Forall y φ
          | S qrank => F_Forall y'
                        (subst_formula_aux qrank (subst_aux φ y (TVar y')) x t)
          end
end.

Definition subst_formula φ x t :=
  subst_formula_aux (quantifier_rank φ) φ x t.

Notation "f [ x \ a ]" := (subst_formula f x a)
  (at level 10, left associativity,
   x at next level) : formula_scope.

Notation "f [ x \ a ]" := (subst_formula f x a)
  (in custom formula at level 74, left associativity,
    f custom formula,
    x constr at level 0, a custom formula) : formula_scope.

Ltac fold_qrank_subst n φ x t :=
  let R := fresh in
  let H := fresh in
  let H' := fresh in
  remember (subst_formula_aux n φ x t) as R eqn:H;
  assert (H' := H); simpl in H'; rewrite H in H'; rewrite <- H' in *;
  clear H'; clear H; clear R.

Ltac fold_qrank_subst_fresh n φ x x' t :=
  fold_qrank_subst n φ x (fresh_var x (quant_subst_fvars φ x' t)).

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
  formula_rank A = 1 -> 
  exists sf, A = F_Simple sf.
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
    (forall m, m < n -> 
      forall ψ, rank ψ = m -> P ψ) ->
    (forall φ, rank φ = n -> P φ)) ->
  forall φ, P φ.
Proof with auto.
  intros P Hind.
  assert (H : forall n φ, rank φ < n -> P φ).
  {
    induction n; intros φ Hrank.
    - lia.
    - apply Hind with (formula_rank φ + quantifier_rank φ)...
      intros m Hlt ψ Hψ. apply IHn. lia.
  }
  intros φ. apply H with (S (rank φ)). lia.
Qed.

Definition is_quantifier P :=
  match P with
  | F_Exists y f₁ => true
  | F_Forall y f₁ => true
  | _ => false
  end.

Definition cons_eq A B :=
  match A, B with
  | F_Simple _, F_Simple _ => true
  | F_Not _, F_Not _ => true
  | F_And _ _, F_And _ _  => true
  | F_Or _ _, F_Or _ _ => true
  | F_Implies _ _, F_Implies _ _ => true
  | F_Exists _ _, F_Exists _ _ => true
  | F_Forall _ _, F_Forall _ _ => true
  | _, _ => false
  end.

Fixpoint shape_eq A B :=
  match A, B with
  | F_Simple _, F_Simple _ => true
  | F_Not A, F_Not B => shape_eq A B
  | F_And A1 A2, F_And B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
  | F_Or A1 A2, F_Or B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
  | F_Implies A1 A2, F_Implies B1 B2 => shape_eq A1 B1 && shape_eq A2 B2
  | F_Exists _ A, F_Exists _ B => shape_eq A B
  | F_Forall _ A, F_Forall _ B => shape_eq A B
  | _, _ => false
  end.

Lemma shape_eq__cons_eq : forall A B,
  shape_eq A B = true ->
    cons_eq A B = true.
Proof with auto.
  intros. destruct A; destruct B; try discriminate...
Qed.

Lemma cons_eq_simple : forall sf B,
  cons_eq (F_Simple sf) B = true ->
  exists sf', B = F_Simple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Lemma shape_eq_simple : forall sf B,
  shape_eq (F_Simple sf) B = true ->
  exists sf', B = F_Simple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Lemma cons_eq_not : forall A1 B,
  cons_eq <! ~ A1 !> B = true ->
  exists B1, B = <! ~ B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Lemma shape_eq_not : forall A1 B,
  shape_eq <! ~ A1 !> B = true ->
  exists B1, B = <! ~ B1 !> /\ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Lemma cons_eq_and : forall A1 A2 B,
  cons_eq <! A1 /\ A2 !> B = true ->
  exists B1 B2, B = <! B1 /\ B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Lemma shape_eq_and : forall A1 A2 B,
  shape_eq <! A1 /\ A2 !> B = true ->
  exists B1 B2, B = <! B1 /\ B2 !> /\
    shape_eq A1 B1 = true /\
    shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Lemma cons_eq_or : forall A1 A2 B,
  cons_eq <! A1 \/ A2 !> B = true ->
  exists B1 B2, B = <! B1 \/ B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Lemma shape_eq_or : forall A1 A2 B,
  shape_eq <! A1 \/ A2 !> B = true ->
  exists B1 B2, B = <! B1 \/ B2 !> /\
    shape_eq A1 B1 = true /\
    shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Lemma cons_eq_implies : forall A1 A2 B,
  cons_eq <! A1 => A2 !> B = true ->
  exists B1 B2, B = <! B1 => B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Lemma shape_eq_implies : forall A1 A2 B,
  shape_eq <! A1 => A2 !> B = true ->
  exists B1 B2, B = <! B1 => B2 !> /\
    shape_eq A1 B1 = true /\
    shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Lemma cons_eq_exists : forall x A1 B,
  cons_eq <! exists x, A1 !> B = true ->
  exists y B1, B = <! exists y, B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Lemma shape_eq_exists : forall x A1 B,
  shape_eq <! exists x, A1 !> B = true ->
  exists y B1, B = <! exists y, B1 !> /\ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Lemma cons_eq_forall : forall x A1 B,
  cons_eq <! forall x, A1 !> B = true ->
  exists y B1, B = <! forall y, B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Lemma shape_eq_forall : forall x A1 B,
  shape_eq <! forall x, A1 !> B = true ->
  exists y B1, B = <! forall y, B1 !> /\ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Lemma shape_eq_refl : forall A,
  shape_eq A A = true.
Proof with auto.
  intros. induction A using formula_ind_naive; simpl; auto; apply Bool.andb_true_iff...
Qed.

Lemma shape_eq_sym : forall A B,
  shape_eq A B = true ->
  shape_eq B A = true.
Proof with auto.
  induction A using formula_ind_naive; destruct B; try discriminate; simpl; auto;
  try repeat rewrite Bool.andb_true_iff; intros [H1 H2]...
Qed.

Lemma shape_eq_trans : forall A B C,
  shape_eq A B = true ->
  shape_eq B C = true ->
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
  shape_eq A B = true ->
    formula_rank A = formula_rank B /\
    quantifier_rank A = quantifier_rank B.
Proof with auto.
  assert (Hfr: forall A B, shape_eq A B = true ->
    formula_rank A = formula_rank B). {
    intros A; induction A using formula_ind_naive; destruct B; try discriminate;
    intros H; simpl; auto;
    try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2];
      auto). }
    assert (Hqr: forall A B, shape_eq A B = true ->
      quantifier_rank A = quantifier_rank B). {
    intros A. induction A using formula_ind_naive; destruct B; try discriminate;
    intros H; simpl; auto;
    try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2];
      auto).
  }
  auto.
Qed.

Lemma rank_eq_if_shape_eq : forall φ ψ,
    shape_eq φ ψ = true ->
    rank φ = rank ψ.
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
  clear A. intros n IH. destruct φ;
    intros Hr x' a r.
  - destruct r; simpl in *...
  - specialize IH with (m:=rank φ) (ψ:=φ).
    destruct r; simpl in *...
    + fold_qrank_subst 0 φ x' a. apply IH; try lia...
    + fold_qrank_subst (S r) φ x' a. apply IH; try lia...
  - subst. specialize IH with (m:=rank φ1) (ψ:=φ1) as IH1.
    specialize IH with (m:=rank φ2) (ψ:=φ2) as IH2.
    assert (HMax :=
      (Nat.max_spec (quantifier_rank φ1) (quantifier_rank φ2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 φ2 x' a. fold_qrank_subst 0 φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) φ2 x' a.
        fold_qrank_subst (S r) φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 φ2 x' a. fold_qrank_subst 0 φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) φ2 x' a.
        fold_qrank_subst (S r) φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
  - subst. specialize IH with (m:=rank φ1) (ψ:=φ1) as IH1.
    specialize IH with (m:=rank φ2) (ψ:=φ2) as IH2.
    assert (HMax :=
      (Nat.max_spec (quantifier_rank φ1) (quantifier_rank φ2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 φ2 x' a. fold_qrank_subst 0 φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) φ2 x' a.
        fold_qrank_subst (S r) φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 φ2 x' a. fold_qrank_subst 0 φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) φ2 x' a.
        fold_qrank_subst (S r) φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
  - subst. specialize IH with (m:=rank φ1) (ψ:=φ1) as IH1.
    specialize IH with (m:=rank φ2) (ψ:=φ2) as IH2.
    assert (HMax :=
      (Nat.max_spec (quantifier_rank φ1) (quantifier_rank φ2))).
    destruct HMax as [[H1 H2] | [H1 H2]]; try lia.
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 φ2 x' a. fold_qrank_subst 0 φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) φ1 x' a.
        fold_qrank_subst (S r) φ2 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
    + destruct r; simpl in *; rewrite H2 in *.
      * fold_qrank_subst 0 φ2 x' a. fold_qrank_subst 0 φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
      * fold_qrank_subst (S r) φ2 x' a.
        fold_qrank_subst (S r) φ1 x' a.
        apply Bool.andb_true_iff. split;
          [apply IH1|apply IH2]; lia...
  - subst. destruct r; simpl in *.
    + destruct (quant_subst_skip_cond x φ x')...
    + fold_qrank_subst_fresh (S r) φ x x' a.
      destruct (quant_subst_skip_cond x φ x'); try lia...
      remember (subst_formula_aux (S r) φ x (fresh_var x (quant_subst_fvars φ x' a)))
        as φ₁. (* the first substitution *)
      remember (subst_formula_aux r φ₁ x' a)
        as φ₂. (* the second substituion *)
      specialize IH with (m:=rank φ) (ψ:=φ) as IHφ.
      specialize IH with (m:=rank φ₁) (ψ:=φ₁) as IHφ₁.
      forward IHφ by lia. forward IHφ by auto.
      specialize (IHφ x (fresh_var x (quant_subst_fvars φ x' a)) (S r)). (* φ₁ *)
      forward IHφ₁. { deduce_rank_eq IHφ. rewrite Heqφ₁. lia. }
      forward IHφ₁ by reflexivity. specialize (IHφ₁ x' a r).
      rewrite <- Heqφ₁ in *. rewrite <- Heqφ₂ in *.
      apply shape_eq_trans with φ₁...
  - subst. destruct r; simpl in *.
    + destruct (quant_subst_skip_cond x φ x')...
    + fold_qrank_subst_fresh (S r) φ x x' a.
      destruct (quant_subst_skip_cond x φ x'); try lia...
      remember (subst_formula_aux (S r) φ x (fresh_var x (quant_subst_fvars φ x' a)))
        as φ₁. (* the first substitution *)
      remember (subst_formula_aux r φ₁ x' a)
        as φ₂. (* the second substituion *)
      specialize IH with (m:=rank φ) (ψ:=φ) as IHφ.
      specialize IH with (m:=rank φ₁) (ψ:=φ₁) as IHφ₁.
      forward IHφ by lia. forward IHφ by auto.
      specialize (IHφ x (fresh_var x (quant_subst_fvars φ x' a)) (S r)). (* φ₁ *)
      forward IHφ₁. { deduce_rank_eq IHφ. rewrite Heqφ₁. lia. }
      forward IHφ₁ by reflexivity. specialize (IHφ₁ x' a r).
      rewrite <- Heqφ₁ in *. rewrite <- Heqφ₂ in *.
      apply shape_eq_trans with φ₁...
Qed.

Lemma subst_preserves_shape : forall φ x a,
  shape_eq (φ[x \ a]) φ  = true.
Proof with auto.
  intros. unfold subst_formula. apply shape_eq_sym. apply subst_preserves_shape_aux. Qed.

Hint Resolve subst_preserves_shape : core.

Lemma formula_ind : forall P,
  (forall sf, P (F_Simple sf)) ->
  (forall φ, P φ -> P <! ~ φ !>) ->
  (forall φ₁ φ₂, P φ₁ -> P φ₂ -> P <! φ₁ /\ φ₂ !>) ->
  (forall φ₁ φ₂, P φ₁ -> P φ₂ -> P <! φ₁ \/ φ₂ !>) ->
  (forall φ₁ φ₂, P φ₁ -> P φ₂ -> P <! φ₁ => φ₂ !>) ->
  (forall x φ, (forall ψ, shape_eq ψ φ = true -> P ψ) -> P <! exists x, φ !>) ->
  (forall x φ, (forall ψ, shape_eq ψ φ = true -> P ψ) -> P <! forall x, φ !>) ->
  forall φ, P φ.
Proof with auto.
  intros P Hsf Hnot Hand Hor Himpl Hexists Hforall φ.
  induction φ using formula_rank_ind. destruct φ; subst; simpl in *.
  - apply Hsf.
  - apply Hnot. apply X with (rank φ); lia.
  - apply Hand. apply X with (rank φ1); lia. apply X with (rank φ2);lia.
  - apply Hor. apply X with (rank φ1); lia. apply X with (rank φ2);lia.
  - apply Himpl. apply X with (rank φ1); lia. apply X with (rank φ2);lia.
  - apply Hexists. intros. apply X with (rank ψ); auto.
    apply rank_eq_if_shape_eq in H. lia.
  - apply Hforall. intros. apply X with (rank ψ); auto.
    apply rank_eq_if_shape_eq in H. lia.
Qed.

Definition state := gmap variable value.

Record fdef := mkFdef {
    fdef_arity : nat;
    fdef_rel : vec value fdef_arity -> value -> Prop;
    fdef_functional : forall {args v₁ v₂}, fdef_rel args v₁ -> fdef_rel args v₂ -> v₁ = v₂
}.

Record pdef := mkPdef {
  pdef_arity : nat;
  pdef_rel : vec value pdef_arity -> Prop;
}.

Record semantics := mkSemantics {
  fdefs : gmap string fdef;
  pdefs : gmap string pdef;
}.

Inductive fn_eval (M : semantics) (fSym : string) (vargs : list value) : value -> Prop :=
  | FnEval : forall value fdef,
    fdefs M !! fSym = Some fdef ->
    forall hlen : length vargs = fdef_arity fdef,
      fdef_rel fdef (list_to_vec_n vargs hlen) value ->
      fn_eval M fSym vargs value.

Inductive teval (M : semantics) (σ : state) : term -> value -> Prop :=
  | TEval_Const : forall v, teval M σ (TConst v) v
  | TEval_Var : forall x v, σ !! x = Some v -> teval M σ (TVar x) v
  | Teval_App : forall f args vargs fval,
    teval_args M σ args vargs ->
    fn_eval M f vargs fval ->
    teval M σ (TApp f args) (fval)
with teval_args (M : semantics) (σ : state) : list term -> list value -> Prop :=
  | TEvalArgs_Nil : teval_args M σ [] []
  | TEvalArgs_Cons : forall t ts v vs,
    teval M σ t v ->
    teval_args M σ ts vs ->
    teval_args M σ (t::ts) (v::vs).

Scheme teval_ind_mut := Induction for teval Sort Prop
with teval_args_ind_mut := Induction for teval_args Sort Prop.

Lemma teval_det : forall {M σ t v₁ v₂},
    teval M σ t v₁ -> teval M σ t v₂ -> v₁ = v₂.
Proof with auto.
  intros M σ t v₁ v₂ H1 H2. generalize dependent v₂.
  generalize dependent v₁. generalize dependent t.
  apply (teval_ind_mut M σ (λ t v₁ _, forall v₂, teval M σ t v₂ -> v₁ = v₂)
           (λ args vargs₁ _, forall vargs₂, teval_args M σ args vargs₂ -> vargs₁ = vargs₂)).
  - intros. inversion H...
  - intros. inversion H; subst. rewrite e in H1. inversion H1...
  - intros. inversion H0; subst. inversion H5; subst. inversion f0; subst.
    apply H in H3. subst vargs0. rewrite H1 in H4. inversion H4; subst.
    assert (Hlen : hlen = hlen0). { apply UIP_nat. } subst.
    apply (fdef_functional _ H2) in H6...
  - inversion 1...
  - intros. destruct vargs₂.
    + inversion H1.
    + inversion H1; subst. f_equal.
      * apply H...
      * apply H0...
Qed.

Lemma teval_args_det : forall {M σ args vargs₁ vargs₂},
    teval_args M σ args vargs₁ -> teval_args M σ args vargs₂ ->
    vargs₁ = vargs₂.
Proof with auto.
  intros M σ. induction args; intros vargs₁ vargs₂ H1 H2.
  - inversion H1. inversion H2...
  - inversion H1; subst. inversion H2; subst. f_equal.
    + eapply teval_det. apply H3. apply H4.
    + apply IHargs...
Qed.

Inductive pred_eval (M : semantics) (pSym : string) (vargs : list value) : Prop :=
  | PredEval : forall pdef,
    pdefs M !! pSym = Some pdef ->
    forall hlen : length vargs = pdef_arity pdef,
    pdef_rel pdef (list_to_vec_n vargs hlen) ->
    pred_eval M pSym vargs.

Inductive sfeval (M : semantics) (σ : state) : simple_formula -> Prop :=
  | SFEval_True : sfeval M σ AT_True
  | SFEval_Eq : forall t₁ t₂ v, teval M σ t₁ v -> teval M σ t₂ v -> sfeval M σ (AT_Eq t₁ t₂)
  | SFEval_Pred : forall pSym args vargs,
    teval_args M σ args vargs ->
    pred_eval M pSym vargs ->
    sfeval M σ (AT_Pred pSym args).

Fixpoint feval (M : semantics) (σ : state) (φ : formula) : Prop :=
  match φ with
  | F_Simple sf => sfeval M σ sf
  | F_Not φ => ¬ feval M σ φ
  | F_And φ ψ => feval M σ φ /\ feval M σ ψ
  | F_Or φ ψ => feval M σ φ \/ feval M σ ψ
  | F_Implies φ ψ => feval M σ φ -> feval M σ ψ
  | F_Exists x φ => exists v, feval M (<[x:=v]>σ) φ
  | F_Forall x φ => forall v, feval M (<[x:=v]>σ) φ
  end.

Axiom feval_lem : forall M σ φ, feval M σ φ \/ ~ feval M σ φ.

Lemma feval_dec : forall M σ φ, Decidable.decidable (feval M σ φ).
Proof. exact feval_lem. Qed.

Lemma feval_dne : forall M σ φ,
  ~ ~ feval M σ φ <-> feval M σ φ.
Proof with auto.
  intros.
  apply (Decidable.not_not_iff _ (feval_dec M σ φ)).
Qed.

(* ******************************************************************* *)
(* fresh_var specification                                             *)
(* ******************************************************************* *)

Notation var_seq x i n := (map (λ j, var_with_sub x j) (seq i n)).

Lemma var_seq_cons : forall x i n,
    var_with_sub x i :: var_seq x (S i) n = var_seq x i (S n).
Proof. reflexivity. Qed.

Lemma var_seq_app_r : forall x i n,
    var_seq x i (S n) = var_seq x i n ++ [var_with_sub x (i + n)].
Proof with auto.
  intros. replace (S n) with (n + 1) by lia. rewrite seq_app.
  rewrite map_app. f_equal.
Qed.

Lemma var_seq_eq : forall x₁ x₂ i n,
    var_name x₁ = var_name x₂ ->
    var_is_initial x₁ = var_is_initial x₂ ->
    var_seq x₁ i n = var_seq x₂ i n.
Proof with auto.
  intros. apply list_fmap_ext. intros j k H1. unfold var_with_sub. f_equal...
Qed.

Lemma length_var_seq : forall x i n,
    length (var_seq x i n) = n.
Proof. intros. rewrite length_map. rewrite length_seq. reflexivity. Qed.

Lemma not_elem_of_var_seq : forall x i n,
    i > var_sub x ->
    x ∉ var_seq x i n.
Proof with auto.
  induction n.
  - intros. simpl. apply not_elem_of_nil.
  - intros. simpl. apply not_elem_of_cons. split.
    * unfold var_with_sub. destruct x. simpl. inversion 1. destruct H0. subst. simpl in H.
      lia.
    * forward IHn by assumption. intros contra. apply IHn. destruct n.
      -- simpl in contra. apply elem_of_nil in contra. contradiction.
      -- rewrite var_seq_app_r in contra. apply elem_of_app in contra.
         destruct contra.
         2:{ apply elem_of_list_singleton in H0. unfold var_with_sub in H0. destruct x.
             simpl in H0. simpl in H. inversion H0. lia. }
        apply elem_of_list_fmap in H0 as [j [H1 H2]]. apply elem_of_list_fmap.
         exists j. split... apply elem_of_seq. apply elem_of_seq in H2. lia.
Qed.

Lemma fresh_var_fresh_aux : forall x fvars fuel,
    fuel > 0 ->
      var_seq x (var_sub x) fuel ⊆+ elements fvars \/
      fresh_var_aux x fvars fuel ∉ fvars.
Proof with auto.
  intros x fvars fuel. generalize dependent x. induction fuel; try lia.
  intros. destruct fuel.
  - simpl. destruct (decide (x ∈ fvars))... rewrite var_with_sub_var_sub_id. left.
    apply singleton_submseteq_l. apply elem_of_elements...
  - forward (IHfuel (var_increase_sub x 1)) by lia.
    destruct IHfuel.
    + simpl. destruct (decide (x ∈ fvars))... left.
      rewrite var_seq_cons. rename fuel into fuel'. remember (S fuel') as fuel.
      assert (fuel > 0) by lia. clear Heqfuel. clear fuel'.
      simpl in H0. rewrite var_with_sub_var_sub_id. apply NoDup_submseteq.
      * apply NoDup_cons. split.
        -- apply not_elem_of_var_seq. lia.
        -- apply NoDup_fmap.
           ++ intros i j H2. unfold var_with_sub in H2. inversion H2...
           ++ apply NoDup_seq.
      * intros v H2. apply elem_of_elements. apply elem_of_cons in H2. destruct H2; subst...
        assert (var_seq (var_increase_sub x 1) (var_sub x + 1) fuel =
                  var_seq x (S (var_sub x)) fuel) as Heq.
        { replace (var_sub x + 1) with (S (var_sub x)) by lia. apply var_seq_eq...  }
        rewrite Heq in *. clear Heq. apply (elem_of_submseteq _ _ _ H2) in H0.
        apply elem_of_elements in H0...
    + simpl. destruct (decide (x ∈ fvars))...
Qed.

Lemma fresh_var_fresh : forall x fvars,
    fresh_var x fvars ∉ fvars.
Proof with auto.
  intros. assert (Haux := fresh_var_fresh_aux x fvars (S (size fvars))).
  forward Haux by lia. destruct Haux...
  exfalso. apply submseteq_length in H. rewrite length_var_seq in H.
  unfold size, set_size in H. simpl in *. lia.
Qed.

Lemma fresh_var_free : forall {x fvars},
    x ∉ fvars ->
    fresh_var x fvars = x.
Proof with auto.
  intros. unfold fresh_var. unfold fresh_var_aux.
  destruct (decide (x ∈ fvars))... contradiction.
Qed.

Lemma fexists_subst_not_free : forall y φ x t,
    x ∉ formula_fvars φ ->
    <! (exists y, φ)[x \ t] !> = <! exists y, φ !>.
Proof with auto.
  intros. unfold subst_formula. simpl. destruct (quant_subst_skip_cond y φ x)...
  contradiction.
Qed.

(* TODO: remove this *)
(* (* if x ∈ FV(φ) and y is a variable, then FV(φ[x \ y]) = FV(φ) ∪ {[y]} \ {[x]}  *) *)
(* (* if (Qy. φ)[x \ t] = (Qx. φ[x \ t]), then x ∉ FV(φ) hence ≡ (Qx. φ) *) *)
(* Lemma temp : forall (x y : variable) φ, *)
(*     x ∈ formula_fvars φ -> *)
(*     formula_fvars (<! φ[x \ y] !>) = formula_fvars φ ∪ {[y]} ∖ {[x]}. *)
(* Proof. *)
