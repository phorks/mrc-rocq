From Stdlib Require Import Strings.String.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From stdpp Require Import gmap.
From MRC Require Import Tactics.

Record vec (A : Type) (n : nat) := {
  vec_to_list : list A;
  vec_to_list_length : length vec_to_list = n
}.

Definition list_to_vec_n {A n} (l : list A) (hlen : length l = n) : vec A n := {|
  vec_to_list := l;
  vec_to_list_length := hlen
|}.

Open Scope bool_scope.

(* Inductive value : Type := *)
(*   | VNat (n : nat) *)
(*   | VInt (z : Z) *)
(*   | VReal (r : R). *)

Definition value := {t : Type & t}.

(* Definition value_to_R (v : value) := *)
(* match v with *)
(*   | VNat n => INR n *)
(*   | VInt z => IZR z *)
(*   | VReal r => r *)
(* end. *)

Unset Elimination Schemes.
Inductive term : Type :=
  | TConst (v : value)
  | TVar (x : string)
  | TApp (symbol : string) (args : list term).
Set Elimination Schemes.

Fixpoint term_rank t :=
  match t with
  | TConst _ => 0
  | TVar _ => 0
  | TApp f args => 1
    + fold_right max 0 (map (fun arg => term_rank arg) args)
  end.

Theorem term_rank_app_gt_args : forall f args arg,
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

Theorem term_formula_rank_ind : forall P,
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

Theorem term_ind : forall P,
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


(* Instance eq_pdef : symPdef "=" := { *)
(*   sym_pdef := {| *)
(*     pdef_arity := 2; *)
(*     pdef_rel args := args !!! 0 = args !!! 1; *)
(*   |} *)
(* }. *)

(* Definition eq_prel_sem (eq : pred_rel) := forall st fctx, *)
(*   (forall t, *)
(*     eq st fctx [t; t] true) /\ *)
(*   (forall t1 t2 b, *)
(*     eq st fctx [t1; t2] b -> *)
(*     eq st fctx [t2; t1] b) /\ *)
(*   (forall t1 t2 t3 b1 b2, *)
(*     eq st fctx [t1; t2] b1 -> *)
(*     eq st fctx [t2; t3] b2 ->  *)
(*     eq st fctx [t1; t3] (b1 && b2)). *)

(* Definition pred_map := partial_map pred_def. *)
(* Definition pred_map_has_eq_sem pmap := exists pdef, *)
(*   pmap "="%string = Some pdef /\ eq_prel_sem (pdef_prel pdef). *)

(* Inductive pcontext : Type := *)
(*   | PCtx  *)
(*     (pmap : pred_map)  *)
(*     (has_eq_sem : pred_map_has_eq_sem pmap). *)

(* Definition pctx_map pctx := *)
(*   match pctx with *)
(*   | PCtx pmap _ => pmap *)
(*   end. *)

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
  | F_Exists (x : string) (f : formula)
  | F_Forall (x : string) (f : formula).
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
Coercion TVar : string >-> term.
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

(* TODO: rename to is_free_in_term *)
Fixpoint appears_in_term x t :=
  match t with
  | TConst v => false
  | TVar y => if (y =? x)%string
    then true
    else false
  | TApp sym args =>
    foldr orb false (map (fun arg => appears_in_term x arg) args)
  end.

(* TODO: rename to is_free_in_simple_formula *)
Definition appears_in_simple_formula x sf :=
  match sf with
  | AT_Eq t₁ t₂ => appears_in_term x t₁ || appears_in_term x t₂
  | AT_Pred sym args =>
    fold_right orb false (map (fun arg => appears_in_term x arg) args)
  | _ => false
  end.

Fixpoint is_free_in x f :=
  match f with
  | F_Simple sf => appears_in_simple_formula x sf
  | F_Not f₁ => is_free_in x f₁
  | F_And f₁ f₂ => is_free_in x f₁ ||  is_free_in x f₂
  | F_Or f₁ f₂ => is_free_in x f₁ || is_free_in x f₂
  | F_Implies f₁ f₂ => is_free_in x f₁ || is_free_in x f₂
  | F_Exists y f₁ => if (y =? x)%string then false else (is_free_in x f₁)
  | F_Forall y f₁ => if (y =? x)%string then false else (is_free_in x f₁)
  end.

Fixpoint subst_term t x a :=
  match t with
  | TConst v => TConst v
  | TVar y => if (y =? x)%string then a else TVar y
  | TApp sym args => TApp sym (map (fun arg => subst_term arg x a) args)
  end.

Definition subst_simple_formula sf x a :=
  match sf with
  | AT_Eq t₁ t₂ => AT_Eq (subst_term t₁ x a) (subst_term t₂ x a)
  | AT_Pred sym args => AT_Pred sym (map (fun arg => subst_term arg x a) args)
  | _ => sf
  end.

Fixpoint term_fvars t : gset string :=
  match t with
  | TConst v => ∅
  | TVar y => {[y]}
  | TApp sym args =>
    foldr (∪) ∅ (map (fun arg => term_fvars arg) args)
  end.

Definition simple_formula_fvars sf : gset string :=
  match sf with
  | AT_Eq t₁ t₂ => term_fvars t₁ ∪ term_fvars t₂
  | AT_Pred _ args =>
    foldr (∪) ∅ (map (fun arg => term_fvars arg) args)
  | _ => ∅
  end.

Fixpoint formula_fvars (f : formula) : gset string :=
  match f with
  | F_Simple sf => simple_formula_fvars sf
  | F_Not f => formula_fvars f
  | F_And f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Or f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Implies f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Exists x f => formula_fvars f ∖ {[x]}
  | F_Forall x f => formula_fvars f ∖ {[x]}
  end.

Open Scope string_scope.
Definition fresh_quantifier (x : string) f a : string :=
  let fvars := formula_fvars f in
  let fix go i (x : string) f fuel : string
    := match fuel with
        | O => x (* there are no fvars in the formula *)
        | S fuel =>
          let x' := x ++ "_" ++ (NilZero.string_of_uint $ Nat.to_uint i) in
          if decide (x' ∈ fvars) then go (S i) x f fuel else x'
      end in
  if appears_in_term x a then go 0 x f (size fvars) else x.

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

Fixpoint subst_formula_qrank qrank :=
  fix subst_aux f x a :=
    match f with
    | F_Simple sf => F_Simple (subst_simple_formula sf x a)
    | F_Not f => F_Not (subst_aux f x a)
    | F_And f₁ f₂ => F_And
      (subst_aux f₁ x a)
      (subst_aux f₂ x a)
    | F_Or f₁ f₂ => F_Or
      (subst_aux f₁ x a)
      (subst_aux f₂ x a)
    | F_Implies f₁ f₂ => F_Implies
      (subst_aux f₁ x a)
      (subst_aux f₂ x a)
    | F_Exists y f => if (y =? x)%string then F_Exists y f else
      let y' := fresh_quantifier y f a in
      match qrank with
      | 0 => F_Exists y f
      | S qrank => F_Exists y' 
          (subst_formula_qrank qrank (subst_aux f y (TVar y')) x a)
      end
    | F_Forall y f => if (y =? x)%string then F_Forall y f else
      let y' := fresh_quantifier y f a in
      match qrank with
      | 0 => F_Forall y f
      | S qrank => F_Forall y' 
          (subst_formula_qrank qrank (subst_aux f y (TVar y')) x a)
      end
end.

Definition formula_subst f x a :=
  subst_formula_qrank (quantifier_rank f) f x a.

Notation "f [ x \ a ]" := (formula_subst f x a)
  (at level 10, left associativity,
   x at next level) : formula_scope.

Notation "f [ x \ a ]" := (formula_subst f x a)
  (in custom formula at level 74, left associativity,
    f custom formula,
    x constr at level 0, a custom formula) : formula_scope.

Ltac fold_qrank_subst n f x a := 
  let R := fresh in
  let H := fresh in
  let H' := fresh in
  remember (subst_formula_qrank n f x a) as R eqn:H;
  assert (H' := H); simpl in H'; rewrite H in H'; rewrite <- H' in *;
  clear H'; clear H; clear R.

Theorem formula_rank_gt_zero : forall A, formula_rank A > 0.
Proof.
  intros A. destruct A; simpl; lia.
Qed.

Theorem formula_rank_nonzero : forall A,
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

Theorem formula_rank_one_is_simple : forall A,
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

Theorem formula_rank_ind : forall P,
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

Theorem shape_eq__cons_eq : forall A B,
  shape_eq A B = true ->
    cons_eq A B = true.
Proof with auto.
  intros. destruct A; destruct B; try discriminate...
Qed.

Theorem cons_eq_simple : forall sf B,
  cons_eq (F_Simple sf) B = true ->
  exists sf', B = F_Simple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Theorem shape_eq_simple : forall sf B,
  shape_eq (F_Simple sf) B = true ->
  exists sf', B = F_Simple sf'.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists sf0...
Qed.

Theorem cons_eq_not : forall A1 B,
  cons_eq <! ~ A1 !> B = true ->
  exists B1, B = <! ~ B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Theorem shape_eq_not : forall A1 B,
  shape_eq <! ~ A1 !> B = true ->
  exists B1, B = <! ~ B1 !> /\ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B...
Qed.

Theorem cons_eq_and : forall A1 A2 B,
  cons_eq <! A1 /\ A2 !> B = true ->
  exists B1 B2, B = <! B1 /\ B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem shape_eq_and : forall A1 A2 B,
  shape_eq <! A1 /\ A2 !> B = true ->
  exists B1 B2, B = <! B1 /\ B2 !> /\
    shape_eq A1 B1 = true /\
    shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem cons_eq_or : forall A1 A2 B,
  cons_eq <! A1 \/ A2 !> B = true ->
  exists B1 B2, B = <! B1 \/ B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem shape_eq_or : forall A1 A2 B,
  shape_eq <! A1 \/ A2 !> B = true ->
  exists B1 B2, B = <! B1 \/ B2 !> /\
    shape_eq A1 B1 = true /\
    shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem cons_eq_implies : forall A1 A2 B,
  cons_eq <! A1 => A2 !> B = true ->
  exists B1 B2, B = <! B1 => B2 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists B1, B2...
Qed.

Theorem shape_eq_implies : forall A1 A2 B,
  shape_eq <! A1 => A2 !> B = true ->
  exists B1 B2, B = <! B1 => B2 !> /\
    shape_eq A1 B1 = true /\
    shape_eq A2 B2 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate.
  apply Bool.andb_true_iff in H. exists B1, B2...
Qed.

Theorem cons_eq_exists : forall x A1 B,
  cons_eq <! exists x, A1 !> B = true ->
  exists y B1, B = <! exists y, B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Theorem shape_eq_exists : forall x A1 B,
  shape_eq <! exists x, A1 !> B = true ->
  exists y B1, B = <! exists y, B1 !> /\ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Theorem cons_eq_forall : forall x A1 B,
  cons_eq <! forall x, A1 !> B = true ->
  exists y B1, B = <! forall y, B1 !>.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Theorem shape_eq_forall : forall x A1 B,
  shape_eq <! forall x, A1 !> B = true ->
  exists y B1, B = <! forall y, B1 !> /\ shape_eq A1 B1 = true.
Proof with auto.
  intros. simpl in H. destruct B; try discriminate. exists x0, B...
Qed.

Theorem shape_eq_refl : forall A,
  shape_eq A A = true.
Proof with auto.
  intros. induction A using formula_ind_naive; simpl; auto; apply Bool.andb_true_iff...
Qed.

Theorem shape_eq_sym : forall A B,
  shape_eq A B = true ->
  shape_eq B A = true.
Proof with auto.
  induction A using formula_ind_naive; destruct B; try discriminate; simpl; auto;
  try repeat rewrite Bool.andb_true_iff; intros [H1 H2]...
Qed.

Theorem shape_eq_trans : forall A B C,
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

Theorem ranks_equal_if_shape_eq : forall A B,
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

Theorem rank_eq_if_shape_eq : forall φ ψ,
    shape_eq φ ψ = true ->
    rank φ = rank ψ.
Proof. intros. apply ranks_equal_if_shape_eq in H. lia. Qed.

Ltac deduce_rank_eq Hsame :=
  let Htemp := fresh in
  let Hfr := fresh "Hfr" in
  let Hqr := fresh "Hqr" in
  apply ranks_equal_if_shape_eq in Hsame as Htemp;
  destruct Htemp as [Hfr Hqr].

Hint Extern 2 (shape_eq ?A ?A = true) =>
  apply shape_eq_refl : core.

Theorem subst_preserves_shape : forall A x a r,
  shape_eq A (subst_formula_qrank r A x a) = true.
Proof with auto.
  intros A.
  apply (formula_rank_ind (fun P => forall x a r,
      shape_eq P (subst_formula_qrank r P x a) = true))...
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
  - subst. destruct r; simpl in *.
    + destruct (String.eqb_spec x x')...
    + fold_qrank_subst (S r) φ x (fresh_quantifier x φ a).
      destruct (String.eqb_spec x x'); try lia...
      remember (subst_formula_qrank (S r) φ x (fresh_quantifier x φ a))
        as φ₁. (* the first substitution *)
      remember (subst_formula_qrank r φ₁ x' a)
        as φ₂. (* the second substituion *)
      specialize IH with (m:=rank φ) (ψ:=φ) as IHφ.
      specialize IH with (m:=rank φ₁) (ψ:=φ₁) as IHφ₁.
      forward IHφ by lia. forward IHφ by auto.
      specialize (IHφ x (fresh_quantifier x φ a) (S r)). (* φ₁ *)
      forward IHφ₁. { deduce_rank_eq IHφ. rewrite Heqφ₁. lia. }
      forward IHφ₁ by reflexivity. specialize (IHφ₁ x' a r).
      rewrite <- Heqφ₁ in *. rewrite <- Heqφ₂ in *.
      apply shape_eq_trans with φ₁...
  - subst. destruct r; simpl in *.
    + destruct (String.eqb_spec x x')...
    + fold_qrank_subst (S r) φ x (fresh_quantifier x φ a).
      destruct (String.eqb_spec x x'); try lia...
      remember (subst_formula_qrank (S r) φ x (fresh_quantifier x φ a))
        as φ₁. (* the first substitution *)
      remember (subst_formula_qrank r φ₁ x' a)
        as φ₂. (* the second substituion *)
      specialize IH with (m:=rank φ) (ψ:=φ) as IHφ.
      specialize IH with (m:=rank φ₁) (ψ:=φ₁) as IHφ₁.
      forward IHφ by lia. forward IHφ by auto.
      specialize (IHφ x (fresh_quantifier x φ a) (S r)). (* φ₁ *)
      forward IHφ₁. { deduce_rank_eq IHφ. rewrite Heqφ₁. lia. }
      forward IHφ₁ by reflexivity. specialize (IHφ₁ x' a r).
      rewrite <- Heqφ₁ in *. rewrite <- Heqφ₂ in *.
      apply shape_eq_trans with φ₁...
Qed.

Theorem formula_ind : forall P,
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

Definition state := gmap string value.

Record fdef := mkFdef {
    fdef_arity : nat;
    fdef_rel : vec value fdef_arity -> value -> Prop;
    fdef_functional : forall args v₁ v₂, fdef_rel args v₁ /\ fdef_rel args v₂
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
  | TEval_Func : forall f args argsv fval,
    teval_args M σ args argsv ->
    fn_eval M f argsv fval ->
    teval M σ (TApp f args) (fval)
with teval_args (M : semantics) (σ : state) : list term -> list value -> Prop :=
  | TEvalArgs_Nil : teval_args M σ [] []
  | TEvalArgs_Cons : forall t ts v vs,
    teval M σ t v ->
    teval_args M σ ts vs ->
    teval_args M σ (t::ts) (v::vs).

Scheme teval_ind_mut := Induction for teval Sort Prop
with teval_args_ind_mut := Induction for teval_args Sort Prop.

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
