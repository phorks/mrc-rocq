From Stdlib Require Import Strings.String.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From stdpp Require Import gmap.
(* From MRC Require Import Tactics. *)

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

Record fdef := {
    fdef_arity : nat;
    fdef_rel : vec value fdef_arity -> value -> Prop;
    fdef_functional : forall args v₁ v₂, fdef_rel args v₁ /\ fdef_rel args v₂
}.

Class symFdef (fsym : string) := {
  sym_fdef : fdef
}.

Unset Elimination Schemes.
Inductive term : Type :=
  | TConst (v : value)
  | TVar (x : string)
  | TApp (symbol : string) (args : list term).
Set Elimination Schemes.

(* Fixpoint term_rank t := *)
(*   match t with *)
(*   | TConst _ => 0 *)
(*   | TVar _ => 0 *)
(*   | TApp f args => 1  *)
(*     + fold_right max 0 (map (fun arg => term_rank arg) args) *)
(*   end. *)

(* Theorem term_rank_app_gt_args : forall f args arg, *)
(*   In arg args -> *)
(*   term_rank arg < term_rank (TApp f args). *)
(* Proof with auto. *)
(*   intros f args arg HIn. *)
(*   simpl. unfold In in HIn. induction args. *)
(*   - destruct HIn. *)
(*   - destruct HIn as [HIn | HIn]. *)
(*     + rewrite HIn in *. simpl. lia. *)
(*     + simpl in *. remember (fold_right Init.Nat.max 0 *)
(*         (map (fun arg0 : term => term_rank arg0) args)) as others. *)
(*       assert (HMax :=  *)
(*         (Nat.max_spec (term_rank a) (others))). *)
(*       destruct HMax as [[H1 H2] | [H1 H2]]; rewrite H2; try lia... *)
(*       * forward IHargs... lia. *)
(* Qed. (* TODO: I did this proof blindly, maybe it can be simplified *) *)

(* Theorem term_rank_induction : forall P, *)
(*   (forall n, *)
(*     (forall m, m < n ->  *)
(*       forall u, term_rank u = m -> P u) -> *)
(*     (forall t, term_rank t = n -> P t)) ->  *)
(*   forall n t, term_rank t < n -> P t. *)
(* Proof with auto. *)
(*   intros P Hind n. induction n; intros t Hrank. *)
(*   - lia. *)
(*   - apply Hind with (term_rank t)... *)
(*     intros m Hlt u Hu. apply IHn. lia. *)
(* Qed. *)

(* Theorem term_ind : forall P, *)
(*   (forall v, P (T_Const v)) -> *)
(*   (forall x, P (T_Var x)) -> *)
(*   (forall f args,  *)
(*     (forall arg, In arg args -> P arg) -> P (T_Func f args)) -> *)
(*   (forall t, P t). *)
(* Proof with auto. *)
(*   intros P Hconst Hvar Hfunc t. *)
(*   apply (term_rank_induction P) with (term_rank t + 1); try lia... *)
(*   clear t. intros n IH t Htr. destruct t... *)
(*   apply Hfunc. intros arg HIn.  *)
(*   apply term_rank_app_gt_args with (f:=symbol) in HIn. *)
(*   apply IH with (term_rank arg); lia. *)
(* Qed. *)

Definition state := gmap string value.

Record pdef := {
  pdef_arity : nat;
  pdef_rel : vec value pdef_arity -> bool -> Prop;
  pdef_functional : forall args b₁ b₂,
    pdef_rel args b₁ ->
    pdef_rel args b₂ ->
    b₁ = b₂
}.

Class symPdef (psym : string) := {
  sym_pdef : pdef
}.

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
  | AT_Pred (symbol : string) (args : list term).

Unset Elimination Schemes.
Inductive formula : Type :=
  | F_Simple (sf : simple_formula)
  | F_Not (f : formula)
  | F_And (f₁ f₂ : formula)
  | F_Or (f₁ f₂ : formula)
  | F_Implies (f₁ f₂ : formula)
  | F_Iff (f₁ f₂ : formula)
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


Notation "<[ e ]>" := e (e custom formula_aux) : formula_scope.
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
Notation "x = y" := (AT_Pred "=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <> y" := (AT_Pred "<>" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity, only parsing).
Notation "x ≠ y" := (AT_Pred "<>" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity, only printing).
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
Notation "x <=> y" := (F_Iff x y) (in custom formula at level 80, only parsing).
Notation "x ⇔ y" := (F_Iff x y) (in custom formula at level 80, only printing).
Notation "'exists' x .. y ',' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only parsing).
Notation "'∃' x .. y '●' f" := (F_Exists x .. (F_Exists y f) ..) (in custom formula at level 85, only printing).
Notation "'forall' x .. y ',' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).
Notation "'∀' x .. y '●' f" := (F_Forall x .. (F_Forall y f) ..) (in custom formula at level 85).

Open Scope formula_scope.

(* Definition x : string := "x". *)
(* Definition y : string := "y". *)
(* Definition z : string := "z". *)

(* Definition f : string := "f". *)

Fixpoint appears_in_term x t :=
  match t with
  | TConst v => false
  | TVar y => if (y =? x)%string
    then true
    else false
  | TApp sym args =>
    foldr orb false (map (fun arg => appears_in_term x arg) args)
  end.

Definition appears_in_simple_formula x sf :=
  match sf with
  | AT_Pred sym args => 
    fold_right orb false (map (fun arg => appears_in_term x arg) args)
  | _ => false
  end.

Fixpoint is_free_in x f :=
  match f with
  | F_Simple sf => appears_in_simple_formula x sf
  | F_Not f₁ => is_free_in x f₁
  | F_And f₁ f₂ => (orb (is_free_in x f₁) (is_free_in x f₂))
  | F_Or f₁ f₂ => (orb (is_free_in x f₁) (is_free_in x f₁))
  | F_Implies f₁ f₂ => (orb (is_free_in x f₁) (is_free_in x f₂))
  | F_Iff f₁ f₂ => (orb (is_free_in x f₁) (is_free_in x f₂))
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
  | F_Iff f₁ f₂ => formula_fvars f₁ ∪ formula_fvars f₂
  | F_Exists x f => formula_fvars f ∖ {[x]}
  | F_Forall x f => formula_fvars f ∖ {[x]}
  end.

Open Scope string_scope.
Definition fresh_quantifier (x : string) f a : string :=
  let fvars := formula_fvars f in
  let fix go i (x : string) f fuel : string
    := match fuel with
        | O => "unreachable"
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
  | F_Iff f₁ f₂ => 1 + max (formula_rank f₁) (formula_rank f₂)
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
  | F_Iff f₁ f₂ => max (quantifier_rank f₁) (quantifier_rank f₂)
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
    | F_Iff f₁ f₂ => F_Iff
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

Theorem rank_induction : forall P,
  (forall n,
    (forall m, m < n -> 
      forall B, rank B = m -> P B) ->
    (forall A, rank A = n -> P A)) -> 
  forall n A, rank A < n -> P A.
Proof with auto.
  intros P Hind n. induction n; intros A Hrank.
  - lia.
  - apply Hind with (formula_rank A + quantifier_rank A)...
    intros m Hlt B HB. apply IHn. lia.
Qed.

(* Definition is_quantifier P := *)
(*   match P with *)
(*   | F_Exists y f₁ => true *)
(*   | F_Forall y f₁ => true *)
(*   | _ => false *)
(*   end. *)

(* Definition fcons_same A B := *)
(*   match A, B with *)
(*   | F_Simple _, F_Simple _ => true *)
(*   | F_Not _, F_Not _ => true *)
(*   | F_And _ _, F_And _ _  => true *)
(*   | F_Or _ _, F_Or _ _ => true *)
(*   | F_Implies _ _, F_Implies _ _ => true *)
(*   | F_Iff _ _, F_Iff _ _ => true *)
(*   | F_Exists _ _, F_Exists _ _ => true *)
(*   | F_Forall _ _, F_Forall _ _ => true *)
(*   | _, _ => false *)
(*   end. *)

(* Fixpoint fstruct_same A B := *)
(*   match A, B with *)
(*   | F_Simple _, F_Simple _ => true *)
(*   | F_Not A, F_Not B => fstruct_same A B *)
(*   | F_And A1 A2, F_And B1 B2 =>  *)
(*     fstruct_same A1 B1 && *)
(*     fstruct_same A2 B2 *)
(*   | F_Or A1 A2, F_Or B1 B2 =>  *)
(*     fstruct_same A1 B1 && *)
(*     fstruct_same A2 B2 *)
(*   | F_Implies A1 A2, F_Implies B1 B2 => *)
(*     fstruct_same A1 B1 && *)
(*     fstruct_same A2 B2   *)
(*   | F_Iff A1 A2, F_Iff B1 B2 => *)
(*     fstruct_same A1 B1 && *)
(*     fstruct_same A2 B2   *)
(*   | F_Exists _ A, F_Exists _ B => *)
(*     fstruct_same A B *)
(*   | F_Forall _ A, F_Forall _ B => *)
(*     fstruct_same A B *)
(*   | _, _ => false *)
(*   end. *)

(* Theorem fstruct_same__fcons_same : forall A B, *)
(*   fstruct_same A B = true ->  *)
(*     fcons_same A B = true. *)
(* Proof with auto. *)
(*   intros. destruct A; destruct B; try discriminate... *)
(* Qed. *)

(* Theorem fcons_same_simple : forall sf B, *)
(*   fcons_same (F_Simple sf) B = true -> *)
(*   exists sf', B = F_Simple sf'. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists sf0... *)
(* Qed. *)

(* Theorem fstruct_same_simple : forall sf B, *)
(*   fstruct_same (F_Simple sf) B = true -> *)
(*   exists sf', B = F_Simple sf'. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists sf0... *)
(* Qed. *)

(* Theorem fcons_same_not : forall A1 B, *)
(*   fcons_same <[ ~ A1 ]> B = true -> *)
(*   exists B1, B = <[ ~ B1 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists B... *)
(* Qed. *)

(* Theorem fstruct_same_not : forall A1 B, *)
(*   fstruct_same <[ ~ A1 ]> B = true -> *)
(*   exists B1, B = <[ ~ B1 ]> /\ fstruct_same A1 B1 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists B... *)
(* Qed. *)

(* Theorem fcons_same_and : forall A1 A2 B, *)
(*   fcons_same <[ A1 /\ A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 /\ B2 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists B1, B2... *)
(* Qed. *)

(* Theorem fstruct_same_and : forall A1 A2 B, *)
(*   fstruct_same <[ A1 /\ A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 /\ B2 ]> /\ *)
(*     fstruct_same A1 B1 = true /\ *)
(*     fstruct_same A2 B2 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. *)
(*   apply Bool.andb_true_iff in H. exists B1, B2... *)
(* Qed. *)

(* Theorem fcons_same_or : forall A1 A2 B, *)
(*   fcons_same <[ A1 \/ A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 \/ B2 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists B1, B2... *)
(* Qed. *)

(* Theorem fstruct_same_or : forall A1 A2 B, *)
(*   fstruct_same <[ A1 \/ A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 \/ B2 ]> /\ *)
(*     fstruct_same A1 B1 = true /\ *)
(*     fstruct_same A2 B2 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. *)
(*   apply Bool.andb_true_iff in H. exists B1, B2... *)
(* Qed. *)

(* Theorem fcons_same_implies : forall A1 A2 B, *)
(*   fcons_same <[ A1 => A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 => B2 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists B1, B2... *)
(* Qed. *)

(* Theorem fstruct_same_implies : forall A1 A2 B, *)
(*   fstruct_same <[ A1 => A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 => B2 ]> /\ *)
(*     fstruct_same A1 B1 = true /\ *)
(*     fstruct_same A2 B2 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. *)
(*   apply Bool.andb_true_iff in H. exists B1, B2... *)
(* Qed. *)

(* Theorem fcons_same_iff : forall A1 A2 B, *)
(*   fcons_same <[ A1 <=> A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 <=> B2 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists B1, B2... *)
(* Qed. *)

(* Theorem fstruct_same_iff : forall A1 A2 B, *)
(*   fstruct_same <[ A1 <=> A2 ]> B = true -> *)
(*   exists B1 B2, B = <[ B1 <=> B2 ]> /\ *)
(*     fstruct_same A1 B1 = true /\ *)
(*     fstruct_same A2 B2 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. *)
(*   apply Bool.andb_true_iff in H. exists B1, B2... *)
(* Qed. *)

(* Theorem fcons_same_exists : forall x A1 B, *)
(*   fcons_same <[ exists x, A1 ]> B = true -> *)
(*   exists y B1, B = <[ exists y, B1 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists x1, B... *)
(* Qed. *)

(* Theorem fstruct_same_exists : forall x A1 B, *)
(*   fstruct_same <[ exists x, A1 ]> B = true -> *)
(*   exists y B1, B = <[ exists y, B1 ]> /\ fstruct_same A1 B1 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists x1, B... *)
(* Qed. *)

(* Theorem fcons_same_forall : forall x A1 B, *)
(*   fcons_same <[ forall x, A1 ]> B = true -> *)
(*   exists y B1, B = <[ forall y, B1 ]>. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists x1, B... *)
(* Qed. *)

(* Theorem fstruct_same_forall : forall x A1 B, *)
(*   fstruct_same <[ forall x, A1 ]> B = true -> *)
(*   exists y B1, B = <[ forall y, B1 ]> /\ fstruct_same A1 B1 = true. *)
(* Proof with auto. *)
(*   intros. simpl in H. destruct B; try discriminate. exists x1, B... *)
(* Qed. *)

(* Theorem fstruct_same_refl : forall A, *)
(*   fstruct_same A A = true. *)
(* Proof with auto. *)
(*   intros. induction A using formula_ind_naive; simpl; auto; apply Bool.andb_true_iff... *)
(* Qed. *)

(* Theorem fstruct_same_sym : forall A B, *)
(*   fstruct_same A B = true -> *)
(*   fstruct_same B A = true. *)
(* Proof with auto. *)
(*   induction A using formula_ind_naive; destruct B; try discriminate; simpl; auto; *)
(*   try repeat rewrite Bool.andb_true_iff; intros [H1 H2]... *)
(* Qed. *)

(* Theorem fstruct_same_trans : forall A B C, *)
(*   fstruct_same A B = true -> *)
(*   fstruct_same B C = true -> *)
(*   fstruct_same A C = true. *)
(* Proof with auto. *)
(*   induction A using formula_ind_naive; intros B C HAB HBC; destruct B; try discriminate; *)
(*     destruct C; try discriminate; simpl;  *)
(*     try solve [inversion HAB; inversion HBC; *)
(*       apply Bool.andb_true_iff in H0 as [H2 H3]; *)
(*       apply Bool.andb_true_iff in H1 as [H0 H1]; *)
(*       rewrite IHA1 with B1 C1; auto; *)
(*       rewrite IHA2 with B2 C2; auto]; *)
(*     try solve [apply IHA with B; auto]... *)
(* Qed. *)

(* Theorem ranks_equal_if_fstruct_same : forall A B, *)
(*   fstruct_same A B = true -> *)
(*     formula_rank A = formula_rank B /\ *)
(*     quantifier_rank A = quantifier_rank B. *)
(* Proof with auto. *)
(*   assert (Hfr: forall A B, fstruct_same A B = true -> *)
(*     formula_rank A = formula_rank B). { *)
(*     intros A; induction A using formula_ind_naive; destruct B; try discriminate;  *)
(*     intros H; simpl; auto; *)
(*     try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2];  *)
(*       auto). } *)
(*     assert (Hqr: forall A B, fstruct_same A B = true -> *)
(*       quantifier_rank A = quantifier_rank B). { *)
(*     intros A. induction A using formula_ind_naive; destruct B; try discriminate;  *)
(*     intros H; simpl; auto; *)
(*     try (inversion H; apply Bool.andb_true_iff in H1 as [H1 H2];  *)
(*       auto). *)
(*   } *)
(*   auto. *)
(* Qed. *)

(* Ltac deduce_rank_eq Hsame :=  *)
(*   let Htemp := fresh in *)
(*   let Hfr := fresh "Hfr" in *)
(*   let Hqr := fresh "Hqr" in *)
(*   apply ranks_equal_if_fstruct_same in Hsame as Htemp; *)
(*   destruct Htemp as [Hfr Hqr]. *)

(* Hint Extern 2 (fstruct_same ?A ?A = true) => *)
(*   apply fstruct_same_refl : core. *)

(* Theorem subst_preserves_structure : forall A x a r, *)
(*   fstruct_same A (subst_formula_qrank r A x a) = true. *)
(* Proof with auto. *)
(*   intros A. *)
(*   apply (rank_induction (fun P => forall x a r, *)
(*       fstruct_same P (subst_formula_qrank r P x a) = true)) *)
(*     with (S (rank A))... *)
(*   clear A. intros n IH. destruct A; *)
(*     intros Hr x a r. *)
(*   - destruct r; simpl in *... *)
(*   - specialize IH with (m:=rank A) (B:=A). *)
(*     destruct r; simpl in *... *)
(*     + fold_qrank_subst 0 A x a. apply IH; try lia... *)
(*     + fold_qrank_subst (S r) A x a. apply IH; try lia... *)
(*   - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1. *)
(*     specialize IH with (m:=rank A2) (B:=A2) as IH2. *)
(*     assert (HMax :=  *)
(*       (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))). *)
(*     destruct HMax as [[H1 H2] | [H1 H2]]; try lia. *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a.  *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a. *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*   - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1. *)
(*     specialize IH with (m:=rank A2) (B:=A2) as IH2. *)
(*     assert (HMax :=  *)
(*       (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))). *)
(*     destruct HMax as [[H1 H2] | [H1 H2]]; try lia. *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a.  *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a. *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*   - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1. *)
(*     specialize IH with (m:=rank A2) (B:=A2) as IH2. *)
(*     assert (HMax :=  *)
(*       (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))). *)
(*     destruct HMax as [[H1 H2] | [H1 H2]]; try lia. *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a.  *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a. *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*   - subst. specialize IH with (m:=rank A1) (B:=A1) as IH1. *)
(*     specialize IH with (m:=rank A2) (B:=A2) as IH2. *)
(*     assert (HMax :=  *)
(*       (Nat.max_spec (quantifier_rank A1) (quantifier_rank A2))). *)
(*     destruct HMax as [[H1 H2] | [H1 H2]]; try lia. *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a.  *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*     + destruct r; simpl in *; rewrite H2 in *. *)
(*       * fold_qrank_subst 0 A2 x a. fold_qrank_subst 0 A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia... *)
(*       * fold_qrank_subst (S r) A2 x a. *)
(*         fold_qrank_subst (S r) A1 x a. *)
(*         apply Bool.andb_true_iff. split;  *)
(*           [apply IH1|apply IH2]; lia...                               *)
(*   - subst. destruct r; simpl in *. *)
(*     + destruct (eqb_spec x0 x)... *)
(*     + fold_qrank_subst (S r) A x0 (fresh_quantifier x0 A a). *)
(*       destruct (eqb_spec x0 x); try lia... *)
(*       remember (subst_formula_qrank (S r) A x0 (fresh_quantifier x0 A a)) *)
(*         as F₁. (* the first substitution *) *)
(*       remember (subst_formula_qrank r F₁ x a) *)
(*         as F₂. (* the second substituion *) *)
(*       specialize IH with (m:=rank A) (B:=A) as IHA. *)
(*       specialize IH with (m:=rank F₁) (B:=F₁) as IHF₁. *)
(*       forward IHA by lia. forward IHA by auto.       *)
(*       specialize (IHA x0 (fresh_quantifier x0 A a) (S r)). (* F₁ *) *)
(*       forward IHF₁. { deduce_rank_eq IHA. rewrite HeqF₁. lia. } *)
(*       forward IHF₁ by reflexivity. specialize (IHF₁ x a r). *)
(*       rewrite <- HeqF₁ in *. rewrite <- HeqF₂ in *. *)
(*       apply fstruct_same_trans with F₁... *)
(*   - subst. destruct r; simpl in *. *)
(*     + destruct (eqb_spec x0 x)... *)
(*     + fold_qrank_subst (S r) A x0 (fresh_quantifier x0 A a). *)
(*       destruct (eqb_spec x0 x); try lia... *)
(*       remember (subst_formula_qrank (S r) A x0 (fresh_quantifier x0 A a)) *)
(*         as F₁. (* the first substitution *) *)
(*       remember (subst_formula_qrank r F₁ x a) *)
(*         as F₂. (* the second substituion *) *)
(*       specialize IH with (m:=rank A) (B:=A) as IHA. *)
(*       specialize IH with (m:=rank F₁) (B:=F₁) as IHF₁. *)
(*       forward IHA by lia. forward IHA by auto.       *)
(*       specialize (IHA x0 (fresh_quantifier x0 A a) (S r)). (* F₁ *) *)
(*       forward IHF₁. { deduce_rank_eq IHA. rewrite HeqF₁. lia. } *)
(*       forward IHF₁ by reflexivity. specialize (IHF₁ x a r). *)
(*       rewrite <- HeqF₁ in *. rewrite <- HeqF₂ in *. *)
(*       apply fstruct_same_trans with F₁... *)
(* Qed. *)

(* Theorem formula_ind : forall P, *)
(*   (forall sf, P (F_Simple sf)) -> *)
(*   (forall f, P f -> P <[ ~ f ]>) -> *)
(*   (forall f₁ f₂, P f₁ -> P f₂ -> P <[ f₁ /\ f₂ ]>) -> *)
(*   (forall f₁ f₂, P f₁ -> P f₂ -> P <[ f₁ \/ f₂ ]>) -> *)
(*   (forall f₁ f₂, P f₁ -> P f₂ -> P <[ f₁ => f₂ ]>) -> *)
(*   (forall f₁ f₂, P f₁ -> P f₂ -> P <[ f₁ <=> f₂ ]>) -> *)
(*   (forall x f, (forall v, P (f[x \ v])) -> P <[ exists x, f ]>) -> *)
(*   (forall x f, (forall v, P (f[x \ v])) -> P <[ forall x, f ]>) -> *)
(*   forall A, P A. *)
(* Proof with auto. *)
(*   intros P Hsf Hnot Hand Hor Himpl Hiff Hsome Hall A. *)
(*   apply rank_induction with (formula_rank A + quantifier_rank A + 1). *)
(*   - clear A. intros n IH. destruct A; intros Hrank. *)
(*     + apply Hsf. *)
(*     + simpl in *. assert (PA: P A). { *)
(*       apply IH with (formula_rank A + quantifier_rank A)... *)
(*       lia. } *)
(*       apply Hnot. assumption. *)
(*     + simpl in *. assert (PA1: P A1). {  *)
(*       apply IH with (formula_rank A1 + quantifier_rank A1)... *)
(*       lia. } assert (PA2: P A2). {  *)
(*       apply IH with (formula_rank A2 + quantifier_rank A2)... *)
(*       lia. } auto. *)
(*     + simpl in *. assert (PA1: P A1). {  *)
(*       apply IH with (formula_rank A1 + quantifier_rank A1)... *)
(*       lia. } assert (PA2: P A2). {  *)
(*       apply IH with (formula_rank A2 + quantifier_rank A2)... *)
(*       lia. } auto. *)
(*     + simpl in *. assert (PA1: P A1). {  *)
(*       apply IH with (formula_rank A1 + quantifier_rank A1)... *)
(*       lia. } assert (PA2: P A2). {  *)
(*       apply IH with (formula_rank A2 + quantifier_rank A2)... *)
(*       lia. } auto. *)
(*     + simpl in *. assert (PA1: P A1). {  *)
(*       apply IH with (formula_rank A1 + quantifier_rank A1)... *)
(*       lia. } assert (PA2: P A2). {  *)
(*       apply IH with (formula_rank A2 + quantifier_rank A2)... *)
(*       lia. } auto. *)
(*     + simpl in *. assert (PA: forall v, P (A[x0 \ v])). { *)
(*       intros v. *)
(*       apply IH with (rank (A[x0 \ v]))... *)
(*       assert (fstruct_same A <[ A [x0 \ v] ]> = true). { *)
(*         apply subst_preserves_structure. } *)
(*       deduce_rank_eq H. *)
(*       lia. } apply Hsome... *)
(*     + simpl in *. assert (PA: forall v, P (A[x0 \ v])). { *)
(*       intros v. *)
(*       apply IH with (rank (A[x0 \ v]))... *)
(*       assert (fstruct_same A <[ A [x0 \ v] ]> = true). { *)
(*         apply subst_preserves_structure. } *)
(*       deduce_rank_eq H. *)
(*       lia. } apply Hall... *)
(*   - lia. *)
(* Qed. *)

Inductive fdef_eval (fSym : string) (vargs : list value) : value -> Prop :=
  | F_Eval : forall value `{symFdef fSym},
      let fdef := sym_fdef in
      forall hlen : length vargs = fdef_arity fdef,
        fdef_rel fdef (list_to_vec_n vargs hlen) value ->
        fdef_eval fSym vargs value.

Inductive teval (st : state) : term -> value -> Prop :=
  | EvalConst : forall v, teval st (TConst v) v
  | EvalVar : forall x v, st !! x = Some v -> teval st (TVar x) v
  | EvalFunc : forall f args argsv fval,
    teval_args st args argsv ->
    fdef_eval f argsv fval ->
    teval st (TApp f args) (fval)
with teval_args (st : state) : list term -> list value -> Prop :=
  | ArgsEval_nil : teval_args st [] []
  | ArgsEval_cons : forall t ts v vs, 
    teval st t v ->
    teval_args st ts vs ->
    teval_args st (t::ts) (v::vs).

Inductive pdef_eval (pSym : string) (vargs : list value) : bool -> Prop :=
  | Pred_Eval : forall pbool `{symPdef pSym},
    let pdef := sym_pdef in
    forall hlen : length vargs = pdef_arity pdef,
    pdef_rel pdef (list_to_vec_n vargs hlen) pbool ->
    pdef_eval pSym vargs pbool.

Inductive sfeval (st : state) : simple_formula -> bool -> Prop :=
  | SFEval_True : sfeval st AT_True true
  | SFEval_False : sfeval st AT_False false
  | SFEval_Pred : forall pSym args vargs peval,
    teval_args st args vargs ->
    pdef_eval pSym vargs peval ->
    sfeval st (AT_Pred pSym args) peval.

Inductive feval (st : state) : formula -> bool -> Prop :=
  | FEval_Simple : forall sf sfval, 
    sfeval st sf sfval ->
    feval st (F_Simple sf) sfval
  | FEval_Not : forall f fval, 
    feval st f fval ->
    feval st (F_Not f) (negb fval)
  | FEval_And : forall f₁ f₂,
    feval st (f₁) true ->
    feval st (f₂) true ->
    feval st (F_And f₁ f₂) true
  | FEVal_And_False1 : forall f₁ f₂,
    feval st (f₁) false ->
    feval st (F_And f₁ f₂) false
  | FEVal_And_False2 : forall f₁ f₂,
    feval st (f₂) false ->
    feval st (F_And f₁ f₂) false
  | FEval_Or1 : forall f₁ f₂,
    feval st (f₁) true ->
    feval st (F_Or f₁ f₂) true
  | FEval_Or2 : forall f₁ f₂,
    feval st (f₂) true ->
    feval st (F_Or f₁ f₂) true
  | FEval_Or_False : forall f₁ f₂,
    feval st (f₁) false ->
    feval st (f₂) false ->
    feval st (F_Or f₁ f₂) false
  | FEval_Implies1 : forall f₁ f₂,
    feval st f₁ false ->
    feval st (F_Implies f₁ f₂) true
  | FEval_Implies2 : forall f₁ f₂,
    feval st f₂ true ->
    feval st (F_Implies f₁ f₂) true
  | FEval_Implies_False : forall f₁ f₂,
    feval st f₁ true ->
    feval st f₂ false ->
    feval st (F_Implies f₁ f₂) false
  | FEval_Iff : forall f₁ f₁val f₂ f₂val,
    feval st (f₁) f₁val ->
    feval st (f₂) f₂val ->
    feval st (F_Iff f₁ f₂) (Bool.eqb f₁val f₂val)
  | FEval_Exists : forall x f, 
    (exists v, feval st (f[x \ v]) true) ->
    feval st (F_Exists x f) true
  | FEval_Exists_False : forall x f,
    (forall v, feval st (f[x \ v]) false) ->
    feval st (F_Exists x f) false
  | FEval_Forall : forall x f, 
    (forall v, feval st (f[x \ v]) true) ->
    feval st (F_Forall x f) true
  | FEval_Forall_False : forall x f,
    (exists v, feval st (f[x \ v]) false) ->
    feval st (F_Forall x f) false.

Hint Constructors feval : core.
