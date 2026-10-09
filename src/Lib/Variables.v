From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From MRC Require Import Prelude.
From MRC.Lib Require Import Base Tactics.

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
Global Instance variable_inhabited : Inhabited variable := populate (mkVar "" 0 false).

Definition raw_var name := mkVar name 0 false.
Definition var_with_sub x i :=
  mkVar (var_name x) (i) (var_is_initial x).
Definition var_increase_sub x i :=
  var_with_sub x (var_sub x + i).
Definition var_with_is_initial x is_initial :=
  mkVar (var_name x) (var_sub x) (is_initial).

Coercion raw_var : string >-> variable.

Lemma var_with_sub_var_sub_id : forall x,
    var_with_sub x (var_sub x) = x.
Proof. intros. unfold var_with_sub. destruct x. reflexivity. Qed.

Lemma var_with_sub_idemp : forall x i j,
  var_with_sub (var_with_sub x j) i = var_with_sub x i.
Proof. intros. unfold var_with_sub. reflexivity. Qed.

Lemma var_sub_of_var_with_sub : forall x i,
    var_sub (var_with_sub x i) = i.
Proof. reflexivity. Qed.

Lemma var_with_is_initial_id x is_initial :
  var_with_is_initial x is_initial = x ↔ var_is_initial x = is_initial.
Proof.
  split; intros.
  - rewrite <- H. simpl. reflexivity.
  - cbv. rewrite <- H. destruct x. simpl. reflexivity.
Qed.


Hint Rewrite var_with_sub_var_sub_id : core.
Hint Rewrite var_with_sub_idemp : core.

(* ******************************************************************* *)
(* final variables                                                     *)
(* ******************************************************************* *)

Record final_variable := mkFinalVar {
  final_var_name : string;
  final_var_sub : nat;
}.

Global Instance final_variable_eq_dec : EqDecision final_variable. Proof. solve_decision. Defined.
Global Instance final_variable_countable : Countable final_variable.
Proof.
  refine (
    {| encode v := encode (final_var_name v, final_var_sub v);
       decode t :=
         match decode t with
         | Some (n, s) => Some (mkFinalVar n s)
         | None => None
         end
    |}).
  intros [n s]. simpl. rewrite decode_encode. reflexivity.
Defined.
Global Instance final_variable_inhabited : Inhabited final_variable :=
  populate (mkFinalVar "" 0).

Definition as_var (x : final_variable) := mkVar (final_var_name x) (final_var_sub x) false.
Coercion as_var : final_variable >-> variable.

Definition as_var_F `{FMap F} (x : F final_variable) : F variable := as_var <$> x.
Definition as_var_set (vs : gset final_variable) : gset variable :=
  set_map as_var vs.

Global Instance as_var_inj : Inj (=) (=) as_var.
Proof.
  intros x1 x2 H. unfold as_var in H. inversion H. destruct x1; destruct x2. simpl in *;
    rewrite H1; rewrite H2; reflexivity.
Qed.


Definition initial_var_of (x : final_variable) := mkVar (var_name x) (var_sub x) true.
Notation "₀ x" := (initial_var_of x) (at level 5, format "₀ x").

Instance initial_var_of_inj : Inj (=) (=) initial_var_of.
Proof.
  intros x1 x2 Heq. unfold initial_var_of in Heq. destruct x1, x2.
  simpl in *. inversion Heq. rewrite <- H0. rewrite <- H1. reflexivity.
Qed.

Lemma initial_var_of_ne_iff x1 x2 :
  ₀x1 ≠ ₀x2 ↔ x1 ≠ x2.
Proof.
  split; intros.
  - intros contra. subst x2. contradiction.
  - intros contra. apply initial_var_of_inj in contra. contradiction.
Qed.

Lemma initial_var_of_eq_final_variable (x y : final_variable) :
  initial_var_of x ≠ y.
Proof. destruct x. unfold as_var. done. Qed.

Definition to_final_var x :=
  mkFinalVar (var_name x) (var_sub x).

Lemma to_final_var_as_var (x : final_variable) :
  to_final_var (as_var x) = x.
Proof. cbv. destruct x. reflexivity. Qed.

Lemma to_final_var_initial_var_of (x : final_variable) :
  to_final_var (initial_var_of x) = x.
Proof. cbv. destruct x. reflexivity. Qed.

Lemma as_var_to_final_var (x : variable) :
  as_var (to_final_var x) = var_with_is_initial x false.
Proof. cbv. reflexivity. Qed.

Lemma initial_var_of_eq_var_with_is_initial (x : final_variable) :
  initial_var_of (x) = var_with_is_initial (as_var x) true.
Proof. cbv. reflexivity. Qed.

Lemma var_is_initial_as_var (x : final_variable) :
  var_is_initial (as_var x) = false.
Proof. reflexivity. Qed.

Definition to_initial_var x := var_with_is_initial x true.

(* ******************************************************************* *)
(* fresh variables                                                     *)
(* ******************************************************************* *)

Fixpoint fresh_var_aux x (fvars : gset variable) fuel :=
  match fuel with
  | O => x
  | S fuel =>
      if decide (x ∈ fvars) then fresh_var_aux (var_increase_sub x 1) fvars fuel else x
  end.

Definition fresh_var (x : variable) (fvars : gset variable) : variable :=
  fresh_var_aux x fvars (S (size fvars)).

Notation var_seq x i n := (var_with_sub x <$> seq i n).

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
    var_name x₁ = var_name x₂ →
    var_is_initial x₁ = var_is_initial x₂ →
    var_seq x₁ i n = var_seq x₂ i n.
Proof with auto.
  intros. apply list_fmap_ext. intros j k H1. unfold var_with_sub. f_equal...
Qed.

Lemma length_var_seq : forall x i n,
    length (var_seq x i n) = n.
Proof. intros. rewrite length_map. rewrite length_seq. reflexivity. Qed.

Lemma not_elem_of_var_seq : forall x i n,
    i > var_sub x →
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
    fuel > 0 →
      var_seq x (var_sub x) fuel ⊆+ elements fvars ∨
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

Lemma fresh_var_fresh x fvars :
  fresh_var x fvars ∉ fvars.
Proof with auto.
  intros. assert (Haux := fresh_var_fresh_aux x fvars (S (size fvars))).
  forward Haux by lia. destruct Haux...
  exfalso. apply submseteq_length in H. rewrite length_var_seq in H.
  unfold size, set_size in H. simpl in *. lia.
Qed.

Lemma fresh_var_id x fvars :
  x ∉ fvars →
  fresh_var x fvars = x.
Proof with auto.
  intros. unfold fresh_var. unfold fresh_var_aux.
  destruct (decide (x ∈ fvars))... contradiction.
Qed.

Lemma fresh_var_ne_inv y X :
  fresh_var y X ≠ y →
  y ∈ X.
Proof with auto.
  intros. unfold fresh_var in H. induction X using set_ind_L.
  - unfold fresh_var_aux in H. destruct (decide (y ∈ ∅))... set_solver.
  - unfold fresh_var_aux in H. simpl in H. destruct (decide (y ∈ _))... set_solver.
Qed.

Notation "↑ₓ xs" := (as_var <$> xs)
                      (at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑ₓ( xs )" := (as_var <$> xs)
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "↑₀ xs" := (initial_var_of <$> xs)
                      (at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑₀( xs )" := (initial_var_of <$> xs)
                      (at level 5, only parsing, xs constr at level 200)
    : refiney_scope.

Open Scope refiney_scope.

(** * Properties of final and initial variables *)
Definition var_final x := var_is_initial x = false.
Definition var_initial x := var_is_initial x = true.

Lemma var_final_as_var x : var_final (as_var x).
Proof. reflexivity. Qed.

Lemma var_final_initial_var_of x : ¬ var_final (initial_var_of x).
Proof. cbv. discriminate. Qed.

Lemma initial_var_of_to_final_var x : var_initial x → ₀(to_final_var x) = x.
Proof.
  unfold to_final_var, initial_var_of, var_initial. destruct x. simpl. intros; by subst.
Qed.

Lemma initial_var_of_to_final_var_inv x : ₀(to_final_var x) = x → var_initial x.
Proof.
  unfold to_final_var, initial_var_of, var_initial. destruct x. simpl. by inversion 1.
Qed.

Lemma initial_var_of_initial x : var_initial ₀x.
Proof. done. Qed.

Lemma var_final_not_initial x : var_final x ↔ ¬ var_initial x.
Proof. unfold var_final, var_initial. by destruct (var_is_initial x). Qed.

Lemma var_initial_not_final x : var_initial x ↔ ¬ var_final x.
Proof. unfold var_final, var_initial. by destruct (var_is_initial x). Qed.

Lemma var_initial_or_final x : var_initial x ∨ var_final x.
Proof. unfold var_initial, var_final. destruct (var_is_initial x); auto. Qed.

Lemma var_final_ne_initial_var_of x (y : final_variable) :
  var_final x →
  x ≠ ₀ y.
Proof.
  intros ? contra. destruct x, y. unfold initial_var_of in contra.
  inversion contra. subst. unfold var_final in H. simpl in H. done.
Qed.

Lemma to_initial_var_inj' x y :
  var_final x →
  var_final y →
  to_initial_var x = to_initial_var y →
  x = y.
Proof.
  intros. destruct x. destruct y. unfold var_final in H, H0. simpl in H, H0.
  inversion H1. subst. reflexivity.
Qed.

Lemma var_initial_to_initial_var x : var_initial (to_initial_var x).
Proof. done. Qed.

Lemma to_final_var_inj_initial {x y} :
  var_initial x →
  var_initial y →
  to_final_var x = to_final_var y →
  x = y.
Proof.
  unfold var_initial, to_final_var. intros. inversion H1.
  destruct x; destruct y. simpl in *. naive_solver.
Qed.

Global Instance set_unfold_var_initial_as_var x : SetUnfold (var_initial (as_var x)) False.
Proof. done. Qed.

Class VarFinal (v : variable) := var_is_final : var_final v.

Global Instance non_initial_var_final {x i} : VarFinal (mkVar x i false).
Proof. reflexivity. Qed.

Global Instance as_var_var_final {x} : VarFinal (as_var x).
Proof. reflexivity. Qed.

Lemma as_var_to_final_var_final (x : variable) :
  var_final x →
  as_var (to_final_var x) = x.
Proof.
  intros. rewrite as_var_to_final_var. destruct x. unfold var_final in H.
  unfold Variables.var_is_initial in H. rewrite H. apply var_with_is_initial_id.
  reflexivity.
Qed.

Lemma disjoint_initial_var_of (xs1 xs2 : list final_variable) :
  xs1 ## xs2 →
  ↑₀ xs1 ## ↑₀ xs2.
Proof. set_solver. Qed.

Lemma NoDup_initial_var_of xs :
  NoDup xs →
  NoDup ↑₀ xs.
Proof. intros. apply NoDup_fmap; [apply initial_var_of_inj | assumption]. Qed.

Lemma NoDup_as_var xs :
  NoDup xs →
  NoDup ↑ₓ xs.
Proof. intros. apply NoDup_fmap; [apply as_var_inj | assumption]. Qed.



Global Instance fresh_var_final x fvars `{VarFinal x} : VarFinal (fresh_var x fvars).
Proof with auto.
  unfold VarFinal. generalize dependent x. unfold fresh_var. induction (S (size fvars)); intros.
  - simpl. apply H.
  - simpl. destruct (decide (x ∈ fvars)).
    + apply IHn. unfold VarFinal, var_final in H. destruct x. simpl in H.
      rewrite H. reflexivity.
    + apply H.
Qed.

Lemma to_initial_var_inj x y `{!VarFinal x} `{!VarFinal y} :
  to_initial_var x = to_initial_var y →
  x = y.
Proof with auto. intros. apply to_initial_var_inj'... Qed.

Definition as_final_var x `{VarFinal x} : final_variable :=
  mkFinalVar (var_name x) (var_sub x).

Lemma as_final_var_as_var x H :
  @as_final_var (as_var x) H = x.
Proof. destruct x. unfold as_final_var. simpl. f_equal. Qed.

Lemma as_var_as_final_var x `{VarFinal x} : as_var (as_final_var x) = x.
Proof.
  unfold as_var, as_final_var. unfold VarFinal, var_final in H. destruct x.
  simpl in *. rewrite H. reflexivity.
Qed.

Lemma disjoint_initial_final_vars (xs1 xs2 : gset variable) :
  (∀ x, x ∈ xs1 → ¬ var_final x) →
  (∀ x, x ∈ xs2 → var_final x) →
  xs1 ## xs2.
Proof. intros. set_solver. Qed.

Lemma disjoint_final_initial_vars (xs1 xs2 : gset variable) :
  (∀ x, x ∈ xs1 → var_final x) →
  (∀ x, x ∈ xs2 → ¬ var_final x) →
  xs1 ## xs2.
Proof. intros. set_solver. Qed.

Lemma initial_var_of_eq_to_initial_var (x : final_variable) :
  initial_var_of x = to_initial_var x.
Proof. cbv. reflexivity. Qed.

Lemma set_to_list_as_var_set_list_to_set w :
  NoDup w →
  set_to_list (as_var_set (list_to_set w)) ≡ₚ ↑ₓ w.
Proof with auto.
  intros. unfold as_var_set. rewrite set_to_list_set_map_perm by exact as_var_inj.
  apply fmap_Permutation. apply set_to_list_list_to_set...
Qed.

Lemma var_is_initial_true {x y} :
  ₀x = y → var_is_initial y.
Proof.
  intros. unfold var_is_initial. destruct y. destruct x. unfold initial_var_of in H.
  simpl in H. inversion H. done.
Qed.

Global Hint Resolve disjoint_initial_var_of : core.
Global Hint Resolve NoDup_initial_var_of : core.
Global Hint Resolve NoDup_as_var : core.
Global Hint Resolve initial_var_of_eq_to_initial_var : core.
Global Hint Mode VarFinal ! : typeclass_instances.

Global Hint Extern 0 (var_final (initial_var_of _)) => apply var_final_initial_var_of : core.
Global Hint Extern 0 (as_var _ = as_var _) => apply as_var_inj : core.
Global Hint Extern 0 (as_final_var (as_var ?x) = ?x) => apply as_final_var_as_var : core.
Global Hint Extern 0 (?x = as_final_var (as_var ?x)) => symmetry; apply as_final_var_as_var : core.
Global Hint Extern 0 (as_var (as_final_var ?x) = ?x) => apply as_var_as_final_var : core.
Global Hint Extern 0 (?x = as_var (as_final_var ?x)) => symmetry; apply as_var_as_final_var : core.

Global Hint Extern 0 =>
  match goal with
  | H1 : var_final ?x, H2 : ?x = initial_var_of ?y |- _ =>
      apply (var_final_ne_initial_var_of x y H1) in H2 as []
  | H1 : var_final ?x, H2 : initial_var_of ?y = ?x |- _ =>
      symmetry in H2;
      apply (var_final_ne_initial_var_of x y H1) in H2 as []
  end : core.
Global Hint Extern 100 (var_final _) => apply var_final_not_initial : core.
Global Hint Resolve var_initial_to_initial_var : core.

Global Hint Extern 0 =>
match goal with
| H : ¬ var_initial (to_initial_var _) |- _ =>
    exfalso; apply H; apply var_initial_to_initial_var
| H : ¬ var_final (as_var ?x) |- _ =>
    destruct (H (var_final_as_var x)) as []
| H : var_final (initial_var_of _) |- _ =>
    apply var_final_initial_var_of in H as []
end : core.

Global Hint Extern 0 =>
  match goal with
  | H : var_final ?x     |- VarFinal ?x => apply H
  end : typeclass_instances.

Global Instance set_unfold_to_final_var_initial_var_of {C}
    x (X : C) P `{ElemOf final_variable C} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (to_final_var (₀x)) X P.
Proof. by rewrite to_final_var_initial_var_of. Qed.

Global Instance set_unfold_to_final_var_as_var {C}
    (x : final_variable) (X : C) P `{ElemOf final_variable C} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (to_final_var (as_var x)) X P.
Proof. by rewrite to_final_var_as_var. Qed.

Global Instance set_unfold_as_final_var_as_var {C}
    (x : final_variable) (X : C) P `{ElemOf final_variable C} `{VarFinal x} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (as_final_var (as_var x)) X P.
Proof. by rewrite as_final_var_as_var. Qed.

Global Instance set_unfold_as_var_as_final_var {C}
    (x : variable) (X : C) P `{ElemOf variable C} `{VarFinal x} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (as_var (as_final_var x)) X P.
Proof. by rewrite as_var_as_final_var. Qed.

Global Instance set_unfold_as_var_to_final_var {C}
    (x : variable) (X : C) P `{ElemOf variable C} `{VarFinal x} :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf (as_var (to_final_var x)) X P.
Proof. by rewrite as_var_to_final_var_final. Qed.

Global Instance set_unfold_elem_of_list_to_set_as_var_final_vars x w Q :
  SetUnfoldElemOf (to_final_var x) w Q →
  SetUnfoldElemOf x
    (list_to_set (as_var <$> w) : gset variable)
    (var_final x ∧ Q).
Proof with auto.
  constructor. set_unfold. split.
  - intros (x'&?&?). subst. split; [apply var_final_as_var |]... apply H.
    rewrite to_final_var_as_var...
  - intros []. exists (to_final_var x). set_unfold. split... unfold var_final in H.
    destruct x. cbv. f_equal...
Qed.

Global Instance set_unfold_elem_of_list_to_set_initials_of_final_variables x w Q :
  SetUnfoldElemOf (to_final_var x) w Q →
  SetUnfoldElemOf x
      (list_to_set (initial_var_of <$> w) : gset variable)
      (¬ var_final x ∧ Q).
Proof with auto.
  constructor. set_unfold. split.
  - intros (x'&?&?). subst. split; [apply var_final_initial_var_of|]. apply H.
    rewrite to_final_var_initial_var_of...
  - intros []. exists (to_final_var x). set_unfold. split... unfold var_final in H0.
    apply not_false_is_true in H0. destruct x. simpl in H0. rewrite H0. f_equal.
Qed.

Global Instance set_unfold_simpl_initial_var_of_eq_final {x y} :
  SetUnfoldSimpl (initial_var_of x = as_var y) False.
Proof. do 2 constructor. done. Qed.


(** * Tactics for generating fresh vars *)
Tactic Notation "mk_fresh" uconstr(X) "as" ident(x) :=
  let H := fresh in
  pose proof (fresh_var_fresh ""%string X) as H;
  let Hfinal := fresh "Hfinal" in
  pose proof (fresh_var_final ""%string X) as Hfinal;
  repeat rewrite not_elem_of_union in H;
  let E := fresh in
  remember (fresh_var ""%string X) as x eqn:E;
  clear E.

Tactic Notation "mk_fresh" uconstr(y) uconstr(X) "as" ident(x) :=
  let H := fresh in
  pose proof (fresh_var_fresh y X) as H;
  let Hfinal := fresh "Hfinal" in
  try pose proof (fresh_var_final y X) as Hfinal;
  repeat rewrite not_elem_of_union in H;
  let E := fresh in
  remember (fresh_var y X) as x eqn:E;
  clear E.


(** * Generating multiple unique fresh vars *)
Fixpoint fresh_vars_n (X : gset variable) (n : nat) : list final_variable :=
  match n with
  | 0 => []
  | S n =>
      let rest := (fresh_vars_n X n) in
      let x := fresh_var String.EmptyString ((list_to_set (↑ₓ rest) ∪ X)) in
      as_final_var x :: rest
  end.

Lemma fresh_vars_n_spec X n :
  let l := fresh_vars_n X n in
  NoDup l ∧ X ## list_to_set (↑ₓ l) ∧ length l = n.
Proof with auto.
  simpl. generalize dependent X. induction n.
  - intros. simpl. split_and!...
    + constructor.
    + set_solver.
  - simpl. intros.
    pose proof (fresh_var_fresh String.EmptyString (list_to_set ↑ₓ (fresh_vars_n X n) ∪ X)).
    split_and!...
    + constructor; [|set_solver].
      apply not_elem_of_union in H as [].  apply not_elem_of_list_to_set in H.
      contradict H. apply elem_of_list_fmap.
      exists (as_final_var
                (fresh_var String.EmptyString (list_to_set ↑ₓ (fresh_vars_n X n) ∪ X))).
      split...
    + intros x??. rewrite elem_of_union, elem_of_singleton in H1. destruct H1; [|set_solver].
      subst. rewrite as_var_as_final_var in H0. set_solver.
    + naive_solver.
Qed.

Definition unique_fresh_vars_for (X : gset variable) (xs : list final_variable) :=
  fresh_vars_n (X ∪ list_to_set (↑ₓ xs)) (length xs).

Lemma unique_fresh_vars_for_spec X xs :
  let zs := unique_fresh_vars_for X xs in
    NoDup zs ∧
    zs ## xs ∧
    list_to_set (↑ₓ zs) ## X ∧
    length zs = length xs.
Proof with auto.
  unfold unique_fresh_vars_for.
  pose proof (fresh_vars_n_spec (X ∪ list_to_set (↑ₓ xs)) (length xs)) as (?&?&?).
  repeat rewrite disjoint_union_l in H0. destruct_and! H0.
  split_and!...
  intros x??. apply (H3 x); apply elem_of_list_to_set; set_solver.
Qed.

Definition fresh_vars_for (X : gset variable) xs : list final_variable :=
  zpair_permute (dedup xs) (unique_fresh_vars_for X (dedup xs)) xs.

Lemma fresh_vars_for_subset X xs :
  fresh_vars_for X xs  ⊆ unique_fresh_vars_for X (dedup xs).
Proof with auto.
  pose proof (unique_fresh_vars_for_spec X (dedup xs)) as (_&_&_&?).
  unfold fresh_vars_for. apply zpair_permute_subset; [lia|set_solver].
Qed.

Lemma fresh_vars_for_superset X xs :
  unique_fresh_vars_for X (dedup xs) ⊆ fresh_vars_for X xs.
Proof with auto.
  pose proof (unique_fresh_vars_for_spec X (dedup xs)) as (_&_&_&?).
  unfold fresh_vars_for. apply zpair_permute_superset; [lia| |set_solver]...
Qed.

Lemma fresh_vars_for_equiv X xs :
  fresh_vars_for X xs ≡ unique_fresh_vars_for X (dedup xs).
Proof.
  split.
  - apply fresh_vars_for_subset.
  - apply fresh_vars_for_superset.
Qed.

Lemma fresh_vars_for_length X xs :
  length (fresh_vars_for X xs) = length xs.
Proof. apply zpair_permute_length. Qed.

Global Instance of_same_length_fresh_var_for {X xs} :
  OfSameLength xs (fresh_vars_for X xs).
Proof. symmetry. apply fresh_vars_for_length. Qed.

Lemma fresh_vars_for_zpair_functional X xs :
  zpair_functional xs (fresh_vars_for X xs).
Proof with auto.
  pose proof (unique_fresh_vars_for_spec X (dedup xs)) as (_&_&_&?).
  unfold fresh_vars_for. apply zpair_permute_functional; [lia| |set_solver]...
Qed.

Lemma fresh_vars_for_zpair_injective X xs :
  zpair_injective xs (fresh_vars_for X xs).
Proof with auto.
  pose proof (unique_fresh_vars_for_spec X (dedup xs)) as (?&_&_&?).
  unfold fresh_vars_for. apply zpair_permute_injective; [lia| |set_solver]...
Qed.

Lemma fresh_vars_for_spec X xs :
  let zs := fresh_vars_for X xs in
    zpair_functional xs zs ∧
    zpair_injective xs zs ∧
    zs ## xs ∧
    list_to_set (↑ₓ zs) ## X.
Proof with auto.
  simpl.
  pose proof (fresh_vars_for_subset X xs).
  pose proof (unique_fresh_vars_for_spec X (dedup xs)) as (?&?&?&?).
  pose proof (fresh_vars_for_zpair_functional X xs).
  pose proof (fresh_vars_for_zpair_injective X xs).
  split_and!... all: set_solver.
Qed.
