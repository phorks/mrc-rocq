From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Stdppp.

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

Definition raw_var name := mkVar name 0 false.
Definition var_with_sub x i :=
  mkVar (var_name x) (i) (var_is_initial x).
Definition var_increase_sub x i :=
  var_with_sub x (var_sub x + i).
Definition var_with_is_initial x is_initial :=
  mkVar (var_name x) (var_sub x) (is_initial).

Coercion raw_var : string >-> variable.
(* Notation "x '₀'" := (final_var_i x). *)

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

Definition as_var (x : final_variable) := mkVar (final_var_name x) (final_var_sub x) false.
Coercion as_var : final_variable >-> variable.
Definition as_var_F `{FMap F} (x : F final_variable) : F variable := as_var <$> x.
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

Record fdef {value value_ty} {hastype : value → value_ty → Prop} := mkFdef {
  fdef_sig : list value → value_ty;
  fdef_rel : list value → value → Prop;
  fdef_typing : ∀ args v, fdef_rel args v → hastype v (fdef_sig args);
  fdef_det : ∀ {args v1 v2}, fdef_rel args v1 → fdef_rel args v2 → v1 = v2;
  fdef_total : ∀ args, ∃ v, fdef_rel args v;
}.

Record pdef {value} := mkPdef {
  pdef_arity : nat;
  pdef_rel : vec value pdef_arity → Prop;
}.

(* Ltac destr_value_ty_choice V τ := *)
(*   let H := fresh "H" in *)
(*   let Hempty := fresh "Hempty" in *)
(*   let v0 := fresh "v0" in *)
(*   let Hv0 := fresh "Hv0" in *)
(*   destruct (value_ty_choice V τ) as [[v0 Hv0]|H]; *)
(*   [ *)
(*     rewrite <- eq_dec_eq in Hv0; rewrite <- value_elem_of_iff_typeof_eq in Hv0 *)
(*   | assert (Hempty : value_ty_is_empty V τ); *)
(*     first (unfold value_ty_is_empty; intros; rewrite value_elem_of_iff_typeof_eq; *)
(*             rewrite eq_dec_eq; apply H); clear H *)
(*   ]. *)

Record model := mkModel {
  value : Type;
  value_ty : Type;
  value_bottom : value;
  hastype : value → value_ty → Prop;
  as_nat : value → option nat;
  fdefs : gmap string (@fdef value value_ty hastype);
  pdefs : gmap string (@pdef value);
}.

Global Instance model_value_bottom {M} : Bottom (value M) := value_bottom M.
Global Instance model_value_Inhabited {M} : Inhabited (value M) := populate (value_bottom M).
