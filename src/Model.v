From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From MRC Require Import Options.
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
(*     var_sub x <= n → *)
(*     var_with_sub x (n) = var_increase_sub x (n - var_sub x). *)
(* Proof. *)

Coercion simple_var : string >-> variable.

Record val := mkVal {
  val_t : Type;
  val_ty : Type;
  val_typeof : val_t → val_ty;
  val_inhabited : Inhabited val_t;
  val_ty_eq_dec : EqDecision val_ty;
  val_ty_inhabited_dec : ∀ τ : val_ty, {x : val_t ? val_typeof x = τ}
}.

Section model.
  Context (V : val).
  Let value := val_t V.
  Let value_ty := val_ty V.
  Let value_typeof := val_typeof V.

  Global Instance val_ty_eq_dec' : EqDecision value_ty := val_ty_eq_dec V.

  Definition val_has_type (v : value) (τ : value_ty) : bool := value_typeof v =? τ.

  Global Instance val_ty_elem_of : ElemOf value value_ty := {
    elem_of v τ := Is_true (val_has_type v τ)
  }.

  Global Instance gset_elem_of_dec : RelDecision (∈@{value_ty}) | 1 := {
    decide_rel v τ := Is_true_dec (val_has_type v τ)
  }.

  Lemma val_elem_of_iff_typeof_eq : ∀ (v : value) τ,
      v ∈ τ ↔ value_typeof v =? τ.
  Proof. reflexivity. Qed.


  Lemma val_elem_of_det : ∀ (v : value) (τ1 τ2 : value_ty),
      v ∈ τ1 → v ∈ τ2 → τ1 = τ2.
  Proof.
    intros v τ1 τ2 H1 H2. unfold elem_of, val_ty_elem_of, val_has_type.
    unfold value_ty in *. rewrite val_elem_of_iff_typeof_eq in H1, H2.
    apply bool_decide_unpack in H1, H2. subst. reflexivity.
  Qed.

  Lemma val_elem_ofb_det : ∀ (v : value) (τ1 τ2 : value_ty),
      v ∈? τ1 → v ∈? τ2 → τ1 = τ2.
  Proof.
    intros v τ1 τ2 H1 H2. apply bool_decide_unpack in H1, H2. apply (val_elem_of_det v); auto.
  Qed.

  Definition val_ty_is_empty (τ : value_ty) := ∀ x, x ∉ τ.

  Fixpoint args_match_sig (args : list value) (sig : list value_ty) :=
    match args, sig with
    | [], [] => true
    | arg :: args, param :: params =>
        if arg ∈? param
        then args_match_sig args params
        else false
    | _, _ => false
    end.

  Record fdef := mkFdef {
      fdef_sig : list value_ty * value_ty;
      fdef_rel : ∀ args, args_match_sig args fdef_sig.1 → ∀ v, v ∈ fdef_sig.2 → Prop;
      fdef_dec : ∀ {args Hsig1 Hsig2 v1 v2 Hret1 Hret2},
                       fdef_rel args Hsig1 v1 Hret1 →
                       fdef_rel args Hsig2 v2 Hret2 →
                       v1 = v2;
      fdef_total : ∀ args H, ∃ v Hret, fdef_rel args H v Hret;
  }.

  Record pdef := mkPdef {
    pdef_sig : list value_ty;
    pdef_rel : ∀ args, args_match_sig args pdef_sig → Prop;
  }.

End model.

Arguments val_has_type {V}.
Arguments val_elem_of_iff_typeof_eq {V}.
Arguments val_elem_of_det {V}.
Arguments val_elem_ofb_det {V}.
Arguments args_match_sig {V}.

Ltac destr_val_ty_is_empty V τ :=
  let H := fresh "H" in
  let Hempty := fresh "Hempty" in
  let v0 := fresh "v0" in
  let Hv0 := fresh "Hv0" in
  destruct (val_ty_inhabited_dec V τ) as [[v0 Hv0]|H];
  [
    rewrite <- eq_dec_eq in Hv0; rewrite <- val_elem_of_iff_typeof_eq in Hv0
  | assert (Hempty : val_ty_is_empty V τ);
    first (unfold val_ty_is_empty; intros; rewrite val_elem_of_iff_typeof_eq;
            rewrite eq_dec_eq; apply H); clear H
  ].


Record model := mkModel {
  model_val : val;
  model_fdefs : gmap string (fdef model_val);
  model_pdefs : gmap string (pdef model_val);
}.
