From stdpp Require Import sets vector.
From MRC Require Import Prelude.

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

Class LengthEqLists {A B} (l1 : list A) (l2 : list B) :=
  length_eq_lists : length l1 = length l2.

Instance length_eq_lists_nil {A B} : @LengthEqLists A B [] [].
Proof. reflexivity. Defined.

Instance length_eq_lists_cons {A B} {x1 : A} {x2 : B} {l1 : list A} {l2 : list B}
  `{LengthEqLists A B l1 l2} : LengthEqLists (x1::l1) (x2::l2).
Proof. unfold LengthEqLists in *. do 2 rewrite length_cons. lia. Qed.

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
