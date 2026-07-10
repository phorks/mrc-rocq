From Stdlib Require Import List.
From stdpp Require Import base tactics.
From MRC Require Import Prelude Tactics.

Module ListBag.
  Record t (A : Type) := make {
    car : list A;
  }.

  Section listbag.
    Context {A : Type}.

    Global Instance listbag_EqDecision `{EqDecision A} : EqDecision (t A).
    Proof.
      intros b1 b2. unfold Decision, EqDecision. destruct b1, b2. pose proof (list_eq_dec).
      specialize (X A). forward X by solve_decision. specialize (X car0 car1). destruct X.
      - subst. left. f_equal.
      - right. intros contra. inversion contra. done.
    Qed.
  (* Section listbag. *)
  (*   Context {A : Type}. *)
  (*   Context (compare : A -> A -> comparison). *)

  (*   (* Private type - constructors not exported *) *)

  (*   (* Smart constructor - only way to create a Bag *) *)
  (*   Definition from_list (l : list A) : t. *)
  (*   Proof. *)
  (*     refine (make (sort (fun x y =>  *)
  (*       match compare x y with  *)
  (*       | Lt => Lt  *)
  (*       | _ => Gt  *)
  (*       end) l) _). *)
  (*     admit. (* Prove sorted *) *)
  (*   Defined. *)

  (*   (* Public operations *) *)
  (*   Definition empty : t := from_list []. *)

  (*   Definition insert (x : A) (b : t) : t := *)
  (*     from_list (x :: elements b). *)

  (*   Definition union (b1 b2 : t) : t := *)
  (*     from_list (elements b1 ++ elements b2). *)

  (*   Fixpoint count_aux (x : A) (l : list A) : nat := *)
  (*     match l with *)
  (*     | [] => 0 *)
  (*     | y :: ys =>  *)
  (*         match compare x y with *)
  (*         | Eq => S (count_aux x ys) *)
  (*         | _ => count_aux x ys *)
  (*         end *)
  (*     end. *)

  (*   Definition count (x : A) (b : t) : nat := *)
  (*     count_aux x (elements b). *)

  (*   (* Equality - structural equality of elements *) *)
  (*   Definition eq (b1 b2 : t) : Prop := *)
  (*     elements b1 = elements b2. *)

  (*   (* Decidable equality *) *)
  (*   Definition eq_dec (b1 b2 : t) : {eq b1 b2} + {~ eq b1 b2}. *)
  (*   Proof. *)
  (*     destruct (list_eq_dec (po_eq_dec) (elements b1) (elements b2)). *)
  (*     - left; unfold eq; auto. *)
  (*     - right; unfold eq; intro H; apply n; auto. *)
  (*   Defined. *)

  (*   (* For internal use in the same file - can access elements *) *)
  (*   (* But external files cannot! *) *)

  (* End Bag. *)
End ListBag.
