From stdpp Require Import sets.

(* HACK: These are not currently used. I will keep them as reference.
   I should delete them at some point. *)
Section sets.
  Context `{Set_ A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Lemma difference_singleton_not_elem_of : forall X x,
    x ∉ X ->
    X ∖ {[x]} ≡ X.
  Proof. set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    Lemma difference_singleton_not_elem_of_L : forall X x,
      x ∉ X ->
      X ∖ {[x]} = X.
    Proof. set_solver. Qed.
  End leibniz.
End sets.
