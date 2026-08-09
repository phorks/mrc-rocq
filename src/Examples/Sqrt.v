From Stdlib Require Import Reals ZArith Sorting.
From stdpp Require Import listset vector.
From MRC Require Import Prog Refinement.
From MRC Require Import SeqNotation.
From MRC.Examples Require Import Model Variables.

Open Scope stdpp_scope.
Open Scope refiney_scope.

Notation Prog := (@prog Model).
Notation Term := (termM Model).
Notation Formula := (formulaM Model).

Definition final_var_to_term (x : Model.final_variable) : term Value Signature := TVar (Model.as_var x).
Coercion final_var_to_term : Model.final_variable >-> Term.

(* Notation "'|[' 'var*' xs ':' ty '⦁' y ']|' " := *)
(*   (PVarList xs y) *)
(*     (in custom prog at level 95, xs custom var_seq, ty custom term_ty, y custom prog) : refiney_scope. *)

(* Definition spec : Prog := <{ |[ var r s : ℕ ⦁ r := ⌊√ s⌋ ]| }>. *)

Definition post : formulaM Model := <! ⌜r = ⌊√ s⌋⌝ !>.
Definition prog1 : Prog := <{ |[ var r s : ℕ ⦁ r : [⌜r = ⌊√ s⌋⌝] ]| }>.

Lemma r1 : spec ≡ prog1.
Proof. unfold spec, prog1, post. by rewrite r_simple_spec. Qed.
