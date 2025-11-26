From Stdlib Require Import Lists.List. Import ListNotations.
From MRC Require Import Prelude.

Declare Custom Entry bracketed_seq_notation.
Declare Custom Entry seq_notation.
Declare Custom Entry seq_elem.

Notation "⟨ xs ⟩" := (xs) (in custom bracketed_seq_notation, only parsing,
                           xs custom seq_elem)
    : refiney_scope.
Notation "xs" := (xs) (in custom bracketed_seq_notation at level 0,
                       only printing,
                       xs custom seq_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom bracketed_seq_notation at level 0)
    : refiney_scope.
Notation "* xs" := xs (in custom bracketed_seq_notation at level 0,
                         xs constr at level 0,
                         only parsing)
    : refiney_scope.
Notation "*$( xs )" := xs (in custom bracketed_seq_notation at level 0,
                             xs constr at level 200,
                             only parsing)
    : refiney_scope.



Notation "xs" := (xs) (in custom seq_notation at level 0,
                       xs custom seq_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom seq_notation at level 0)
    : refiney_scope.

Notation "x" := ([x]) (in custom seq_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "$( x )" := ([x]) (in custom seq_elem at level 5,
                           only parsing,
                             x constr at level 200)
    : refiney_scope.
Notation "* x" := x (in custom seq_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "*$( x )" := x (in custom seq_elem at level 5, x constr at level 200)
    : refiney_scope.
Infix "," := app (in custom seq_elem at level 10, right associativity) : refiney_scope.
(* Open Scope refiney_scope. *)
(* Notation "'seq' s" := s (at level 10, s custom seq_notation). *)

(* Definition l := [3; 4]. *)
(* Definition ss : list nat := seq *l. *)

(* Print ss. *)
