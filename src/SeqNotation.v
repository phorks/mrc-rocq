From Stdlib Require Import Lists.List. Import ListNotations.
From stdpp Require Import base.
From MRC Require Import Prelude.
From MRC Require Import Model.

Declare Custom Entry var_seq.
Declare Custom Entry var_seq_elem.

Notation "xs" := (xs) (in custom var_seq at level 0,
                       xs custom var_seq_elem)
    : refiney_scope.
Notation "∅" := ([]) (in custom var_seq at level 0)
    : refiney_scope.

Notation "x" := ([x]) (in custom var_seq_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "↑ₓ xs" := (as_var <$> xs)
                      (in custom var_seq_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑ₓ( xs )" := (as_var <$> xs)
                      (in custom var_seq_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "↑₀ xs" := (initial_var_of <$> xs)
                      (in custom var_seq_elem at level 5, xs constr at level 0)
    : refiney_scope.
Notation "↑₀( xs )" := (initial_var_of <$> xs)
                      (in custom var_seq_elem at level 5, only parsing, xs constr at level 200)
    : refiney_scope.
Notation "$( x )" := ([x]) (in custom var_seq_elem at level 5,
                           only parsing,
                           x constr at level 200)
    : refiney_scope.
Notation "* x" := x (in custom var_seq_elem at level 0, x constr at level 0)
    : refiney_scope.
Notation "*$( x )" := x (in custom var_seq_elem at level 5, only parsing, x constr at level 200)
    : refiney_scope.
Infix "," := app (in custom var_seq_elem at level 10, right associativity) : refiney_scope.
(* Open Scope refiney_scope. *)
(* Notation "'seq' s" := s (at level 10, s custom seq_notation). *)

(* Definition l := [3; 4]. *)
(* Definition ss : list nat := seq *l. *)

(* Print ss. *)
