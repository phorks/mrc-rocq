From Equations Require Import Equations.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From stdpp Require Import base list_monad sets.
From MRC Require Import Prelude.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import SeqNotation.
From MRC Require Import PredCalc.Basic.
From MRC Require Import PredCalc.Equiv.
From MRC Require Import PredCalc.SemanticFacts.
From MRC Require Import PredCalc.EquivLemmas.

Section syntactic.
  Context {value : Type}.
  Local Notation term := (term value).
  Local Notation atomic_formula := (atomic_formula value).
  Local Notation formula := (formula value).

  Implicit Types x y : variable.
  Implicit Types t : term.
  Implicit Types af : atomic_formula.
  Implicit Types A : formula.
  Implicit Types xs : list variable.
  Implicit Types ts : list term.
  Implicit Types vs : list value.

  Definition FEqList ts1 ts2 `{OfSameLength _ _ ts1 ts2} : formula :=
    of_same_length_rect
      (λ A, A)
      (λ rec t1 t2 B, <! ⌜t1 = t2⌝ ∧ $(rec B) !>) <! true !> ts1 ts2.

  Fixpoint FAndList (As : list formula) :=
    match As with
    | [] => FAtom AT_True
    | A :: As => FAnd A (FAndList As)
    end.

  Fixpoint FOrList (As : list formula) :=
    match As with
    | [] => FAtom AT_False
    | A :: As => FAnd A (FOrList As)
    end.

  Fixpoint FExistsList (xs : list variable) (A : formula) :=
    match xs with
    | [] => A
    | x :: xs => FExists x (FExistsList xs A)
    end.

  Fixpoint FForallList (xs : list variable) (A : formula) :=
    match xs with
    | [] => A
    | x :: xs => FForall x (FForallList xs A)
    end.

  Definition seq_subst A xs ts `{OfSameLength _ _ xs ts} : formula :=
    of_same_length_rect (λ A, A) (λ rec x t B, <! $(rec B)[x \ t] !>) A xs ts.

  Definition subst_initials {M} A (w : gset final_variable) : (formula (value M)) :=
    simult_subst A (set_to_map (λ x, (₀x, (TVar x))) w).

End syntactic.

Notation "ts =* us" := (FAtom (AT_Eq ts us))
                      (in custom term_relation at level 60,
                          ts custom term at level 60,
                          us custom term at level 60,
                          no associativity) : refiney_scope.
Notation "∧* As" := (FAndList As) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "∧* As" := (FAndList As) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "∨* As" := (FOrList As) (in custom formula at level 75, right associativity) : refiney_scope.
Notation "∃* xs , A" := (FExistsList xs A)
                          (in custom formula at level 99, only parsing)
    : refiney_scope.
Notation "∃* xs ● A" := (FExistsList xs A)
                          (in custom formula at level 99, only printing)
    : refiney_scope.
Notation "∀* xs , A" := (FForallList xs A)
                              (in custom formula at level 99, only parsing)
    :refiney_scope.
Notation "∀* xs ● A" := (FForallList xs A)
                              (in custom formula at level 99, only parsing)
    :refiney_scope.

Notation "A [; xs \ ts ;]" := (seq_subst A xs ts)
                                (in custom formula at level 74, left associativity,
                                    xs custom seq_notation,
                                    ts custom term_seq_notation) : refiney_scope.

Definition subst_initials {M} A (w : gset final_variable) : (formula (value M)) :=
  simult_subst A (set_to_map (λ x, (₀x, (TVar x))) w).
