From Stdlib Require Import Lists.List. Import ListNotations.
From stdpp Require Import base gmap.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.

Section prog.
Context {M : model}.

Definition state := gmap variable (value M).
Definition formula := state → Prop.

Implicit Types x : variable.
Implicit Types A B : formula.
Implicit Types v : value M.

Global Instance f_equiv : Equiv formula := λ A B, ∀ σ, A σ = B σ.

Definition f_subst A x v : formula := λ σ, A (<[x:=v]> σ).
Definition is_free x A := ∀ v, f_subst A x v ≡ A.

Definition f_not A := λ σ, ¬ A σ.
Definition f_and A B := λ σ, A σ ∧ B σ.
Definition f_or A B := λ σ, A σ ∨ B σ.
Definition f_exists x A := λ σ, ∃ v, f_subst A x v σ.
Definition f_forall x A := λ σ, ∀ v, f_subst A x v σ.

Declare Custom Entry formula.
Declare Scope formula_scope.
Declare Custom Entry formula_aux.
Delimit Scope formula_scope with formula.

Notation "<! e !>" := e (e custom formula_aux) : formula_scope.
Notation "e" := e (in custom formula_aux at level 0, e custom formula) : formula_scope.

Notation "( x )" := x (in custom formula, x at level 99) : formula_scope.
(* Notation "'`' f x .. y '`'" := (.. (f x) .. y) *)
(*                                   (in custom formula at level 0, only parsing, *)
(*                                       f constr at level 0, x constr at level 9, *)
(*                                       y constr at level 9) : formula_scope. *)
Notation "x" := x (in custom formula at level 0, x constr at level 0) : formula_scope.

Notation "x + y" := (TApp "+" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "x - y" := (TApp "-" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "x * y" := (TApp "*" (@cons term x (@cons term y nil))) (in custom formula at level 50, left associativity).
Notation "f '(' x ',' .. ',' y ')'" := (TApp f (@cons term x .. (@cons term y nil) ..)) (in custom formula at level 40).

Notation "'true'" := (AT_True) (in custom formula at level 0).
Notation "'false'" := (AT_False) (in custom formula at level 0).
Notation "x = y" := (AT_Eq x y) (in custom formula at level 70, no associativity).
Notation "x <> y" := (FNot (FSimple (AT_Eq x y))) (in custom formula at level 70, no associativity, only parsing).
Notation "x ≠ y" := (FNot (FSimple (AT_Eq x y))) (in custom formula at level 70, no associativity, only printing).
Notation "x < y" := (AT_Pred "<" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x <= y" := (AT_Pred "<=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x > y" := (AT_Pred ">" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "x >= y" := (AT_Pred ">=" (@cons term x (@cons term y nil))) (in custom formula at level 70, no associativity).
Notation "'¬' x" := (FNot x) (in custom formula at level 75).
Notation "x ∧ y" := (FAnd x y) (in custom formula at level 80, left associativity).
Notation "x ∨ y" := (FOr x y) (in custom formula at level 80, left associativity).
Notation "x => y" := (FImpl x y) (in custom formula at level 80, only parsing).
Notation "x ⇒ y" := (FImpl x y) (in custom formula at level 80, only printing).
Notation "x <=> y" := (FIff x y) (in custom formula at level 80, only parsing).
Notation "x ⇔ y" := (FIff x y) (in custom formula at level 80, only printing).
Notation "'exists' x .. y ',' A" := (FExists x .. (FExists y A) ..) (in custom formula at level 85, only parsing).
Notation "'∃' x .. y '●' A" := (FExists x .. (FExists y A) ..) (in custom formula at level 85, only printing).
Notation "'forall' x .. y ',' A" := (FForall x .. (FForall y A) ..) (in custom formula at level 85).
Global Notation "'∀' x .. y '●' A" := (FForall x .. (FForall y A) ..) (in custom formula at level 85).

  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).

  Record ni_formula := mkNiFormula {
    ni_formula_formula : formula;
    ni_formula_no_initials : ∀ x, x ∈ formula_fvars ni_formula_formula → var_is_initial x = false
  }.

  Global Coercion ni_formula_formula : ni_formula >-> formula.

  Inductive prog : Type :=
  | PAsgn (x : ni_variable) (t : term)
  | PSeq (p1 p2 : prog)
  | PIf (gcs : list gcom)
  | PDo (gcs : list gcom)
  | PSpec (w : list ni_variable) (pre : ni_formula) (post : formula)
  | PVar (x : variable) (p : prog)
  | PConst (x : variable) (p : prog)
  with gcom :=
  | GCom (g : formula) (p : prog).

  Definition gcom_guard (c : gcom) :=
    match c with
    | GCom a _ => a
    end.

  Definition gcom_cmd (c : gcom) :=
    match c with
    | GCom _ p => p
    end.

  Fixpoint gcoms_any_guard (gcoms : list gcom) : formula :=
    match gcoms with
    | [] => <! true !>
    | h::t => <! `gcom_guard h` ∨ `gcoms_any_guard t` !>
    end.

  Fixpoint gcoms_all_cmds (gcoms : list gcom) (a : formula) : formula :=
    match gcoms with
    | [] => <! true !>
    | h::t => <! (`gcom_guard h` => a) ∧ `gcoms_all_cmds t a` !>
    end.

  Fixpoint spec_post_wp (w : list ni_variable) post A : formula :=
    match w with
    | [] => <! post => A !>
    | h :: t => <! forall h, `spec_post_wp t post A` !>
    end.

  Fixpoint subst_initials A (w : list ni_variable) : formula :=
    match w with
    | [] => A
    | x :: xs => subst_initials (A[(x)₀ \ x]) xs
    end.

  Fixpoint wp (p : prog) (A : formula) : formula :=
    match p with
    | PAsgn x e => A[x \ e]
    | PSeq p1 p2 => wp p1 (wp p2 A)
    | PIf gcs => <! `gcoms_any_guard (gcs)` ∧ `gcoms_all_cmds (gcs) A` !>
    | PDo gcs => <! false !>
    | PSpec w pre post => <! pre ∧ `subst_initials (spec_post_wp w post A) w` !>
    | PVar x p => <! forall x, `wp p A` !>
    | PConst x p => <! exists x, `wp p A` !>
    end.

End prog.

Declare Custom Entry prog.
Declare Custom Entry gcom.
Declare Scope prog_scope.
Declare Custom Entry prog_aux.
Bind Scope prog_scope with prog.
Delimit Scope prog_scope with prog.

Notation "<{ e }>" := e (e custom prog_aux) : prog_scope.
Notation "e" := e (in custom prog_aux at level 0, e custom prog) : prog_scope.

Notation "( x )" := x (in custom prog, x at level 99) : prog_scope.
Notation "'`' x '`'" := (x)
                          (in custom prog at level 0, only parsing,
                              x constr at level 0) : prog_scope.
Notation "x" := x (in custom prog at level 0, x constr at level 0) : prog_scope.

Notation "x := e" := (PAsgn x e)
                       (in custom prog at level 95,  x constr at level 0,
                           e custom formula at level 85, no associativity) : prog_scope.

Notation "x ; y" := (PSeq x y)
                      (in custom prog at level 95, right associativity) : prog_scope.

Notation "x -> y" := (GCom x y)
                       (in custom gcom at level 60, x custom formula,
                           y custom prog,
                           no associativity) : prog_scope.

Notation "'if' | x | .. | y 'fi'" :=
  (PIf (cons (x) .. (cons (y) nil) ..))
    (in custom prog at level 95,
        x custom gcom,
        y custom gcom, no associativity) : prog_scope.

Notation "'do' | x | .. | y 'od'" :=
  (PDo (cons (x) .. (cons (y) nil) ..))
    (in custom prog at level 95,
        x custom gcom,
        y custom gcom, no associativity) : prog_scope.

Notation "x , .. , y : [ p , q ]" :=
  (PSpec (cons x .. (cons y nil) ..) p q)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y constr at level 0,
        p custom formula at level 85, q custom formula at level 85) : prog_scope.

Notation "'|[' 'var' x ',' y ']|' " :=
  (PVar x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog) : prog_scope.

Notation "'|[' 'const' x ',' y ']|' " :=
  (PConst x y)
    (in custom prog at level 95, no associativity,
        x constr at level 0, y custom prog at next level) : prog_scope.

Open Scope prog_scope.
