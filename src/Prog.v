From Stdlib Require Import Lists.List. Import ListNotations.
From stdpp Require Import base.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.

Section prog.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).

  Record ni_formula := mkNiFormula {
    ni_formula_formula : formula;
    ni_formula_no_initials : ∀ x, x ∈ formula_fvars ni_formula_formula → var_is_initial x = false
  }.

  Global Coercion ni_formula_formula : ni_formula >-> formula.

  Inductive prog : Type :=
  | PAsgn (x : variable) (t : term)
  | PSeq (p1 p2 : prog)
  | PIf (gcs : list gcom)
  | PDo (gcs : list gcom)
  | PSpec (w : list variable) (pre : ni_formula) (post : formula)
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

  Fixpoint spec_post_wp (w : list variable) post A : formula :=
    match w with
    | [] => <! post => A !>
    | h :: t => <! forall h, `spec_post_wp t post A` !>
    end.

  Fixpoint subst_initials A (w : list variable) : formula :=
    match w with
    | [] => A
    | x :: xs => subst_initials (A[x \ (var_non_initial x)]) xs
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
