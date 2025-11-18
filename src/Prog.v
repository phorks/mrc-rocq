From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From stdpp Require Import base gmap.
From MRC Require Import Options.
From MRC Require Import Tactics.
From MRC Require Import Model.
From MRC Require Import Stdppp.
From MRC Require Import PredCalc.

Section prog.
  Context {M : model}.
  Local Notation term := (term (value M)).
  Local Notation formula := (formula (value M)).

  Inductive prog : Type :=
  | PAsgn (x : final_variable) (t : term)
  | PSeq (p1 p2 : prog)
  | PIf (gcmds : list (formula * prog))
  | PWhile (g : formula) (p: prog) (inv : formula) (variant : variable)
  | PSpec (w : list ni_variable) (pre : final_formula) (post : formula)
  | PVar (x : variable) (p : prog)
  | PConst (x : variable) (p : prog).

  Fixpoint modified_ni_vars p : list ni_variable :=
    match p with
    | PAsgn x t => [x]
    | PSeq p1 p2 => modified_ni_vars p1 ++ modified_ni_vars p2
    | PIf gcmds => mjoin ((modified_ni_vars ∘ snd) <$> gcmds)
    | PWhile _ p _ _ => modified_ni_vars p
    | PSpec w pre post => w
    | PVar x p => modified_ni_vars p
    | PConst x p => modified_ni_vars p
    end.

  Definition modified_vars p : list variable := ni_var_var <$> modified_ni_vars p.

  Fixpoint prog_fvars p : gset variable :=
    match p with
    | PAsgn x t => {[ni_var_var x]}
    | PSeq p1 p2 => prog_fvars p1 ∪ prog_fvars p2
    | PIf gcmds => ⋃ ((prog_fvars ∘ snd) <$> gcmds)
    | PWhile _ p _ _ => prog_fvars p
    | PSpec w pre post => list_to_set (ni_var_var <$> w) ∪ formula_fvars pre ∪ formula_fvars post
    | PVar x p => prog_fvars p ∖ {[x]}
    | PConst x p => prog_fvars p ∖ {[x]}
  end.

  Fixpoint any_guard (gcmds : list (formula * prog)) : formula :=
    match gcmds with
    | [] => <! true !>
    | (g, _)::cmds => <! g ∨ `any_guard cmds` !>
    end.

  Fixpoint all_cmds (gcmds : list (formula * prog)) (A : formula) : formula :=
    match gcmds with
    | [] => <! true !>
    | (g, _)::cmds => <! (g => A) ∧ `all_cmds cmds A` !>
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
    | PIf gcs => <! `any_guard (gcs)` ∧ `all_cmds (gcs) A` !>
    | PWhile g p inv v =>
        let x := fresh_var (raw_var "x") (formula_fvars inv ∪ prog_fvars p ∪ formula_fvars A) in
        <! forall* `modified_vars p`,
            (inv ∧ g => `wp p inv`) ∧
            (inv ∧ ¬ g => A) ∧
            (inv ∧ g ∧ v = x => `wp p (<! v < x !>)`) !>
    | PSpec w pre post => <! pre ∧ `subst_initials (spec_post_wp w post A) w` !>
    | PVar x p => <! forall x, `wp p A` !>
    | PConst x p => <! exists x, `wp p A` !>
    end.

End prog.

Declare Custom Entry prog.
Declare Custom Entry gcmd.
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

Notation "x -> y" := ((x, y))
                       (in custom gcmd at level 60, x custom formula,
                           y custom prog,
                           no associativity) : prog_scope.

Notation "'if' | x | .. | y 'fi'" :=
  (PIf (cons (x) .. (cons (y) nil) ..))
    (in custom prog at level 95,
        x custom gcmd,
        y custom gcmd, no associativity) : prog_scope.

Notation "'while' g 'do' p 'invariant' i 'variant' v 'end'" :=
  (PWhile g p i v)
    (in custom prog at level 95,
        g custom formula, p custom prog, i custom formula, no associativity) : prog_scope.

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
