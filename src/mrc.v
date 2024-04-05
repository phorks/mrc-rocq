From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.


Inductive prog :=
  | PAsgn (x : string) (e : term)
  | PSeq (p1 p2 : prog)
  | PIf (h : gcom) (t : list gcom)
  | PSpec (w : list string) (pre post : formula)
with gcom :=
  | GCom (a : formula) (p : prog).

Definition guard (c : gcom) :=
  match c with
  | GCom a _ => a
  end.

Definition cmd (c : gcom) :=
  match c with
  | GCom _ p => p
  end.  

Fixpoint gcoms_any_guard (gcoms : list gcom) : formula :=
  match gcoms with 
  | [] => <[ true ]>
  | h::t => <[ `guard h` \/ `gcoms_any_guard t` ]>
  end.

Fixpoint gcoms_all_cmds (gcoms : list gcom) (a : formula) : formula :=
  match gcoms with
  | [] => <[ true ]>
  | h::t => <[ (`guard h` => a) /\ `gcoms_all_cmds t a` ]>
  end.

Fixpoint wp (p : prog) (A : formula) : formula :=
  match p with
  | PAsgn x e => subst x e A
  | PSeq p1 p2 => wp p1 (wp p2 A)
  | PIf h t => gcoms_any_guard (h::t) /\ gcoms_all_cmds (h :: t) A
  | PSpec [] pre post => pre /\ post
  | _ => A
  end.  