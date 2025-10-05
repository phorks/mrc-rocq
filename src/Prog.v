From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Init.Nat.
From MRC Require Import PredCalc.

Inductive prog : Type :=
  | PAsgn (x : string) (e : term)
  | PSeq (p1 p2 : prog)
  | PIf (gcs : list gcom)
  | PDo (gcs : list gcom)
  | PSpec (w : list string) (pre post : formula)
  | PVar (x : string) (p : prog)
  | PConst (x : string) (p : prog)
with gcom :=
  | GCom (g : formula) (p : prog).

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
  | [] => <[ true ]>
  | h::t => <[ `gcom_guard h` \/ `gcoms_any_guard t` ]>
  end.

Fixpoint gcoms_all_cmds (gcoms : list gcom) (a : formula) : formula :=
  match gcoms with
  | [] => <[ true ]>
  | h::t => <[ (`gcom_guard h` => a) /\ `gcoms_all_cmds t a` ]>
  end.

Fixpoint spec_post_wp (w : list string) post A :=
  match w with
  | [] => <[ post => A ]>
  | h :: t => <[ forall h, `spec_post_wp t post A` ]>
  end.

Definition initsym x :=
  append x "_0"%string.

Definition is_initsym x := 
  let l := String.length x in
  if 3 <? l
    then String.eqb (substring (l - 2) 2 x) "_0"
    else false.
  

Fixpoint subst_initials f (w : list string) :=
  match w with
  | [] => f
  | h :: t =>
    let h0 := initsym h in
    <[ (`subst_initials f t`)[h0 \ h] ]>
  end.

Fixpoint wp (p : prog) (A : formula) : formula :=
  match p with
  | PAsgn x e => A[x \ e]
  | PSeq p1 p2 => wp p1 (wp p2 A)
  | PIf gcs => <[ `gcoms_any_guard (gcs)` /\ `gcoms_all_cmds (gcs) A` ]>
  | PDo gcs => <[ false ]>
  | PSpec w pre post => <[ pre /\ `subst_initials (spec_post_wp w post A) w` ]>
  | PVar x p => <[ forall x, `wp p A` ]>
  | PConst x p => <[ exists x, `wp p A` ]>
  end.
