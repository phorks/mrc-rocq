From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From MRC Require Import Maps.

Inductive aexp :=
  | AValue {X:Type} (value: X)
  | AVar (x : string)
  | ASymbol {X:Type} (symbol: X).

Definition state := total_map aexp.
Definition Assertion := state -> Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "'forall' x, P" := (fun st => forall x, assert P st) (at level 80) : assertion_scope.
(* Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope. *)
(* Open Scope assertion_scope. *)

Definition ATrue : Assertion := fun st => True.

Inductive prog :=
  | PAsgn (x : string) (e : aexp)
  | PSeq (p1 p2 : prog)
  | PIf (h : gcom) (t : list gcom)
  | PSpec (w : list string) (pre post : Assertion)
with gcom :=
  | GCom (a : Assertion) (p : prog).

Definition subst (x : string) (e : aexp) (a : Assertion) :=
  fun st => a (x !-> e; st).

Definition guard (c : gcom) :=
  match c with
  | GCom a _ => a
  end.

Definition cmd (c : gcom) :=
  match c with
  | GCom _ p => p
  end.

Fixpoint gcoms_any_guard (gcoms : list gcom) : Assertion :=
  match gcoms with 
  | [] => ATrue
  | h::t => (guard h) \/ gcoms_any_guard t
  end.

Fixpoint gcoms_all_cmds (gcoms : list gcom) (a : Assertion) : Assertion :=
  match gcoms with
  | [] => ATrue
  | h::t => (guard h -> a) /\ (gcoms_all_cmds t a)
  end.

Fixpoint wp (p : prog) (A : Assertion) : Assertion :=
  match p with
  | PAsgn x e => subst x e A
  | PSeq p1 p2 => wp p1 (wp p2 A)
  | PIf h t => gcoms_any_guard (h::t) /\ gcoms_all_cmds (h :: t) A
  | PSpec [] pre post => pre /\ post
  | _ => A
  end.
  


Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition t : string := "t".

Parameter floor : nat -> nat.
Parameter sqrt : nat -> nat.

Axiom sqrt_definition : forall (m n : nat),
    m = sqrt n <-> m*m = n.

Axiom floor_definition : forall (m n : nat),
    m = floor n <-> m <= n < m + 1.

Example sqrt_81 : 9 = sqrt 81.
    apply sqrt_definition. lia.
Qed.

Example sqrt_82 : 9 = sqrt 82.
    apply sqrt_definition.
Abort.

Example floor_sqrt_82 : 9 = floor (sqrt 82).
    apply floor_definition. simpl. 
    assert (H: 9 = floor (sqrt 81)).
    { apply floor_definition. rewrite <- sqrt_81. lia.  }
    apply floor_definition in H. lia.

Example sqrt_82 : sqrt 9 82.
Proof.
    apply n_sqrt. simpl. lia.
Qed.

Inductive com : Type :=
    | eq (x : string) (v: Prop).
    | 

Axiom sqrt_definition : forall (x : string) (n: nat),
     eq x (sqrt n) <-> n * n <= m < (n+1)*(n+1).