From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From MRC Require Import PredCalc.
From MRC Require Import FormulaProps.
From MRC Require Import Prog.


Open Scope general_fassertion_scope.
Definition refines (p1 p2 : prog) fctx pctx :=
  forall A,
    (forall x, is_free_in (initsym x) A = false) ->
    formula_implies (wp p1 A) (wp p2 A) fctx pctx.

Declare Scope general_refinement_scope.
Notation "x '[=' y" := (forall fctx pctx, refines x y fctx pctx) 
    (in custom prog at level 60, 
    x custom prog,
    y custom prog at level 95,
    only parsing)
  : general_refinement_scope.

Notation "x '⊑' y" := (forall fctx pctx, refines x y fctx pctx) 
    (in custom prog at level 60, 
    x custom prog,
    y custom prog at level 95,
    only printing,
    format "x  '⊑'  y")
  : general_refinement_scope.  

Open Scope general_refinement_scope.

Theorem assignment : forall pre post w E,
  pre ==> post[w \ E] ->
  <{ w : [pre, post] [= w := E }>.
  intros pre post w E H. unfold refines. intros fctx pctx A H0.
  simpl. 
Qed.

Compute wp <{ x : [1 < 2, 2 < 3] }> <[ 5 = 7 ]>.

Theorem strengthen_post : forall pre post post' w,
  post' ==> post ->
  <{ w : [pre, post] [= w : [pre, post'] }>.
Proof.
  intros pre post post' w H. unfold refines. intros fctx pctx A.
  simpl.  


