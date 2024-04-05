From MRC Require Import PredCalc.

Theorem and_comm : forall f1 f2 fctx pctx,
  formula_equiv <[ f1 /\ f2 ]> <[ f2 /\ f1 ]> fctx pctx.
Proof. 
  intros f1 f2 fctx pctx. split; intros val st H.
  - destruct val.
    + right. inversion H; subst.
      rewrite Bool.andb_comm. apply FEval_And; assumption.
    + left. reflexivity.
  - destruct val.
    + right. inversion H; subst.
      apply Bool.andb_true_iff in H2 as [Hf1 Hf2].
      apply FEval_And; subst; assumption. 
    + left. reflexivity.
Qed.

Theorem or_comm : forall f1 f2 fctx pctx,
  formula_equiv <[ f1 \/ f2 ]> <[ f2 \/ f1 ]> fctx pctx.
Proof.
  intros f1 f2 fctx pctx. split; intros val st H.
  - inversion H; subst.
    + right. apply FEval_Or2. assumption.
    + right. apply FEval_Or1. assumption.
    + left. reflexivity.
  - inversion H; subst.
    + right. apply FEval_Or2. assumption.
    + right. apply FEval_Or1. assumption.
    + left. reflexivity.
Qed.

Theorem and_idemp : forall f fctx pctx,
  formula_equiv <[ f /\ f ]> <[ f ]> fctx pctx.
Proof.
  intros f fctx pctx. split; intros val st H.
  - destruct val; auto. right. inversion H; subst.
    apply Bool.andb_true_iff in H2 as [H2 H2'].
    subst. simpl. assumption.
  - destruct val; auto. right. 
    replace true with (andb true true) by reflexivity.
    apply FEval_And; assumption.
Qed.

Theorem or_idemp : forall f fctx pctx,
  formula_equiv <[ f \/ f ]> <[ f ]> fctx pctx.
Proof.
  intros f fctx pctx. split; intros val st H.
  - destruct val; auto. right. inversion H; subst; auto.
  - destruct val; auto. right. 
    replace true with (orb true true) by reflexivity.
    apply FEval_Or1; assumption.
Qed.