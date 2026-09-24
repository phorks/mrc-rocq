From stdpp Require Import base.

Class Smp P Q := { smp_smp : P ↔ Q  }.
Class SmpHyp P Q := { smp_hyp : P → Q }.
Class SmpHypKeep P Q := { smp_hyp_keep : P → Q }.
Class SmpGoal P Q := { smp_goal : Q → P }.

Global Hint Mode Smp + - : typeclass_instances.
Global Hint Mode SmpHyp + - : typeclass_instances.

Global Instance smp_hyp_default {P Q} `{Smp P Q} : SmpHyp P Q | 100 :=
  {| smp_hyp := proj1 smp_smp |}.

Global Instance smp_goal_default {P Q} `{Smp P Q} : SmpGoal P Q | 100 :=
  {| smp_goal := proj2 smp_smp |}.

Definition smp_rw1 `{Smp P Q} : P → Q := proj1 smp_smp.
Definition smp_rw2 `{Smp P Q} : Q → P := proj2 smp_smp.

Tactic Notation "smp" :=
  let rec rw_hyps :=
    try match goal with
    | H : ?P |- _ =>
       lazymatch type of P with
       | Prop =>
          let temp := fresh "temp" in
          tryif (assert (temp:=smp_hyp_keep H)) then
            revert temp; revert H;
            first [rw_hyps; intros H; let H' := fresh H in intros H' | fail]
          else
            (try first [apply smp_hyp in H | apply smp_rw1 in H]);
            revert H;
            first [rw_hyps; intros H | intros H; fail 1]
       | _ => fail
       end
    end in
  try first [apply smp_goal | apply smp_rw2]; rw_hyps; simpl in *.
