From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From MRC Require Import Prelude.
From MRC Require Import Tactics.
From MRC Require Import Stdppp.
From MRC Require Import Model.
From MRC Require Import PredCalc.Basic.
Import EqNotations.

Class ModelWithSum (M : model) := sum_sym : model_fsym M.

Definition term_sum {M} `{ModelWithSum M} (t u : termM M) : termM M :=
  TApp sum_sym [t; u].

Notation "t + u" := (term_sum t u)
                      (in custom term at level 50,
                          t custom term,
                          u custom term,
                          left associativity) : refiney_scope.

Class ModelWithSub (M : model) := sub_sym : model_fsym M.

Definition term_sub {M} `{ModelWithSub M} (t u : termM M) : termM M :=
  TApp sub_sym [t; u].

Notation "t - u" := (term_sub t u)
                      (in custom term at level 50,
                          t custom term,
                          u custom term,
                          left associativity) : refiney_scope.

Class ModelWithMul (M : model) := mul_sym : model_fsym M.
Definition term_mul {M} `{ModelWithMul M} (t u : termM M) : termM M :=
  TApp mul_sym [t; u].

Notation "t * u" := (term_mul t u)
                      (in custom term at level 50,
                          t custom term,
                          u custom term,
                          left associativity) : refiney_scope.

Class ModelWithOrder (M : model) := {
  lt_sym : model_psym M;
  lt_pdef_arity : pdef_arity (pdefs M lt_sym) = 2;
}.

Definition lt_pdef_rel {M : model} (v1 v2 : value M) `{ModelWithOrder M} : Prop.
Proof.
  pose proof (pdef_rel (pdefs M lt_sym)). rewrite lt_pdef_arity in X. apply (X [# v1; v2]).
Defined.

Definition term_lt {M} `{ModelWithOrder M} (t u : termM M) : formulaM M :=
  FAtom (AT_Pred lt_sym [t; u]).

Definition term_le {M} `{ModelWithOrder M} (t u : termM M) : formulaM M :=
  FOr (term_lt t u) (FAtom (AT_Eq t u)).

Definition term_gt {M} `{ModelWithOrder M} (t u : termM M) : formulaM M :=
  term_lt u t.

Definition term_ge {M} `{ModelWithOrder M} (t u : termM M) : formulaM M :=
  term_le u t.

Notation "t = u" := (FAtom (AT_Eq t u))
                      (in custom term_relation at level 60,
                          t custom term at level 60,
                          u custom term at level 60,
                          no associativity) : refiney_scope.
Notation "t '≠' u" := (FNot (FAtom (AT_Eq t u)))
                       (in custom term_relation at level 60,
                           t custom term at level 60,
                           u custom term at level 60,
                           no associativity) : refiney_scope.

Notation "t < u" := (term_lt t u)
                      (in custom term_relation at level 60,
                          t custom term at level 60,
                          u custom term at level 60,
                          no associativity) : refiney_scope.

Notation "t ≤ u" := (term_le t u)
                      (in custom term_relation at level 60,
                          t custom term at level 60,
                          u custom term at level 60,
                          no associativity) : refiney_scope.

Notation "t > u" := (term_gt t u)
                      (in custom term_relation at level 60,
                          t custom term at level 60,
                          u custom term at level 60,
                          no associativity) : refiney_scope.

Notation "t ≥ u" := (term_ge t u)
                      (in custom term_relation at level 60,
                          t custom term at level 60,
                          u custom term at level 60,
                          no associativity) : refiney_scope.

Class ModelWithNat (M : model) := {
  nat_to_value : nat → value M;
  nat_ty : value_ty M;
  nat_to_value_ty : ∀ n, hastype M (nat_to_value n) nat_ty;
  value_to_nat : value M → option nat;
  hastype_nat_ty : ∀ v, hastype M v nat_ty ↔ ∃ n, value_to_nat v = Some n;
  value_to_nat_nat_to_value : ∀ n, value_to_nat (nat_to_value n) = Some n;
  nat_with_sum :: ModelWithSum M;
  nat_sum_fdef : ∀ v1 v2 n1 n2,
      value_to_nat v1 = Some n1 →
      value_to_nat v2 = Some n2 →
      fn_eval sum_sym [v1; v2] (nat_to_value (n1 + n2));
  nat_with_sub :: ModelWithSub M;
  nat_sub_fdef : ∀ v1 v2 n1 n2,
      value_to_nat v1 = Some n1 →
      value_to_nat v2 = Some n2 →
      fn_eval sub_sym [v1; v2] (nat_to_value (n1 - n2));
  nat_with_mul :: ModelWithMul M;
  nat_mul_fdef : ∀ v1 v2 n1 n2,
      value_to_nat v1 = Some n1 →
      value_to_nat v2 = Some n2 →
      fn_eval mul_sym [v1; v2] (nat_to_value (n1 * n2));
  nat_with_order :: ModelWithOrder M;
  nat_lt_pdef : ∀ v1 v2 n1 n2,
      value_to_nat v1 = Some n1 →
      value_to_nat v2 = Some n2 →
      lt_pdef_rel v1 v2 ↔ n1 < n2;
}.

Notation ℕ := (@nat_ty _).
