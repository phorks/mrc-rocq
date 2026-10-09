From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From MRC Require Import Prelude.
From MRC Require Import Lib.

Record fdef {value} `{Bottom value} := mkFdef {
  (* fdef_sig : list value → value_ty; *)
  fdef_rel : list value → value → Prop;
  (* fdef_typing : ∀ args v, fdef_rel args v → hastype v (fdef_sig args); *)
  fdef_det : ∀ {args v1 v2}, fdef_rel args v1 → fdef_rel args v2 → v1 = v2;
  fdef_known : ∀ args, ¬ fdef_rel args ⊥;
  (* fdef_total : ∀ args, ∃ v, fdef_rel args v; *)
}.

Record pdef {value} := mkPdef {
  pdef_arity : nat;
  pdef_rel : vec value pdef_arity → Prop;
}.

(* A (first-order) language (or signature) minus the arity function  *)
Record signature := mkSignature {
  sgn_fsym : Type;
  sgn_fsym_EqDecision : EqDecision sgn_fsym;
  sgn_psym : Type;
  sgn_psym_EqDecision : EqDecision sgn_psym;
}.

Record model := mkModel {
  value : Type;
  value_bottom :: Bottom value;
  is_bottom_dec :: ∀ v : value, Decision (v = ⊥);
  value_ty : Type;
  hastype : value → value_ty → Prop;
  ty_unknown :: Top value_ty;
  hastype_unknown : ∀ v, hastype v ⊤;
  model_sgn : signature;
  fdefs : sgn_fsym model_sgn → @fdef value _;
  pdefs : sgn_psym model_sgn → @pdef value;
}.

Global Notation model_fsym M := (sgn_fsym (model_sgn M)).
Global Instance model_fsym_EqDecision {M} : EqDecision (model_fsym M) :=
  (sgn_fsym_EqDecision (model_sgn M)).

Global Notation model_psym M := (sgn_psym (model_sgn M)).
Global Instance model_psym_EqDecision {M} : EqDecision (model_psym M) :=
  (sgn_psym_EqDecision (model_sgn M)).

(* Global Instance model_value_bottom {M} : Bottom (value M) := value_bottom M. *)
Global Instance model_value_Inhabited {M} : Inhabited (value M) :=
  populate (value_bottom M).
