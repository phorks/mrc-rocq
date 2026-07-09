From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From stdpp Require Import listset.
From MRC Require Export PredCalc.

Inductive Value :=
  | VUnit
  | VNat (n : nat)
  | VInt (i : Z)
  | VReal (r : R)
  | VStr (s : string)
  | VPair (v1 v2 : Value)
  | VSeq (l : list Value)
  | VBag (s : listset Value)
  | VUnknown.

Inductive FSym :=
  | FSum
  | FSub
  | FMul
  | FSqrt
  | FFloor
  | FLen (* #as *)
  | FConcat (* as ++ bs *)
  | FIndex (* as[i] *)
  | FToBag (* bag as *)
  | FPrefix (* as↑n *)
  | FSuffix (* as↓n *)
.

Global Instance FSym_EqDecision : EqDecision FSym.
Proof. solve_decision. Qed.

Inductive PSym :=
  | Lt
  | In
  | IsUnit
  | IsNat
  | IsInt
  | IsReal.

Global Instance PSym_EqDecision : EqDecision PSym.
Proof. solve_decision. Qed.

Definition Symbols := Model.mkSymbols FSym FSym_EqDecision PSym PSym_EqDecision.

Notation Term := (term Value Symbols).
Notation Formula := (formula Value Symbols).

Inductive FSum_rel : list Value → Value → Prop :=
  | FSum_IntInt : ∀ i1 i2, FSum_rel [VInt i1; VInt i2] (VInt (i1 + i2))
  | FSum_IntReal : ∀ i r, FSum_rel [VInt i; VReal r] (VReal (IZR i + r))
  | FSum_RealInt : ∀ r i, FSum_rel [VReal r; VInt i] (VReal (r + IZR i))
.

Inductive FSum_rel_total : list Value → Value → Prop :=
  | FSum_Total : ∀ args v, (FSum_rel args v ∨ v = VUnknown ∧ ∀ v', ¬ FSum_rel args v') → FSum_rel_total args v.

Program Definition FSum_fdef : @Model.fdef Value := {| Model.fdef_rel := FSum_rel |}.
Next Obligation.
  inversion H; inversion H0; try congruence.
Qed.
Next Obligation.


Proof.
  refine {[ Model.fdef_rel = FSum_rel ]}.

Inductive Value_Ty :=
  | TEmpty
  | TUnit
  | TNat
  | TInt
  | TReal
  | TStr
  | TPair (τ1 τ2 : Value_Ty)
  | TList (τ : Value_Ty)
  | TSet (τ : Value_Ty)
  | TRel (τ1 τ2 : Value_Ty)
  | TFun (τ1 τ2 : Value_Ty)
  | TFinSet (τ : Value_Ty) (* finite powerset *)
  | TSetComp (τ : Value_Ty) (P : Term → Formula)
  | TUnion (τ1 τ2 : Value_Ty)
  | TIntersection (τ1 τ2 : Value_Ty)
  | TSubtraction (τ1 τ2 : Value_Ty).

Definition Model := Model.mkModel Value Value_Ty VUnknown Symbols.

Fixpoint hastype (v : Value) (τ : Value_Ty) : Formula :=
  match v, τ with
  | VUnit, TUnit => <! true !>
  | VNat _, TNat => <! true !>
  | VInt _, TInt => <! true !>
  | VReal _, TReal => <! true !>
  | VStr _, TStr => <! true !>
  | VPair v1 v2, TPair τ1 τ2 => <! $(hastype v1 τ2) ∧ $(hastype v2 τ2) !>
  | _, _ => <! false !> end.
  | VList l, TList τ => ∀ v, v ∈ l → hastype v τ (* define contains as a function symbol and ∈ notation for formula *)
  | VFinSet s, TFinSet τ =>  ∀ v, v ∈ l → hastype v τ (* define contains as a function symbol and ∈ notation for formula *)
  | VFinSet s, TFinRel τ1 τ2 => hastype v (TSet (τ1 * τ2))
  | VFinSet s, TFun τ1 τ2 => hastype v (TRel τ1 τ2) ∧ ∀ a b1 b2, (a, b1) ∈ s → (a, b2) ∈ s → b1 = b2
  | VFinSet s, TSet τ => ∀ v, v ∈ s → hastype v τ
  | _, TSetComp τ P => hastype v τ ∧ P v
  | _, TUnion τ1 τ2 => hastype v τ1 ∨ hastype v τ2
  | _, TIntersection τ1 τ2 => hastype v τ1 ∧ hastype v τ2
  | _, TSubtraction τ1 τ2 => hastype v τ1 ∧ ¬ hastype v τ2
  | _, _ => false
  end.

Inductive hastype : value → value_ty → Prop :=
  | VTUnit : hastype VUnit TUnit
  | VTNat n : hastype (VNat n) TNat
  | VTInt i : hastype (VInt i) TInt
  | VTReal r : hastype (VReal r) TReal
  | VTStr s : hastype (VStr s) TStr
  | VTPair v1 v2 τ1 τ2 : hastype v1 τ1 → hastype v2 τ2 → hastype (VPair v1 v2) (TPair τ1 τ2)
  | VTList (τ : value_ty)
  | VTSet (τ : value_ty)
  | VTRel (τ1 τ2 : value_ty)
  | VTFun (τ1 τ2 : value_ty)
  | VTPow (τ : value_ty)
  | VTSetComp (τ : value_ty) (P : variable → formula value)
  | VTUnion (τ1 τ2 : value_ty)
  | VTIntersection (τ1 τ2 : value_ty)
  | VTSubtraction (τ1 τ2 : value_ty).

Lemma value_hastype_det : ∀ (v : value) (τ1 τ2 : value_ty),
    v ∈ τ1 → v ∈ τ2 → τ1 = τ2.
Proof.
  intros v τ1 τ2 H1 H2. unfold elem_of, value_ty_elem_of, value_has_type.
  rewrite value_elem_of_iff_typeof_eq in H1, H2.
  apply bool_decide_unpack in H1, H2. subst. reflexivity.
Qed.
