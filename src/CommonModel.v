From Stdlib Require Import Reals.Reals.
From Coq Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From stdpp Require Import listset.


Parameter variable : Type.
Parameter formula : Type → Type.

Inductive value :=
  | VUnit
  | VNat (n : nat)
  | VInt (i : Z)
  | VReal (r : R)
  | VStr (s : string)
  | VPair (v1 v2 : value)
  | VList (l : list value)
  | VFinSet (s : listset value).

Inductive value_ty :=
  | TEmpty
  | TUnit
  | TNat
  | TInt
  | TReal
  | TStr
  | TPair (τ1 τ2 : value_ty)
  | TList (τ : value_ty)
  | TSet (τ : value_ty)
  | TRel (τ1 τ2 : value_ty)
  | TFun (τ1 τ2 : value_ty)
  | TFinSet (τ : value_ty) (* finite powerset *)
  | TSetComp (τ : value_ty) (P : value → formula value)
  | TUnion (τ1 τ2 : value_ty)
  | TIntersection (τ1 τ2 : value_ty)
  | TSubtraction (τ1 τ2 : value_ty).

Fixpoint hastype (v : value) (τ : value_ty) : formula value :=
  match v, τ with
  | VUnit, TUnit => true
  | VNat _, TNat => true
  | VInt _, TInt => true
  | VReal _, TReal => true
  | VStr _, TStr => true
  | VPair v1 v2, TPair τ1 τ2 => hastype v1 v2 && hastype v1 v2
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
